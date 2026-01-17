import ModularPhysics.Core.ClassicalFieldTheory.Noether
import ModularPhysics.Core.SpaceTime.Metrics

namespace ModularPhysics.Core.ClassicalFieldTheory

open SpaceTime

/-- Canonical energy-momentum tensor T^μν -/
axiom energyMomentumTensor (F : Type*) :
  ClassicalField F → SpaceTimePoint → Fin 4 → Fin 4 → ℝ

/-- Belinfante-Rosenfeld tensor (symmetric, gauge-invariant) -/
axiom belinfanteRosenfeld (F : Type*) :
  ClassicalField F → SpaceTimePoint → Fin 4 → Fin 4 → ℝ

/-- Energy-momentum conservation: ∂_μ T^μν = 0 (flat spacetime) -/
axiom energy_momentum_conservation {F : Type*} (phi : ClassicalField F)
    (h : eulerLagrange phi)
    (x : SpaceTimePoint) (nu : Fin 4) :
  ∑ mu, partialDerivative (fun y => energyMomentumTensor F phi y mu nu) mu x = 0

/-- Covariant conservation in curved spacetime: ∇_μ T^μν = 0 -/
axiom covariant_energy_momentum_conservation {F : Type*}
    (metric : SpacetimeMetric) (phi : ClassicalField F)
    (x : SpaceTimePoint) (nu : Fin 4) :
  ∑ mu, covariantDerivative metric (fun y => energyMomentumTensor F phi y mu nu) mu x = 0

/-- Total energy E = ∫ T⁰⁰ d³x -/
axiom totalEnergy {F : Type*} (phi : ClassicalField F) : ℝ

/-- Total momentum P^i = ∫ T⁰ⁱ d³x -/
axiom totalMomentum {F : Type*} (phi : ClassicalField F) : Fin 3 → ℝ

/-- Total angular momentum J^ij = ∫ (x^i T⁰ʲ - x^j T⁰ⁱ) d³x -/
axiom totalAngularMomentum {F : Type*} (phi : ClassicalField F) : Fin 3 → ℝ

/-- Perfect fluid stress-energy tensor: T_μν = (ρ + p)u_μ u_ν + p g_μν -/
def perfectFluidStressEnergy (metric : SpacetimeMetric)
    (ρ p : SpaceTimePoint → ℝ)  -- energy density and pressure
    (u : SpaceTimePoint → Fin 4 → ℝ)  -- 4-velocity
    : TensorField 4 4 :=
  fun x μ ν => (ρ x + p x) * u x μ * u x ν + p x * metric.g x μ ν

end ModularPhysics.Core.ClassicalFieldTheory
