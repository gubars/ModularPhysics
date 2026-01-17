import ModularPhysics.Core.ClassicalFieldTheory.EulerLagrange

namespace ModularPhysics.Core.ClassicalFieldTheory

open SpaceTime

/-- Noether current j^μ associated with continuous symmetry -/
axiom noetherCurrent {F : Type*}
  (phi : ClassicalField F)
  (symmetry : ClassicalField F → ClassicalField F) :
  SpaceTimePoint → Fin 4 → ℝ

/-- Noether's theorem: continuous symmetry → conserved current

    If δL = ∂_μ K^μ under symmetry transformation, then
    ∂_μ j^μ = 0 (on-shell)
-/
axiom noether_theorem {F : Type*}
  (phi : ClassicalField F)
  (symmetry : ClassicalField F → ClassicalField F)
  (h : eulerLagrange phi)
  (x : SpaceTimePoint)
  (nu : Fin 4) :
  ∑ mu, partialDerivative (fun y => noetherCurrent phi symmetry y mu) mu x = 0

/-- Conserved charge Q = ∫ j⁰ d³x -/
axiom conservedCharge {F : Type*}
  (phi : ClassicalField F)
  (symmetry : ClassicalField F → ClassicalField F) : ℝ

/-- Time translation → energy conservation -/
axiom energy_from_time_translation {F : Type*} (phi : ClassicalField F)
  (x : SpaceTimePoint) :
  ∃ (time_translation : ClassicalField F → ClassicalField F),
    conservedCharge phi time_translation = noetherCurrent phi time_translation x 0

/-- Spatial translation → momentum conservation -/
axiom momentum_from_spatial_translation {F : Type*} (phi : ClassicalField F) (i : Fin 3)
  (x : SpaceTimePoint) :
  ∃ (spatial_translation : ClassicalField F → ClassicalField F),
    conservedCharge phi spatial_translation = noetherCurrent phi spatial_translation x i.succ

end ModularPhysics.Core.ClassicalFieldTheory
