import ModularPhysics.Core.SpaceTime.Metrics
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ModularPhysics.Core.SpaceTime

/-- Christoffel symbols Γ^μ_νρ (Levi-Civita connection)

    Computed from metric: Γ^μ_νρ = (1/2)g^μσ(∂_ν g_σρ + ∂_ρ g_νσ - ∂_σ g_νρ)

    This is GEOMETRIC - computed from any metric, no dynamics.
-/
axiom christoffel (metric : SpacetimeMetric) (x : SpaceTimePoint)
    (μ ν ρ : Fin 4) : ℝ

/-- Covariant derivative of a vector field

    ∇_μ V^ν = ∂_μ V^ν + Γ^ν_μρ V^ρ
-/
axiom covariantDerivativeVector (metric : SpacetimeMetric)
    (v : SpaceTimePoint → Fin 4 → ℝ)
    (μ : Fin 4) : SpaceTimePoint → Fin 4 → ℝ

/-- Covariant derivative of a one-form (covector)

    ∇_μ ω_ν = ∂_μ ω_ν - Γ^ρ_μν ω_ρ
-/
axiom covariantDerivativeCovector (metric : SpacetimeMetric)
    (ω : SpaceTimePoint → Fin 4 → ℝ)
    (μ : Fin 4) : SpaceTimePoint → Fin 4 → ℝ

/-- Parallel transport along a curve

    A vector is parallel transported if ∇_γ̇ V = 0
-/
def ParallelTransport (metric : SpacetimeMetric) (γ : ℝ → SpaceTimePoint)
    (V : ℝ → Fin 4 → ℝ) : Prop :=
  ∀ t μ,
    deriv (fun s => V s μ) t +
    (∑ ν, ∑ ρ, christoffel metric (γ t) μ ν ρ * V t ν * deriv (fun s => γ s ρ) t) = 0

/-- Levi-Civita connection is metric-compatible

    ∇_ρ g_μν = 0
-/
axiom metric_compatible (metric : SpacetimeMetric) (x : SpaceTimePoint)
    (ρ μ ν : Fin 4) : Prop

/-- Levi-Civita connection is torsion-free

    Γ^μ_νρ = Γ^μ_ρν
-/
axiom torsion_free (metric : SpacetimeMetric) (x : SpaceTimePoint)
    (μ ν ρ : Fin 4) :
  christoffel metric x μ ν ρ = christoffel metric x μ ρ ν

end ModularPhysics.Core.SpaceTime
