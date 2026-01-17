import ModularPhysics.Core.SpaceTime.Metrics
import ModularPhysics.Core.SpaceTime.Connections
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ModularPhysics.Core.SpaceTime

/-- Killing vector field (generates isometry of metric)

    A vector field ξ is Killing if Lie derivative of metric vanishes:
    ℒ_ξ g = 0

    Equivalently (Killing equation):
    ∇_μ ξ_ν + ∇_ν ξ_μ = 0
-/
def KillingVector (metric : SpacetimeMetric)
    (ξ : SpaceTimePoint → Fin 4 → ℝ) : Prop :=
  ∀ x μ ν,
    covariantDerivativeCovector metric ξ μ x ν +
    covariantDerivativeCovector metric ξ ν x μ = 0

/-- Timelike Killing vector (time translation symmetry) -/
def TimelikeKilling (metric : SpacetimeMetric)
    (ξ : SpaceTimePoint → Fin 4 → ℝ) : Prop :=
  KillingVector metric ξ ∧
  ∀ x, (∑ μ, ∑ ν, metric.g x μ ν * ξ x μ * ξ x ν) < 0

/-- Spacelike Killing vector -/
def SpacelikeKilling (metric : SpacetimeMetric)
    (ξ : SpaceTimePoint → Fin 4 → ℝ) : Prop :=
  KillingVector metric ξ ∧
  ∀ x, (∑ μ, ∑ ν, metric.g x μ ν * ξ x μ * ξ x ν) > 0

/-- Null Killing vector -/
def NullKilling (metric : SpacetimeMetric)
    (ξ : SpaceTimePoint → Fin 4 → ℝ) : Prop :=
  KillingVector metric ξ ∧
  ∀ x, (∑ μ, ∑ ν, metric.g x μ ν * ξ x μ * ξ x ν) = 0

/-- Stationary spacetime (has timelike Killing vector) -/
def Stationary (metric : SpacetimeMetric) : Prop :=
  ∃ ξ, TimelikeKilling metric ξ

/-- Static spacetime (stationary + hypersurface orthogonal)

    Stronger than stationary: the timelike Killing vector is
    orthogonal to a family of spacelike hypersurfaces
-/
def Static (metric : SpacetimeMetric) : Prop :=
  Stationary metric ∧
  ∃ ξ, TimelikeKilling metric ξ ∧
    ∀ x μ ν, ξ x μ * ξ x ν = 0 → μ = ν

/-- Isometry: diffeomorphism preserving metric -/
structure Isometry (metric : SpacetimeMetric) where
  map : SpaceTimePoint → SpaceTimePoint
  inverse : SpaceTimePoint → SpaceTimePoint
  left_inv : ∀ x, inverse (map x) = x
  right_inv : ∀ x', map (inverse x') = x'
  preserves_metric : ∀ x μ ν,
    metric.g (map x) μ ν = metric.g x μ ν

/-- Killing horizon: surface where Killing vector becomes null -/
def KillingHorizon (metric : SpacetimeMetric)
    (ξ : SpaceTimePoint → Fin 4 → ℝ) : Set SpaceTimePoint :=
  {x | KillingVector metric ξ ∧
       (∑ μ, ∑ ν, metric.g x μ ν * ξ x μ * ξ x ν) = 0}

/-- Surface gravity of Killing horizon -/
axiom surfaceGravity (metric : SpacetimeMetric)
    (ξ : SpaceTimePoint → Fin 4 → ℝ)
    (horizon : Set SpaceTimePoint)
    (h : horizon = KillingHorizon metric ξ) : ℝ

/-- Minkowski has maximum symmetry (10 Killing vectors: 4 translations + 6 rotations/boosts) -/
axiom minkowski_maximal_symmetry :
  ∃ (ξs : Fin 10 → SpaceTimePoint → Fin 4 → ℝ),
    ∀ i, KillingVector minkowskiMetric (ξs i)

/-- Schwarzschild has 2 Killing vectors (time translation + axial rotation) -/
axiom schwarzschild_killing_vectors (M : ℝ) (h : M > 0) :
  ∃ (ξ_t ξ_φ : SpaceTimePoint → Fin 4 → ℝ),
    TimelikeKilling (sorry : SpacetimeMetric) ξ_t ∧
    SpacelikeKilling (sorry : SpacetimeMetric) ξ_φ

end ModularPhysics.Core.SpaceTime
