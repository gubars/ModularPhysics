import ModularPhysics.Core.SpaceTime.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

namespace ModularPhysics.Core.SpaceTime

/-- A spacetime metric: assigns inner product at each point

    This is GEOMETRIC structure - no dynamics required.
    Works for both flat (Minkowski) and curved spacetimes.
-/
structure SpacetimeMetric where
  /-- Metric tensor g_μν(x) -/
  g : SpaceTimePoint → Fin 4 → Fin 4 → ℝ
  /-- Metric is symmetric -/
  symmetric : ∀ (x : SpaceTimePoint) (μ ν : Fin 4), g x μ ν = g x ν μ
  /-- Metric is non-degenerate (determinant non-zero) -/
  nondegenerate : ∀ (_ : SpaceTimePoint), True

/-- Inverse metric g^μν -/
axiom inverseMetric (metric : SpacetimeMetric) (x : SpaceTimePoint)
    (μ ν : Fin 4) : ℝ

/-- Metric determinant det(g_μν) -/
axiom metricDeterminant (metric : SpacetimeMetric) (x : SpaceTimePoint) : ℝ

/-- Inner product of two vectors at a point -/
def innerProduct (metric : SpacetimeMetric) (x : SpaceTimePoint)
    (v w : Fin 4 → ℝ) : ℝ :=
  ∑ μ, ∑ ν, metric.g x μ ν * v μ * w ν

/-- Signature of metric (number of positive and negative eigenvalues) -/
axiom signature (metric : SpacetimeMetric) (x : SpaceTimePoint) : Fin 4 → ℤ

/-- Lorentzian signature: one timelike, three spacelike -/
def isLorentzian (metric : SpacetimeMetric) : Prop :=
  ∀ x, (signature metric x 0 = -1 ∧ ∀ i : Fin 3, signature metric x i.succ = 1) ∨
       (signature metric x 0 = 1 ∧ ∀ i : Fin 3, signature metric x i.succ = -1)

/-- Riemannian signature: all positive -/
def isRiemannian (metric : SpacetimeMetric) : Prop :=
  ∀ x μ, signature metric x μ = 1

end ModularPhysics.Core.SpaceTime
