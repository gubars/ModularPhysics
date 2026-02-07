import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.MeasureTheory.Integral.CircleAverage
import ModularPhysics.StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Infrastructure.PoissonIntegral

/-!
# Mean Value Property Implies Harmonicity

This file proves the converse of the mean value property: if a continuous function
on an open set satisfies the mean value property everywhere, then it is harmonic.

## Mathematical Background

**Theorem (Converse of Mean Value Property)**: Let U ⊆ ℂ be open, and let f : U → ℝ
be continuous. If f satisfies the mean value property:
  f(z₀) = (1/2π) ∫₀^{2π} f(z₀ + re^{iθ}) dθ
for all z₀ ∈ U and all r > 0 with B(z₀, r) ⊆ U, then f is harmonic on U.

**Proof**: The proof goes through the Poisson integral representation developed in
`PoissonIntegral.lean`. For each point z ∈ U, we take a small closed ball around z
contained in U, and apply `mvp_implies_harmonicOnNhd` which shows that continuous
functions satisfying MVP on a closed ball are harmonic on the open ball.

## Main Results

* `harmonicOnNhd_of_mvp` - MVP on open set implies harmonic
* `harmonicOn_of_continuous_mean_value` - Standard formulation with ball containment

## References

* Axler, Bourdon, Ramey "Harmonic Function Theory"
* Evans "Partial Differential Equations" Chapter 2
-/

namespace RiemannSurfaces.Analytic.Infrastructure

open Complex Metric Set Filter MeasureTheory InnerProductSpace Real

/-!
## Mean Value Property Characterization

The key insight is that the mean value property characterizes harmonic functions.
-/

/-- A function satisfies the mean value property on a set if for every interior point
    and every ball contained in the set, the function value equals the circle average. -/
def SatisfiesMVP (f : ℂ → ℝ) (U : Set ℂ) : Prop :=
  ∀ z ∈ U, ∀ r > 0, closedBall z r ⊆ U → f z = circleAverage f z r

/-- The mean value property restricted to a single point with all valid radii. -/
def SatisfiesMVPAt (f : ℂ → ℝ) (z : ℂ) (U : Set ℂ) : Prop :=
  ∀ r > 0, closedBall z r ⊆ U → f z = circleAverage f z r

/-- SatisfiesMVP implies SatisfiesMVPAt at every point. -/
theorem satisfiesMVP_iff_satisfiesMVPAt (f : ℂ → ℝ) (U : Set ℂ) :
    SatisfiesMVP f U ↔ ∀ z ∈ U, SatisfiesMVPAt f z U :=
  Iff.rfl

/-!
## Main Theorem: Mean Value Property Implies Harmonicity

The proof uses the Poisson integral infrastructure from `PoissonIntegral.lean`:
1. For each point z in U, take a small closed ball B̄(z, R/2) ⊆ U
2. Apply `mvp_implies_harmonicOnNhd` which shows MVP + continuous → harmonic
3. This gives HarmonicAt f z
-/

/-- Main theorem: If f is continuous on an open set and satisfies the mean value
    property, then f is harmonic.

    This is a fundamental characterization of harmonic functions. The proof
    localizes to closed balls and applies the Poisson integral representation
    from `PoissonIntegral.lean`. -/
theorem harmonicOnNhd_of_mvp (f : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U)
    (hcont : ContinuousOn f U)
    (hmvp : SatisfiesMVP f U) :
    HarmonicOnNhd f U := by
  intro z hz
  -- Get a ball around z contained in U
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hU z hz
  -- Restrict to a smaller ball to have closedBall contained in U
  have hR' : R / 2 > 0 := by linarith
  have hclosed : closedBall z (R / 2) ⊆ U := by
    calc closedBall z (R / 2) ⊆ ball z R := closedBall_subset_ball (by linarith)
      _ ⊆ U := hball
  -- f is continuous on this closed ball
  have hcont' : ContinuousOn f (closedBall z (R / 2)) :=
    hcont.mono hclosed
  -- f satisfies MVP on this ball (convert to the form needed by mvp_implies_harmonicOnNhd)
  have hmvp' : ∀ w ∈ ball z (R / 2), ∀ r > 0, closedBall w r ⊆ closedBall z (R / 2) →
      f w = circleAverage f w r := by
    intro w hw r hr hsub
    apply hmvp w (hclosed (ball_subset_closedBall hw)) r hr
    calc closedBall w r ⊆ closedBall z (R / 2) := hsub
      _ ⊆ U := hclosed
  -- Apply the Poisson integral result: MVP on closed ball → harmonic on open ball
  exact mvp_implies_harmonicOnNhd f z (R / 2) hR' hcont' hmvp' z (mem_ball_self hR')

/-- Corollary: The standard formulation with ball containment. -/
theorem harmonicOn_of_continuous_mean_value (f : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U)
    (hcont : ContinuousOn f U)
    (hmvp : ∀ z ∈ U, ∀ r > 0, ball z r ⊆ U → f z = circleAverage f z r) :
    IsOpen U ∧ HarmonicOnNhd f U := by
  constructor
  · exact hU
  · apply harmonicOnNhd_of_mvp f U hU hcont
    -- Convert ball containment to closedBall containment
    intro z hz r hr hclosed
    -- closedBall z r ⊆ U implies ball z r ⊆ U
    have hball : ball z r ⊆ U := ball_subset_closedBall.trans hclosed
    exact hmvp z hz r hr hball

end RiemannSurfaces.Analytic.Infrastructure
