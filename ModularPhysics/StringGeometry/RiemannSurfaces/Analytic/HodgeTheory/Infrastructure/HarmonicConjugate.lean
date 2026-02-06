import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Harmonic Conjugate Theory

This file develops the theory of harmonic conjugates using Mathlib's theorem
that harmonic functions on balls are real parts of holomorphic functions.

## Mathematical Background

If u : ℂ → ℝ is harmonic, then locally there exists v : ℂ → ℝ (the harmonic conjugate)
such that f = u + iv is holomorphic. The function v is unique up to a constant.

The key insight is that Mathlib's `harmonic_is_realOfHolomorphic` gives us:
  HarmonicOnNhd f (ball z R) → ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball z R) ∧ f = Re ∘ F

The imaginary part Im ∘ F is then the harmonic conjugate.

## Main Results

* `harmonic_conjugate_exists_ball` - Local existence on balls
* `harmonic_conjugate_exists_at` - Local existence at a point

## References

* Ahlfors, "Complex Analysis", Chapter 4
* Mathlib.Analysis.Complex.Harmonic.Analytic
-/

namespace RiemannSurfaces.Analytic.Infrastructure

open Complex Metric Set InnerProductSpace Filter Topology

/-!
## Local Existence of Harmonic Conjugate
-/

/-- A harmonic conjugate of u is a function v such that u + iv is holomorphic.
    We use DifferentiableOn ℂ to express holomorphicity. -/
def IsHarmonicConjugate' (u v : ℂ → ℝ) (U : Set ℂ) : Prop :=
  DifferentiableOn ℂ (fun z => (⟨u z, v z⟩ : ℂ)) U

/-- On a ball, a harmonic function has a harmonic conjugate.
    This follows directly from `harmonic_is_realOfHolomorphic`. -/
theorem harmonic_conjugate_exists_ball {u : ℂ → ℝ} {z₀ : ℂ} {R : ℝ} (hR : R > 0)
    (hu : HarmonicOnNhd u (ball z₀ R)) :
    ∃ v : ℂ → ℝ, IsHarmonicConjugate' u v (ball z₀ R) ∧ HarmonicOnNhd v (ball z₀ R) := by
  -- Use Mathlib's theorem: harmonic function is real part of holomorphic
  obtain ⟨F, hF_ana, hF_eq⟩ := harmonic_is_realOfHolomorphic hu
  -- The conjugate is the imaginary part of F
  use fun z => (F z).im
  constructor
  · -- u + i·v is holomorphic on ball
    -- The key is that on the ball, u = Re(F), so u + i·Im(F) = F
    intro z hz
    -- F is differentiable at z
    have hFdiff : DifferentiableAt ℂ F z := (hF_ana z hz).differentiableAt
    -- Show that (u z, (F z).im) = F z using Complex.ext
    have heq : ∀ w ∈ ball z₀ R, (⟨u w, (F w).im⟩ : ℂ) = F w := fun w hw => by
      apply Complex.ext
      · -- u w = (F w).re follows from hF_eq
        exact (hF_eq hw).symm
      · rfl
    -- The function (w ↦ ⟨u w, (F w).im⟩) equals F on ball, so it's differentiable
    have hfeq : (fun w => (⟨u w, (F w).im⟩ : ℂ)) =ᶠ[𝓝 z] F := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      use ball z₀ R
      have hz_in_ball : ball z₀ R ∈ 𝓝 z := isOpen_ball.mem_nhds hz
      exact ⟨hz_in_ball, fun w hw => heq w hw⟩
    exact (hFdiff.congr_of_eventuallyEq hfeq).differentiableWithinAt
  · -- v = Im ∘ F is harmonic
    intro z hz
    exact (hF_ana z hz).harmonicAt_im

/-- Local existence of harmonic conjugate at a point.
    If u is harmonic at z₀, there exists a ball and a harmonic conjugate on that ball. -/
theorem harmonic_conjugate_exists_at {u : ℂ → ℝ} {z₀ : ℂ} (hu : HarmonicAt u z₀) :
    ∃ ε > 0, ∃ v : ℂ → ℝ, IsHarmonicConjugate' u v (ball z₀ ε) ∧ HarmonicOnNhd v (ball z₀ ε) := by
  -- HarmonicAt gives harmonicity in a neighborhood
  -- Use isOpen_setOf_harmonicAt to get a ball where u is harmonic
  have hopen := isOpen_setOf_harmonicAt u
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen z₀ hu
  -- u is harmonic on ball z₀ ε
  have hu_ball : HarmonicOnNhd u (ball z₀ ε) := fun z hz => hball hz
  -- Apply the ball version
  obtain ⟨v, hv_conj, hv_harm⟩ := harmonic_conjugate_exists_ball hε hu_ball
  exact ⟨ε, hε, v, hv_conj, hv_harm⟩

/-- The harmonic conjugate v is also harmonic on the ball. -/
theorem harmonic_conjugate_is_harmonic {u v : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hconj : IsHarmonicConjugate' u v U) :
    HarmonicOnNhd v U := by
  -- DifferentiableOn on open set implies AnalyticOnNhd
  have hana : AnalyticOnNhd ℂ (fun w => (⟨u w, v w⟩ : ℂ)) U := hconj.analyticOnNhd hU
  intro z hz
  -- The imaginary part of an analytic function is harmonic
  exact (hana z hz).harmonicAt_im

/-- Both u and v are harmonic if u + iv is holomorphic. -/
theorem harmonic_of_holomorphic_pair {u v : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hconj : IsHarmonicConjugate' u v U) :
    HarmonicOnNhd u U ∧ HarmonicOnNhd v U := by
  -- DifferentiableOn on open set implies AnalyticOnNhd
  have hana : AnalyticOnNhd ℂ (fun w => (⟨u w, v w⟩ : ℂ)) U := hconj.analyticOnNhd hU
  constructor
  · -- u = Re(u + iv) is harmonic
    intro z hz
    exact (hana z hz).harmonicAt_re
  · exact harmonic_conjugate_is_harmonic hU hconj

/-!
## Global Existence on Simply Connected Domains

On simply connected domains, the harmonic conjugate exists globally (not just locally).
The proof uses that simply connected domains in ℂ are contractible to a point,
so any local construction can be extended globally without monodromy issues.
-/

/-- On a simply connected domain, a harmonic function has a global harmonic conjugate.

    The proof idea: locally we can find conjugates using `harmonic_is_realOfHolomorphic`.
    On a simply connected domain, these local conjugates can be patched together
    because the domain has trivial fundamental group (no monodromy).

    This is a deep result requiring path integration theory. -/
theorem harmonic_conjugate_simply_connected {u : ℂ → ℝ} {U : Set ℂ}
    (hU : IsOpen U) [SimplyConnectedSpace ↥U]
    (hu : HarmonicOnNhd u U) :
    ∃ v : ℂ → ℝ, IsHarmonicConjugate' u v U ∧ HarmonicOnNhd v U := by
  -- This requires path integration or sheaf-theoretic arguments
  -- The key is that on simply connected domains, any locally defined function
  -- (like the harmonic conjugate) extends globally
  sorry

end RiemannSurfaces.Analytic.Infrastructure
