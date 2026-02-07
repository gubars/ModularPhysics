import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import ModularPhysics.StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Infrastructure.MaximumPrinciple

/-!
# Poisson Integral on Discs

This file develops the Poisson integral for discs in ℂ, which is used to prove
that continuous functions satisfying the mean value property are harmonic.

## Main Results

* `mvp_maximum_principle` - Maximum principle for functions satisfying MVP
* `schwarzIntegral` - The Schwarz integral (holomorphic, Re = Poisson integral)
* `mvp_eq_poissonIntegral` - MVP function equals its Poisson integral
* `mvp_implies_harmonicOnNhd` - MVP implies harmonicity

## Strategy

Given f continuous on closedBall c R satisfying MVP on ball c R:
1. Define the Schwarz integral H(z) = Poisson-type integral of f
2. H is holomorphic on ball c R (parametric integral with holomorphic integrand)
3. P[f] = Re(H) is harmonic, hence satisfies MVP
4. f - P[f] satisfies MVP and vanishes on the boundary
5. By maximum principle for MVP functions: f = P[f]
6. Therefore f = Re(holomorphic), hence f is harmonic

## References

* Axler, Bourdon, Ramey "Harmonic Function Theory" Ch 1
* Ahlfors "Complex Analysis" Ch 6
-/

namespace RiemannSurfaces.Analytic.Infrastructure

open Complex Metric Set Filter MeasureTheory InnerProductSpace Real Topology

/-!
## Maximum Principle for MVP Functions

The maximum principle holds for continuous functions satisfying the mean value property,
without assuming they are harmonic. The proof is identical to the harmonic case:
if f attains its maximum at an interior point, then MVP forces f to be constant
on any circle around that point where the maximum is attained, and by iteration
f is constant on the entire connected component.
-/

/-- If f is continuous on a closed ball, satisfies MVP, and its maximum is attained
    at a point on the sphere (boundary circle), then the maximum on the ball
    equals the maximum on the sphere.

    This is a helper for the MVP maximum principle. -/
theorem mvp_max_le_sphere_max (f : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hcont : ContinuousOn f (closedBall c R))
    (hmvp : ∀ z ∈ ball c R, ∀ r > 0, closedBall z r ⊆ closedBall c R →
      f z = circleAverage f z r)
    (z₀ : ℂ) (hz₀ : z₀ ∈ ball c R)
    (hmax : ∀ z ∈ closedBall c R, f z ≤ f z₀) :
    ∀ z ∈ closedBall c R, f z = f z₀ := by
  -- First, show f = f(z₀) on ball c R using the clopen argument
  have hball : ∀ z ∈ ball c R, f z = f z₀ := by
    -- Define S = {z ∈ ball c R | f z = f z₀}
    let S := {z ∈ ball c R | f z = f z₀}
    -- Use connectedness: S is open, ball \ S is open, S nonempty → S = ball
    have hball_conn := (convex_ball c R).isConnected (nonempty_ball.mpr hR)
    -- S is open: if f(w) = f(z₀) and w ∈ ball, then f = f(z₀) on a neighborhood
    have hS_open : IsOpen S := by
      rw [isOpen_iff_forall_mem_open]
      intro w ⟨hw_ball, hfw⟩
      -- Take ε so that closedBall w ε ⊆ closedBall c R
      set ε := (R - dist w c) / 2 with hε_def
      have hw_dist : dist w c < R := mem_ball.mp hw_ball
      have hε_pos : 0 < ε := by linarith
      have h_sub : closedBall w ε ⊆ closedBall c R := by
        intro x hx; rw [mem_closedBall] at hx ⊢
        linarith [dist_triangle x w c]
      -- For each x ∈ ball w ε with x ≠ w, x ∈ sphere w (dist x w)
      -- By MVP at w: f(w) = circleAvg(f, w, dist x w)
      -- By eq_of_circleAverage_eq_of_le: f = f(z₀) on sphere w (dist x w)
      refine ⟨ball w ε, ?_, isOpen_ball, mem_ball_self hε_pos⟩
      intro x hx
      have hx_ball : x ∈ ball c R := by
        rw [mem_ball] at hx ⊢; linarith [dist_triangle x w c]
      constructor
      · exact hx_ball
      · by_cases hxw : x = w
        · rw [hxw, hfw]
        · -- x ≠ w, so dist x w > 0
          set s := dist x w with hs_def
          have hs_pos : 0 < s := dist_pos.mpr hxw
          have hs_lt : s < ε := mem_ball.mp hx
          -- closedBall w s ⊆ closedBall c R
          have hs_sub : closedBall w s ⊆ closedBall c R :=
            (closedBall_subset_closedBall hs_lt.le).trans h_sub
          -- MVP at w gives f(w) = circleAvg(f, w, s)
          have hmvp_s := hmvp w hw_ball s hs_pos hs_sub
          -- f ≤ f(z₀) = f(w) on sphere w |s|
          have abs_s : |s| = s := abs_of_pos hs_pos
          have sph_sub : sphere w |s| ⊆ closedBall w s := by
            rw [abs_s]; exact sphere_subset_closedBall
          have hle_sph : ∀ y ∈ sphere w |s|, f y ≤ f z₀ :=
            fun y hy => hmax y (hs_sub (sph_sub hy))
          -- Continuity on sphere
          have hcont_sph : ContinuousOn f (sphere w |s|) :=
            hcont.mono (sph_sub.trans hs_sub)
          -- circleAverage f w s = f(z₀)
          have havg : circleAverage f w s = f z₀ := by rw [← hmvp_s, hfw]
          -- Apply eq_of_circleAverage_eq_of_le from MaximumPrinciple.lean
          have h_eq := eq_of_circleAverage_eq_of_le hs_pos.ne' hcont_sph hle_sph havg
          -- x ∈ sphere w |s| since dist x w = s > 0
          have hx_sph : x ∈ sphere w |s| := by
            rw [mem_sphere, abs_of_pos hs_pos]
          exact h_eq x hx_sph
    -- ball \ S is open (by continuity of f)
    have hT_open : IsOpen (ball c R \ S) := by
      have : ball c R \ S = ball c R ∩ f ⁻¹' {f z₀}ᶜ := by
        ext z; simp only [mem_diff, mem_sep_iff, mem_inter_iff, mem_preimage,
          mem_compl_iff, mem_singleton_iff, not_and, S]
        constructor
        · intro ⟨hz, hne⟩; exact ⟨hz, hne hz⟩
        · intro ⟨hz, hne⟩; exact ⟨hz, fun _ => hne⟩
      rw [this]
      exact (hcont.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball
        isOpen_compl_singleton
    -- S nonempty
    have hS_ne : (ball c R ∩ S).Nonempty := ⟨z₀, hz₀, hz₀, rfl⟩
    -- By preconnectedness, ball ⊆ S
    have h_subset := hball_conn.isPreconnected.subset_left_of_subset_union
      hS_open hT_open disjoint_sdiff_self_right
      (fun z hz => by
        by_cases hzS : z ∈ S
        · exact Or.inl hzS
        · exact Or.inr ⟨hz, hzS⟩)
      hS_ne
    intro z hz
    exact (h_subset hz).2
  -- Extend from ball to closedBall by continuity
  intro z hz
  rcases (mem_closedBall.mp hz).eq_or_lt with h | h
  · -- z on the boundary: use density of ball in closedBall
    -- z ∈ closure(ball c R), f = f(z₀) on ball, f continuous → f(z) = f(z₀)
    have h_closure : z ∈ closure (ball c R) := by
      rw [closure_ball c hR.ne']; exact hz
    haveI h_nebot : (𝓝[ball c R] z).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp h_closure
    -- f converges to f(z) along 𝓝[ball c R] z (by continuity on closedBall)
    have h_tendsto : Tendsto f (𝓝[ball c R] z) (𝓝 (f z)) :=
      (hcont.continuousWithinAt hz).mono ball_subset_closedBall
    -- f equals the constant f(z₀) on ball c R
    have h_ev_eq : f =ᶠ[𝓝[ball c R] z] fun _ => f z₀ :=
      eventuallyEq_iff_exists_mem.mpr ⟨ball c R, self_mem_nhdsWithin,
        fun w hw => hball w hw⟩
    -- So f converges to f(z₀) along the same filter
    have h_tendsto' : Tendsto (fun _ => f z₀) (𝓝[ball c R] z) (𝓝 (f z)) :=
      h_tendsto.congr' h_ev_eq
    -- By uniqueness of limits, f(z) = f(z₀)
    exact tendsto_nhds_unique h_tendsto' tendsto_const_nhds
  · exact hball z (mem_ball.mpr h)

/-- Maximum principle for MVP functions on closed balls:
    if f satisfies MVP and attains its maximum at an interior point,
    then f is constant. -/
theorem mvp_maximum_principle (f : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hcont : ContinuousOn f (closedBall c R))
    (hmvp : ∀ z ∈ ball c R, ∀ r > 0, closedBall z r ⊆ closedBall c R →
      f z = circleAverage f z r)
    (z₀ : ℂ) (hz₀ : z₀ ∈ ball c R)
    (hmax : ∀ z ∈ closedBall c R, f z ≤ f z₀) :
    ∀ z ∈ closedBall c R, f z = f z₀ :=
  mvp_max_le_sphere_max f c R hR hcont hmvp z₀ hz₀ hmax

/-- If f satisfies MVP, is continuous on closedBall, and vanishes on the sphere,
    then f = 0 on the ball. -/
theorem mvp_zero_boundary_implies_zero (f : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hcont : ContinuousOn f (closedBall c R))
    (hmvp : ∀ z ∈ ball c R, ∀ r > 0, closedBall z r ⊆ closedBall c R →
      f z = circleAverage f z r)
    (hbdry : ∀ z, ‖z - c‖ = R → f z = 0) :
    ∀ z ∈ ball c R, f z = 0 := by
  sorry

/-!
## The Schwarz Integral

The Schwarz integral is a holomorphic function on a disc whose real part
gives the Poisson integral (harmonic extension of boundary data).

For a disc B(c, R) and continuous boundary data g on sphere(c, R):
  S(z) = (1/2π) ∫₀²π g(c + Re^{iθ}) · (Re^{iθ} + (z-c)) / (Re^{iθ} - (z-c)) dθ

S is holomorphic in z for |z-c| < R, and Re(S(z)) = P[g](z) is the Poisson integral.
-/

/-- The Schwarz integral for boundary data on a circle.
    This is holomorphic in z inside the disc, and its real part is the Poisson integral. -/
noncomputable def schwarzIntegral (g : ℂ → ℝ) (c : ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
    ((g (circleMap c R θ) : ℝ) : ℂ) *
      ((circleMap c R θ - c + (z - c)) / (circleMap c R θ - z))

/-- The Poisson integral: Re of the Schwarz integral. -/
noncomputable def poissonIntegralDisc (g : ℂ → ℝ) (c : ℂ) (R : ℝ) (z : ℂ) : ℝ :=
  (schwarzIntegral g c R z).re

/-!
## Properties of the Schwarz/Poisson Integral

Key properties needed for the MVP → Harmonic proof:
1. The Schwarz integral is holomorphic inside the disc
2. The Poisson integral (= Re(Schwarz)) is therefore harmonic
3. The Poisson integral has the correct boundary values
-/

/-- The Schwarz integral is differentiable (holomorphic) at points inside the disc.
    This follows from differentiation under the integral sign:
    the integrand is holomorphic in z (for fixed θ), and the z-derivative
    is bounded by an integrable function. -/
theorem schwarzIntegral_differentiableAt (g : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hg : ContinuousOn g (sphere c R))
    (z : ℂ) (hz : z ∈ ball c R) :
    DifferentiableAt ℂ (schwarzIntegral g c R) z := by
  sorry

/-- The Poisson integral is harmonic on the ball.
    This follows from the Schwarz integral being holomorphic:
    Re(holomorphic) is harmonic. -/
theorem poissonIntegral_harmonicOnNhd (g : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hg : ContinuousOn g (sphere c R)) :
    HarmonicOnNhd (poissonIntegralDisc g c R) (ball c R) := by
  intro z hz
  -- Schwarz integral is holomorphic at z
  have hSdiff := schwarzIntegral_differentiableAt g c R hR hg z hz
  -- Re(holomorphic) is harmonic
  -- Need: DifferentiableAt ℂ → AnalyticAt ℂ → harmonicAt_re
  have hSdiffOn : DifferentiableOn ℂ (schwarzIntegral g c R) (ball c R) := by
    intro w hw
    exact (schwarzIntegral_differentiableAt g c R hR hg w hw).differentiableWithinAt
  have hSana : AnalyticOnNhd ℂ (schwarzIntegral g c R) (ball c R) :=
    hSdiffOn.analyticOnNhd isOpen_ball
  exact (hSana z hz).harmonicAt_re

/-- The Poisson integral has the correct boundary values:
    as z → ζ on the sphere, poissonIntegralDisc g c R z → g(ζ). -/
theorem poissonIntegral_boundary_values (g : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hg : ContinuousOn g (sphere c R)) :
    ∀ ζ, ζ ∈ sphere c R →
      Filter.Tendsto (poissonIntegralDisc g c R) (𝓝[ball c R] ζ) (𝓝 (g ζ)) := by
  sorry

/-!
## MVP Implies Harmonic

The main theorem: continuous functions satisfying MVP are harmonic.
-/

/-- A continuous function satisfying MVP on a closed ball equals
    its Poisson integral on the ball. -/
theorem mvp_eq_poissonIntegral (f : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hcont : ContinuousOn f (closedBall c R))
    (hmvp : ∀ z ∈ ball c R, ∀ r > 0, closedBall z r ⊆ closedBall c R →
      f z = circleAverage f z r) :
    ∀ z ∈ ball c R, f z = poissonIntegralDisc f c R z := by
  -- Define h = f - P[f]
  -- h satisfies MVP (f satisfies MVP, P[f] is harmonic hence satisfies MVP)
  -- h = 0 on sphere (P[f] has boundary values f)
  -- By MVP maximum principle: h = 0 on ball
  sorry

/-- **Main theorem**: Continuous functions satisfying MVP on a ball are harmonic.

    This is the key result connecting the mean value property to harmonicity.
    The proof goes through the Poisson integral representation:
    f = Re(Schwarz integral) → f is the real part of a holomorphic function → f is harmonic.

    This directly proves `harmonicOnNhd_of_mvp` without needing separate
    `smooth_of_mvp_ball` and `laplacian_zero_of_mvp` results. -/
theorem mvp_implies_harmonicOnNhd (f : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hcont : ContinuousOn f (closedBall c R))
    (hmvp : ∀ z ∈ ball c R, ∀ r > 0, closedBall z r ⊆ closedBall c R →
      f z = circleAverage f z r) :
    HarmonicOnNhd f (ball c R) := by
  intro z hz
  -- f = P[f] on ball
  have hfP := mvp_eq_poissonIntegral f c R hR hcont hmvp
  -- P[f] is harmonic on ball
  have hP_harm := poissonIntegral_harmonicOnNhd f c R hR
    (hcont.mono (sphere_subset_closedBall))
  -- f = P[f] at z, so f is harmonic at z
  have hfz := hfP z hz
  -- HarmonicAt for P[f] at z
  have hPz := hP_harm z hz
  -- f =ᶠ[𝓝 z] P[f] on a neighborhood
  have hfeq : f =ᶠ[nhds z] poissonIntegralDisc f c R := by
    apply eventuallyEq_iff_exists_mem.mpr
    use ball c R, isOpen_ball.mem_nhds hz
    intro w hw
    exact hfP w hw
  -- Transfer harmonicity via local equality
  exact (harmonicAt_congr_nhds hfeq.symm).mp hPz

/-- Corollary: MVP implies smoothness (C^∞). -/
theorem mvp_implies_contDiffOn (f : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hcont : ContinuousOn f (closedBall c R))
    (hmvp : ∀ z ∈ ball c R, ∀ r > 0, closedBall z r ⊆ closedBall c R →
      f z = circleAverage f z r) :
    ContDiffOn ℝ ⊤ f (ball c R) := by
  -- f is harmonic on ball → f = Re(holomorphic) → f is smooth
  have hharm := mvp_implies_harmonicOnNhd f c R hR hcont hmvp
  -- Use harmonic_is_realOfHolomorphic to get f = Re(F) for analytic F
  -- Then f inherits C^∞ from F
  sorry

/-- Corollary: MVP + C² implies Δf = 0 (for compatibility with existing code). -/
theorem mvp_implies_laplacian_zero (f : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hcont : ContinuousOn f (closedBall c R))
    (hmvp : ∀ z ∈ ball c R, ∀ r > 0, closedBall z r ⊆ closedBall c R →
      f z = circleAverage f z r) :
    ∀ z ∈ ball c R, InnerProductSpace.laplacian f z = 0 := by
  intro z hz
  exact (mvp_implies_harmonicOnNhd f c R hR hcont hmvp z hz).2.self_of_nhds

end RiemannSurfaces.Analytic.Infrastructure
