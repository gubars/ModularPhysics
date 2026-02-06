import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Clopen

/-!
# Maximum Principle for Harmonic Functions

This file develops the maximum principle for harmonic functions by bridging
from Mathlib's maximum modulus principle for holomorphic functions.

## Mathematical Background

The maximum principle for harmonic functions states: if a harmonic function u
attains its maximum at an interior point of a connected domain, then u is constant.

**Proof Strategy**: We use the mean value property. If u(z₀) is a maximum, then
by the mean value property, u(z₀) equals the average over any small circle around z₀.
Since u ≤ u(z₀) everywhere, and the average equals u(z₀), we must have u = u(z₀)
on the entire circle. Iterating this argument across the connected domain gives
the result.

## Main Results

* `harmonic_eq_of_circleAverage_eq` - f = M on sphere if average = M and f ≤ M
* `harmonic_maximum_principle_ball` - maximum principle on balls
* `harmonic_maximum_principle_connected` - maximum principle on connected open sets

## References

* Ahlfors, "Complex Analysis"
* Gilbarg-Trudinger, "Elliptic Partial Differential Equations of Second Order"
-/

namespace RiemannSurfaces.Analytic.Infrastructure

open Complex Metric Set Filter MeasureTheory InnerProductSpace Real

/-!
## Helper Lemmas for HarmonicOnNhd
-/

/-- Negation of a harmonic function is harmonic. -/
theorem HarmonicOnNhd.neg {f : ℂ → ℝ} {s : Set ℂ} (hf : HarmonicOnNhd f s) :
    HarmonicOnNhd (-f) s := by
  intro x hx
  have hfx := hf x hx
  -- HarmonicAt f x means there's a neighborhood where laplacian vanishes
  -- For -f, use that (-1) • f = -f
  have h : (-f) = ((-1 : ℝ) • f) := by ext y; simp [Pi.smul_apply]
  rw [h]
  exact hfx.const_smul

/-- If f is harmonic on a neighborhood of a set, it's continuous on that set. -/
theorem HarmonicOnNhd.continuousOn {f : ℂ → ℝ} {s : Set ℂ} (hf : HarmonicOnNhd f s) :
    ContinuousOn f s := by
  intro x hx
  exact (hf x hx).1.continuousAt.continuousWithinAt

/-!
## Circle Average Lemmas

Key lemma: if f is continuous, f ≤ M on sphere, and circleAverage f = M, then f = M on sphere.
-/

/-- If a continuous function satisfies f ≤ M on a sphere and its circle average equals M,
    then f = M everywhere on the sphere.

    **Proof**: Let g = M - f ≥ 0 on sphere. The average of g is M - M = 0.
    Since g ≥ 0 and has zero average, g = 0 a.e. by integral theory.
    By continuity, g = 0 everywhere, so f = M. -/
theorem eq_of_circleAverage_eq_of_le {f : ℂ → ℝ} {z₀ : ℂ} {r : ℝ} {M : ℝ}
    (hr : r ≠ 0) (hcont : ContinuousOn f (sphere z₀ |r|))
    (hle : ∀ z ∈ sphere z₀ |r|, f z ≤ M)
    (havg : circleAverage f z₀ r = M) :
    ∀ z ∈ sphere z₀ |r|, f z = M := by
  -- The key insight: M - circleAverage f = circleAverage (const M) - circleAverage f
  -- = circleAverage (M - f) = 0
  -- Since M - f ≥ 0 and average is 0, we must have M - f = 0 a.e., hence everywhere by continuity
  intro z hz
  -- Suppose f z < M for some z
  by_contra hne
  push_neg at hne
  have hlt : f z < M := lt_of_le_of_ne (hle z hz) hne
  -- The function g = M - f is continuous and positive at z
  let g : ℂ → ℝ := fun w => M - f w
  have g_cont : ContinuousOn g (sphere z₀ |r|) := continuousOn_const.sub hcont
  have g_nonneg : ∀ w ∈ sphere z₀ |r|, 0 ≤ g w := fun w hw => sub_nonneg.mpr (hle w hw)
  have g_pos_at_z : 0 < g z := sub_pos.mpr hlt
  -- The average of g is 0
  have g_avg : circleAverage g z₀ r = 0 := by
    have hci : CircleIntegrable f z₀ r := hcont.circleIntegrable'
    rw [show g = (fun _ => M) - f from rfl]
    rw [circleAverage_sub (circleIntegrable_const M z₀ r) hci]
    rw [circleAverage_const, havg, sub_self]
  -- But this contradicts g_pos_at_z since g is continuous and nonnegative
  -- A continuous nonnegative function with zero average must be zero everywhere
  have hci_g : CircleIntegrable g z₀ r := g_cont.circleIntegrable'
  -- Use that g(z) > 0 and g is continuous to get a neighborhood where g > 0
  -- The integral of g over that neighborhood is positive, contradiction
  have g_avg_pos : 0 < circleAverage g z₀ r := by
    -- Let h(θ) = g(circleMap z₀ r θ). This is continuous and nonneg, positive somewhere.
    let h : ℝ → ℝ := fun θ => g (circleMap z₀ r θ)
    have h_cont : Continuous h := g_cont.comp_continuous (continuous_circleMap z₀ r)
      (fun θ => circleMap_mem_sphere' z₀ r θ)
    have h_nonneg : ∀ θ, 0 ≤ h θ := fun θ => g_nonneg _ (circleMap_mem_sphere' z₀ r θ)
    have h_intble : IntervalIntegrable h MeasureTheory.volume 0 (2 * Real.pi) :=
      h_cont.intervalIntegrable _ _
    -- The circle average equals (2π)⁻¹ * ∫ h
    rw [circleAverage_def, smul_eq_mul]
    apply mul_pos (inv_pos.mpr Real.two_pi_pos)
    -- Use interval integral positivity: nonneg function with positive value somewhere
    -- The interval integral version: (0 < ∫ x in a..b, f x) ↔ a < b ∧ 0 < μ (support f ∩ Ioc a b)
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae
        (Filter.Eventually.of_forall h_nonneg) h_intble]
    constructor
    · exact Real.two_pi_pos
    · -- Show 0 < volume (support h ∩ Ioc 0 (2π))
      -- Since g(z) > 0 and z ∈ sphere, there exists θ₀ with h(θ₀) > 0
      -- By continuity, h > 0 on a neighborhood of θ₀
      -- This gives positive measure
      -- Key: the support of h is open (h continuous, (0, ∞) open)
      -- and nonempty (contains some θ with circleMap z₀ r θ = z)
      have h_support_open : IsOpen (Function.support h) := by
        rw [Function.support_eq_preimage]
        exact isOpen_compl_singleton.preimage h_cont
      -- The support intersects (0, 2π)
      -- Use: circleMap z₀ r is surjective onto sphere z₀ |r|
      -- So some θ ∈ [0, 2π) maps to z, and h(θ) = g(z) > 0
      have h_support_nonempty_in_interval : (Function.support h ∩ Ioc 0 (2 * Real.pi)).Nonempty := by
        -- z ∈ sphere z₀ |r|, so z = circleMap z₀ r θ for some θ ∈ Ioc 0 (2π)
        -- Use image_circleMap_Ioc: circleMap c R '' Ioc 0 (2π) = sphere c |R|
        have hz' : z ∈ sphere z₀ |r| := hz
        rw [← image_circleMap_Ioc z₀ r] at hz'
        obtain ⟨θ, hθ_mem, hθ_eq⟩ := hz'
        -- Now θ ∈ Ioc 0 (2π) and circleMap z₀ r θ = z, so h(θ) = g(z) > 0
        refine ⟨θ, ?_, hθ_mem⟩
        rw [Function.mem_support]
        simp only [h, hθ_eq, ne_eq]
        exact g_pos_at_z.ne'
      -- The support of h is open and intersects Ioc 0 (2π) nontrivially
      -- Since support h is open and nonempty in Ioc, it contains an open interval in Ioc
      -- which has positive Lebesgue measure
      obtain ⟨θ₀, hθ₀⟩ := h_support_nonempty_in_interval
      -- θ₀ is in the support of h (open set) and in Ioc 0 (2π)
      have hθ₀_support : θ₀ ∈ Function.support h := hθ₀.1
      have hθ₀_Ioc : θ₀ ∈ Ioc 0 (2 * Real.pi) := hθ₀.2
      -- Since support h is open, there's an interval around θ₀ in the support
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp h_support_open θ₀ hθ₀_support
      -- Take the intersection with Ioc 0 (2π)
      have hsub : Ioo (max 0 (θ₀ - ε)) (min (2 * Real.pi) (θ₀ + ε)) ⊆
             Function.support h ∩ Ioc 0 (2 * Real.pi) := by
        intro x hx
        constructor
        · apply hball
          rw [Metric.mem_ball, Real.dist_eq]
          have h1 : x < θ₀ + ε := lt_of_lt_of_le hx.2 (min_le_right _ _)
          have h2 : θ₀ - ε < x := lt_of_le_of_lt (le_max_right _ _) hx.1
          rw [abs_lt]
          constructor <;> linarith
        · constructor
          · exact lt_of_le_of_lt (le_max_left _ _) hx.1
          · exact le_of_lt (lt_of_lt_of_le hx.2 (min_le_left _ _))
      have hIoo_pos : 0 < volume (Ioo (max 0 (θ₀ - ε)) (min (2 * Real.pi) (θ₀ + ε))) := by
        rw [Measure.measure_Ioo_pos]
        -- Need: max 0 (θ₀ - ε) < min (2π) (θ₀ + ε)
        -- Use: max a b < c ↔ a < c ∧ b < c, and a < min b c ↔ a < b ∧ a < c
        apply max_lt
        · -- 0 < min (2π) (θ₀ + ε)
          apply lt_min
          · exact Real.two_pi_pos
          · linarith [hθ₀_Ioc.1]
        · -- θ₀ - ε < min (2π) (θ₀ + ε)
          apply lt_min
          · linarith [hθ₀_Ioc.2]
          · linarith
      exact lt_of_lt_of_le hIoo_pos (measure_mono hsub)
  linarith [g_avg_pos, g_avg.symm.le]

/-!
## Maximum Principle from Mean Value Property

The key insight is that if u(z₀) = max and u(z₀) = (average over circle),
then u must equal u(z₀) on the entire circle (since all values ≤ max).
-/

/-- Strong maximum principle for harmonic functions on a ball:
    If a harmonic function attains its maximum at the center, it's constant.

    This is the key lemma. The proof uses the mean value property:
    if f(z₀) = max and f(z₀) = average, then f = f(z₀) everywhere. -/
theorem harmonic_maximum_principle_ball {f : ℂ → ℝ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : HarmonicOnNhd f (closedBall z₀ r))
    (hmax : ∀ z ∈ closedBall z₀ r, f z ≤ f z₀) :
    ∀ z ∈ closedBall z₀ r, f z = f z₀ := by
  intro z hz
  -- If z = z₀, the result is trivial
  by_cases hzz : z = z₀
  · rw [hzz]
  -- Otherwise, z lies on some sphere of radius ρ = ‖z - z₀‖ with 0 < ρ ≤ r
  · have hρ_pos : 0 < ‖z - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzz)
    have hρ_le : ‖z - z₀‖ ≤ r := mem_closedBall.mp hz
    set ρ := ‖z - z₀‖ with hρ_def
    -- f is harmonic on closedBall z₀ ρ
    have hf_ρ : HarmonicOnNhd f (closedBall z₀ ρ) := fun w hw =>
      hf w (closedBall_subset_closedBall hρ_le hw)
    -- z ∈ sphere z₀ ρ (= sphere z₀ |ρ| since ρ > 0)
    have hz_sphere : z ∈ sphere z₀ |ρ| := by
      rw [mem_sphere, abs_of_pos hρ_pos, hρ_def, Complex.dist_eq]
    -- f ≤ f z₀ on sphere z₀ ρ
    have hle_sphere : ∀ w ∈ sphere z₀ |ρ|, f w ≤ f z₀ := fun w hw => by
      apply hmax
      rw [mem_sphere, abs_of_pos hρ_pos] at hw
      rw [mem_closedBall]
      calc dist w z₀ = ρ := hw
        _ ≤ r := hρ_le
    -- By mean value property: f z₀ = circleAverage f z₀ ρ
    have hmvp : circleAverage f z₀ ρ = f z₀ := by
      -- HarmonicOnNhd on closedBall z₀ ρ with ρ > 0 gives mean value property
      have hf_closed : HarmonicOnNhd f (closedBall z₀ |ρ|) := by
        rwa [abs_of_pos hρ_pos]
      exact HarmonicOnNhd.circleAverage_eq hf_closed
    -- f is continuous on sphere z₀ |ρ|
    have hcont : ContinuousOn f (sphere z₀ |ρ|) := by
      apply ContinuousOn.mono (HarmonicOnNhd.continuousOn hf_ρ)
      rw [abs_of_pos hρ_pos]
      exact sphere_subset_closedBall
    -- Apply eq_of_circleAverage_eq_of_le
    have hne : ρ ≠ 0 := hρ_pos.ne'
    exact eq_of_circleAverage_eq_of_le hne hcont hle_sphere hmvp z hz_sphere

/-- Maximum principle for harmonic functions on connected open sets. -/
theorem harmonic_maximum_principle_connected {f : ℂ → ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsConnected U)
    (hf : HarmonicOnNhd f U)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U) (hmax : ∀ z ∈ U, f z ≤ f z₀) :
    ∀ z ∈ U, f z = f z₀ := by
  -- Let S = {z ∈ U : f z = f z₀}. We show S is clopen in U.
  let S := {z ∈ U | f z = f z₀}
  -- S is nonempty (contains z₀)
  have hz₀S : z₀ ∈ S := ⟨hz₀, rfl⟩
  -- S is relatively open in U: if z ∈ S, then f = f(z₀) on a small ball around z
  have hopen : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    intro z ⟨hz, hfz⟩
    -- Get a small ball around z contained in U
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z hz
    -- On this ball, f attains max at z (since f(z) = f(z₀) = max)
    have hmax' : ∀ w ∈ closedBall z (r/2), f w ≤ f z := by
      intro w hw
      have hwU : w ∈ U := hball (closedBall_subset_ball (by linarith) hw)
      calc f w ≤ f z₀ := hmax w hwU
        _ = f z := hfz.symm
    -- Apply maximum principle on ball
    have hf' : HarmonicOnNhd f (closedBall z (r/2)) := by
      intro w hw
      exact hf w (hball (closedBall_subset_ball (by linarith) hw))
    have heq : ∀ w ∈ closedBall z (r/2), f w = f z :=
      harmonic_maximum_principle_ball (by linarith : 0 < r/2) hf' hmax'
    -- So ball z (r/2) ⊆ S
    refine ⟨ball z (r/2), ?_, ?_, mem_ball_self (by linarith)⟩
    · intro w hw
      constructor
      · exact hball (ball_subset_ball (by linarith) hw)
      · rw [heq w (ball_subset_closedBall hw), hfz]
    · exact isOpen_ball
  -- Use connectedness argument directly: S is open and nonempty, so if U \ S is also open,
  -- then by connectedness either S = ∅ or S = U. Since S ≠ ∅, we get S = U.
  -- To show U \ S is open, we show its complement in U (which is S) is closed relative to U.
  -- But we already showed S is open in the ambient space.
  -- Key: for connected U, if S ⊆ U is both open in ambient and relatively closed in U, then S = ∅ or S = U.
  -- Relative closure: S is closed in U iff for any sequence in S converging to z ∈ U, we have z ∈ S.
  -- This follows from continuity of f.
  have hcont_f : ContinuousOn f U := HarmonicOnNhd.continuousOn hf
  -- S is clopen in U (with subspace topology)
  -- We use IsPreconnected.subset_isClopen: if s is preconnected, t is clopen, s ∩ t nonempty, then s ⊆ t
  -- Here we need to work in the subspace topology
  -- Alternative: use IsConnected.eq_univ_of_nonempty_clopen on the subtype
  -- Actually, simplest is to use that S is open in ambient and equal to U ∩ f⁻¹'{f z₀}
  -- Since S is open and its complement in U is {z ∈ U | f z ≠ f z₀} = U ∩ f⁻¹'({f z₀}ᶜ)
  -- which is also open (since f is continuous on U and {f z₀}ᶜ is open)
  -- So S is clopen in U.
  have hS_def : S = U ∩ f ⁻¹' {f z₀} := by
    ext z; simp only [mem_sep_iff, mem_inter_iff, mem_preimage, mem_singleton_iff, S]
  have hS_complement_open : IsOpen (U \ S) := by
    have : U \ S = U ∩ f ⁻¹' {f z₀}ᶜ := by
      ext z
      simp only [mem_diff, mem_sep_iff, mem_inter_iff, mem_preimage, mem_compl_iff,
        mem_singleton_iff, not_and, S]
      constructor
      · intro ⟨hz, hne⟩; exact ⟨hz, hne hz⟩
      · intro ⟨hz, hne⟩; exact ⟨hz, fun _ => hne⟩
    rw [this]
    -- f is continuous on U, so f⁻¹'{f z₀}ᶜ ∩ U is open in U, hence open since U is open
    exact hcont_f.isOpen_inter_preimage hU isOpen_compl_singleton
  -- U is connected, S is nonempty and open, U \ S is open
  -- By connectedness, either S = ∅ or U \ S = ∅
  have hconn_pre : IsPreconnected U := hconn.isPreconnected
  have h_disjoint : Disjoint S (U \ S) := disjoint_sdiff_self_right
  have h_cover : U ⊆ S ∪ (U \ S) := fun z hz => by
    by_cases hzS : z ∈ S
    · exact Or.inl hzS
    · exact Or.inr ⟨hz, hzS⟩
  -- IsPreconnected means no separation by two disjoint open sets
  -- Since S and U \ S are both open, disjoint, cover U, and U is preconnected,
  -- one of them must be empty when intersected with U
  have h_union : U = S ∪ (U \ S) := by
    ext z; constructor
    · intro hz; exact h_cover hz
    · intro hz; cases hz with
      | inl h => exact h.1
      | inr h => exact h.1
  -- Use that preconnected sets can't be separated
  -- We want to show ∀ z ∈ U, f z = f z₀, i.e., U ⊆ S
  -- Use that S is clopen in U and U is connected
  -- Apply IsPreconnected.subset_left_of_subset_union
  intro z hz
  -- Use subset_left_of_subset_union: if U is preconnected, S and U\S are open,
  -- disjoint, cover U, and S ∩ U nonempty, then U ⊆ S
  have h_nonempty : (U ∩ S).Nonempty := ⟨z₀, hz₀, hz₀S⟩
  have h_subset := hconn_pre.subset_left_of_subset_union hopen hS_complement_open
    disjoint_sdiff_self_right h_cover h_nonempty
  exact (h_subset hz).2

/-- Minimum principle (maximum principle for -f). -/
theorem harmonic_minimum_principle_connected {f : ℂ → ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsConnected U)
    (hf : HarmonicOnNhd f U)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U) (hmin : ∀ z ∈ U, f z₀ ≤ f z) :
    ∀ z ∈ U, f z = f z₀ := by
  -- Apply maximum principle to -f
  have hf_neg : HarmonicOnNhd (-f) U := HarmonicOnNhd.neg hf
  have hmax : ∀ z ∈ U, (-f) z ≤ (-f) z₀ := by
    intro z hz
    simp only [Pi.neg_apply, neg_le_neg_iff]
    exact hmin z hz
  have heq := harmonic_maximum_principle_connected hU hconn hf_neg z₀ hz₀ hmax
  intro z hz
  have := heq z hz
  simp only [Pi.neg_apply, neg_inj] at this
  exact this

end RiemannSurfaces.Analytic.Infrastructure
