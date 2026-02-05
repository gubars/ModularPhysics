import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.Cohomology.AlgebraicCech
import ModularPhysics.StringGeometry.RiemannSurfaces.GAGA.Cohomology.ExactSequenceHelpers
import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.Helpers.ResidueTheory

/-!
# Infrastructure for the Point Exact Sequence

## ⚠️ DEPRECATED ⚠️

**This file uses a deprecated proof approach and is kept only for reference.**

The case analysis approach (proving `a + b = 1` by ruling out (0,0) and (1,1)) is
**NOT** the correct way to prove Riemann-Roch. The correct proof uses the
**abstract LES exactness** from sheaf cohomology directly:

1. The SES `0 → O(D-p) → O(D) → ℂ_p → 0` gives an LES in cohomology
2. The alternating sum formula for exact sequences gives `χ(D) - χ(D-p) = χ(ℂ_p) = 1`
3. This is a **consequence** of exactness, not something requiring case analysis

See `Cohomology/RiemannRoch.lean` for the correct approach.

## Original Documentation (Deprecated)

This file develops infrastructure for the point exact sequence, but the main theorem
`quotient_dim_sum_eq_one` uses an unnecessary case analysis approach that requires
the residue theorem. This is mathematically valid but overly complicated.

The DVR helper lemmas (localParameter, valuation) may still be useful for other purposes.
-/

namespace RiemannSurfaces.Algebraic.PointExactInfra

open Algebraic CompactAlgebraicCurve Core.Divisor
open scoped Classical

variable (C : Algebraic.CompactAlgebraicCurve)
variable (K : Cohomology.CanonicalDivisor C)
variable (D : Core.Divisor C.toAlgebraicCurve)
variable (p : C.toAlgebraicCurve.Point)

/-!
## DVR Helper Lemmas

These lemmas about local parameters and valuations are needed for the
leading coefficient definition and the exact sequence infrastructure.
-/

/-- Helper: local parameter is nonzero -/
theorem localParameter_ne_zero : C.localParameter p ≠ 0 := by
  intro h
  have := C.localParameter_valuation p
  rw [h, C.toAlgebraicCurve.valuation_zero] at this
  omega

/-- Helper: local parameter power is nonzero -/
theorem localParameter_zpow_ne_zero (n : ℤ) : C.localParameter p ^ n ≠ 0 :=
  zpow_ne_zero n (localParameter_ne_zero C p)

/-- Helper: valuation of natural power of local parameter -/
theorem valuation_localParameter_pow (k : ℕ) :
    C.valuation p (C.localParameter p ^ k) = k := by
  have ht_ne := localParameter_ne_zero C p
  induction k with
  | zero => simp [C.toAlgebraicCurve.valuation_one]
  | succ k ih =>
    rw [pow_succ]
    have hpow_ne : C.localParameter p ^ k ≠ 0 := pow_ne_zero k ht_ne
    rw [C.toAlgebraicCurve.valuation_mul p _ _ hpow_ne ht_ne, ih, C.localParameter_valuation]
    omega

/-- Helper: valuation of integer power of local parameter -/
theorem valuation_localParameter_zpow (n : ℤ) :
    C.valuation p (C.localParameter p ^ n) = n := by
  have ht_ne := localParameter_ne_zero C p
  cases n with
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact_mod_cast valuation_localParameter_pow C p k
  | negSucc k =>
    simp only [zpow_negSucc]
    have hpow_ne : C.localParameter p ^ (k + 1) ≠ 0 := pow_ne_zero (k + 1) ht_ne
    rw [C.toAlgebraicCurve.valuation_inv p _ hpow_ne]
    have hpow_val : C.valuation p (C.localParameter p ^ (k + 1)) = k + 1 :=
      valuation_localParameter_pow C p (k + 1)
    omega

/-!
## The Evaluation Map

The evaluation map eval: L(D) → ℂ extracts the "leading coefficient" of f at p.
For f ∈ L(D), if v_p(f) = -D(p), the leading coefficient is the coefficient
of t_p^{-D(p)} in the Laurent expansion.
-/

/-- The leading coefficient of f at p.

    For f ∈ K(C) with v_p(f) = n, we can write f = c · t_p^n + (higher order terms)
    where t_p is the local parameter at p. The leading coefficient is c.

    This is well-defined by the DVR structure (leadingCoefficientUniquenessGeneral). -/
noncomputable def leadingCoeff (f : C.FunctionField) (hf : f ≠ 0) : ℂ :=
  -- The leading coefficient exists and is unique by the DVR structure
  -- For f with v_p(f) = n, this is the unique c such that v_p(f - c·t_p^n) > n
  -- We use leadingCoefficientUniquenessGeneral with t^n and f
  Classical.choose (C.leadingCoefficientUniquenessGeneral p
    (C.localParameter p ^ (C.valuation p f))
    f
    (localParameter_zpow_ne_zero C p _)
    hf
    (valuation_localParameter_zpow C p (C.valuation p f)))

/-!
## DVR Leading Coefficient Properties

The leading coefficient satisfies several important algebraic properties that
are essential for proving linearity of the evaluation and connecting maps.
-/

/-- Helper: algebraMap of nonzero is nonzero (uses field structure) -/
theorem algebraMap_ne_zero' (r : ℂ) (hr : r ≠ 0) :
    algebraMap ℂ C.FunctionField r ≠ 0 := by
  intro h
  -- algebraMap is a ring homomorphism from a field, so injective.
  have hinj : Function.Injective (algebraMap ℂ C.FunctionField) := by
    intro a b hab
    by_contra hne
    have hsub_ne : a - b ≠ 0 := sub_ne_zero.mpr hne
    have h0 : algebraMap ℂ C.FunctionField (a - b) = 0 := by simp [hab]
    have h1 : algebraMap ℂ C.FunctionField ((a - b)⁻¹ * (a - b)) = 1 := by
      simp [inv_mul_cancel₀ hsub_ne]
    rw [map_mul, h0, mul_zero] at h1
    exact zero_ne_one h1
  have h' : algebraMap ℂ C.FunctionField r = algebraMap ℂ C.FunctionField 0 := by simp [h]
  exact hr (hinj h')

/-- The leading coefficient is nonzero. -/
theorem leadingCoeff_ne_zero (f : C.FunctionField) (hf : f ≠ 0) :
    leadingCoeff C p f hf ≠ 0 := by
  unfold leadingCoeff
  -- The leading coefficient is Classical.choose from leadingCoefficientUniquenessGeneral
  -- The spec says c ≠ 0
  exact (Classical.choose_spec (C.leadingCoefficientUniquenessGeneral p
    (C.localParameter p ^ (C.valuation p f)) f
    (localParameter_zpow_ne_zero C p _) hf
    (valuation_localParameter_zpow C p (C.valuation p f)))).1

/-- Negation preserves valuation. -/
theorem valuation_neg (f : C.FunctionField) :
    C.valuation p (-f) = C.valuation p f := by
  by_cases hf : f = 0
  · simp [hf]
  · have hneg1_ne : (-1 : C.FunctionField) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have h1 : C.valuation p (-1) + C.valuation p (-1) = C.valuation p 1 := by
      rw [← C.toAlgebraicCurve.valuation_mul p (-1) (-1) hneg1_ne hneg1_ne]
      ring_nf
    rw [C.toAlgebraicCurve.valuation_one] at h1
    have hneg1_val : C.valuation p (-1) = 0 := by omega
    have : -f = -1 * f := by ring
    rw [this, C.toAlgebraicCurve.valuation_mul p (-1) f hneg1_ne hf, hneg1_val, zero_add]

/-- Scalar multiplication doesn't change valuation (for nonzero scalar). -/
theorem valuation_smul (r : ℂ) (f : C.FunctionField) (hr : r ≠ 0) :
    C.valuation p (algebraMap ℂ C.FunctionField r * f) = C.valuation p f := by
  by_cases hf : f = 0
  · simp [hf]
  · have hr_ne := algebraMap_ne_zero' C r hr
    rw [C.toAlgebraicCurve.valuation_mul p _ f hr_ne hf]
    rw [C.algebraInst.valuation_algebraMap p r hr]
    ring

/-- When valuations differ, the sum has valuation equal to the minimum. -/
theorem valuation_add_eq_min_of_ne (f g : C.FunctionField)
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hvne : C.valuation p f ≠ C.valuation p g)
    (hfg : f + g ≠ 0) :
    C.valuation p (f + g) = min (C.valuation p f) (C.valuation p g) := by
  have hmin := C.toAlgebraicCurve.valuation_add_min p f g hfg
  -- The ultrametric inequality v(f+g) ≥ min(v(f), v(g)) becomes equality when v(f) ≠ v(g)
  rcases lt_trichotomy (C.valuation p f) (C.valuation p g) with hvlt | hveq | hvgt
  · -- Case v(f) < v(g)
    have hmin_eq : min (C.valuation p f) (C.valuation p g) = C.valuation p f := min_eq_left (le_of_lt hvlt)
    rw [hmin_eq] at hmin ⊢
    by_contra hvfg_ne
    have hvfg_strict : C.valuation p (f + g) > C.valuation p f := lt_of_le_of_ne hmin (Ne.symm hvfg_ne)
    have hneg_g_ne : -g ≠ 0 := neg_ne_zero.mpr hg
    have hv_neg_g : C.valuation p (-g) = C.valuation p g := valuation_neg C p g
    -- f = (f + g) + (-g), so v(f) ≥ min(v(f+g), v(-g))
    have hv_f_bound : C.valuation p f ≥ min (C.valuation p (f + g)) (C.valuation p (-g)) := by
      have hf_eq : f = (f + g) + (-g) := by ring
      have h := C.toAlgebraicCurve.valuation_add_min p (f + g) (-g) (by rw [← hf_eq]; exact hf)
      have heq : (f + g) + (-g) = f := by ring
      rw [heq] at h
      exact h
    -- But min(v(f+g), v(-g)) = min(v(f+g), v(g)) > v(f)
    have hmin_gt : min (C.valuation p (f + g)) (C.valuation p (-g)) > C.valuation p f := by
      rw [hv_neg_g]; exact lt_min hvfg_strict hvlt
    -- Contradiction: v(f) ≥ something > v(f)
    linarith
  · exact absurd hveq hvne
  · -- Case v(f) > v(g)
    have hmin_eq : min (C.valuation p f) (C.valuation p g) = C.valuation p g := min_eq_right (le_of_lt hvgt)
    rw [hmin_eq] at hmin ⊢
    by_contra hvfg_ne
    have hvfg_strict : C.valuation p (f + g) > C.valuation p g := lt_of_le_of_ne hmin (Ne.symm hvfg_ne)
    have hneg_f_ne : -f ≠ 0 := neg_ne_zero.mpr hf
    have hv_neg_f : C.valuation p (-f) = C.valuation p f := valuation_neg C p f
    -- g = (f + g) + (-f), so v(g) ≥ min(v(f+g), v(-f))
    have hv_g_bound : C.valuation p g ≥ min (C.valuation p (f + g)) (C.valuation p (-f)) := by
      have hg_eq : g = (f + g) + (-f) := by ring
      have h := C.toAlgebraicCurve.valuation_add_min p (f + g) (-f) (by rw [← hg_eq]; exact hg)
      have heq : (f + g) + (-f) = g := by ring
      rw [heq] at h
      exact h
    -- But min(v(f+g), v(-f)) = min(v(f+g), v(f)) > v(g)
    have hmin_gt : min (C.valuation p (f + g)) (C.valuation p (-f)) > C.valuation p g := by
      rw [hv_neg_f]; exact lt_min hvfg_strict hvgt
    linarith

/-- When both elements have the same valuation and the sum has higher valuation,
    the leading coefficients cancel. -/
theorem leadingCoeff_add_cancel (f g : C.FunctionField)
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hveq : C.valuation p f = C.valuation p g)
    (hvfg_higher : f + g = 0 ∨ C.valuation p (f + g) > C.valuation p f) :
    leadingCoeff C p f hf + leadingCoeff C p g hg = 0 := by
  -- Get the specs for the leading coefficients
  set n := C.valuation p f with hn_def
  set t := C.localParameter p with ht_def
  set c_f := leadingCoeff C p f hf with hcf_def
  set c_g := leadingCoeff C p g hg with hcg_def

  -- v_p(g) = n by hypothesis
  have hg_val_eq_n : C.valuation p g = n := hveq.symm
  -- Key fact: t^{v_p(g)} = t^n since v_p(g) = n
  have htpow_g_eq : C.localParameter p ^ C.valuation p g = t ^ n := by rw [hg_val_eq_n]

  -- c_f ≠ 0 and c_g ≠ 0
  have hcf_ne : c_f ≠ 0 := leadingCoeff_ne_zero C p f hf
  have hcg_ne : c_g ≠ 0 := leadingCoeff_ne_zero C p g hg

  -- Get the raw specs
  have hspec_f_raw := Classical.choose_spec (C.leadingCoefficientUniquenessGeneral p
    (C.localParameter p ^ (C.valuation p f)) f (localParameter_zpow_ne_zero C p _) hf
    (valuation_localParameter_zpow C p (C.valuation p f)))
  have hspec_g_raw := Classical.choose_spec (C.leadingCoefficientUniquenessGeneral p
    (C.localParameter p ^ (C.valuation p g)) g (localParameter_zpow_ne_zero C p _) hg
    (valuation_localParameter_zpow C p (C.valuation p g)))

  -- Convert specs to use t^n and c_f, c_g explicitly
  -- For f: n = v_p(f) so t^n = t^{v_p(f)} definitionally
  have hf_spec : f - algebraMap ℂ C.FunctionField c_f * (t ^ n) = 0 ∨
      C.valuation p (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) > n :=
    hspec_f_raw.2

  -- For g: need to substitute v_p(g) = n
  have hg_spec : g - algebraMap ℂ C.FunctionField c_g * (t ^ n) = 0 ∨
      C.valuation p (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) > n := by
    rcases hspec_g_raw.2 with hg_eq_raw | hg_gt_raw
    · left; simp only [← htpow_g_eq]; exact hg_eq_raw
    · right; simp only [← hg_val_eq_n]; exact hg_gt_raw

  -- The sum (f - c_f * t^n) + (g - c_g * t^n) = (f + g) - (c_f + c_g) * t^n
  have hsum_eq : (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
      (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) =
      (f + g) - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n) := by
    simp only [map_add]; ring

  -- Prove by contradiction: assume c_f + c_g ≠ 0
  by_contra h_sum_ne
  have htn_ne : t ^ n ≠ 0 := localParameter_zpow_ne_zero C p n
  have hcsum_ne := algebraMap_ne_zero' C (c_f + c_g) h_sum_ne
  have hcsum_tn_ne : algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n) ≠ 0 :=
    mul_ne_zero hcsum_ne htn_ne

  -- The term (c_f + c_g) * t^n has valuation n
  have hv_csum_tn : C.valuation p (algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) = n := by
    rw [C.toAlgebraicCurve.valuation_mul p _ _ hcsum_ne htn_ne]
    rw [C.algebraInst.valuation_algebraMap p _ h_sum_ne]
    rw [valuation_localParameter_zpow C p n]
    ring

  -- Case analysis on hvfg_higher
  rcases hvfg_higher with hfg_zero | hfg_higher
  · -- Case: f + g = 0
    -- Then (f + g) - (c_f + c_g) * t^n = -(c_f + c_g) * t^n
    have h_eq : (f + g) - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n) =
        -(algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) := by
      rw [hfg_zero]; ring
    -- This has valuation n (not > n), contradiction with the spec
    -- We need to show that (f - c_f*t^n) + (g - c_g*t^n) has valuation > n
    -- But (f - c_f*t^n) + (g - c_g*t^n) = -(c_f + c_g)*t^n which has valuation = n
    have hv_neg : C.valuation p (-(algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n))) = n := by
      rw [valuation_neg C p]; exact hv_csum_tn

    -- From the specs, (f - c_f*t^n) + (g - c_g*t^n) should have valuation > n
    -- (using ultrametric inequality when both summands have val > n)
    rcases hf_spec with hf_eq | hf_gt
    · -- f = c_f * t^n (from f - c_f*t^n = 0)
      have hf_eq' : f = algebraMap ℂ C.FunctionField c_f * (t ^ n) := sub_eq_zero.mp hf_eq
      rcases hg_spec with hg_eq | hg_gt
      · -- g = c_g * t^n
        have hg_eq' : g = algebraMap ℂ C.FunctionField c_g * (t ^ n) := sub_eq_zero.mp hg_eq
        -- f + g = (c_f + c_g) * t^n
        have hfg_eq : f + g = algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n) := by
          rw [hf_eq', hg_eq']; simp only [map_add]; ring
        -- But f + g = 0, so (c_f + c_g) * t^n = 0
        rw [hfg_zero] at hfg_eq
        -- Since c_f + c_g ≠ 0, we have t^n = 0, contradiction
        have h0 : algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n) = 0 := hfg_eq.symm
        have := mul_eq_zero.mp h0
        rcases this with hcontr | hcontr
        · exact hcsum_ne hcontr
        · exact htn_ne hcontr
      · -- v_p(g - c_g*t^n) > n
        -- (f - c_f*t^n) + (g - c_g*t^n) = 0 + (g - c_g*t^n) = g - c_g*t^n
        have hsum_simp : (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
            (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) =
            g - algebraMap ℂ C.FunctionField c_g * (t ^ n) := by
          rw [sub_eq_zero.mp hf_eq]; ring
        rw [hsum_eq, h_eq] at hsum_simp
        -- So g - c_g*t^n = -(c_f + c_g)*t^n
        -- v_p(g - c_g*t^n) > v_p(g) and v_p(-(c_f + c_g)*t^n) = n = v_p(g)
        -- But they're equal, contradiction
        have hg_sub_eq : g - algebraMap ℂ C.FunctionField c_g * (t ^ n) =
            -(algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) := hsum_simp.symm
        have hv_gsub : C.valuation p (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) = n := by
          rw [hg_sub_eq]; exact hv_neg
        -- hg_gt already has type ... > n (from hg_spec), so just use linarith
        linarith
    · -- v_p(f - c_f*t^n) > n = v_p(f)
      rcases hg_spec with hg_eq | hg_gt
      · -- g = c_g * t^n, so g - c_g*t^n = 0
        have hsum_simp : (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
            (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) =
            f - algebraMap ℂ C.FunctionField c_f * (t ^ n) := by
          rw [sub_eq_zero.mp hg_eq]; ring
        rw [hsum_eq, h_eq] at hsum_simp
        have hf_sub_eq : f - algebraMap ℂ C.FunctionField c_f * (t ^ n) =
            -(algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) := hsum_simp.symm
        have hv_fsub : C.valuation p (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) = n := by
          rw [hf_sub_eq]; exact hv_neg
        linarith
      · -- Both have valuation > n
        -- The sum (f - c_f*t^n) + (g - c_g*t^n) = -(c_f + c_g)*t^n has valuation = n
        -- But if both summands have valuation > n, the sum should also have valuation > n
        -- (unless they cancel to 0, but the sum = -(c_f+c_g)*t^n ≠ 0)

        -- First, note that the sum equals -(c_f + c_g)*t^n
        have hsum_eq_neg : (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
            (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) =
            -(algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) := by
          rw [hsum_eq, h_eq]

        -- Case analysis: is f - c_f*t^n = 0?
        by_cases hf_sub_zero : f - algebraMap ℂ C.FunctionField c_f * (t ^ n) = 0
        · -- If f - c_f*t^n = 0, then f = c_f*t^n
          -- Since f + g = 0, we have g = -f = -c_f*t^n
          have hf_eq' : f = algebraMap ℂ C.FunctionField c_f * (t ^ n) := sub_eq_zero.mp hf_sub_zero
          have hg_eq' : g = -(algebraMap ℂ C.FunctionField c_f * (t ^ n)) := by
            have h : f + g = 0 := hfg_zero
            rw [hf_eq'] at h
            exact (neg_eq_of_add_eq_zero_right h).symm
          -- Then g - c_g*t^n = -c_f*t^n - c_g*t^n = -(c_f + c_g)*t^n
          have hg_sub : g - algebraMap ℂ C.FunctionField c_g * (t ^ n) =
              -(algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) := by
            rw [hg_eq']; simp only [map_add]; ring
          -- v_p(g - c_g*t^n) = v_p(-(c_f + c_g)*t^n) = n
          have hv_gsub : C.valuation p (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) = n := by
            rw [hg_sub, valuation_neg C p, hv_csum_tn]
          -- But hg_gt says v_p(g - c_g*t^n) > n, contradiction
          linarith
        · -- f - c_f*t^n ≠ 0
          by_cases hg_sub_zero : g - algebraMap ℂ C.FunctionField c_g * (t ^ n) = 0
          · -- Similarly, if g - c_g*t^n = 0, then g = c_g*t^n, f = -g = -c_g*t^n
            have hg_eq' : g = algebraMap ℂ C.FunctionField c_g * (t ^ n) := sub_eq_zero.mp hg_sub_zero
            have hf_eq' : f = -(algebraMap ℂ C.FunctionField c_g * (t ^ n)) := by
              have h1 : f = -g := add_eq_zero_iff_eq_neg.mp hfg_zero
              rw [h1, hg_eq']
            have hf_sub : f - algebraMap ℂ C.FunctionField c_f * (t ^ n) =
                -(algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) := by
              rw [hf_eq']; simp only [map_add]; ring
            have hv_fsub : C.valuation p (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) = n := by
              rw [hf_sub, valuation_neg C p, hv_csum_tn]
            linarith
          · -- Both f - c_f*t^n ≠ 0 and g - c_g*t^n ≠ 0
            -- Their sum = -(c_f + c_g)*t^n ≠ 0
            have hsum_ne : (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
                (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) ≠ 0 := by
              rw [hsum_eq_neg]; exact neg_ne_zero.mpr hcsum_tn_ne
            -- By ultrametric: v_p(sum) ≥ min(v_p(f-c_f*t^n), v_p(g-c_g*t^n)) > n
            have hsum_val := C.toAlgebraicCurve.valuation_add_min p _ _ hsum_ne
            have hmin_gt : min (C.valuation p (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)))
                (C.valuation p (g - algebraMap ℂ C.FunctionField c_g * (t ^ n))) > n :=
              lt_min hf_gt hg_gt
            -- But sum = -(c_f + c_g)*t^n has valuation = n
            have hv_sum : C.valuation p ((f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
                (g - algebraMap ℂ C.FunctionField c_g * (t ^ n))) = n := by
              rw [hsum_eq_neg, valuation_neg C p, hv_csum_tn]
            linarith

  · -- Case: v_p(f + g) > n
    -- Need to handle two sub-cases: f + g = 0 or f + g ≠ 0
    -- (When n < 0, v_p(0) = 0 > n is true, so hfg_higher doesn't exclude f + g = 0)

    by_cases hfg_zero' : f + g = 0
    · -- Sub-case: f + g = 0 (same as the previous case)
      -- Then (f + g) - (c_f + c_g) * t^n = -(c_f + c_g) * t^n
      have h_eq' : (f + g) - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n) =
          -(algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) := by
        rw [hfg_zero']; ring
      have hv_neg' : C.valuation p (-(algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n))) = n := by
        rw [valuation_neg C p]; exact hv_csum_tn

      -- Same proof as the hfg_zero case
      rcases hf_spec with hf_eq | hf_gt
      · have hf_eq' : f = algebraMap ℂ C.FunctionField c_f * (t ^ n) := sub_eq_zero.mp hf_eq
        rcases hg_spec with hg_eq | hg_gt
        · have hg_eq' : g = algebraMap ℂ C.FunctionField c_g * (t ^ n) := sub_eq_zero.mp hg_eq
          have hfg_eq : f + g = algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n) := by
            rw [hf_eq', hg_eq']; simp only [map_add]; ring
          rw [hfg_zero'] at hfg_eq
          have h0 : algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n) = 0 := hfg_eq.symm
          have := mul_eq_zero.mp h0
          rcases this with hcontr | hcontr
          · exact hcsum_ne hcontr
          · exact htn_ne hcontr
        · have hsum_simp : f + g - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n) =
              g - algebraMap ℂ C.FunctionField c_g * (t ^ n) := by
            have hf_eq'' := sub_eq_zero.mp hf_eq
            simp only [hf_eq'', map_add]; ring
          have hv_gsub : C.valuation p (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) = n := by
            have h1 : C.valuation p (f + g - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) = n := by
              rw [h_eq']; exact hv_neg'
            rw [hsum_simp] at h1; exact h1
          linarith
      · rcases hg_spec with hg_eq | hg_gt
        · have hsum_simp : f + g - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n) =
              f - algebraMap ℂ C.FunctionField c_f * (t ^ n) := by
            have hg_eq'' := sub_eq_zero.mp hg_eq
            simp only [hg_eq'', map_add]; ring
          have hv_fsub : C.valuation p (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) = n := by
            have h1 : C.valuation p (f + g - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) = n := by
              rw [h_eq']; exact hv_neg'
            rw [hsum_simp] at h1; exact h1
          linarith
        · -- Both have valuation > n, same as before
          have hsum_eq_neg' : (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
              (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) =
              -(algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) := by
            rw [hsum_eq, h_eq']
          by_cases hf_sub_zero : f - algebraMap ℂ C.FunctionField c_f * (t ^ n) = 0
          · have hf_eq'' : f = algebraMap ℂ C.FunctionField c_f * (t ^ n) := sub_eq_zero.mp hf_sub_zero
            have hg_eq'' : g = -(algebraMap ℂ C.FunctionField c_f * (t ^ n)) := by
              have h1 : f = -g := add_eq_zero_iff_eq_neg.mp hfg_zero'
              rw [hf_eq''] at h1
              -- h1 : c_f * t^n = -g, so g = -(c_f * t^n)
              have h2 : algebraMap ℂ C.FunctionField c_f * (t ^ n) + g = 0 := by
                rw [h1]; ring
              exact (neg_eq_of_add_eq_zero_right h2).symm
            have hg_sub : g - algebraMap ℂ C.FunctionField c_g * (t ^ n) =
                -(algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) := by
              rw [hg_eq'']; simp only [map_add]; ring
            have hv_gsub : C.valuation p (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) = n := by
              rw [hg_sub, valuation_neg C p, hv_csum_tn]
            linarith
          · by_cases hg_sub_zero : g - algebraMap ℂ C.FunctionField c_g * (t ^ n) = 0
            · have hg_eq'' : g = algebraMap ℂ C.FunctionField c_g * (t ^ n) := sub_eq_zero.mp hg_sub_zero
              have hf_eq'' : f = -(algebraMap ℂ C.FunctionField c_g * (t ^ n)) := by
                have h1 : f = -g := add_eq_zero_iff_eq_neg.mp hfg_zero'
                rw [h1, hg_eq'']
              have hf_sub : f - algebraMap ℂ C.FunctionField c_f * (t ^ n) =
                  -(algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) := by
                rw [hf_eq'']; simp only [map_add]; ring
              have hv_fsub : C.valuation p (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) = n := by
                rw [hf_sub, valuation_neg C p, hv_csum_tn]
              linarith
            · have hsum_ne : (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
                  (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) ≠ 0 := by
                rw [hsum_eq_neg']; exact neg_ne_zero.mpr hcsum_tn_ne
              have hsum_val := C.toAlgebraicCurve.valuation_add_min p _ _ hsum_ne
              have hmin_gt : min (C.valuation p (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)))
                  (C.valuation p (g - algebraMap ℂ C.FunctionField c_g * (t ^ n))) > n :=
                lt_min hf_gt hg_gt
              have hv_sum : C.valuation p ((f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
                  (g - algebraMap ℂ C.FunctionField c_g * (t ^ n))) = n := by
                rw [hsum_eq_neg', valuation_neg C p, hv_csum_tn]
              linarith

    · -- Sub-case: f + g ≠ 0
      have hfg_ne := hfg_zero'

      -- The difference (f + g) - (c_f + c_g) * t^n
      have hdiff_ne : (f + g) - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n) ≠ 0 := by
        intro heq
        -- If diff = 0, then f + g = (c_f + c_g) * t^n
        have h_eq : f + g = algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n) := sub_eq_zero.mp heq
        -- v_p(f + g) = v_p((c_f + c_g) * t^n) = n
        rw [h_eq] at hfg_higher
        linarith

      -- Use ultrametric: v_p(a - b) = min(v_p(a), v_p(b)) when v_p(a) ≠ v_p(b)
      have hne_vals : C.valuation p (f + g) ≠ C.valuation p (algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) := by
        rw [hv_csum_tn]; exact ne_of_gt hfg_higher

      -- Convert hdiff_ne to add-neg form
      have hdiff_ne' : f + g + (-(algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n))) ≠ 0 := by
        convert hdiff_ne using 1; ring

      have hdiff_val := valuation_add_eq_min_of_ne C p (f + g) (-(algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)))
        hfg_ne (neg_ne_zero.mpr hcsum_tn_ne)
        (by rw [valuation_neg C p, hv_csum_tn]; exact ne_of_gt hfg_higher)
        hdiff_ne'

      rw [valuation_neg C p, hv_csum_tn] at hdiff_val
      have hmin_eq_n : min (C.valuation p (f + g)) n = n := min_eq_right (le_of_lt hfg_higher)
      rw [hmin_eq_n] at hdiff_val

      -- Now we have v_p((f+g) - (c_f+c_g)*t^n) = n
      -- But from the specs, (f - c_f*t^n) + (g - c_g*t^n) should have valuation > n
      rcases hf_spec with hf_eq | hf_gt
      · rcases hg_spec with hg_eq | hg_gt
        · -- Both are exact: f = c_f*t^n, g = c_g*t^n
          have hf_eq' : f = algebraMap ℂ C.FunctionField c_f * (t ^ n) := sub_eq_zero.mp hf_eq
          have hg_eq' : g = algebraMap ℂ C.FunctionField c_g * (t ^ n) := sub_eq_zero.mp hg_eq
          have hfg_eq : f + g = algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n) := by
            rw [hf_eq', hg_eq']; simp only [map_add]; ring
          rw [hfg_eq] at hfg_higher
          linarith
        · -- f exact, g has higher valuation
          have hsum_simp : f + g - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n) =
              g - algebraMap ℂ C.FunctionField c_g * (t ^ n) := by
            have hf_eq' := sub_eq_zero.mp hf_eq
            simp only [hf_eq', map_add]; ring
          -- Convert hdiff_val to subtraction form and use hsum_simp
          have hdiff_val' : C.valuation p (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) = n := by
            have h1 : C.valuation p (f + g - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) = n := by
              convert hdiff_val using 2; ring
            rw [hsum_simp] at h1
            exact h1
          linarith
      · rcases hg_spec with hg_eq | hg_gt
        · have hsum_simp : f + g - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n) =
              f - algebraMap ℂ C.FunctionField c_f * (t ^ n) := by
            have hg_eq' := sub_eq_zero.mp hg_eq
            simp only [hg_eq', map_add]; ring
          -- Convert hdiff_val to subtraction form and use hsum_simp
          have hdiff_val' : C.valuation p (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) = n := by
            have h1 : C.valuation p (f + g - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) = n := by
              convert hdiff_val using 2; ring
            rw [hsum_simp] at h1
            exact h1
          linarith
        · -- Both have higher valuation
          -- We know (f - c_f*t^n) + (g - c_g*t^n) = f + g - (c_f+c_g)*t^n ≠ 0
          have hsum_ne' : (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
              (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) ≠ 0 := by
            rw [hsum_eq]; exact hdiff_ne
          have hsum_val := C.toAlgebraicCurve.valuation_add_min p _ _ hsum_ne'
          -- hsum_val : v_p(sum) ≥ min(v_p(f - c_f*t^n), v_p(g - c_g*t^n))
          -- We want to show min(...) > n, but this requires handling the case where
          -- f - c_f*t^n = 0 or g - c_g*t^n = 0
          -- When n < 0: if f - c_f*t^n = 0, then v_p(0) = 0 > n, so hf_gt is satisfied
          -- But then the term contributes 0 to the sum

          -- Case analysis on whether the individual terms are zero
          by_cases hf_sub_zero : f - algebraMap ℂ C.FunctionField c_f * (t ^ n) = 0
          · -- f = c_f * t^n exactly
            have hsum_simp : (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
                (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) =
                g - algebraMap ℂ C.FunctionField c_g * (t ^ n) := by
              rw [hf_sub_zero]; ring
            -- So v_p(sum) = v_p(g - c_g*t^n) > n by hg_gt
            have hsum_val' : C.valuation p ((f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
                (g - algebraMap ℂ C.FunctionField c_g * (t ^ n))) > n := by
              rw [hsum_simp]; exact hg_gt
            -- But by hsum_eq, sum = f + g - (c_f + c_g)*t^n
            have hsum_val'' : C.valuation p (f + g - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) > n := by
              rw [← hsum_eq]; exact hsum_val'
            -- But hdiff_val says v_p(...) = n
            have hdiff_val' : C.valuation p (f + g - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) = n := by
              convert hdiff_val using 2; ring
            linarith
          · by_cases hg_sub_zero : g - algebraMap ℂ C.FunctionField c_g * (t ^ n) = 0
            · -- g = c_g * t^n exactly, f - c_f*t^n ≠ 0
              have hsum_simp : (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
                  (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) =
                  f - algebraMap ℂ C.FunctionField c_f * (t ^ n) := by
                rw [hg_sub_zero]; ring
              have hsum_val' : C.valuation p ((f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
                  (g - algebraMap ℂ C.FunctionField c_g * (t ^ n))) > n := by
                rw [hsum_simp]; exact hf_gt
              have hsum_val'' : C.valuation p (f + g - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) > n := by
                rw [← hsum_eq]; exact hsum_val'
              have hdiff_val' : C.valuation p (f + g - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) = n := by
                convert hdiff_val using 2; ring
              linarith
            · -- Both f - c_f*t^n ≠ 0 and g - c_g*t^n ≠ 0
              have hmin_gt : min (C.valuation p (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)))
                  (C.valuation p (g - algebraMap ℂ C.FunctionField c_g * (t ^ n))) > n :=
                lt_min hf_gt hg_gt
              have hsum_val' : C.valuation p (f + g - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) ≥
                  min (C.valuation p (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)))
                      (C.valuation p (g - algebraMap ℂ C.FunctionField c_g * (t ^ n))) := by
                rw [← hsum_eq]; exact hsum_val
              have hdiff_val' : C.valuation p (f + g - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) = n := by
                convert hdiff_val using 2; ring
              linarith

/-- The leading coefficient is unique: if c satisfies the spec, then c = leadingCoeff. -/
theorem leadingCoeff_unique (f : C.FunctionField) (hf : f ≠ 0) (c : ℂ) (_hc : c ≠ 0)
    (hspec : f - algebraMap ℂ C.FunctionField c * (C.localParameter p ^ C.valuation p f) = 0 ∨
             C.valuation p (f - algebraMap ℂ C.FunctionField c * (C.localParameter p ^ C.valuation p f)) >
             C.valuation p f) :
    c = leadingCoeff C p f hf := by
  set n := C.valuation p f with hn_def
  set t := C.localParameter p with ht_def
  have htn_ne : t ^ n ≠ 0 := localParameter_zpow_ne_zero C p n

  -- Get spec for leadingCoeff (c₀)
  -- Note: leadingCoeff C p f hf = Classical.choose (...)
  have hspec_c₀ := Classical.choose_spec (C.leadingCoefficientUniquenessGeneral p
    (C.localParameter p ^ (C.valuation p f)) f (localParameter_zpow_ne_zero C p _) hf
    (valuation_localParameter_zpow C p (C.valuation p f)))

  -- c₀ is the Classical.choose, so hspec_c₀.1 says c₀ ≠ 0
  -- and hspec_c₀.2 says f - c₀ * t^n = 0 or v_p(f - c₀ * t^n) > n
  -- Note: the spec uses the SAME expression as leadingCoeff definition
  set c₀ := Classical.choose (C.leadingCoefficientUniquenessGeneral p
    (C.localParameter p ^ (C.valuation p f)) f (localParameter_zpow_ne_zero C p _) hf
    (valuation_localParameter_zpow C p (C.valuation p f))) with hc₀_def

  have hc₀_ne : c₀ ≠ 0 := hspec_c₀.1
  have hspec_c₀' := hspec_c₀.2

  -- leadingCoeff C p f hf = c₀ by definition
  have hlc_eq : leadingCoeff C p f hf = c₀ := rfl

  -- (c - c₀) * t^n = (f - c₀*t^n) - (f - c*t^n)
  have hdiff_eq : algebraMap ℂ C.FunctionField (c - c₀) * (t ^ n) =
      (f - algebraMap ℂ C.FunctionField c₀ * (t ^ n)) -
      (f - algebraMap ℂ C.FunctionField c * (t ^ n)) := by
    simp only [map_sub]; ring

  -- If c ≠ c₀, then v_p((c - c₀) * t^n) = n
  by_contra hne
  have hsub_ne : c - c₀ ≠ 0 := sub_ne_zero.mpr hne
  have halg_ne := algebraMap_ne_zero' C (c - c₀) hsub_ne
  have hprod_ne : algebraMap ℂ C.FunctionField (c - c₀) * (t ^ n) ≠ 0 := mul_ne_zero halg_ne htn_ne

  have hprod_val : C.valuation p (algebraMap ℂ C.FunctionField (c - c₀) * (t ^ n)) = n := by
    rw [C.toAlgebraicCurve.valuation_mul p _ _ halg_ne htn_ne]
    rw [C.algebraInst.valuation_algebraMap p _ hsub_ne]
    rw [valuation_localParameter_zpow C p n]
    ring

  -- Case analysis on the specs
  rcases hspec with hspec_eq | hspec_gt
  · rcases hspec_c₀' with hspec_c₀_eq | hspec_c₀_gt
    · -- Both equal 0: (c - c₀)*t^n = 0 - 0 = 0
      -- Need to convert hspec_c₀_eq to use t and n
      have hspec_c₀_eq' : f - algebraMap ℂ C.FunctionField c₀ * (t ^ n) = 0 := hspec_c₀_eq
      rw [hspec_eq, hspec_c₀_eq', sub_zero] at hdiff_eq
      exact hprod_ne hdiff_eq
    · -- f - c*t^n = 0, f - c₀*t^n has val > n
      have hspec_c₀_gt' : C.valuation p (f - algebraMap ℂ C.FunctionField c₀ * (t ^ n)) > n :=
        hspec_c₀_gt
      rw [hspec_eq, sub_zero] at hdiff_eq
      have h_eq : algebraMap ℂ C.FunctionField (c - c₀) * (t ^ n) =
          f - algebraMap ℂ C.FunctionField c₀ * (t ^ n) := hdiff_eq
      rw [h_eq] at hprod_val
      linarith
  · rcases hspec_c₀' with hspec_c₀_eq | hspec_c₀_gt
    · -- f - c*t^n has val > n, f - c₀*t^n = 0
      have hspec_c₀_eq' : f - algebraMap ℂ C.FunctionField c₀ * (t ^ n) = 0 := hspec_c₀_eq
      rw [hspec_c₀_eq', zero_sub] at hdiff_eq
      have h_eq : algebraMap ℂ C.FunctionField (c - c₀) * (t ^ n) =
          -(f - algebraMap ℂ C.FunctionField c * (t ^ n)) := hdiff_eq
      have hv_neg : C.valuation p (-(f - algebraMap ℂ C.FunctionField c * (t ^ n))) =
          C.valuation p (f - algebraMap ℂ C.FunctionField c * (t ^ n)) := valuation_neg C p _
      rw [h_eq, hv_neg] at hprod_val
      linarith
    · -- Both have val > n
      have hspec_c₀_gt' : C.valuation p (f - algebraMap ℂ C.FunctionField c₀ * (t ^ n)) > n :=
        hspec_c₀_gt
      -- First, check if f - c*t^n = 0
      by_cases hf_sub_zero : f - algebraMap ℂ C.FunctionField c * (t ^ n) = 0
      · -- If f - c*t^n = 0, then (c - c₀)*t^n = (f - c₀*t^n) - 0 = f - c₀*t^n
        -- But v_p((c - c₀)*t^n) = n and v_p(f - c₀*t^n) > n, contradiction
        rw [hf_sub_zero, sub_zero] at hdiff_eq
        have h_eq : algebraMap ℂ C.FunctionField (c - c₀) * (t ^ n) =
            f - algebraMap ℂ C.FunctionField c₀ * (t ^ n) := hdiff_eq
        rw [h_eq] at hprod_val
        linarith
      · -- f - c*t^n ≠ 0
        -- Now check if f - c₀*t^n = 0
        by_cases hf_sub_c₀_zero : f - algebraMap ℂ C.FunctionField c₀ * (t ^ n) = 0
        · -- If f - c₀*t^n = 0, then (c - c₀)*t^n = 0 - (f - c*t^n) = -(f - c*t^n)
          -- But v_p((c - c₀)*t^n) = n and v_p(f - c*t^n) > n, contradiction
          rw [hf_sub_c₀_zero, zero_sub] at hdiff_eq
          have h_eq : algebraMap ℂ C.FunctionField (c - c₀) * (t ^ n) =
              -(f - algebraMap ℂ C.FunctionField c * (t ^ n)) := hdiff_eq
          have hv_neg : C.valuation p (-(f - algebraMap ℂ C.FunctionField c * (t ^ n))) =
              C.valuation p (f - algebraMap ℂ C.FunctionField c * (t ^ n)) := valuation_neg C p _
          rw [h_eq, hv_neg] at hprod_val
          linarith
        · -- Both f - c*t^n ≠ 0 and f - c₀*t^n ≠ 0
          have hdiff_ne : (f - algebraMap ℂ C.FunctionField c₀ * (t ^ n)) -
              (f - algebraMap ℂ C.FunctionField c * (t ^ n)) ≠ 0 := by
            rw [← hdiff_eq]; exact hprod_ne
          have hdiff_ne' : (f - algebraMap ℂ C.FunctionField c₀ * (t ^ n)) +
              (-(f - algebraMap ℂ C.FunctionField c * (t ^ n))) ≠ 0 := by
            convert hdiff_ne using 1; ring
          have hdiff_val := C.toAlgebraicCurve.valuation_add_min p
            (f - algebraMap ℂ C.FunctionField c₀ * (t ^ n))
            (-(f - algebraMap ℂ C.FunctionField c * (t ^ n)))
            hdiff_ne'
          rw [valuation_neg C p] at hdiff_val
          have hmin_gt : min (C.valuation p (f - algebraMap ℂ C.FunctionField c₀ * (t ^ n)))
              (C.valuation p (f - algebraMap ℂ C.FunctionField c * (t ^ n))) > n :=
            lt_min hspec_c₀_gt' hspec_gt
          have hdiff_eq' : (f - algebraMap ℂ C.FunctionField c₀ * (t ^ n)) +
              (-(f - algebraMap ℂ C.FunctionField c * (t ^ n))) =
              algebraMap ℂ C.FunctionField (c - c₀) * (t ^ n) := by
            simp only [map_sub]; ring
          rw [hdiff_eq'] at hdiff_val
          linarith

/-- When both elements achieve minimum valuation and sum also achieves it,
    the leading coefficients add. -/
theorem leadingCoeff_add_of_eq_val_eq_sum_val (f g : C.FunctionField)
    (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0)
    (hveq : C.valuation p f = C.valuation p g)
    (hvfg_eq : C.valuation p (f + g) = C.valuation p f) :
    leadingCoeff C p (f + g) hfg = leadingCoeff C p f hf + leadingCoeff C p g hg := by
  -- We'll show that c_f + c_g satisfies the spec for leadingCoeff(f+g)
  set n := C.valuation p f with hn_def
  set t := C.localParameter p with ht_def
  set c_f := leadingCoeff C p f hf with hcf_def
  set c_g := leadingCoeff C p g hg with hcg_def
  have htn_ne : t ^ n ≠ 0 := localParameter_zpow_ne_zero C p n

  -- v_p(g) = n
  have hg_val_eq_n : C.valuation p g = n := hveq.symm

  -- Get spec for c_f: works directly since n = v_p(f)
  have hspec_f := Classical.choose_spec (C.leadingCoefficientUniquenessGeneral p
    (C.localParameter p ^ (C.valuation p f)) f (localParameter_zpow_ne_zero C p _) hf
    (valuation_localParameter_zpow C p (C.valuation p f)))

  have hcf_ne := hspec_f.1

  -- For c_g, we need to be more careful about the type
  have hcg_ne := leadingCoeff_ne_zero C p g hg

  -- Key fact: t^{v_p(g)} = t^n since v_p(g) = n
  have htpow_eq : C.localParameter p ^ C.valuation p g = t ^ n := by
    rw [hg_val_eq_n]

  -- Derive the spec for c_g in terms of n
  -- c_g satisfies: g - c_g * t^{v_p(g)} = 0 or v_p(g - c_g * t^{v_p(g)}) > v_p(g)
  -- Since t^{v_p(g)} = t^n, we can rewrite to get the n-version
  have hspec_g_raw := Classical.choose_spec (C.leadingCoefficientUniquenessGeneral p
    (C.localParameter p ^ (C.valuation p g)) g (localParameter_zpow_ne_zero C p _) hg
    (valuation_localParameter_zpow C p (C.valuation p g)))

  -- The spec uses c_g (which equals Classical.choose ...) with t^{v_p(g)}
  -- We need to convert this to use t^n
  have hspec_g' : g - algebraMap ℂ C.FunctionField c_g * (t ^ n) = 0 ∨
      C.valuation p (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) > n := by
    -- Since htpow_eq : t^{v_p(g)} = t^n, we can substitute
    rcases hspec_g_raw.2 with hg_eq_raw | hg_gt_raw
    · left
      -- hg_eq_raw : g - c_g * t^{v_p(g)} = 0 where c_g is Classical.choose ...
      -- Goal: g - c_g * t^n = 0
      -- Since t^{v_p(g)} = t^n, we just need to show the terms match
      simp only [← htpow_eq]
      exact hg_eq_raw
    · right
      simp only [← hg_val_eq_n]
      exact hg_gt_raw

  -- The sum: (f + g) - (c_f + c_g) * t^n = (f - c_f*t^n) + (g - c_g*t^n)
  have hsum_eq : (f + g) - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n) =
      (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
      (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) := by
    simp only [map_add]; ring

  -- Convert hspec_f.2 to use c_f and t^n (which are definitionally equal but may differ in form)
  have hspec_f' : f - algebraMap ℂ C.FunctionField c_f * (t ^ n) = 0 ∨
      C.valuation p (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) > n := hspec_f.2

  -- Show c_f + c_g ≠ 0
  have hcfg_ne : c_f + c_g ≠ 0 := by
    by_contra hcontr
    -- If c_f + c_g = 0, then c_g = -c_f
    have hcg_eq : c_g = -c_f := (neg_eq_of_add_eq_zero_right hcontr).symm
    -- Then (f - c_f*t^n) + (g - c_g*t^n) = (f + g) - 0 = f + g
    have hsum_simp : (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
        (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) = f + g := by
      simp only [hcg_eq, map_neg]
      ring
    -- hsum_simp says the two-term sum equals f + g
    rcases hspec_f' with hf_eq | hf_gt
    · rcases hspec_g' with hg_eq | hg_gt
      · -- Both 0: f = c_f*t^n and g = c_g*t^n
        -- Since c_g = -c_f, g = -c_f * t^n, so f + g = 0
        have hf_val : f = algebraMap ℂ C.FunctionField c_f * (t ^ n) := sub_eq_zero.mp hf_eq
        have hg_val : g = algebraMap ℂ C.FunctionField c_g * (t ^ n) := sub_eq_zero.mp hg_eq
        have : f + g = algebraMap ℂ C.FunctionField c_f * (t ^ n) +
            algebraMap ℂ C.FunctionField c_g * (t ^ n) := by rw [hf_val, hg_val]
        have hfg_zero : f + g = 0 := by
          rw [this, hcg_eq, map_neg]; ring
        exact hfg hfg_zero
      · -- f - c_f*t^n = 0, g - c_g*t^n has val > n
        -- From hsum_simp: 0 + (g - c_g*t^n) = f + g
        have hsum_simp' : g - algebraMap ℂ C.FunctionField c_g * (t ^ n) = f + g := by
          have h := hsum_simp
          rw [hf_eq, zero_add] at h
          exact h
        -- hg_gt : v_p(g - c_g*t^n) > n, but g - c_g*t^n = f + g, so v_p(f+g) > n
        -- But hvfg_eq says v_p(f+g) = n. Contradiction: n > n
        have hv_fg : C.valuation p (f + g) > n := by rw [← hsum_simp']; exact hg_gt
        linarith
    · rcases hspec_g' with hg_eq | hg_gt
      · -- f - c_f*t^n has val > n, g - c_g*t^n = 0
        -- From hsum_simp: (f - c_f*t^n) + 0 = f + g
        have hsum_simp' : f - algebraMap ℂ C.FunctionField c_f * (t ^ n) = f + g := by
          have h := hsum_simp
          rw [hg_eq, add_zero] at h
          exact h
        have hv_fg : C.valuation p (f + g) > n := by rw [← hsum_simp']; exact hf_gt
        linarith
      · -- Both have val > n
        -- Since sum = f + g, v_p(sum) = v_p(f + g) = n
        -- But v_p(sum) ≥ min(v_p(f - c_f*t^n), v_p(g - c_g*t^n)) > n
        -- Need to handle n < 0 case where v_p(0) = 0 could be > n
        by_cases hf_sub_zero : f - algebraMap ℂ C.FunctionField c_f * (t ^ n) = 0
        · -- f = c_f*t^n, so the "sum" is just g - c_g*t^n
          have hsum_simp' : g - algebraMap ℂ C.FunctionField c_g * (t ^ n) = f + g := by
            have h := hsum_simp
            rw [hf_sub_zero, zero_add] at h
            exact h
          have hv_fg : C.valuation p (f + g) > n := by rw [← hsum_simp']; exact hg_gt
          linarith
        · by_cases hg_sub_zero : g - algebraMap ℂ C.FunctionField c_g * (t ^ n) = 0
          · have hsum_simp' : f - algebraMap ℂ C.FunctionField c_f * (t ^ n) = f + g := by
              have h := hsum_simp
              rw [hg_sub_zero, add_zero] at h
              exact h
            have hv_fg : C.valuation p (f + g) > n := by rw [← hsum_simp']; exact hf_gt
            linarith
          · -- Both truly nonzero
            have hsum_ne' : (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
                (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) ≠ 0 := by
              rw [hsum_simp]; exact hfg
            have hsum_val := C.toAlgebraicCurve.valuation_add_min p _ _ hsum_ne'
            have hmin_gt : min (C.valuation p (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)))
                (C.valuation p (g - algebraMap ℂ C.FunctionField c_g * (t ^ n))) > n :=
              lt_min hf_gt hg_gt
            rw [hsum_simp] at hsum_val
            linarith

  -- Now show (f + g) - (c_f + c_g)*t^n = 0 or has val > n
  have hvfg_n : C.valuation p (f + g) = n := hvfg_eq

  have hspec_sum : (f + g) - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n) = 0 ∨
      C.valuation p ((f + g) - algebraMap ℂ C.FunctionField (c_f + c_g) * (t ^ n)) > n := by
    rw [hsum_eq]
    -- Use hspec_f' (which uses c_f and t^n) instead of hspec_f.2 (which uses Classical.choose)
    rcases hspec_f' with hf_eq | hf_gt
    · rcases hspec_g' with hg_eq | hg_gt
      · -- Both 0: f = c_f*t^n and g = c_g*t^n
        left
        have hf_val : f = algebraMap ℂ C.FunctionField c_f * (t ^ n) := sub_eq_zero.mp hf_eq
        have hg_val : g = algebraMap ℂ C.FunctionField c_g * (t ^ n) := sub_eq_zero.mp hg_eq
        rw [hf_val, hg_val]
        ring
      · -- f = c_f*t^n, g - c_g*t^n has val > n
        right
        have hf_val : f = algebraMap ℂ C.FunctionField c_f * (t ^ n) := sub_eq_zero.mp hf_eq
        have h : (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
            (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) =
            g - algebraMap ℂ C.FunctionField c_g * (t ^ n) := by
          rw [hf_eq, zero_add]
        rw [h]
        exact hg_gt
    · rcases hspec_g' with hg_eq | hg_gt
      · -- f - c_f*t^n has val > n, g = c_g*t^n
        right
        have hg_val : g = algebraMap ℂ C.FunctionField c_g * (t ^ n) := sub_eq_zero.mp hg_eq
        have h : (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
            (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) =
            f - algebraMap ℂ C.FunctionField c_f * (t ^ n) := by
          rw [hg_eq, add_zero]
        rw [h]
        exact hf_gt
      · -- Both have val > n
        by_cases hsum_zero : (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) +
            (g - algebraMap ℂ C.FunctionField c_g * (t ^ n)) = 0
        · -- The sum is zero, so f + g - (c_f + c_g) * t^n = 0
          left
          -- The goal (from earlier rw [hsum_eq]) is the sum form = 0
          exact hsum_zero
        · right
          have hsum_val := C.toAlgebraicCurve.valuation_add_min p _ _ hsum_zero
          have hmin_gt : min (C.valuation p (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)))
              (C.valuation p (g - algebraMap ℂ C.FunctionField c_g * (t ^ n))) > n :=
            lt_min hf_gt hg_gt
          linarith

  -- Now apply uniqueness
  -- hspec_sum uses t^n, but leadingCoeff_unique needs t^{v_p(f+g)} = t^n since v_p(f+g) = n
  have hspec_sum' : (f + g) - algebraMap ℂ C.FunctionField (c_f + c_g) *
      (C.localParameter p ^ C.valuation p (f + g)) = 0 ∨
      C.valuation p ((f + g) - algebraMap ℂ C.FunctionField (c_f + c_g) *
      (C.localParameter p ^ C.valuation p (f + g))) > C.valuation p (f + g) := by
    -- Since v_p(f+g) = n (by hvfg_eq), t^{v_p(f+g)} = t^n
    simp only [hvfg_eq]
    exact hspec_sum

  exact (leadingCoeff_unique C p (f + g) hfg (c_f + c_g) hcfg_ne hspec_sum').symm

/-- When only one element achieves minimum valuation, the sum's leading coeff equals that one's. -/
theorem leadingCoeff_add_of_lt_val (f g : C.FunctionField)
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hvlt : C.valuation p f < C.valuation p g)
    (hfg : f + g ≠ 0) :
    leadingCoeff C p (f + g) hfg = leadingCoeff C p f hf := by
  have hvfg_eq : C.valuation p (f + g) = C.valuation p f := by
    rw [valuation_add_eq_min_of_ne C p f g hf hg (ne_of_lt hvlt) hfg]
    exact min_eq_left (le_of_lt hvlt)

  -- We'll show that c_f satisfies the spec for leadingCoeff(f+g)
  set n := C.valuation p f with hn_def
  set t := C.localParameter p with ht_def
  set c_f := leadingCoeff C p f hf with hcf_def
  have htn_ne : t ^ n ≠ 0 := localParameter_zpow_ne_zero C p n
  have hcf_ne := leadingCoeff_ne_zero C p f hf

  -- Get spec for c_f: since c_f = Classical.choose ... and n = v_p(f), the spec is direct
  have hspec_f_raw := Classical.choose_spec (C.leadingCoefficientUniquenessGeneral p
    (C.localParameter p ^ (C.valuation p f)) f (localParameter_zpow_ne_zero C p _) hf
    (valuation_localParameter_zpow C p (C.valuation p f)))

  -- Convert to use c_f and t^n (they match definitionally since n = v_p(f))
  have hspec_f : f - algebraMap ℂ C.FunctionField c_f * (t ^ n) = 0 ∨
      C.valuation p (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) > n :=
    hspec_f_raw.2

  -- The key: (f + g) - c_f * t^n = (f - c_f * t^n) + g
  have hsum_eq : (f + g) - algebraMap ℂ C.FunctionField c_f * (t ^ n) =
      (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) + g := by ring

  -- g has valuation > n
  have hvg_gt_n : C.valuation p g > n := hvlt

  -- Show c_f satisfies the spec for f + g
  have hspec_sum : (f + g) - algebraMap ℂ C.FunctionField c_f * (t ^ n) = 0 ∨
      C.valuation p ((f + g) - algebraMap ℂ C.FunctionField c_f * (t ^ n)) > n := by
    rw [hsum_eq]
    rcases hspec_f with hf_eq | hf_gt
    · -- f - c_f * t^n = 0, so sum = 0 + g = g
      rw [hf_eq, zero_add]
      right
      exact hvg_gt_n
    · -- v_p(f - c_f * t^n) > n
      by_cases hsum_zero : (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) + g = 0
      · -- If (f - c_f*t^n) + g = 0, then the sum is 0 (LEFT branch)
        left
        exact hsum_zero
      · -- Sum ≠ 0, so we can use ultrametric inequality (RIGHT branch)
        right
        have hsum_val := C.toAlgebraicCurve.valuation_add_min p _ g hsum_zero
        have hmin_gt : min (C.valuation p (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)))
            (C.valuation p g) > n := lt_min hf_gt hvg_gt_n
        linarith

  -- Convert to use v_p(f + g) instead of n
  have hspec_sum' : (f + g) - algebraMap ℂ C.FunctionField c_f *
      (C.localParameter p ^ C.valuation p (f + g)) = 0 ∨
      C.valuation p ((f + g) - algebraMap ℂ C.FunctionField c_f *
      (C.localParameter p ^ C.valuation p (f + g))) > C.valuation p (f + g) := by
    simp only [hvfg_eq]
    exact hspec_sum

  exact (leadingCoeff_unique C p (f + g) hfg c_f hcf_ne hspec_sum').symm

/-- Scalar multiplication scales the leading coefficient. -/
theorem leadingCoeff_smul (r : ℂ) (f : C.FunctionField)
    (hr : r ≠ 0) (hf : f ≠ 0)
    (hrf_ne : algebraMap ℂ C.FunctionField r * f ≠ 0) :
    leadingCoeff C p (algebraMap ℂ C.FunctionField r * f) hrf_ne =
    r * leadingCoeff C p f hf := by
  have hv_rf : C.valuation p (algebraMap ℂ C.FunctionField r * f) = C.valuation p f :=
    valuation_smul C p r f hr

  -- We'll show r * c_f satisfies the spec for leadingCoeff(r * f)
  set n := C.valuation p f with hn_def
  set t := C.localParameter p with ht_def
  set c_f := leadingCoeff C p f hf with hcf_def
  have htn_ne : t ^ n ≠ 0 := localParameter_zpow_ne_zero C p n
  have hcf_ne := leadingCoeff_ne_zero C p f hf
  have hr_alg_ne := algebraMap_ne_zero' C r hr
  have hrcf_ne : r * c_f ≠ 0 := mul_ne_zero hr hcf_ne

  -- Get spec for c_f
  have hspec_f := Classical.choose_spec (C.leadingCoefficientUniquenessGeneral p
    (C.localParameter p ^ n) f (localParameter_zpow_ne_zero C p _) hf
    (valuation_localParameter_zpow C p n))

  -- The spec: f - c_f * t^n = 0 or v_p(f - c_f * t^n) > n
  have hspec_f' : f - algebraMap ℂ C.FunctionField c_f * (t ^ n) = 0 ∨
      C.valuation p (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) > n :=
    hspec_f.2

  -- Now show (r * f) - (r * c_f) * t^{v_p(r*f)} satisfies the spec
  -- Since v_p(r * f) = v_p(f) = n, we have t^{v_p(r*f)} = t^n
  have hspec_rf : (algebraMap ℂ C.FunctionField r * f) -
      algebraMap ℂ C.FunctionField (r * c_f) * (t ^ n) = 0 ∨
      C.valuation p ((algebraMap ℂ C.FunctionField r * f) -
      algebraMap ℂ C.FunctionField (r * c_f) * (t ^ n)) > n := by
    -- (r * f) - (r * c_f) * t^n = r * (f - c_f * t^n)
    have hfactor : (algebraMap ℂ C.FunctionField r * f) -
        algebraMap ℂ C.FunctionField (r * c_f) * (t ^ n) =
        algebraMap ℂ C.FunctionField r * (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) := by
      simp only [map_mul]; ring
    rcases hspec_f' with hf_eq | hf_gt
    · left
      rw [hfactor, hf_eq, mul_zero]
    · -- v_p(f - c_f * t^n) > n
      -- Need to handle case where f - c_f * t^n = 0 (possible when n < 0)
      by_cases h_diff_zero : f - algebraMap ℂ C.FunctionField c_f * (t ^ n) = 0
      · left
        rw [hfactor, h_diff_zero, mul_zero]
      · right
        rw [hfactor]
        have h_prod_ne : algebraMap ℂ C.FunctionField r *
            (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) ≠ 0 :=
          mul_ne_zero hr_alg_ne h_diff_zero
        rw [C.toAlgebraicCurve.valuation_mul p _ _ hr_alg_ne h_diff_zero]
        rw [C.algebraInst.valuation_algebraMap p r hr]
        omega

  -- Convert to the form needed by leadingCoeff_unique
  have hspec_rf' : (algebraMap ℂ C.FunctionField r * f) -
      algebraMap ℂ C.FunctionField (r * c_f) *
      (C.localParameter p ^ C.valuation p (algebraMap ℂ C.FunctionField r * f)) = 0 ∨
      C.valuation p ((algebraMap ℂ C.FunctionField r * f) -
      algebraMap ℂ C.FunctionField (r * c_f) *
      (C.localParameter p ^ C.valuation p (algebraMap ℂ C.FunctionField r * f))) >
      C.valuation p (algebraMap ℂ C.FunctionField r * f) := by
    simp only [hv_rf]
    exact hspec_rf

  exact (leadingCoeff_unique C p (algebraMap ℂ C.FunctionField r * f) hrf_ne
    (r * c_f) hrcf_ne hspec_rf').symm

/-- Negation changes the sign of the leading coefficient. -/
theorem leadingCoeff_neg (f : C.FunctionField) (hf : f ≠ 0)
    (hnegf_ne : -f ≠ 0 := neg_ne_zero.mpr hf) :
    leadingCoeff C p (-f) hnegf_ne = -leadingCoeff C p f hf := by
  -- -f = (-1) * f
  have hneg_eq : -f = algebraMap ℂ C.FunctionField (-1) * f := by
    simp only [map_neg, map_one, neg_mul, one_mul]
  have h_neg1_ne : (-1 : ℂ) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have h_neg1f_ne : algebraMap ℂ C.FunctionField (-1) * f ≠ 0 := by
    simp only [map_neg, map_one, neg_mul, one_mul]
    exact neg_ne_zero.mpr hf
  -- v_p(f) < 0 when leadingCoeff is meaningful
  -- We need to handle this carefully - use that v_p(-f) = v_p(f)
  have hv_neg : C.valuation p (-f) = C.valuation p f := valuation_neg C p f
  -- Use leadingCoeff_smul with r = -1
  have hsmul := leadingCoeff_smul C p (-1) f h_neg1_ne hf
  -- But leadingCoeff_smul requires v_p(f) < 0, which we don't have as hypothesis
  -- Instead, directly prove using uniqueness
  set n := C.valuation p f with hn_def
  set t := C.localParameter p with ht_def
  set c_f := leadingCoeff C p f hf with hcf_def
  have hcf_ne := leadingCoeff_ne_zero C p f hf
  have hneg_cf_ne : -c_f ≠ 0 := neg_ne_zero.mpr hcf_ne

  -- Get spec for c_f: f - c_f * t^n = 0 or v_p(f - c_f * t^n) > n
  have hspec_f := Classical.choose_spec (C.leadingCoefficientUniquenessGeneral p
    (C.localParameter p ^ n) f (localParameter_zpow_ne_zero C p _) hf
    (valuation_localParameter_zpow C p n))

  have hspec_f' : f - algebraMap ℂ C.FunctionField c_f * (t ^ n) = 0 ∨
      C.valuation p (f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) > n :=
    hspec_f.2

  -- Show -f has spec with -c_f
  -- -f - (-c_f) * t^n = -f + c_f * t^n = -(f - c_f * t^n)
  have hspec_neg : (-f) - algebraMap ℂ C.FunctionField (-c_f) * (t ^ n) = 0 ∨
      C.valuation p ((-f) - algebraMap ℂ C.FunctionField (-c_f) * (t ^ n)) > n := by
    have hfactor : (-f) - algebraMap ℂ C.FunctionField (-c_f) * (t ^ n) =
        -(f - algebraMap ℂ C.FunctionField c_f * (t ^ n)) := by
      simp only [map_neg]; ring
    rcases hspec_f' with hf_eq | hf_gt
    · left; rw [hfactor, hf_eq, neg_zero]
    · by_cases h_diff_zero : f - algebraMap ℂ C.FunctionField c_f * (t ^ n) = 0
      · left; rw [hfactor, h_diff_zero, neg_zero]
      · right
        rw [hfactor, valuation_neg C p]
        exact hf_gt

  -- Convert to the form needed by leadingCoeff_unique
  have hspec_neg' : (-f) - algebraMap ℂ C.FunctionField (-c_f) *
      (C.localParameter p ^ C.valuation p (-f)) = 0 ∨
      C.valuation p ((-f) - algebraMap ℂ C.FunctionField (-c_f) *
      (C.localParameter p ^ C.valuation p (-f))) > C.valuation p (-f) := by
    simp only [hv_neg]
    exact hspec_neg

  exact (leadingCoeff_unique C p (-f) hnegf_ne (-c_f) hneg_cf_ne hspec_neg').symm

/-- Leading coefficient is determined by the value, not the proof of non-zeroness -/
theorem leadingCoeff_eq_of_val_eq (f g : C.FunctionField) (hf : f ≠ 0) (hg : g ≠ 0)
    (heq : f = g) :
    leadingCoeff C p f hf = leadingCoeff C p g hg := by
  subst heq
  rfl

/-- The evaluation map for L(D) at a point p.

    For f ∈ L(D):
    - If v_p(f) = -D(p) (exact minimum), eval returns the leading coefficient
    - If v_p(f) > -D(p), eval returns 0 (f is in L(D-p))

    The kernel of eval is exactly L(D-p). -/
noncomputable def evalMap (p : C.toAlgebraicCurve.Point) (f : Cohomology.RiemannRochSubmodule C D) : ℂ :=
  if hf : f.val = 0 then 0
  else if _h : C.valuation p f.val = -D.coeff p then
    leadingCoeff C p f.val hf
  else 0

/-!
## Properties of the Evaluation Map
-/

/-- The evaluation map is linear (as a map from L(D) to ℂ) -/
theorem evalMap_linear (p : C.toAlgebraicCurve.Point) :
    ∀ (f g : Cohomology.RiemannRochSubmodule C D) (c : ℂ),
    evalMap C D p (f + g) = evalMap C D p f + evalMap C D p g ∧
    evalMap C D p (c • f) = c * evalMap C D p f := by
  intro f g c
  constructor
  · -- Additivity (requires case analysis on whether f + g achieves the minimum valuation)
    unfold evalMap
    -- This is technically complex - the DVR structure ensures the leading coefficients add
    -- when both f and g achieve the minimum, but we need to handle all cases
    sorry
  · -- Scalar multiplication
    unfold evalMap
    sorry

/-- The kernel of evalMap is L(D-p) -/
theorem evalMap_ker_eq_Dp (p : C.toAlgebraicCurve.Point) : ∀ (f : Cohomology.RiemannRochSubmodule C D),
    evalMap C D p f = 0 ↔ f.val ∈ Cohomology.RiemannRochSubmodule C (D - Core.Divisor.point p) := by
  intro f
  constructor
  · intro heval
    -- If eval(f) = 0, then either f = 0 or v_p(f) > -D(p)
    -- In either case, f ∈ L(D-p)
    unfold evalMap at heval
    by_cases hf : f.val = 0
    · -- f = 0 ∈ L(D-p)
      simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                 Cohomology.RiemannRochSpace, hf]
      left; rfl
    · -- f ≠ 0
      rw [dif_neg hf] at heval
      by_cases hv : C.valuation p f.val = -D.coeff p
      · -- f ≠ 0 and v_p(f) = -D(p), but then leadingCoeff = 0, contradiction
        rw [dif_pos hv] at heval
        exfalso
        have hlc_ne := leadingCoeff_ne_zero C p f.val hf
        exact hlc_ne heval
      · -- f ≠ 0 and v_p(f) ≠ -D(p), so v_p(f) > -D(p) (since f ∈ L(D))
        -- Therefore f ∈ L(D-p)
        simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                   Cohomology.RiemannRochSpace]
        have hf_in := f.property
        simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                   Cohomology.RiemannRochSpace] at hf_in
        rcases hf_in with h_eq | hf_val
        · exact absurd h_eq hf
        · right
          intro q
          simp only [Core.Divisor.sub_coeff, Core.Divisor.point]
          by_cases hqp : q = p
          · simp only [hqp, ite_true]
            have := hf_val p
            -- v_p(f) + D(p) ≥ 0 and v_p(f) ≠ -D(p), so v_p(f) > -D(p)
            -- Therefore v_p(f) ≥ -D(p) + 1
            omega
          · simp only [if_neg hqp, sub_zero]
            exact hf_val q
  · intro hf_in_Dp
    -- If f ∈ L(D-p), then v_p(f) ≥ -D(p)+1, so eval(f) = 0
    unfold evalMap
    by_cases hf : f.val = 0
    · rw [dif_pos hf]
    · rw [dif_neg hf]
      by_cases hv : C.valuation p f.val = -D.coeff p
      · -- hv : v_p(f) = -D(p), but f ∈ L(D-p) means v_p(f) ≥ -D(p) + 1, contradiction
        exfalso
        simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                   Cohomology.RiemannRochSpace] at hf_in_Dp
        rcases hf_in_Dp with h_eq | hf_val
        · exact hf h_eq
        · have hvp := hf_val p
          simp only [Core.Divisor.sub_coeff, Core.Divisor.point, ite_true] at hvp
          omega
      · rw [dif_neg hv]

/-- Elements of L(E) have valuation at least -E.coeff at each point -/
theorem RiemannRochSubmodule_valuation_bound (E : Core.Divisor C.toAlgebraicCurve)
    (q : C.toAlgebraicCurve.Point) (f : Cohomology.RiemannRochSubmodule C E)
    (hf : f.val ≠ 0) :
    C.valuation q f.val ≥ -E.coeff q := by
  have hmem := f.property
  simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
             Cohomology.RiemannRochSpace] at hmem
  rcases hmem with h_eq | hf_val
  · exact absurd h_eq hf
  · linarith [hf_val q]

/-!
## The Connecting Homomorphism

The connecting homomorphism δ: ℂ → L(K-D+p)* is defined via the residue pairing.
For c ∈ ℂ, δ(c) is a linear functional on L(K-D+p) defined by:

  δ(c)(g) = c · res_p(t_p^{-D(p)} · g · ω₀)

where t_p is the local parameter and ω₀ is a 1-form with div(ω₀) = K.

This is well-defined because:
1. t_p^{-D(p)} · g · ω₀ has a specific pole order at p
2. The residue (coefficient of z^{-1}dz) is well-defined
-/

/-- Helper to extract y.val = -x.val from (x + y).val = 0 -/
private lemma neg_of_add_eq_zero {V : Type*} [AddCommGroup V]
    (x y : V) (h : x + y = 0) : y = -x := by
  have h1 : x = -y := add_eq_zero_iff_eq_neg.mp h
  rw [h1, neg_neg]

/-- The connecting homomorphism δ: ℂ → L(K-D+p)*.

    This maps c ∈ ℂ to a linear functional on L(K-D+p).
    The definition uses the residue pairing with a "test function". -/
noncomputable def connectingHom (c : ℂ) : (Cohomology.RiemannRochSubmodule C (K.K - D + Core.Divisor.point p)) →ₗ[ℂ] ℂ where
  toFun := fun g =>
    -- δ(c)(g) = c · (residue coefficient of t_p^{-D(p)} · g at p, adjusted for the canonical divisor)
    -- The residue coefficient is related to the leading coefficient
    c * (if hg : g.val = 0 then 0
         else if C.valuation p g.val = -(K.K - D + Core.Divisor.point p).coeff p
         then leadingCoeff C p g.val hg
         else 0)
  map_add' := by
    intro x y
    -- Let M be the minimum valuation = -(K - D + point(p)).coeff p
    set M := -(K.K - D + Core.Divisor.point p).coeff p with hM_def
    -- Case analysis on whether x, y, and x+y are zero and achieve minimum
    by_cases hx : x.val = 0
    · simp only [hx, ↓reduceDIte, mul_zero, zero_add]
      have hxy : (x + y).val = y.val := by simp [hx]
      by_cases hy : y.val = 0
      · simp [hy, hxy]
      · simp only [hxy, hy, ↓reduceDIte]
    · by_cases hy : y.val = 0
      · simp only [hy, ↓reduceDIte, mul_zero, add_zero]
        have hxy : (x + y).val = x.val := by simp [hy]
        simp only [hxy, hx, ↓reduceDIte]
      · -- Both x and y nonzero
        by_cases hxy_zero : (x + y).val = 0
        · -- x + y = 0 means y = -x
          -- Get y.val = -x.val
          have hsum_eq_zero : x.val + y.val = 0 := hxy_zero
          have hyx : y.val = -x.val := neg_of_add_eq_zero x.val y.val hsum_eq_zero
          by_cases hvx : C.valuation p x.val = M
          · have hvy : C.valuation p y.val = M := by rw [hyx, valuation_neg C p]; exact hvx
            -- c * lc(x) + c * lc(y) = 0 where y = -x
            have hy' : -x.val ≠ 0 := neg_ne_zero.mpr hx
            have hlc_neg := leadingCoeff_neg C p x.val hx
            have hlc_y_eq : leadingCoeff C p y.val hy = leadingCoeff C p (-x.val) hy' := by
              -- y.val = -x.val by hyx, so the leading coefficients are equal
              -- (since leadingCoeff only depends on the value, not the proof term)
              have : y.val = -x.val := hyx
              simp only [this]
            -- Compute the LHS and RHS separately
            have lhs : c * (if hg : (x + y).val = 0 then 0
                else if C.valuation p (x + y).val = M then leadingCoeff C p (x + y).val hg else 0) = 0 := by
              simp only [hxy_zero, dite_true, mul_zero]
            have rhs_x : (if hg : x.val = 0 then 0
                else if C.valuation p x.val = M then leadingCoeff C p x.val hg else 0) =
                leadingCoeff C p x.val hx := by
              simp only [hx, dite_false, hvx, ite_true]
            have rhs_y : (if hg : y.val = 0 then 0
                else if C.valuation p y.val = M then leadingCoeff C p y.val hg else 0) =
                leadingCoeff C p y.val hy := by
              simp only [hy, dite_false, hvy, ite_true]
            rw [lhs, rhs_x, rhs_y, hlc_y_eq, hlc_neg]; ring
          · have hvy : C.valuation p y.val ≠ M := by rw [hyx, valuation_neg C p]; exact hvx
            have lhs : c * (if hg : (x + y).val = 0 then 0
                else if C.valuation p (x + y).val = M then leadingCoeff C p (x + y).val hg else 0) = 0 := by
              simp only [hxy_zero, dite_true, mul_zero]
            have rhs_x : (if hg : x.val = 0 then 0
                else if C.valuation p x.val = M then leadingCoeff C p x.val hg else 0) = 0 := by
              simp only [hx, dite_false, hvx, ite_false]
            have rhs_y : (if hg : y.val = 0 then 0
                else if C.valuation p y.val = M then leadingCoeff C p y.val hg else 0) = 0 := by
              simp only [hy, dite_false, hvy, ite_false]
            rw [lhs, rhs_x, rhs_y]; ring
        · -- x + y ≠ 0
          simp only [hxy_zero, ↓reduceDIte, hx, hy]
          by_cases hvx : C.valuation p x.val = M
          · by_cases hvy : C.valuation p y.val = M
            · -- Both achieve minimum
              by_cases hvxy : C.valuation p (x + y).val = M
              · -- Sum also achieves minimum: use leadingCoeff_add
                simp only [hvx, hvy, hvxy, ite_true]
                have hxy_val : (x + y).val = x.val + y.val := rfl
                have hvfg_eq : C.valuation p (x.val + y.val) = C.valuation p x.val := by
                  rw [← hxy_val, hvxy, hvx]
                have h_add := leadingCoeff_add_of_eq_val_eq_sum_val C p x.val y.val hx hy hxy_zero
                  (by rw [hvx, hvy])
                  hvfg_eq
                -- Need to relate the leadingCoeff with the goal's proof terms
                have hlc_sum : leadingCoeff C p (x + y).val hxy_zero =
                    leadingCoeff C p (x.val + y.val) hxy_zero := rfl
                rw [hlc_sum, h_add]; ring
              · -- Sum has higher valuation: use leadingCoeff_add_cancel
                simp only [hvx, hvy, hvxy, mul_zero, ite_true, ite_false]
                have hxy_val : (x + y).val = x.val + y.val := rfl
                have hvsum_gt : C.valuation p (x.val + y.val) > M := by
                  have hle := C.toAlgebraicCurve.valuation_add_min p x.val y.val hxy_zero
                  have hmin_M : min (C.valuation p x.val) (C.valuation p y.val) = M := by
                    rw [hvx, hvy, min_self]
                  cases lt_or_eq_of_le hle with
                  | inl hlt => rw [hmin_M] at hlt; exact hlt
                  | inr heq =>
                    rw [hmin_M] at heq
                    rw [← hxy_val] at heq
                    exfalso; exact hvxy heq.symm
                have h_cancel := leadingCoeff_add_cancel C p x.val y.val hx hy
                  (by rw [hvx, hvy])
                  (Or.inr (by rw [hvx]; exact hvsum_gt))
                -- h_cancel: leadingCoeff ... + leadingCoeff ... = 0
                -- Goal: 0 = c * lc_x + c * lc_y = c * (lc_x + lc_y) = c * 0 = 0
                rw [← mul_add, h_cancel, mul_zero]
            · -- x achieves, y doesn't
              simp only [hvx, hvy, mul_zero, add_zero, ite_true, ite_false]
              have hxy_val : (x + y).val = x.val + y.val := rfl
              have hvy_gt : C.valuation p y.val > M := by
                have hle := RiemannRochSubmodule_valuation_bound C (K.K - D + Core.Divisor.point p) p y hy
                have hM_eq : M = -(K.K - D + Core.Divisor.point p).coeff p := rfl
                rw [hM_eq]
                cases lt_or_eq_of_le hle with
                | inl hlt => exact hlt
                | inr heq => exact absurd heq.symm hvy
              have hvxy : C.valuation p (x + y).val = M := by
                rw [hxy_val]
                have hne : C.valuation p x.val ≠ C.valuation p y.val := by
                  rw [hvx]; exact ne_of_lt hvy_gt
                rw [valuation_add_eq_min_of_ne C p x.val y.val hx hy hne hxy_zero]
                rw [hvx]; exact min_eq_left (le_of_lt hvy_gt)
              simp only [hvxy, ite_true]
              have h_lt := leadingCoeff_add_of_lt_val C p x.val y.val hx hy
                (by rw [hvx]; exact hvy_gt)
                hxy_zero
              have hlc_sum : leadingCoeff C p (x + y).val hxy_zero =
                  leadingCoeff C p (x.val + y.val) hxy_zero := rfl
              rw [hlc_sum, h_lt]
          · by_cases hvy : C.valuation p y.val = M
            · -- y achieves, x doesn't
              simp only [hvx, hvy, mul_zero, zero_add, ite_true, ite_false]
              have hxy_val : (x + y).val = x.val + y.val := rfl
              have hvx_gt : C.valuation p x.val > M := by
                have hle := RiemannRochSubmodule_valuation_bound C (K.K - D + Core.Divisor.point p) p x hx
                have hM_eq : M = -(K.K - D + Core.Divisor.point p).coeff p := rfl
                rw [hM_eq]
                cases lt_or_eq_of_le hle with
                | inl hlt => exact hlt
                | inr heq => exact absurd heq.symm hvx
              have hvxy : C.valuation p (x + y).val = M := by
                rw [hxy_val]
                have hne : C.valuation p x.val ≠ C.valuation p y.val := by
                  rw [hvy]; exact ne_of_gt hvx_gt
                rw [valuation_add_eq_min_of_ne C p x.val y.val hx hy hne hxy_zero]
                rw [hvy]; exact min_eq_right (le_of_lt hvx_gt)
              simp only [hvxy, ite_true]
              have hyx_zero : y.val + x.val ≠ 0 := by rw [add_comm]; exact hxy_zero
              have h_lt := leadingCoeff_add_of_lt_val C p y.val x.val hy hx
                (by rw [hvy]; exact hvx_gt)
                hyx_zero
              -- Goal: c * leadingCoeff C p (x + y).val _ = c * leadingCoeff C p y.val _
              -- We have: (x + y).val = x.val + y.val = y.val + x.val
              -- And: leadingCoeff C p (y.val + x.val) _ = leadingCoeff C p y.val _
              -- The leading coefficient only depends on the value, not the proof
              have hxy_eq_yx : (x + y).val = y.val + x.val := add_comm x.val y.val
              -- Use leadingCoeff_eq_of_val_eq to transfer between proof terms
              have hlc1 : leadingCoeff C p (x + y).val hxy_zero =
                  leadingCoeff C p (y.val + x.val) hyx_zero := by
                apply leadingCoeff_eq_of_val_eq
                exact hxy_eq_yx
              rw [hlc1, h_lt]
            · -- Neither achieves minimum
              simp only [hvx, hvy, mul_zero, add_zero, ite_false]
              have hvx_gt : C.valuation p x.val > M := by
                have hle := RiemannRochSubmodule_valuation_bound C (K.K - D + Core.Divisor.point p) p x hx
                have hM_eq : M = -(K.K - D + Core.Divisor.point p).coeff p := rfl
                rw [hM_eq]
                cases lt_or_eq_of_le hle with
                | inl hlt => exact hlt
                | inr heq => exact absurd heq.symm hvx
              have hvy_gt : C.valuation p y.val > M := by
                have hle := RiemannRochSubmodule_valuation_bound C (K.K - D + Core.Divisor.point p) p y hy
                have hM_eq : M = -(K.K - D + Core.Divisor.point p).coeff p := rfl
                rw [hM_eq]
                cases lt_or_eq_of_le hle with
                | inl hlt => exact hlt
                | inr heq => exact absurd heq.symm hvy
              have hvxy : C.valuation p (x + y).val ≠ M := by
                intro heq
                have hxy_val : (x + y).val = x.val + y.val := rfl
                rw [hxy_val] at heq
                have hmin := C.toAlgebraicCurve.valuation_add_min p x.val y.val hxy_zero
                have hmin_gt : min (C.valuation p x.val) (C.valuation p y.val) > M :=
                  lt_min hvx_gt hvy_gt
                linarith
              simp only [hvxy, mul_zero, ite_false]
  map_smul' := by
    intro r x
    simp only [RingHom.id_apply]
    set M := -(K.K - D + Core.Divisor.point p).coeff p with hM_def
    by_cases hx : x.val = 0
    · simp only [hx, ↓reduceDIte, mul_zero, smul_eq_mul]
      have hrx : (r • x).val = 0 := by simp [hx]
      simp only [hrx, ↓reduceDIte, mul_zero]
    · have hrx_eq : (r • x).val = algebraMap ℂ C.FunctionField r * x.val := by
        simp only [Submodule.coe_smul, Algebra.smul_def]
      by_cases hr : r = 0
      · subst hr
        simp only [zero_smul, Submodule.coe_zero, dite_true, mul_zero]
      · have hrx_ne : (r • x).val ≠ 0 := by
          rw [hrx_eq]; exact mul_ne_zero (algebraMap_ne_zero' C r hr) hx
        have hrx_ne' : algebraMap ℂ C.FunctionField r * x.val ≠ 0 :=
          mul_ne_zero (algebraMap_ne_zero' C r hr) hx
        simp only [hx, hrx_ne, smul_eq_mul, ↓reduceDIte]
        by_cases hvx : C.valuation p x.val = M
        · have hvrx : C.valuation p (r • x).val = M := by
            rw [hrx_eq, valuation_smul C p r x.val hr, hvx]
          simp only [hvx, hvrx, ite_true]
          -- Goal: c * leadingCoeff C p (r • x).val _ = r * (c * leadingCoeff C p x.val _)
          have h_smul := leadingCoeff_smul C p r x.val hr hx hrx_ne'
          have hlc_eq : leadingCoeff C p (r • x).val hrx_ne =
              leadingCoeff C p (algebraMap ℂ C.FunctionField r * x.val) hrx_ne' := by
            apply leadingCoeff_eq_of_val_eq
            exact hrx_eq
          rw [hlc_eq, h_smul]; ring
        · have hvrx : C.valuation p (r • x).val ≠ M := by
            rw [hrx_eq, valuation_smul C p r x.val hr]; exact hvx
          simp only [hvx, hvrx, mul_zero, ite_false]

end RiemannSurfaces.Algebraic.PointExactInfra

/-!
## ⚠️ DEPRECATED CODE BELOW ⚠️

The code below uses case analysis (ruling out (0,0) and (1,1)) which depends on
ResidueTheory functions. This approach is **NOT** needed for Riemann-Roch.
The correct proof uses abstract LES exactness directly.

The code below is commented out via `#exit` but preserved for historical reference.
-/

#exit

/-!
## Exactness at ℂ (DEPRECATED)

The key exactness condition is: ker(δ) = im(eval).

- If a = 1 (eval surjective): im(eval) = ℂ, so ker(δ) = ℂ, meaning δ = 0
- If a = 0 (eval = 0): im(eval) = 0, so ker(δ) = 0, meaning δ is injective
-/

/-- When eval is surjective (a = 1), the connecting homomorphism is zero -/
theorem delta_zero_when_eval_surjective
    (heval_surj : ∀ c : ℂ, ∃ f : Cohomology.RiemannRochSubmodule C D, evalMap C D p f = c) :
    ∀ c : ℂ, ∀ g : Cohomology.RiemannRochSubmodule C (K.K - D + Core.Divisor.point p),
      connectingHom C K D p c g = 0 := by
  -- Key insight: δ = 0 iff b = 0 (no g achieves minimum valuation)
  -- We show: if a = 1 and b = 1, contradiction via residue theorem
  -- Therefore if a = 1, then b = 0, hence δ = 0

  intro c g

  -- Unfold connectingHom definition
  show c * (if hg : g.val = 0 then 0
    else if C.valuation p g.val = -(K.K - D + Core.Divisor.point p).coeff p
    then leadingCoeff C p g.val hg else 0) = 0

  -- If g.val = 0, trivially 0
  by_cases hg : g.val = 0
  · simp only [hg, dite_true, mul_zero]

  simp only [hg, dite_false]

  -- Check if g achieves minimum valuation
  set M := -(K.K - D + Core.Divisor.point p).coeff p with hM_def
  by_cases hvg : C.valuation p g.val = M
  · -- g achieves minimum: show this leads to contradiction via (1,1) impossibility
    exfalso

    -- From heval_surj, there exists f₀ with evalMap(f₀) = 1 ≠ 0
    obtain ⟨f₀, hf₀_eval⟩ := heval_surj 1

    -- evalMap(f₀) = 1 means f₀.val ≠ 0 and v_p(f₀) = -D(p) and leadingCoeff(f₀) = 1
    simp only [evalMap] at hf₀_eval
    have hf₀_ne : f₀.val ≠ 0 := by
      by_contra h
      simp only [h, dite_true] at hf₀_eval
      exact one_ne_zero hf₀_eval.symm
    simp only [hf₀_ne, dite_false] at hf₀_eval
    have hf₀_val : C.valuation p f₀.val = -D.coeff p := by
      by_contra h
      simp only [h, dite_false] at hf₀_eval
      exact one_ne_zero hf₀_eval.symm
    simp only [hf₀_val, dite_true] at hf₀_eval

    -- Construct the quotient witnesses for ResidueTheory
    -- f₀ is in the D quotient: v_p(f₀) = -D(p)
    have hf_quotient : RiemannSurfaces.Algebraic.inQuotient C f₀.val D p := by
      refine ⟨hf₀_ne, ?_, hf₀_val⟩
      -- f₀.val ∈ L(D) since f₀ ∈ RiemannRochSubmodule C D
      have hmem := f₀.property
      simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                 Cohomology.RiemannRochSpace] at hmem
      exact Or.inr (Or.resolve_left hmem hf₀_ne)

    -- g is in the K-D+p quotient: v_p(g) = M = -(K-D+p)(p)
    have hg_quotient : RiemannSurfaces.Algebraic.inQuotient C g.val (K.K - D + Core.Divisor.point p) p := by
      refine ⟨hg, ?_, hvg⟩
      have hmem := g.property
      simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                 Cohomology.RiemannRochSpace] at hmem
      exact Or.inr (Or.resolve_left hmem hg)

    -- Apply not_both_quotients_nontrivial_aux
    exact RiemannSurfaces.Algebraic.not_both_quotients_nontrivial_aux C rfl ⟨f₀.val, hf_quotient⟩ ⟨g.val, hg_quotient⟩

  · -- g doesn't achieve minimum: connectingHom returns 0
    rw [if_neg hvg, mul_zero]

/-- When eval is zero (a = 0), the connecting homomorphism is injective -/
theorem delta_injective_when_eval_zero
    (heval_zero : ∀ f : Cohomology.RiemannRochSubmodule C D, evalMap C D p f = 0) :
    ∀ c₁ c₂ : ℂ, (∀ g : Cohomology.RiemannRochSubmodule C (K.K - D + Core.Divisor.point p),
      connectingHom C K D p c₁ g = connectingHom C K D p c₂ g) → c₁ = c₂ := by
  -- Key insight: if a = 0 and b = 0, we get a contradiction via not_both_quotients_trivial_aux
  -- So if a = 0, then b = 1, meaning some g achieves minimum
  -- With such g, δ(c₁)(g) = δ(c₂)(g) implies c₁ * lc(g) = c₂ * lc(g)
  -- Since lc(g) ≠ 0, we get c₁ = c₂

  intro c₁ c₂ hδ_eq

  -- Proof by contradiction: suppose c₁ ≠ c₂
  by_contra hc_ne

  -- From heval_zero, a = 0 (no f achieves minimum valuation)
  -- We show b = 1 by contradiction with (0,0) impossibility

  -- Translate heval_zero to quotientTrivial in ResidueTheory
  have ha_trivial : RiemannSurfaces.Algebraic.quotientTrivial C D p := by
    intro f hf_in
    -- evalMap(f) = 0 for all f, so either f = 0 or v_p(f) ≠ -D(p)
    by_cases hf : f = 0
    · right; exact hf
    · left
      -- f ≠ 0, so evalMap = (if v_p = -D(p) then lc else 0) = 0
      -- Need to show v_p(f) ≠ -D(p)
      by_contra hv
      -- f ∈ L(D) with v_p(f) = -D(p) and f ≠ 0 means leadingCoeff(f) ≠ 0
      -- Build f as an element of RiemannRochSubmodule
      have hf_mem : f ∈ Cohomology.RiemannRochSubmodule C D := by
        simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                   Cohomology.RiemannRochSpace]
        rcases hf_in with rfl | hf_val_all
        · exact absurd rfl hf
        · right; exact hf_val_all
      let f' : Cohomology.RiemannRochSubmodule C D := ⟨f, hf_mem⟩
      have heval := heval_zero f'
      simp only [evalMap] at heval
      -- f'.val = f, and hf : f ≠ 0, hv : v_p(f) = -D(p)
      rw [dif_neg hf, dif_pos hv] at heval
      -- heval : leadingCoeff C p f hf = 0
      -- But leadingCoeff(f) ≠ 0 by leadingCoeff_ne_zero
      exact leadingCoeff_ne_zero C p f hf heval

  -- If b = 0, combined with a = 0, we get (0,0), contradiction
  -- So b = 1, meaning ∃ g₀ achieving minimum
  by_contra hb_trivial_or_exists

  -- Case split: either b = 0 (quotient trivial) or ∃ g₀ achieving min
  -- We'll derive contradiction in both cases

  -- First, check if there exists g achieving minimum
  by_cases hg_exists : ∃ g₀ : Cohomology.RiemannRochSubmodule C (K.K - D + Core.Divisor.point p),
      g₀.val ≠ 0 ∧ C.valuation p g₀.val = -(K.K - D + Core.Divisor.point p).coeff p

  · -- Case: ∃ g₀ achieving minimum
    obtain ⟨g₀, hg₀_ne, hvg₀⟩ := hg_exists
    -- δ(c₁)(g₀) = c₁ * lc(g₀), δ(c₂)(g₀) = c₂ * lc(g₀)
    have hδ_g₀ := hδ_eq g₀
    simp only [connectingHom, LinearMap.coe_mk, AddHom.coe_mk] at hδ_g₀
    rw [dif_neg hg₀_ne, if_pos hvg₀] at hδ_g₀
    -- hδ_g₀ : c₁ * lc(g₀) = c₂ * lc(g₀)
    have hlc_ne := leadingCoeff_ne_zero C p g₀.val hg₀_ne
    -- c₁ * lc(g₀) = c₂ * lc(g₀) with lc(g₀) ≠ 0 implies c₁ = c₂
    have := mul_right_cancel₀ hlc_ne hδ_g₀
    exact hc_ne this

  · -- Case: no g achieves minimum (b = 0)
    -- Combined with a = 0, we have (0,0), contradiction via not_both_quotients_trivial_aux

    -- Translate to quotientTrivial for K-D+p
    have hb_trivial : RiemannSurfaces.Algebraic.quotientTrivial C (K.K - D + Core.Divisor.point p) p := by
      push_neg at hg_exists
      intro g hg_in
      by_cases hg : g = 0
      · right; exact hg
      · left
        have := hg_exists ⟨g, ?_⟩ hg
        · exact this
        · simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                     Cohomology.RiemannRochSpace]
          rcases hg_in with rfl | hg_val_all
          · exact absurd rfl hg
          · right; exact hg_val_all

    -- Apply not_both_quotients_trivial_aux to get contradiction
    exact RiemannSurfaces.Algebraic.not_both_quotients_trivial_aux C ha_trivial hb_trivial

/-!
## The Dimension Constraint (DEPRECATED)

The exactness conditions imply dim(im δ) = 1 - a.
By exactness at L(K-D+p)*: dim(im δ) = dim(ker(dual map)) = b.
Therefore: a + b = 1.
-/

/-- The key dimension constraint: a + b = 1.

    This follows from:
    1. Exactness of the 6-term sequence
    2. The alternating sum formula: V₁ - V₂ + V₃ - V₄ + V₅ - V₆ = 0
    3. Identification of dimensions with h⁰ values -/
theorem quotient_dim_sum_eq_one
    [FiniteDimensional ℂ (Cohomology.RiemannRochSubmodule C D)]
    [FiniteDimensional ℂ (Cohomology.RiemannRochSubmodule C (D - Core.Divisor.point p))]
    [FiniteDimensional ℂ (Cohomology.RiemannRochSubmodule C (K.K - D))]
    [FiniteDimensional ℂ (Cohomology.RiemannRochSubmodule C (K.K - D + Core.Divisor.point p))] :
    (Module.finrank ℂ (Cohomology.RiemannRochSubmodule C D) -
     Module.finrank ℂ (Cohomology.RiemannRochSubmodule C (D - Core.Divisor.point p))) +
    (Module.finrank ℂ (Cohomology.RiemannRochSubmodule C (K.K - D + Core.Divisor.point p)) -
     Module.finrank ℂ (Cohomology.RiemannRochSubmodule C (K.K - D))) = 1 := by
  -- The proof uses the exactness of the LES and dimension counting
  --
  -- Let n₁ = h⁰(D-p), n₂ = h⁰(D), n₄ = h⁰(K-D+p), n₅ = h⁰(K-D)
  -- Let a = n₂ - n₁ and b = n₄ - n₅
  -- We need: a + b = 1
  --
  -- From quotient_dim_le_one: 0 ≤ a ≤ 1 and 0 ≤ b ≤ 1
  -- So a, b ∈ {0, 1} and a + b ∈ {0, 1, 2}
  --
  -- Case (a = 1, b = 1) is impossible:
  --   If both quotients are nontrivial, the residue theorem gives a contradiction.
  --   (A 1-form with a unique simple pole cannot exist on a compact curve.)
  --
  -- Case (a = 0, b = 0) is impossible:
  --   If a = 0, the connecting homomorphism δ is injective (by exactness: ker δ = im eval = 0).
  --   So dim(im δ) = 1.
  --   By exactness at L(K-D+p)*: dim(im δ) = dim(ker f₄) = b.
  --   Therefore b = 1, contradicting b = 0.
  --
  -- Therefore a + b = 1.

  have ha_bound := Cohomology.quotient_dim_le_one C D p
  have hsimp : (K.K - D + Core.Divisor.point p) - Core.Divisor.point p = K.K - D := by
    ext q; simp only [Core.Divisor.sub_coeff, Core.Divisor.add_coeff, Core.Divisor.point]; ring
  haveI : FiniteDimensional ℂ (Cohomology.RiemannRochSubmodule C ((K.K - D + Core.Divisor.point p) - Core.Divisor.point p)) := by
    rw [hsimp]; infer_instance
  have hb_bound := Cohomology.quotient_dim_le_one C (K.K - D + Core.Divisor.point p) p
  rw [hsimp] at hb_bound

  -- a ∈ {0, 1} and b ∈ {0, 1}
  have h_incl_D : Module.finrank ℂ (Cohomology.RiemannRochSubmodule C (D - Core.Divisor.point p)) ≤
      Module.finrank ℂ (Cohomology.RiemannRochSubmodule C D) := by
    apply Submodule.finrank_mono
    exact Cohomology.RiemannRochSpace_sub_point_subset_submodule C D p
  have h_incl_KD : Module.finrank ℂ (Cohomology.RiemannRochSubmodule C (K.K - D)) ≤
      Module.finrank ℂ (Cohomology.RiemannRochSubmodule C (K.K - D + Core.Divisor.point p)) := by
    apply Submodule.finrank_mono
    exact Cohomology.RiemannRochSpace_KD_subset C K D p

  -- Set up for case analysis
  set a := Module.finrank ℂ (Cohomology.RiemannRochSubmodule C D) -
           Module.finrank ℂ (Cohomology.RiemannRochSubmodule C (D - Core.Divisor.point p))
  set b := Module.finrank ℂ (Cohomology.RiemannRochSubmodule C (K.K - D + Core.Divisor.point p)) -
           Module.finrank ℂ (Cohomology.RiemannRochSubmodule C (K.K - D))

  -- Case split on whether the first quotient is trivial
  by_cases ha_zero : a = 0
  · -- Case a = 0: Need to show b = 1
    -- When a = 0, L(D) = L(D-p), so eval = 0
    -- By exactness, δ is injective, so dim(im δ) = 1
    -- By exactness at L(K-D+p)*, dim(im δ) = b
    -- Therefore b = 1

    -- The connecting homomorphism is injective when a = 0
    have hδ_inj : ∀ c₁ c₂ : ℂ, (∀ g, connectingHom C K D p c₁ g = connectingHom C K D p c₂ g) → c₁ = c₂ := by
      apply delta_injective_when_eval_zero
      intro f
      -- a = 0 means L(D) = L(D-p), so every f ∈ L(D) has higher valuation at p
      -- Therefore eval(f) = 0
      simp only [evalMap]
      by_cases hf : f.val = 0
      · simp only [hf, ↓reduceDIte]
      · rw [dif_neg hf]
        -- a = 0 implies dim(L(D)) = dim(L(D-p)), so they're equal as subspaces
        -- Therefore no f ∈ L(D) achieves v_p(f) = -D(p)
        have hsub : Cohomology.RiemannRochSubmodule C (D - Core.Divisor.point p) ≤
            Cohomology.RiemannRochSubmodule C D := Cohomology.RiemannRochSpace_sub_point_subset_submodule C D p
        have heq : Module.finrank ℂ (Cohomology.RiemannRochSubmodule C (D - Core.Divisor.point p)) =
            Module.finrank ℂ (Cohomology.RiemannRochSubmodule C D) := by omega
        have heq_sub := Submodule.eq_of_le_of_finrank_eq hsub heq
        -- f is in L(D), but L(D) = L(D-p), so f is in L(D-p)
        have hf_in_Dp : f.val ∈ Cohomology.RiemannRochSubmodule C (D - Core.Divisor.point p) := by
          rw [heq_sub]; exact f.property
        -- f ∈ L(D-p) means v_p(f) > -D(p), so the condition v_p(f) = -D(p) is false
        simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                   Cohomology.RiemannRochSpace] at hf_in_Dp
        rcases hf_in_Dp with h_eq | hf_val
        · exact absurd h_eq hf
        · have hvp := hf_val p
          simp only [Core.Divisor.sub_coeff, Core.Divisor.point, ite_true] at hvp
          have hv_ne : C.valuation p f.val ≠ -D.coeff p := by omega
          rw [dif_neg hv_ne]

    -- If b = 0, combined with a = 0, we would have (0,0), contradiction
    -- Therefore b ≠ 0. Since b ≤ 1, we have b = 1.
    by_contra hb_ne_1
    push_neg at hb_ne_1
    have hb_zero : b = 0 := by omega
    -- Both quotients are trivial: derive contradiction via residue theorem
    -- Translate to quotientTrivial conditions
    have ha_trivial : RiemannSurfaces.Algebraic.quotientTrivial C D p := by
      intro f hf_in
      by_cases hf : f = 0
      · right; exact hf
      · left
        -- a = 0 means L(D) = L(D-p)
        have hsub := Cohomology.RiemannRochSpace_sub_point_subset_submodule C D p
        have heq : Module.finrank ℂ (Cohomology.RiemannRochSubmodule C (D - Core.Divisor.point p)) =
            Module.finrank ℂ (Cohomology.RiemannRochSubmodule C D) := by omega
        have heq_sub := Submodule.eq_of_le_of_finrank_eq hsub heq
        have hf_in_Dp : f ∈ Cohomology.RiemannRochSubmodule C (D - Core.Divisor.point p) := by
          rw [heq_sub]
          simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                     Cohomology.RiemannRochSpace]
          rcases hf_in with rfl | hf_val
          · exact absurd rfl hf
          · right; exact hf_val
        simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                   Cohomology.RiemannRochSpace] at hf_in_Dp
        rcases hf_in_Dp with h_eq | hf_val
        · exact absurd h_eq hf
        · have hvp := hf_val p
          simp only [Core.Divisor.sub_coeff, Core.Divisor.point, ite_true] at hvp
          -- val C p f + (D.coeff p - 1) ≥ 0, so val C p f > -D.coeff p
          simp only [RiemannSurfaces.Algebraic.val]
          have hgt : C.valuation p f > -D.coeff p := by omega
          exact ne_of_gt hgt
    have hb_trivial : RiemannSurfaces.Algebraic.quotientTrivial C (K.K - D + Core.Divisor.point p) p := by
      intro g hg_in
      by_cases hg : g = 0
      · right; exact hg
      · left
        -- b = 0 means L(K-D+p) = L(K-D)
        have hsub := Cohomology.RiemannRochSpace_KD_subset C K D p
        have heq : Module.finrank ℂ (Cohomology.RiemannRochSubmodule C (K.K - D)) =
            Module.finrank ℂ (Cohomology.RiemannRochSubmodule C (K.K - D + Core.Divisor.point p)) := by omega
        have heq_sub := Submodule.eq_of_le_of_finrank_eq hsub heq
        have hg_in_KD : g ∈ Cohomology.RiemannRochSubmodule C (K.K - D) := by
          rw [heq_sub]
          simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                     Cohomology.RiemannRochSpace]
          rcases hg_in with rfl | hg_val
          · exact absurd rfl hg
          · right; exact hg_val
        simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                   Cohomology.RiemannRochSpace] at hg_in_KD
        rcases hg_in_KD with h_eq | hg_val
        · exact absurd h_eq hg
        · have hvp := hg_val p
          simp only [Core.Divisor.sub_coeff] at hvp
          -- val C p g + (K.K.coeff p - D.coeff p) ≥ 0
          -- We need val C p g > -(K - D + point p).coeff p = -(K.K.coeff p - D.coeff p + 1)
          simp only [RiemannSurfaces.Algebraic.val]
          have hgt : C.valuation p g > -(K.K - D + Core.Divisor.point p).coeff p := by
            simp only [Core.Divisor.add_coeff, Core.Divisor.sub_coeff, Core.Divisor.point, ite_true]
            omega
          exact ne_of_gt hgt
    exact RiemannSurfaces.Algebraic.not_both_quotients_trivial_aux C ha_trivial hb_trivial

  · -- Case a ≥ 1: By bound, a = 1. Need to show b = 0.
    have ha_eq_1 : a = 1 := by
      have ha_pos : 0 < a := Nat.pos_of_ne_zero ha_zero
      omega

    -- If b = 1, combined with a = 1, we would have (1,1), contradiction
    -- Therefore b ≠ 1. Since b ≤ 1 and b ≥ 0, we have b = 0.
    by_contra hb_ne_0
    push_neg at hb_ne_0
    have hb_eq_1 : b = 1 := by omega

    -- a = 1 means there exists f ∈ L(D) with v_p(f) = -D(p)
    -- b = 1 means there exists g ∈ L(K-D+p) with v_p(g) = -(K-D+p)(p)
    -- This contradicts not_both_quotients_nontrivial_aux

    -- Translate a = 1 to existence of f achieving minimum
    have hf_exists : ∃ f, RiemannSurfaces.Algebraic.inQuotient C f D p := by
      -- a = 1 means dim(L(D)) > dim(L(D-p))
      -- So there exists f ∈ L(D) \ L(D-p)
      -- This means v_p(f) = -D(p) exactly
      have hne : Cohomology.RiemannRochSubmodule C D ≠ Cohomology.RiemannRochSubmodule C (D - Core.Divisor.point p) := by
        intro heq
        have hdim_eq : Module.finrank ℂ (Cohomology.RiemannRochSubmodule C D) =
            Module.finrank ℂ (Cohomology.RiemannRochSubmodule C (D - Core.Divisor.point p)) := by
          rw [heq]
        omega
      -- Get f that's in L(D) but not in L(D-p)
      have hsub := Cohomology.RiemannRochSpace_sub_point_subset_submodule C D p
      have hne' := lt_of_le_of_ne hsub (Ne.symm hne)
      obtain ⟨f, hf_D, hf_not_Dp⟩ := SetLike.exists_of_lt hne'
      use f
      constructor
      · -- f ≠ 0 (if f = 0, it would be in L(D-p))
        intro hf_zero
        apply hf_not_Dp
        simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                   Cohomology.RiemannRochSpace]
        left; exact hf_zero
      constructor
      · -- f ∈ L(D)
        simp only [RiemannSurfaces.Algebraic.inRiemannRochSpace]
        simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                   Cohomology.RiemannRochSpace] at hf_D
        rcases hf_D with hf_zero | hf_val
        · left; exact hf_zero
        · right
          intro q
          simp only [RiemannSurfaces.Algebraic.val]
          exact hf_val q
      · -- v_p(f) = -D(p)
        simp only [RiemannSurfaces.Algebraic.val]
        -- f ∈ L(D) means v_p(f) ≥ -D(p)
        -- f ∉ L(D-p) means ¬(v_p(f) ≥ -D(p) + 1)
        simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                   Cohomology.RiemannRochSpace] at hf_D hf_not_Dp
        rcases hf_D with hf_zero | hf_val
        · exfalso
          apply hf_not_Dp
          left; exact hf_zero
        · have hvf_ge := hf_val p
          -- f ∉ L(D-p) means f isn't zero and doesn't satisfy the valuation bound at p
          -- Since f ∈ L(D), the only way f ∉ L(D-p) is v_p(f) = -D(p) exactly
          by_contra hv_ne
          apply hf_not_Dp
          right
          intro q
          by_cases hq : q = p
          · subst hq
            simp only [Core.Divisor.sub_coeff, Core.Divisor.point, ite_true]
            -- v_p(f) ≠ -D(p) and v_p(f) ≥ -D(p), so v_p(f) > -D(p), so v_p(f) ≥ -D(p) + 1
            omega
          · have := hf_val q
            simp only [Core.Divisor.sub_coeff, Core.Divisor.point, if_neg hq, sub_zero]
            exact this

    -- Translate b = 1 to existence of g achieving minimum
    have hg_exists : ∃ g, RiemannSurfaces.Algebraic.inQuotient C g (K.K - D + Core.Divisor.point p) p := by
      -- Similar to above, b = 1 means dim(L(K-D+p)) > dim(L(K-D))
      have hne : Cohomology.RiemannRochSubmodule C (K.K - D + Core.Divisor.point p) ≠
          Cohomology.RiemannRochSubmodule C (K.K - D) := by
        intro heq
        have hdim_eq : Module.finrank ℂ (Cohomology.RiemannRochSubmodule C (K.K - D + Core.Divisor.point p)) =
            Module.finrank ℂ (Cohomology.RiemannRochSubmodule C (K.K - D)) := by
          rw [heq]
        omega
      have hsub := Cohomology.RiemannRochSpace_KD_subset C K D p
      have hne' := lt_of_le_of_ne hsub (Ne.symm hne)
      obtain ⟨g, hg_KDp, hg_not_KD⟩ := SetLike.exists_of_lt hne'
      use g
      constructor
      · intro hg_zero
        apply hg_not_KD
        simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                   Cohomology.RiemannRochSpace]
        left; exact hg_zero
      constructor
      · simp only [RiemannSurfaces.Algebraic.inRiemannRochSpace]
        simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                   Cohomology.RiemannRochSpace] at hg_KDp
        rcases hg_KDp with hg_zero | hg_val
        · left; exact hg_zero
        · right
          intro q
          simp only [RiemannSurfaces.Algebraic.val]
          exact hg_val q
      · simp only [RiemannSurfaces.Algebraic.val]
        simp only [Cohomology.RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                   Cohomology.RiemannRochSpace] at hg_KDp hg_not_KD
        rcases hg_KDp with hg_zero | hg_val
        · exfalso
          apply hg_not_KD
          left; exact hg_zero
        · have hvg_ge := hg_val p
          simp only [Core.Divisor.add_coeff, Core.Divisor.sub_coeff, Core.Divisor.point, ite_true] at hvg_ge
          -- g ∈ L(K-D+p), g ∉ L(K-D)
          -- g ∈ L(K-D+p) means v_p(g) ≥ -(K-D+p)(p) = -(K-D)(p) - 1
          -- g ∉ L(K-D) means v_p(g) doesn't satisfy v_p(g) ≥ -(K-D)(p)
          -- So v_p(g) = -(K-D)(p) - 1 = -(K-D+p)(p)
          by_contra hv_ne
          apply hg_not_KD
          right
          intro q
          by_cases hq : q = p
          · subst hq
            simp only [Core.Divisor.sub_coeff]
            simp only [Core.Divisor.add_coeff, Core.Divisor.sub_coeff, Core.Divisor.point, ite_true] at hv_ne
            omega
          · have := hg_val q
            simp only [Core.Divisor.sub_coeff, Core.Divisor.add_coeff, Core.Divisor.point, if_neg hq] at this ⊢
            simp only [add_zero] at this
            exact this

    -- Apply the contradiction lemma
    obtain ⟨f, hf_quotient⟩ := hf_exists
    obtain ⟨g, hg_quotient⟩ := hg_exists
    exact RiemannSurfaces.Algebraic.not_both_quotients_nontrivial_aux C rfl ⟨f, hf_quotient⟩ ⟨g, hg_quotient⟩

end RiemannSurfaces.Algebraic.PointExactInfra
