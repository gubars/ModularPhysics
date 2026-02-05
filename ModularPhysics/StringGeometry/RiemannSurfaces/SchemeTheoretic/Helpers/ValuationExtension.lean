/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Order.Group.Nat

/-!
# Extending DVR Valuations to Fraction Fields

For a DVR R with fraction field K = Frac(R), we extend `addVal : R → ℕ∞`
to an integer-valued valuation `extendedVal : K → ℤ` defined by:
- `extendedVal(a/b) = addVal(a) - addVal(b)` for a, b in R, b ≠ 0

## Main Definitions

* `DVRValuation.extendedVal` - The extended valuation K → ℤ

## Main Results

* `extendedVal_zero` - v(0) = 0 by convention
* `extendedVal_mul` - v(fg) = v(f) + v(g)
* `extendedVal_add_min` - v(f+g) ≥ min(v(f), v(g))
* `extendedVal_algebraMap` - v(r) = addVal(r) for r in R

## References

* Mathlib.RingTheory.DiscreteValuationRing.Basic
* Neukirch, "Algebraic Number Theory", Chapter I.3
-/

open scoped Classical

namespace DVRValuation

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-!
## Fraction Field Helpers

Note: Some of these helpers only use IsFractionRing, not IsDomain/IsDiscreteValuationRing.
The linter warnings about unused section variables are expected.
-/

/-- The numerator part of the fraction representation. -/
noncomputable def fracNum (f : K) : R :=
  Classical.choose (IsFractionRing.div_surjective (A := R) f)

/-- The denominator part of the fraction representation. -/
noncomputable def fracDenom (f : K) : R :=
  Classical.choose (Classical.choose_spec (IsFractionRing.div_surjective (A := R) f))

/-- The denominator is a non-zero divisor. -/
theorem fracDenom_mem_nonZeroDivisors (f : K) :
    fracDenom f ∈ nonZeroDivisors R :=
  (Classical.choose_spec (Classical.choose_spec (IsFractionRing.div_surjective (A := R) f))).1

/-- The denominator is nonzero. -/
theorem fracDenom_ne_zero (f : K) : (fracDenom f : R) ≠ 0 :=
  nonZeroDivisors.ne_zero (fracDenom_mem_nonZeroDivisors f)

/-- The fraction representation is correct. -/
theorem fracData_eq (f : K) :
    algebraMap R K (fracNum f) / algebraMap R K (fracDenom f) = f :=
  (Classical.choose_spec (Classical.choose_spec (IsFractionRing.div_surjective (A := R) f))).2

/-- If f ≠ 0, then the numerator is nonzero. -/
theorem fracNum_ne_zero_of_ne_zero {f : K} (hf : f ≠ 0) : (fracNum f : R) ≠ 0 := by
  intro h
  have heq : algebraMap R K (fracNum f) / algebraMap R K (fracDenom f) = f := fracData_eq f
  rw [h, map_zero, zero_div] at heq
  exact hf heq.symm

/-!
## DVR Valuation Helpers
-/

/-- For nonzero elements of a DVR, addVal is finite. -/
theorem addVal_ne_top_of_ne_zero {r : R} (hr : r ≠ 0) :
    IsDiscreteValuationRing.addVal R r ≠ ⊤ := by
  simp only [ne_eq, IsDiscreteValuationRing.addVal_eq_top_iff]
  exact hr

/-- Extract natural number value from addVal for nonzero elements. -/
noncomputable def addValNat (r : R) (_ : r ≠ 0) : ℕ :=
  (IsDiscreteValuationRing.addVal R r).toNat

theorem addValNat_eq (r : R) (hr : r ≠ 0) :
    (addValNat r hr : ℕ∞) = IsDiscreteValuationRing.addVal R r := by
  simp only [addValNat]
  rw [ENat.coe_toNat]
  exact addVal_ne_top_of_ne_zero hr

/-!
## Well-Definedness Lemma

The key to proving properties of extendedVal is showing the valuation is independent
of the fraction representation chosen.
-/

/-- The valuation difference v(a) - v(b) depends only on the fraction a/b, not on the
    particular representation. If a/b = c/d in K, then v(a) - v(b) = v(c) - v(d).

    **Proof:** a/b = c/d implies ad = bc (by IsFractionRing.injective).
    By addVal_mul: v(ad) = v(a) + v(d) and v(bc) = v(b) + v(c).
    Since ad = bc, we have v(a) + v(d) = v(b) + v(c), so v(a) - v(b) = v(c) - v(d). -/
theorem valuation_well_defined {a b c d : R} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (heq : algebraMap R K a / algebraMap R K b = algebraMap R K c / algebraMap R K d) :
    (addValNat a ha : ℤ) - (addValNat b hb : ℤ) = (addValNat c hc : ℤ) - (addValNat d hd : ℤ) := by
  -- From the equality of fractions, derive a * d = b * c
  have hbK : algebraMap R K b ≠ 0 := by
    intro h; exact hb (IsFractionRing.injective R K (h.trans (algebraMap R K).map_zero.symm))
  have hdK : algebraMap R K d ≠ 0 := by
    intro h; exact hd (IsFractionRing.injective R K (h.trans (algebraMap R K).map_zero.symm))
  have heq' : algebraMap R K a * algebraMap R K d = algebraMap R K b * algebraMap R K c := by
    have h1 : algebraMap R K a / algebraMap R K b * algebraMap R K b = algebraMap R K a := by
      field_simp
    have h2 : algebraMap R K c / algebraMap R K d * algebraMap R K d = algebraMap R K c := by
      field_simp
    calc algebraMap R K a * algebraMap R K d
        = (algebraMap R K a / algebraMap R K b * algebraMap R K b) * algebraMap R K d := by rw [h1]
      _ = (algebraMap R K a / algebraMap R K b) * (algebraMap R K b * algebraMap R K d) := by ring
      _ = (algebraMap R K c / algebraMap R K d) * (algebraMap R K b * algebraMap R K d) := by rw [heq]
      _ = algebraMap R K b * (algebraMap R K c / algebraMap R K d * algebraMap R K d) := by ring
      _ = algebraMap R K b * algebraMap R K c := by rw [h2]
  -- Use injectivity of algebraMap to get a * d = b * c in R
  rw [← map_mul, ← map_mul] at heq'
  have had_eq_bc : a * d = b * c := IsFractionRing.injective R K heq'
  -- Use multiplicativity of addVal
  have had_ne : a * d ≠ 0 := mul_ne_zero ha hd
  have hbc_ne : b * c ≠ 0 := mul_ne_zero hb hc
  -- addVal(a * d) = addVal(a) + addVal(d) and same for b * c
  have hval_ad : IsDiscreteValuationRing.addVal R (a * d) =
      IsDiscreteValuationRing.addVal R a + IsDiscreteValuationRing.addVal R d :=
    IsDiscreteValuationRing.addVal_mul
  have hval_bc : IsDiscreteValuationRing.addVal R (b * c) =
      IsDiscreteValuationRing.addVal R b + IsDiscreteValuationRing.addVal R c :=
    IsDiscreteValuationRing.addVal_mul
  -- ad = bc implies v(ad) = v(bc)
  rw [had_eq_bc] at hval_ad
  -- Now v(a) + v(d) = v(b) + v(c) in ℕ∞
  have h_enats : IsDiscreteValuationRing.addVal R a + IsDiscreteValuationRing.addVal R d =
           IsDiscreteValuationRing.addVal R b + IsDiscreteValuationRing.addVal R c := by
    rw [← hval_ad, ← hval_bc]
  -- Convert to natural numbers (values are finite for nonzero elements)
  simp only [addValNat]
  -- Convert addVal values to Nat using toNat
  have ha_fin := addVal_ne_top_of_ne_zero ha
  have hb_fin := addVal_ne_top_of_ne_zero hb
  have hc_fin := addVal_ne_top_of_ne_zero hc
  have hd_fin := addVal_ne_top_of_ne_zero hd
  -- Use the equality in ℕ∞ to derive the equality in ℤ
  have h_nat : (IsDiscreteValuationRing.addVal R a).toNat +
               (IsDiscreteValuationRing.addVal R d).toNat =
               (IsDiscreteValuationRing.addVal R b).toNat +
               (IsDiscreteValuationRing.addVal R c).toNat := by
    have := congrArg ENat.toNat h_enats
    simp only [ENat.toNat_add ha_fin hd_fin, ENat.toNat_add hb_fin hc_fin] at this
    exact this
  omega

/-!
## Main Definition
-/

/-- Extended valuation from DVR to its fraction field.

    For f = a/b in K, returns v(a) - v(b) where v is the DVR valuation.
    Convention: v(0) = 0 (though mathematically v(0) = +∞). -/
noncomputable def extendedVal : K → ℤ := fun f =>
  if hf : f = 0 then 0
  else
    have hnum : fracNum (R := R) f ≠ 0 := fracNum_ne_zero_of_ne_zero hf
    have hdenom : fracDenom (R := R) f ≠ 0 := fracDenom_ne_zero f
    (addValNat (fracNum f) hnum : ℤ) - (addValNat (fracDenom f) hdenom : ℤ)

/-!
## Basic Properties
-/

/-- v(0) = 0 by our convention. -/
theorem extendedVal_zero : extendedVal (R := R) (0 : K) = 0 := by
  simp [extendedVal]

/-- v(1) = 0. -/
theorem extendedVal_one : extendedVal (R := R) (1 : K) = 0 := by
  simp only [extendedVal]
  split_ifs with h
  · rfl
  · -- 1 = 1/1 in the fraction field, so 1 = algebraMap R K 1
    -- The fracNum/fracDenom representation of 1 should give v(num) - v(denom)
    -- which equals v(1) - v(1) = 0 - 0 = 0 by well-definedness
    have hnum : fracNum (R := R) (1 : K) ≠ 0 := fracNum_ne_zero_of_ne_zero h
    have hdenom : fracDenom (R := R) (1 : K) ≠ 0 := fracDenom_ne_zero (1 : K)
    have h1_ne : (1 : R) ≠ 0 := one_ne_zero
    -- 1 in K = algebraMap R K 1 / algebraMap R K 1 = fracNum / fracDenom
    have heq1 : algebraMap R K (fracNum (R := R) (1 : K)) /
                algebraMap R K (fracDenom (R := R) (1 : K)) = (1 : K) := fracData_eq (1 : K)
    have heq2 : algebraMap R K 1 / algebraMap R K 1 = (1 : K) := by simp
    have heq : algebraMap R K (fracNum (R := R) (1 : K)) /
               algebraMap R K (fracDenom (R := R) (1 : K)) =
               algebraMap R K 1 / algebraMap R K 1 := by rw [heq1, heq2]
    have hwd := valuation_well_defined hnum hdenom h1_ne h1_ne heq
    -- v(1) = 0
    have h1_val : addValNat (1 : R) h1_ne = 0 := by
      simp only [addValNat]
      rw [IsDiscreteValuationRing.addVal_one]
      rfl
    simp only [h1_val, sub_self] at hwd
    exact hwd

/-- v(fg) = v(f) + v(g) for f, g ≠ 0.

    This extends the multiplicativity of addVal to the fraction field. -/
theorem extendedVal_mul (f g : K) (hf : f ≠ 0) (hg : g ≠ 0) :
    extendedVal (R := R) (f * g) = extendedVal (R := R) f + extendedVal (R := R) g := by
  simp only [extendedVal, dif_neg hf, dif_neg hg]
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  simp only [dif_neg hfg]
  -- Abbreviations for readability
  set a := fracNum (R := R) f with ha_def
  set b := fracDenom (R := R) f with hb_def
  set c := fracNum (R := R) g with hc_def
  set d := fracDenom (R := R) g with hd_def
  set e := fracNum (R := R) (f * g) with he_def
  set w := fracDenom (R := R) (f * g) with hw_def
  -- Nonzero hypotheses
  have ha : a ≠ 0 := fracNum_ne_zero_of_ne_zero hf
  have hb : b ≠ 0 := fracDenom_ne_zero f
  have hc : c ≠ 0 := fracNum_ne_zero_of_ne_zero hg
  have hd : d ≠ 0 := fracDenom_ne_zero g
  have he : e ≠ 0 := fracNum_ne_zero_of_ne_zero hfg
  have hw : w ≠ 0 := fracDenom_ne_zero (f * g)
  have hac : a * c ≠ 0 := mul_ne_zero ha hc
  have hbd : b * d ≠ 0 := mul_ne_zero hb hd
  -- Fraction representations
  have heq_f : algebraMap R K a / algebraMap R K b = f := fracData_eq f
  have heq_g : algebraMap R K c / algebraMap R K d = g := fracData_eq g
  have heq_fg : algebraMap R K e / algebraMap R K w = f * g := fracData_eq (f * g)
  -- Key: both (e/w) and (ac/bd) equal f*g
  have hbK : algebraMap R K b ≠ 0 := by
    intro h; exact hb (IsFractionRing.injective R K (h.trans (algebraMap R K).map_zero.symm))
  have hdK : algebraMap R K d ≠ 0 := by
    intro h; exact hd (IsFractionRing.injective R K (h.trans (algebraMap R K).map_zero.symm))
  have heq_prod : algebraMap R K (a * c) / algebraMap R K (b * d) = f * g := by
    rw [map_mul, map_mul]
    calc algebraMap R K a * algebraMap R K c / (algebraMap R K b * algebraMap R K d)
        = (algebraMap R K a / algebraMap R K b) * (algebraMap R K c / algebraMap R K d) := by
          field_simp
      _ = f * g := by rw [heq_f, heq_g]
  have heq : algebraMap R K e / algebraMap R K w = algebraMap R K (a * c) / algebraMap R K (b * d) := by
    rw [heq_fg, heq_prod]
  -- Apply well-definedness: v(e) - v(w) = v(ac) - v(bd)
  have hwd := valuation_well_defined he hw hac hbd heq
  -- v(ac) = v(a) + v(c) and v(bd) = v(b) + v(d)
  have hval_ac : (addValNat (a * c) hac : ℤ) = addValNat a ha + addValNat c hc := by
    unfold addValNat
    have h := IsDiscreteValuationRing.addVal_mul (R := R) (a := a) (b := c)
    have ha_fin := addVal_ne_top_of_ne_zero ha
    have hc_fin := addVal_ne_top_of_ne_zero hc
    -- v(a*c) = v(a) + v(c), convert to toNat
    have hac_eq : (IsDiscreteValuationRing.addVal R (a * c)).toNat =
        (IsDiscreteValuationRing.addVal R a).toNat + (IsDiscreteValuationRing.addVal R c).toNat := by
      rw [h, ENat.toNat_add ha_fin hc_fin]
    simp only [hac_eq, Nat.cast_add]
  have hval_bd : (addValNat (b * d) hbd : ℤ) = addValNat b hb + addValNat d hd := by
    unfold addValNat
    have h := IsDiscreteValuationRing.addVal_mul (R := R) (a := b) (b := d)
    have hb_fin := addVal_ne_top_of_ne_zero hb
    have hd_fin := addVal_ne_top_of_ne_zero hd
    have hbd_eq : (IsDiscreteValuationRing.addVal R (b * d)).toNat =
        (IsDiscreteValuationRing.addVal R b).toNat + (IsDiscreteValuationRing.addVal R d).toNat := by
      rw [h, ENat.toNat_add hb_fin hd_fin]
    simp only [hbd_eq, Nat.cast_add]
  rw [hwd, hval_ac, hval_bd]
  ring

/-- v(f + g) ≥ min(v(f), v(g)) when f + g ≠ 0 (ultrametric inequality).

    This extends the ultrametric property of addVal. -/
theorem extendedVal_add_min (f g : K) (hfg : f + g ≠ 0) :
    extendedVal (R := R) (f + g) ≥ min (extendedVal (R := R) f) (extendedVal (R := R) g) := by
  -- Handle edge cases: f = 0 or g = 0
  by_cases hf : f = 0
  · -- f = 0: f + g = g, min(v(0), v(g)) = min(0, v(g))
    simp only [hf, zero_add, extendedVal_zero]
    exact min_le_right 0 _
  by_cases hg : g = 0
  · -- g = 0: f + g = f, min(v(f), v(0)) = min(v(f), 0)
    simp only [hg, add_zero, extendedVal_zero]
    exact min_le_left _ 0
  -- Main case: f ≠ 0 and g ≠ 0
  -- For f = a/b and g = c/d, we have f + g = (ad + bc)/(bd)
  set a := fracNum (R := R) f with ha_def
  set b := fracDenom (R := R) f with hb_def
  set c := fracNum (R := R) g with hc_def
  set d := fracDenom (R := R) g with hd_def
  set e := fracNum (R := R) (f + g) with he_def
  set w := fracDenom (R := R) (f + g) with hw_def
  -- Nonzero hypotheses
  have ha : a ≠ 0 := fracNum_ne_zero_of_ne_zero hf
  have hb : b ≠ 0 := fracDenom_ne_zero f
  have hc : c ≠ 0 := fracNum_ne_zero_of_ne_zero hg
  have hd : d ≠ 0 := fracDenom_ne_zero g
  have he : e ≠ 0 := fracNum_ne_zero_of_ne_zero hfg
  have hw : w ≠ 0 := fracDenom_ne_zero (f + g)
  have hbd : b * d ≠ 0 := mul_ne_zero hb hd
  -- Fraction representations
  have heq_f : algebraMap R K a / algebraMap R K b = f := fracData_eq f
  have heq_g : algebraMap R K c / algebraMap R K d = g := fracData_eq g
  have heq_fg : algebraMap R K e / algebraMap R K w = f + g := fracData_eq (f + g)
  -- f + g = (ad + bc) / (bd)
  have hbK : algebraMap R K b ≠ 0 := by
    intro h; exact hb (IsFractionRing.injective R K (h.trans (algebraMap R K).map_zero.symm))
  have hdK : algebraMap R K d ≠ 0 := by
    intro h; exact hd (IsFractionRing.injective R K (h.trans (algebraMap R K).map_zero.symm))
  have heq_sum : algebraMap R K (a * d + b * c) / algebraMap R K (b * d) = f + g := by
    rw [map_add, map_mul, map_mul, map_mul]
    calc (algebraMap R K a * algebraMap R K d + algebraMap R K b * algebraMap R K c) /
         (algebraMap R K b * algebraMap R K d)
        = algebraMap R K a / algebraMap R K b + algebraMap R K c / algebraMap R K d := by
          field_simp
      _ = f + g := by rw [heq_f, heq_g]
  -- Since f + g ≠ 0, we have a * d + b * c ≠ 0
  have had_bc : a * d + b * c ≠ 0 := by
    intro h
    have : f + g = 0 := by
      rw [← heq_sum, h, map_zero, zero_div]
    exact hfg this
  -- By well-definedness: v(e) - v(w) = v(ad + bc) - v(bd)
  have heq : algebraMap R K e / algebraMap R K w =
             algebraMap R K (a * d + b * c) / algebraMap R K (b * d) := by
    rw [heq_fg, heq_sum]
  have hwd := valuation_well_defined he hw had_bc hbd heq
  -- Use addVal_add: min(v(ad), v(bc)) ≤ v(ad + bc)
  have h_ultra := IsDiscreteValuationRing.addVal_add (R := R) (a := a * d) (b := b * c)
  -- Convert to our notation
  simp only [extendedVal, dif_neg hf, dif_neg hg, dif_neg hfg]
  -- Goal: v(e) - v(w) ≥ min(v(a) - v(b), v(c) - v(d))
  -- By hwd: v(e) - v(w) = v(ad+bc) - v(bd)
  -- By h_ultra: v(ad+bc) ≥ min(v(ad), v(bc))
  -- v(ad) = v(a) + v(d), v(bc) = v(b) + v(c), v(bd) = v(b) + v(d)
  -- min(v(ad), v(bc)) - v(bd) = min(v(a)+v(d) - v(b)-v(d), v(b)+v(c) - v(b)-v(d))
  --                           = min(v(a) - v(b), v(c) - v(d))
  -- Need to translate addVal to addValNat for our definitions
  have had : a * d ≠ 0 := mul_ne_zero ha hd
  have hbc : b * c ≠ 0 := mul_ne_zero hb hc
  -- All values are finite for nonzero elements
  have ha_fin := addVal_ne_top_of_ne_zero ha
  have hb_fin := addVal_ne_top_of_ne_zero hb
  have hc_fin := addVal_ne_top_of_ne_zero hc
  have hd_fin := addVal_ne_top_of_ne_zero hd
  have had_fin := addVal_ne_top_of_ne_zero had
  have hbc_fin := addVal_ne_top_of_ne_zero hbc
  have hbd_fin := addVal_ne_top_of_ne_zero hbd
  have had_bc_fin := addVal_ne_top_of_ne_zero had_bc
  -- Abbreviate valuations as natural numbers
  set va := (IsDiscreteValuationRing.addVal R a).toNat with hva
  set vb := (IsDiscreteValuationRing.addVal R b).toNat with hvb
  set vc := (IsDiscreteValuationRing.addVal R c).toNat with hvc
  set vd := (IsDiscreteValuationRing.addVal R d).toNat with hvd
  set vad := (IsDiscreteValuationRing.addVal R (a * d)).toNat with hvad
  set vbc := (IsDiscreteValuationRing.addVal R (b * c)).toNat with hvbc
  set vbd := (IsDiscreteValuationRing.addVal R (b * d)).toNat with hvbd
  set vsum := (IsDiscreteValuationRing.addVal R (a * d + b * c)).toNat with hvsum
  -- v(ad) = v(a) + v(d), v(bc) = v(b) + v(c), v(bd) = v(b) + v(d)
  have hval_ad : vad = va + vd := by
    have h := IsDiscreteValuationRing.addVal_mul (R := R) (a := a) (b := d)
    simp only [hvad, hva, hvd, h, ENat.toNat_add ha_fin hd_fin]
  have hval_bc : vbc = vb + vc := by
    have h := IsDiscreteValuationRing.addVal_mul (R := R) (a := b) (b := c)
    simp only [hvbc, hvb, hvc, h, ENat.toNat_add hb_fin hc_fin]
  have hval_bd : vbd = vb + vd := by
    have h := IsDiscreteValuationRing.addVal_mul (R := R) (a := b) (b := d)
    simp only [hvbd, hvb, hvd, h, ENat.toNat_add hb_fin hd_fin]
  -- Final arithmetic
  unfold addValNat at hwd ⊢
  simp only [ha_def, hb_def, hc_def, hd_def] at hwd ⊢
  rw [hwd]
  -- Need: vsum - vbd ≥ min(va - vb, vc - vd) in ℤ
  -- h_ultra : min(addVal(ad), addVal(bc)) ≤ addVal(ad+bc)
  -- Convert to ℕ using toNat
  have h_ultra_nat : min vad vbc ≤ vsum := by
    have h_tonat := ENat.toNat_le_toNat h_ultra had_bc_fin
    -- toNat(min(x, y)) = min(toNat(x), toNat(y)) when both are finite
    have h_min_tonat : (min (IsDiscreteValuationRing.addVal R (a * d))
                           (IsDiscreteValuationRing.addVal R (b * c))).toNat =
                       min vad vbc := by
      simp only [hvad, hvbc]
      by_cases heq : (IsDiscreteValuationRing.addVal R (a * d)) ≤
                     (IsDiscreteValuationRing.addVal R (b * c))
      · rw [min_eq_left heq, min_eq_left (ENat.toNat_le_toNat heq hbc_fin)]
      · push_neg at heq
        rw [min_eq_right (le_of_lt heq), min_eq_right (ENat.toNat_le_toNat (le_of_lt heq) had_fin)]
    rw [h_min_tonat] at h_tonat
    exact h_tonat
  -- Final arithmetic using omega
  -- min(vad, vbc) ≤ vsum  and  vad = va + vd, vbc = vb + vc, vbd = vb + vd
  -- implies vsum - vbd ≥ min(va - vb, vc - vd)
  have h1 : (vsum : ℤ) - vbd ≥ min (vad : ℤ) (vbc : ℤ) - vbd := by
    have h : min vad vbc ≤ vsum := h_ultra_nat
    have hvad_le : min vad vbc ≤ vad := Nat.min_le_left vad vbc
    have hvbc_le : min vad vbc ≤ vbc := Nat.min_le_right vad vbc
    omega
  have h2 : min (vad : ℤ) (vbc : ℤ) - vbd = min ((vad : ℤ) - vbd) ((vbc : ℤ) - vbd) := by
    by_cases hle : (vad : ℤ) ≤ (vbc : ℤ)
    · rw [min_eq_left hle, min_eq_left]; omega
    · push_neg at hle
      rw [min_eq_right (le_of_lt hle), min_eq_right]; omega
  have h3 : ((vad : ℤ) - vbd) = (va : ℤ) - vb := by
    simp only [hval_ad, hval_bd, Nat.cast_add]; ring
  have h4 : ((vbc : ℤ) - vbd) = (vc : ℤ) - vd := by
    simp only [hval_bc, hval_bd, Nat.cast_add]; ring
  rw [h2, h3, h4] at h1
  simp only [hva, hvb, hvc, hvd, hvsum, hvbd] at h1
  exact h1

/-- v(r) = addValNat(r) for nonzero r in R (embedded into K). -/
theorem extendedVal_algebraMap (r : R) (hr : r ≠ 0) :
    extendedVal (R := R) (algebraMap R K r) = addValNat r hr := by
  simp only [extendedVal]
  have hne : algebraMap R K r ≠ 0 := by
    intro h
    rw [← (algebraMap R K).map_zero] at h
    exact hr (IsFractionRing.injective R K h)
  simp only [dif_neg hne]
  -- The key is that algebraMap R K r = (algebraMap R K r) / (algebraMap R K 1)
  -- and the fractional representation fracNum/fracDenom gives the same element
  -- Use well-definedness: if a/b = c/d then v(a) - v(b) = v(c) - v(d)
  have hnum : fracNum (R := R) (algebraMap R K r) ≠ 0 := fracNum_ne_zero_of_ne_zero hne
  have hdenom : fracDenom (R := R) (algebraMap R K r) ≠ 0 := fracDenom_ne_zero (algebraMap R K r)
  have h1_ne : (1 : R) ≠ 0 := one_ne_zero
  -- algebraMap R K r = algebraMap R K (fracNum) / algebraMap R K (fracDenom) by fracData_eq
  -- algebraMap R K r = algebraMap R K r / algebraMap R K 1 (trivially)
  have heq1 : algebraMap R K (fracNum (R := R) (algebraMap R K r)) /
              algebraMap R K (fracDenom (R := R) (algebraMap R K r)) =
              algebraMap R K r := fracData_eq (algebraMap R K r)
  have heq2 : algebraMap R K r / algebraMap R K 1 = algebraMap R K r := by simp
  have heq : algebraMap R K (fracNum (R := R) (algebraMap R K r)) /
             algebraMap R K (fracDenom (R := R) (algebraMap R K r)) =
             algebraMap R K r / algebraMap R K 1 := by rw [heq1, heq2]
  -- Apply well-definedness
  have hwd := valuation_well_defined hnum hdenom hr h1_ne heq
  -- v(fracNum) - v(fracDenom) = v(r) - v(1)
  -- v(1) = 0, so v(fracNum) - v(fracDenom) = v(r)
  have h1_val : addValNat (1 : R) h1_ne = 0 := by
    simp only [addValNat]
    rw [IsDiscreteValuationRing.addVal_one]
    rfl
  simp only [h1_val] at hwd
  exact hwd

/-- v(f⁻¹) = -v(f) for f ≠ 0. -/
theorem extendedVal_inv (f : K) (hf : f ≠ 0) :
    extendedVal (R := R) f⁻¹ = -extendedVal (R := R) f := by
  simp only [extendedVal, dif_neg hf]
  have hinv : f⁻¹ ≠ 0 := inv_ne_zero hf
  simp only [dif_neg hinv]
  -- For f = a/b, we have f⁻¹ = b/a
  -- v(f⁻¹) = v(b) - v(a) = -(v(a) - v(b)) = -v(f)
  set a := fracNum (R := R) f with ha_def
  set b := fracDenom (R := R) f with hb_def
  set c := fracNum (R := R) f⁻¹ with hc_def
  set d := fracDenom (R := R) f⁻¹ with hd_def
  -- Nonzero hypotheses
  have ha : a ≠ 0 := fracNum_ne_zero_of_ne_zero hf
  have hb : b ≠ 0 := fracDenom_ne_zero f
  have hc : c ≠ 0 := fracNum_ne_zero_of_ne_zero hinv
  have hd : d ≠ 0 := fracDenom_ne_zero f⁻¹
  -- Fraction representations: f = a/b, f⁻¹ = c/d
  have heq_f : algebraMap R K a / algebraMap R K b = f := fracData_eq f
  have heq_inv : algebraMap R K c / algebraMap R K d = f⁻¹ := fracData_eq f⁻¹
  -- Also f⁻¹ = (a/b)⁻¹ = b/a
  have hbK : algebraMap R K b ≠ 0 := by
    intro h; exact hb (IsFractionRing.injective R K (h.trans (algebraMap R K).map_zero.symm))
  have haK : algebraMap R K a ≠ 0 := by
    intro h; exact ha (IsFractionRing.injective R K (h.trans (algebraMap R K).map_zero.symm))
  have heq_ba : algebraMap R K b / algebraMap R K a = f⁻¹ := by
    rw [← heq_f]
    field_simp
  -- Both c/d and b/a equal f⁻¹
  have heq : algebraMap R K c / algebraMap R K d = algebraMap R K b / algebraMap R K a := by
    rw [heq_inv, heq_ba]
  -- Apply well-definedness: v(c) - v(d) = v(b) - v(a)
  have hwd := valuation_well_defined hc hd hb ha heq
  -- v(c) - v(d) = v(b) - v(a) = -(v(a) - v(b))
  linarith

/-- Units in R have valuation 0 when viewed in K. -/
theorem extendedVal_unit (u : Rˣ) :
    extendedVal (R := R) (algebraMap R K u) = 0 := by
  have hu : (u : R) ≠ 0 := Units.ne_zero u
  rw [extendedVal_algebraMap (u : R) hu]
  -- addVal of a unit is 0
  have hval : IsDiscreteValuationRing.addVal R u = 0 :=
    IsDiscreteValuationRing.addVal_eq_zero_of_unit u
  simp only [addValNat]
  rw [hval]
  rfl

end DVRValuation
