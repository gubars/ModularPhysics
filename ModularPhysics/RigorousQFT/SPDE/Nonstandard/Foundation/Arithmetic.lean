/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Arithmetic Helper Lemmas

This file provides helper lemmas for integer/real arithmetic, particularly for:
- Integer division and its relationship to real division
- Cast conversions between ℕ, ℤ, and ℝ
- Floor and ceiling properties

These are used throughout the SPDE/Nonstandard development, especially in
the Local CLT proofs where we need to convert between integer and real bounds.

## Main Results

* `int_div2_le_real_div2` - Integer division is at most real division
* `int_div2_ge_real_div2_sub_half` - Integer division is at least real division minus 1/2
* `int_ge_one_of_real_gt_half_nonneg` - Integer > 0.5 as real implies integer ≥ 1
* `natCast_intCast_eq` - ((n : ℤ) : ℝ) = (n : ℝ) for naturals

## Implementation Notes

These lemmas are designed to be short and composable, reducing boilerplate
in longer proofs involving mixed integer/real arithmetic.

**Important distinction**: `(((n : ℤ) / 2) : ℝ)` is the cast of integer division to real,
while `((n : ℤ) : ℝ) / 2` is real division after casting. These are NOT equal in general!
-/

open Int

namespace SPDE.Nonstandard.Arithmetic

/-! ## Cast Conversions -/

/-- Natural to integer to real equals natural to real directly. -/
theorem natCast_intCast_eq (n : ℕ) : ((n : ℤ) : ℝ) = (n : ℝ) := Int.cast_natCast n

/-- Integer absolute value cast to real equals real absolute value. -/
theorem int_abs_cast (j : ℤ) : ((|j| : ℤ) : ℝ) = |((j : ℤ) : ℝ)| := by
  exact_mod_cast Int.cast_abs

/-! ## Integer Division Bounds -/

/-- Integer division by 2 is at most real division by 2.
    Here q = (n : ℤ) / 2 is an integer, and we show (q : ℝ) ≤ (n : ℝ) / 2. -/
theorem int_div2_le_real_div2 (n : ℕ) : ((((n : ℤ) / 2) : ℤ) : ℝ) ≤ (n : ℝ) / 2 := by
  have h : ((n : ℤ) / 2) * 2 ≤ (n : ℤ) := Int.ediv_mul_le (n : ℤ) (by norm_num : (2 : ℤ) ≠ 0)
  have h' : ((((n : ℤ) / 2) : ℤ) : ℝ) * 2 ≤ ((n : ℤ) : ℝ) := by exact_mod_cast h
  have hcast : ((n : ℤ) : ℝ) = (n : ℝ) := natCast_intCast_eq n
  rw [hcast] at h'
  linarith

/-- Integer division by 2 is at least real division by 2 minus 1/2.
    Here q = (n : ℤ) / 2 is an integer, and we show (q : ℝ) ≥ (n : ℝ) / 2 - 1/2. -/
theorem int_div2_ge_real_div2_sub_half (n : ℕ) : ((((n : ℤ) / 2) : ℤ) : ℝ) ≥ (n : ℝ) / 2 - 1/2 := by
  have hdiv_bound : 2 * ((n : ℤ) / 2) ≥ (n : ℤ) - 1 := by omega
  let q : ℤ := (n : ℤ) / 2
  have hcast_n : ((n : ℤ) : ℝ) = (n : ℝ) := natCast_intCast_eq n
  -- Cast hdiv_bound to ℝ: we have (n : ℤ) - 1 ≤ 2 * q as integers
  -- So ((n : ℤ) - 1 : ℝ) ≤ (2 * q : ℝ) = 2 * (q : ℝ)
  have h1 : (2 : ℝ) * (q : ℝ) ≥ (n : ℝ) - 1 := by
    have hle : ((n : ℤ) - 1 : ℤ) ≤ 2 * q := hdiv_bound
    -- Cast to ℝ
    have h_cast : (((n : ℤ) - 1 : ℤ) : ℝ) ≤ ((2 * q : ℤ) : ℝ) := Int.cast_le.mpr hle
    -- Simplify LHS: (((n : ℤ) - 1 : ℤ) : ℝ) = ((n : ℤ) : ℝ) - 1 = (n : ℝ) - 1
    -- Simplify RHS: ((2 * q : ℤ) : ℝ) = 2 * (q : ℝ)
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_one, hcast_n] at h_cast
    exact h_cast
  linarith

/-- An integer whose real cast is > 1/2 and ≥ 0 must be ≥ 1. -/
theorem int_ge_one_of_real_gt_half_nonneg {m : ℤ} (hpos : 0 ≤ m) (hgt : (m : ℝ) > 1/2) : 1 ≤ m := by
  by_contra h_neg
  push_neg at h_neg
  have h1 : m ≤ 0 := by omega
  have h2 : (m : ℝ) ≤ 0 := by exact_mod_cast h1
  linarith

/-- An integer strictly less than another as reals implies ≤ as integers. -/
theorem int_le_of_real_lt {a b : ℤ} (h : (a : ℝ) < (b : ℝ)) : a ≤ b := by
  by_contra hgt
  push_neg at hgt
  have h' : (b : ℝ) < (a : ℝ) := by exact_mod_cast hgt
  linarith

/-! ## Sum Bounds with Division -/

/-- If n ≥ 9 and j ≥ -(n/2), then (n : ℤ) / 2 + j ≥ 0. -/
theorem int_div2_add_ge_zero (n : ℕ) (j : ℤ) (hn : 9 ≤ n) (hj_lower : -((n : ℤ)/2) ≤ j) :
    0 ≤ (n : ℤ) / 2 + j := by
  have hnat_div_le : (n : ℤ) / 2 ≥ (n/2 : ℕ) := by omega
  have hn' : (n/2 : ℕ) ≥ 4 := by omega
  omega

/-- Real bound (n:ℝ)/2 + j > 1 combined with integrality gives (n:ℤ)/2 + j ≥ 1.
    This is the key lemma for index lower bounds. -/
theorem int_div2_add_ge_one_of_real_gt_one (n : ℕ) (j : ℤ) (hn : 9 ≤ n)
    (hj_lower : -((n : ℤ)/2) ≤ j) (h_real : (n : ℝ) / 2 + (j : ℝ) > 1) :
    1 ≤ (n : ℤ) / 2 + j := by
  have hge0 : 0 ≤ (n : ℤ) / 2 + j := int_div2_add_ge_zero n j hn hj_lower
  have hintdiv_real := int_div2_ge_real_div2_sub_half n
  let q : ℤ := (n : ℤ) / 2
  -- hintdiv_real: (q : ℝ) ≥ (n : ℝ) / 2 - 1/2
  have hsum_gt : (q : ℝ) + (j : ℝ) > 1/2 := by
    have h1 : (q : ℝ) ≥ (n : ℝ) / 2 - 1/2 := hintdiv_real
    have h2 : (q : ℝ) + (j : ℝ) ≥ (n : ℝ) / 2 - 1/2 + (j : ℝ) := by linarith
    have h3 : (n : ℝ) / 2 - 1/2 + (j : ℝ) = (n : ℝ) / 2 + (j : ℝ) - 1/2 := by ring
    have h4 : (n : ℝ) / 2 + (j : ℝ) > 1 := h_real
    linarith
  have hsum_real : (((q + j) : ℤ) : ℝ) > 1/2 := by
    have heq : (((q + j) : ℤ) : ℝ) = (q : ℝ) + (j : ℝ) := by norm_cast
    rw [heq]
    exact hsum_gt
  exact int_ge_one_of_real_gt_half_nonneg hge0 hsum_real

/-- Real bound (n:ℝ)/2 + j < n - 1 combined with integrality gives (n:ℤ)/2 + j ≤ n - 1.
    This is the key lemma for index upper bounds. -/
theorem int_div2_add_le_n_sub_one_of_real_lt (n : ℕ) (j : ℤ)
    (h_real : (n : ℝ) / 2 + (j : ℝ) < (n : ℝ) - 1) :
    (n : ℤ) / 2 + j ≤ (n : ℤ) - 1 := by
  let q : ℤ := (n : ℤ) / 2
  have hdiv_le := int_div2_le_real_div2 n
  have hcast : ((n : ℤ) : ℝ) = (n : ℝ) := natCast_intCast_eq n
  -- hdiv_le: (q : ℝ) ≤ (n : ℝ) / 2
  have hsum_lt : (q : ℝ) + (j : ℝ) < (n : ℝ) - 1 := by linarith
  -- q + j < (n : ℤ) - 1 as reals, so q + j ≤ (n : ℤ) - 1 as integers
  have hint : q + j < (n : ℤ) - 1 ∨ q + j = (n : ℤ) - 1 ∨ q + j > (n : ℤ) - 1 := lt_trichotomy _ _
  rcases hint with hlt | heq | hgt
  · exact le_of_lt hlt
  · exact le_of_eq heq
  · -- Contradiction: we have q + j > (n : ℤ) - 1 as integers, but < as reals
    exfalso
    have h' : (((n : ℤ) - 1) : ℝ) < ((q + j) : ℝ) := by exact_mod_cast hgt
    -- Simplify the casts
    simp only [hcast] at h'
    linarith

end SPDE.Nonstandard.Arithmetic
