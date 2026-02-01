/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.Anderson.RandomWalkMoments
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.LoebMeasure.BinomialProbability
import ModularPhysics.RigorousQFT.SPDE.Nonstandard.Foundation.Arithmetic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Local Central Limit Theorem

This file provides infrastructure for the local central limit theorem, which shows that
the binomial distribution converges to the Gaussian distribution.

## Main Results

* `stirling_lower_bound` - Lower bound: n! ≥ √(2πn) (n/e)^n
* `stirling_upper_bound` - Upper bound: n! ≤ √(2πn) (n/e)^n e^(1/(12n))
* `binomial_gaussian_ratio` - |C(n,k)/2^n - φ((k-n/2)/√(n/4))/√(n/4)| = O(1/n)
* `binomial_near_gaussian` - The binomial prob is close to the Gaussian density

## Overview

For a symmetric random walk S_n with n steps:
- P(S_n = 2k - n) = C(n,k) / 2^n for k = 0, ..., n
- The centered, scaled walk has mean 0 and variance n/4
- By the local CLT: C(n,k)/2^n ≈ (1/√(πn/2)) exp(-(2k-n)²/(2n))

The local CLT is stronger than the standard CLT because it gives pointwise convergence
of the probability mass function, not just convergence of distribution functions.

## References

* Feller, W. "An Introduction to Probability Theory and Its Applications" Vol. 1, Ch. VII
* Petrov, V. V. "Sums of Independent Random Variables"
-/

open Real Finset

namespace SPDE.Nonstandard

/-! ## Stirling's Approximation Infrastructure

Stirling's formula: n! ≈ √(2πn) (n/e)^n

We state the bounds needed for the local CLT without proving them in full detail.
The full proofs would require Wallis' product formula or the Gamma function integral.
-/

/-- Stirling's approximation: n! ≈ √(2πn) (n/e)^n.
    We define the Stirling approximation function for convenience.
    Note: Matches Mathlib's formulation in `Stirling.le_factorial_stirling`. -/
noncomputable def stirlingApprox (n : ℕ) : ℝ :=
  if n = 0 then 1
  else Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n

/-- Stirling lower bound: n! ≥ √(2πn) (n/e)^n for n ≥ 1.
    This follows directly from Mathlib's `Stirling.le_factorial_stirling`. -/
theorem stirling_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    stirlingApprox n ≤ (n.factorial : ℝ) := by
  unfold stirlingApprox
  simp only [Nat.one_le_iff_ne_zero.mp hn, ↓reduceIte]
  exact Stirling.le_factorial_stirling n

/-- Mathlib's Stirling sequence: stirlingSeq n = n! / (√(2n) (n/e)^n).
    The limit is √π. We relate this to our definition. -/
theorem stirlingSeq_eq_factorial_div (n : ℕ) (_hn : n ≠ 0) :
    Stirling.stirlingSeq n = (n.factorial : ℝ) / (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n) := rfl

/-- Our stirlingApprox is √π times the denominator of stirlingSeq. -/
theorem stirlingApprox_eq (n : ℕ) (hn : n ≠ 0) :
    stirlingApprox n = Real.sqrt Real.pi * (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n) := by
  simp only [stirlingApprox, hn, ↓reduceIte]
  -- Goal: √(2πn) * (n/e)^n = √π * (√(2n) * (n/e)^n)
  -- √(2πn) = √(2π) * √n = √π * √2 * √n = √π * √(2n)
  have hsqrt_eq : Real.sqrt (2 * Real.pi * n) = Real.sqrt Real.pi * Real.sqrt (2 * n) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [hsqrt_eq, mul_assoc]

/-- Stirling ratio: n! / stirlingApprox(n) → 1 as n → ∞.
    Uses Mathlib's `tendsto_stirlingSeq_sqrt_pi`. -/
theorem stirling_ratio_tendsto_one :
    Filter.Tendsto (fun n => (n.factorial : ℝ) / stirlingApprox n)
      Filter.atTop (nhds 1) := by
  -- stirlingSeq n → √π means n! / (√(2n)(n/e)^n) → √π
  -- Our stirlingApprox n = √(2πn)(n/e)^n = √π · √(2n) · (n/e)^n
  -- So n!/stirlingApprox n = (n! / (√(2n)(n/e)^n)) / √π = stirlingSeq n / √π → 1
  have hpi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hpi_ne : Real.sqrt Real.pi ≠ 0 := ne_of_gt hpi_pos
  have htend := Stirling.tendsto_stirlingSeq_sqrt_pi
  have htend' : Filter.Tendsto (fun n => Stirling.stirlingSeq n / Real.sqrt Real.pi)
      Filter.atTop (nhds 1) := by
    convert htend.div_const (Real.sqrt Real.pi) using 1
    rw [div_self hpi_ne]
  apply Filter.Tendsto.congr' _ htend'
  filter_upwards [Filter.eventually_ne_atTop 0] with n hn
  simp only [Stirling.stirlingSeq, stirlingApprox, hn, ↓reduceIte]
  -- Need to show: n! / (√(2πn) * (n/e)^n) = (n! / (√(2n) * (n/e)^n)) / √π
  -- LHS denominator: √(2πn) * (n/e)^n = √(2π) * √n * (n/e)^n = √π * √2 * √n * (n/e)^n
  -- RHS denominator (after div by √π): √π * √(2n) * (n/e)^n = √π * √2 * √n * (n/e)^n
  have hsqrt_eq : Real.sqrt (2 * Real.pi * n) = Real.sqrt Real.pi * Real.sqrt (2 * n) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    -- Goal: √2 * √π * √n = √π * (√2 * √n)
    -- Rewrite LHS: √2 * √π = √π * √2
    rw [mul_comm (Real.sqrt 2) (Real.sqrt Real.pi)]
    -- Now: √π * √2 * √n = √π * (√2 * √n)
    rw [mul_assoc]
  rw [hsqrt_eq]
  have hdenom_pos : 0 < Real.sqrt (2 * n) * (n / Real.exp 1) ^ n := by positivity
  have hdenom_ne : Real.sqrt (2 * n) * (n / Real.exp 1) ^ n ≠ 0 := ne_of_gt hdenom_pos
  field_simp

/-- Stirling upper bound in terms of the ratio.
    For any ε > 0, for sufficiently large n: n! ≤ (1 + ε) · √(2πn) (n/e)^n.
    This follows from the ratio converging to 1. -/
theorem stirling_upper_bound_eventual (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, (n.factorial : ℝ) ≤ (1 + ε) * stirlingApprox n := by
  have htendsto := stirling_ratio_tendsto_one
  rw [Metric.tendsto_atTop] at htendsto
  obtain ⟨N₀, hN₀⟩ := htendsto ε hε
  use max 1 N₀
  intro n hn
  have hn1 : 1 ≤ n := le_of_max_le_left hn
  have hnN₀ : N₀ ≤ n := le_of_max_le_right hn
  specialize hN₀ n hnN₀
  rw [Real.dist_eq, abs_lt] at hN₀
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn1
  have hstirling_pos : 0 < stirlingApprox n := by
    simp only [stirlingApprox, hn0, ↓reduceIte]
    positivity
  have hratio : (n.factorial : ℝ) / stirlingApprox n < 1 + ε := by linarith
  calc (n.factorial : ℝ)
      = (n.factorial : ℝ) / stirlingApprox n * stirlingApprox n := by
        field_simp
    _ ≤ (1 + ε) * stirlingApprox n := by
        apply mul_le_mul_of_nonneg_right (le_of_lt hratio) (le_of_lt hstirling_pos)

/-! ## Binomial Coefficient Asymptotics

For the local CLT, we need to understand C(n, n/2 + k) for |k| = O(√n).
-/

/-- Binomial coefficient in terms of factorials (as real numbers). -/
theorem choose_eq_factorial_div (n k : ℕ) (hk : k ≤ n) :
    (Nat.choose n k : ℝ) = n.factorial / (k.factorial * (n - k).factorial) := by
  have hkf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hnkf : ((n - k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))
  have h := Nat.choose_mul_factorial_mul_factorial hk
  calc (Nat.choose n k : ℝ)
      = (Nat.choose n k * k.factorial * (n - k).factorial : ℕ) / (k.factorial * (n - k).factorial) := by
        push_cast
        field_simp
    _ = (n.factorial : ℕ) / (k.factorial * (n - k).factorial) := by
        congr 1
        exact_mod_cast h
    _ = n.factorial / (k.factorial * (n - k).factorial) := by norm_cast

/-- The Stirling sequence for (2n) expressed in terms of stirlingSeq.
    Used to relate (2n)! to stirlingSeq(2n). -/
theorem factorial_eq_stirlingSeq (n : ℕ) (hn : n ≠ 0) :
    (n.factorial : ℝ) = Stirling.stirlingSeq n * Real.sqrt (2 * n) * (n / Real.exp 1) ^ n := by
  simp only [Stirling.stirlingSeq]
  field_simp

/-- The Stirling sequence is bounded above by stirlingSeq(1) for n ≥ 1. -/
theorem stirlingSeq_le_one (n : ℕ) (hn : 1 ≤ n) : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
  match n with
  | 0 => omega
  | n + 1 =>
    -- stirlingSeq(n+1) ≤ stirlingSeq(1) = stirlingSeq(0+1) by antitone property
    exact Stirling.stirlingSeq'_antitone (Nat.zero_le n)

/-- Key inequality: e²/(2π) ≤ 2, equivalently e/(π√2) ≤ √(2/π). -/
theorem e_sq_le_four_pi : Real.exp 1 ^ 2 / (2 * Real.pi) ≤ 2 := by
  have hpi : Real.pi > 3 := pi_gt_three
  have he_upper : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  -- e² < 2.72² = 7.3984
  have hsmall : Real.exp 1 < 2.72 := by linarith
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have h1 : Real.exp 1 ^ 2 < 7.4 := by
    calc Real.exp 1 ^ 2
        < (2.72 : ℝ) ^ 2 := by nlinarith [sq_nonneg (Real.exp 1 - 2.72)]
      _ < 7.4 := by norm_num
  -- 2π > 6
  have h2 : 2 * Real.pi > 6 := by linarith
  -- e²/(2π) < 7.4/6 ≤ 2
  have hpi_pos : 0 < 2 * Real.pi := by linarith
  -- Show e²/(2π) ≤ 2 by showing e² ≤ 4π
  rw [div_le_iff₀ hpi_pos]
  -- Need: e² ≤ 4π, equivalently e² < 4π
  -- We have: e² < 7.4 and 4π > 12.56 > 7.4
  have h4pi : 4 * Real.pi > 12 := by linarith
  linarith

/-- The central binomial coefficient C(2n, n) satisfies C(2n, n) ≤ 4^n / √(πn/2) for n ≥ 1.
    This is a bound that's weaker than the asymptotic C(2n, n) ~ 4^n / √(πn) but holds for all n ≥ 1.

    **Proof strategy**: Using Stirling's approximation:
    - (2n)! ≤ stirlingSeq(1) · √(4n) · (2n/e)^{2n} (antitone property)
    - (n!)² ≥ π · 2n · (n/e)^{2n} (lower bound from stirlingSeq ≥ √π)

    This gives C(2n,n) ≤ (e/√2) · 4^n / (π√n) ≤ 4^n / √(πn/2) since e²/(2π) ≤ 2. -/
theorem central_binomial_asymptotic (n : ℕ) (hn : 1 ≤ n) :
    (Nat.choose (2 * n) n : ℝ) ≤ 4^n / Real.sqrt (Real.pi * n / 2) := by
  -- Handle n = 1 separately for clarity (the general proof works, but this is cleaner)
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)

  -- Express C(2n, n) using factorials
  have hchoose : (Nat.choose (2 * n) n : ℝ) = (2 * n).factorial / (n.factorial * n.factorial) := by
    have h_le : n ≤ 2 * n := Nat.le_mul_of_pos_left n (by norm_num)
    rw [choose_eq_factorial_div (2 * n) n h_le]
    have h_sub : 2 * n - n = n := by omega
    simp only [h_sub]

  -- Stirling lower bound: n! ≥ √(2πn) · (n/e)^n, so (n!)² ≥ 2πn · (n/e)^{2n}
  have hfact_lower : Real.pi * (2 * n) * (n / Real.exp 1) ^ (2 * n) ≤ (n.factorial : ℝ) ^ 2 := by
    have hstirling := stirling_lower_bound n hn
    unfold stirlingApprox at hstirling
    simp only [hn0, ↓reduceIte] at hstirling
    -- stirlingApprox n = √(2πn) · (n/e)^n ≤ n!
    -- So (√(2πn) · (n/e)^n)² ≤ (n!)²
    -- i.e., 2πn · (n/e)^{2n} ≤ (n!)²
    have hstirling_nonneg : 0 ≤ Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n := by positivity
    have h_sq : (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) ^ 2 ≤
        (n.factorial : ℝ) ^ 2 := pow_le_pow_left₀ hstirling_nonneg hstirling 2
    have hsqrt_sq : (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) ^ 2 =
        2 * Real.pi * n * (n / Real.exp 1) ^ (2 * n) := by
      rw [mul_pow, sq_sqrt (by positivity), ← pow_mul]
      ring
    rw [hsqrt_sq] at h_sq
    calc Real.pi * (2 * n) * (n / Real.exp 1) ^ (2 * n)
        = 2 * Real.pi * n * (n / Real.exp 1) ^ (2 * n) := by ring
      _ ≤ (n.factorial : ℝ) ^ 2 := h_sq

  -- Stirling upper bound using stirlingSeq: (2n)! ≤ stirlingSeq(1) · √(4n) · (2n/e)^{2n}
  have hfact_upper : ((2 * n).factorial : ℝ) ≤
      Stirling.stirlingSeq 1 * Real.sqrt (4 * n) * (2 * n / Real.exp 1) ^ (2 * n) := by
    have h2n_ne : 2 * n ≠ 0 := Nat.mul_ne_zero (by norm_num) hn0
    have h2n_ge : 1 ≤ 2 * n := by omega
    -- (2n)! = stirlingSeq(2n) · √(2·(2n)) · (2n/e)^{2n}
    have heq := factorial_eq_stirlingSeq (2 * n) h2n_ne
    -- Note: √(2 * (2 * n)) = √(4 * n)
    have hsqrt_eq : Real.sqrt (2 * ↑(2 * n)) = Real.sqrt (4 * n) := by
      norm_cast; ring_nf
    rw [heq]
    -- stirlingSeq(2n) ≤ stirlingSeq(1) by antitone property
    have hle := stirlingSeq_le_one (2 * n) h2n_ge
    have hsqrt_pos : 0 < Real.sqrt (2 * ↑(2 * n)) := Real.sqrt_pos.mpr (by positivity)
    have hpow_pos : 0 < (↑(2 * n) / Real.exp 1) ^ (2 * n) := by positivity
    calc Stirling.stirlingSeq (2 * n) * Real.sqrt (2 * ↑(2 * n)) * (↑(2 * n) / Real.exp 1) ^ (2 * n)
        ≤ Stirling.stirlingSeq 1 * Real.sqrt (2 * ↑(2 * n)) * (↑(2 * n) / Real.exp 1) ^ (2 * n) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hpow_pos)
          apply mul_le_mul_of_nonneg_right hle (le_of_lt hsqrt_pos)
      _ = Stirling.stirlingSeq 1 * Real.sqrt (4 * n) * (2 * n / Real.exp 1) ^ (2 * n) := by
          rw [hsqrt_eq]; norm_cast

  -- stirlingSeq(1) = e/√2
  have hseq1 : Stirling.stirlingSeq 1 = Real.exp 1 / Real.sqrt 2 := Stirling.stirlingSeq_one

  -- Combine the bounds
  have hfact_sq_pos : 0 < (n.factorial : ℝ) ^ 2 := by positivity
  have hfact_prod_pos : 0 < (n.factorial : ℝ) * n.factorial := by positivity

  -- C(2n,n) = (2n)! / (n!)² ≤ [stirlingSeq(1) · √(4n) · (2n/e)^{2n}] / [π · 2n · (n/e)^{2n}]
  have hratio_bound : (Nat.choose (2 * n) n : ℝ) ≤
      Stirling.stirlingSeq 1 * Real.sqrt (4 * n) * (2 * n / Real.exp 1) ^ (2 * n) /
      (Real.pi * (2 * n) * (n / Real.exp 1) ^ (2 * n)) := by
    rw [hchoose]
    have h1 : (n.factorial : ℝ) * n.factorial = (n.factorial : ℝ) ^ 2 := by ring
    rw [h1]
    -- Use div_le_div₀: a/b ≤ c/d when 0 ≤ c, a ≤ c, 0 < d, d ≤ b
    have hstirling_pos : 0 < Stirling.stirlingSeq 1 := Stirling.stirlingSeq'_pos 0
    have hnum_nonneg : 0 ≤ Stirling.stirlingSeq 1 * Real.sqrt (4 * n) * (2 * n / Real.exp 1) ^ (2 * n) := by
      apply mul_nonneg
      apply mul_nonneg (le_of_lt hstirling_pos) (Real.sqrt_nonneg _)
      apply pow_nonneg; apply div_nonneg; linarith; exact le_of_lt (Real.exp_pos 1)
    have hdenom_pos : 0 < Real.pi * (2 * n) * (n / Real.exp 1) ^ (2 * n) := by
      apply mul_pos
      apply mul_pos Real.pi_pos; linarith
      apply pow_pos; apply div_pos hn_pos (Real.exp_pos 1)
    exact div_le_div₀ hnum_nonneg hfact_upper hdenom_pos hfact_lower

  -- Simplify the bound
  -- [stirlingSeq(1) · √(4n) · (2n/e)^{2n}] / [π · 2n · (n/e)^{2n}]
  -- = stirlingSeq(1) · √(4n) / (π · 2n) · [(2n)^{2n} / n^{2n}]
  -- = (e/√2) · 2√n / (2πn) · 4^n
  -- = (e/√2) · 4^n / (π√n)
  have hsimp : Stirling.stirlingSeq 1 * Real.sqrt (4 * n) * (2 * n / Real.exp 1) ^ (2 * n) /
      (Real.pi * (2 * n) * (n / Real.exp 1) ^ (2 * n)) =
      Stirling.stirlingSeq 1 / Real.pi * (4 : ℝ) ^ n / Real.sqrt n := by
    have hexp_ne : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    -- (2n/e)^{2n} / (n/e)^{2n} = (2n/n)^{2n} = 2^{2n} = 4^n
    have hpow_ratio : (2 * n / Real.exp 1) ^ (2 * n) / (n / Real.exp 1) ^ (2 * n) = (4 : ℝ) ^ n := by
      have h1 : (2 * (n : ℝ)) ^ (2 * n) = (2 : ℝ) ^ (2 * n) * (n : ℝ) ^ (2 * n) := by
        rw [mul_pow]
      have h2 : (4 : ℝ) ^ n = 2 ^ (2 * n) := by
        have : (4 : ℝ) = 2 ^ 2 := by norm_num
        rw [this, ← pow_mul]
      rw [div_pow, div_pow, h1, h2]
      have hexp_pow_ne : Real.exp 1 ^ (2 * n) ≠ 0 := pow_ne_zero _ hexp_ne
      have hn_pow_ne : (n : ℝ) ^ (2 * n) ≠ 0 := pow_ne_zero _ hn_ne
      field_simp
    -- √(4n) / (2n) = 2√n / (2n) = 1/√n
    have hsqrt4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    have hsqrt_ratio : Real.sqrt (4 * n) / (2 * n) = 1 / Real.sqrt n := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsqrt4]
      have hsqrt_n_ne : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn_pos)
      field_simp
      rw [Real.sq_sqrt (le_of_lt hn_pos)]
    calc Stirling.stirlingSeq 1 * Real.sqrt (4 * n) * (2 * n / Real.exp 1) ^ (2 * n) /
          (Real.pi * (2 * n) * (n / Real.exp 1) ^ (2 * n))
        = Stirling.stirlingSeq 1 * (Real.sqrt (4 * n) / (2 * n)) *
          ((2 * n / Real.exp 1) ^ (2 * n) / (n / Real.exp 1) ^ (2 * n)) / Real.pi := by
          have h2n_ne : (2 * n : ℝ) ≠ 0 := by linarith
          have hdenom_ne : Real.pi * (2 * n) * (n / Real.exp 1) ^ (2 * n) ≠ 0 := by
            apply mul_ne_zero; apply mul_ne_zero hpi_ne h2n_ne
            apply pow_ne_zero; exact div_ne_zero hn_ne hexp_ne
          field_simp
      _ = Stirling.stirlingSeq 1 * (1 / Real.sqrt n) * (4 : ℝ) ^ n / Real.pi := by
          rw [hsqrt_ratio, hpow_ratio]
      _ = Stirling.stirlingSeq 1 / Real.pi * (4 : ℝ) ^ n / Real.sqrt n := by ring

  rw [hsimp] at hratio_bound

  -- Now show: stirlingSeq(1) / π · 4^n / √n ≤ 4^n / √(πn/2)
  -- i.e., stirlingSeq(1) / π ≤ √n / √(πn/2) = √(2/π)
  -- i.e., (e/√2) / π ≤ √(2/π)
  -- i.e., e / (π√2) ≤ √(2/π)
  -- i.e., e² / (2π²) ≤ 2/π
  -- i.e., e² ≤ 4π ✓
  have hcoeff : Stirling.stirlingSeq 1 / Real.pi ≤ Real.sqrt (2 / Real.pi) := by
    rw [hseq1]
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hsqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2_pos
    have hpi_ne : Real.pi ≠ 0 := ne_of_gt hpi_pos
    -- Need: e/√2 / π ≤ √(2/π)
    -- Equivalently: e/√2 ≤ π · √(2/π) = √(2π)
    rw [div_le_iff₀ hpi_pos]
    -- Goal: e/√2 ≤ √(2/π) * π
    -- √(2/π) * π = π * √2 / √π = √π * √2 = √(2π)
    have hrhs : Real.sqrt (2 / Real.pi) * Real.pi = Real.sqrt (2 * Real.pi) := by
      rw [Real.sqrt_div (by linarith : (0 : ℝ) ≤ 2)]
      have hpi_nonneg : 0 ≤ Real.pi := le_of_lt hpi_pos
      have hsqrt_pi_sq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt hpi_nonneg
      field_simp
      rw [mul_comm, Real.sqrt_mul hpi_nonneg, ← mul_assoc, hsqrt_pi_sq]
    rw [hrhs]
    -- Now need: e/√2 ≤ √(2π)
    -- Squaring: e²/2 ≤ 2π, i.e., e² ≤ 4π
    rw [div_le_iff₀ hsqrt2_pos]
    -- Goal: e ≤ √(2π) * √2 = √(4π) = 2√π
    have hrhs2 : Real.sqrt (2 * Real.pi) * Real.sqrt 2 = Real.sqrt (4 * Real.pi) := by
      rw [← Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 2 * Real.pi)]
      congr 1; ring
    rw [hrhs2]
    -- Goal: e ≤ √(4π)
    -- We have: e < 3 and 4π > 12, so √(4π) > √12 > 3 > e
    have h4pi : 4 * Real.pi > 12 := by linarith [pi_gt_three]
    have hsqrt9 : Real.sqrt 9 = 3 := by
      rw [show (9 : ℝ) = 3^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
    have hsqrt_12 : Real.sqrt 12 > 3 := by
      rw [← hsqrt9]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have he : Real.exp 1 < 3 := exp_one_lt_three
    have hchain : Real.exp 1 < Real.sqrt (4 * Real.pi) :=
      calc Real.exp 1 < 3 := he
        _ < Real.sqrt 12 := hsqrt_12
        _ < Real.sqrt (4 * Real.pi) := Real.sqrt_lt_sqrt (by norm_num) h4pi
    exact le_of_lt hchain

  -- Final assembly: stirlingSeq(1)/π · 4^n/√n ≤ √(2/π) · 4^n/√n = 4^n/√(πn/2)
  have hfinal : Stirling.stirlingSeq 1 / Real.pi * (4 : ℝ) ^ n / Real.sqrt n ≤
      (4 : ℝ) ^ n / Real.sqrt (Real.pi * n / 2) := by
    have h4n_pos : (0 : ℝ) < 4 ^ n := by positivity
    have hsqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
    -- √(2/π) · 4^n / √n = 4^n / (√n · √(π/2)) = 4^n / √(πn/2)
    have hsqrt_eq : Real.sqrt (2 / Real.pi) * (4 : ℝ) ^ n / Real.sqrt n =
        (4 : ℝ) ^ n / Real.sqrt (Real.pi * n / 2) := by
      have h1 : Real.sqrt (Real.pi * n / 2) = Real.sqrt (Real.pi / 2) * Real.sqrt n := by
        have heq : Real.pi * n / 2 = (Real.pi / 2) * n := by ring
        rw [heq, Real.sqrt_mul (by positivity : 0 ≤ Real.pi / 2)]
      rw [h1]
      have hpi2_pos : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
      have hsqrt_pi2_ne : Real.sqrt (Real.pi / 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpi2_pos)
      have hsqrt_n_ne : Real.sqrt n ≠ 0 := ne_of_gt hsqrt_n_pos
      -- √(2/π) = 1 / √(π/2) since √(2/π) · √(π/2) = √((2/π)·(π/2)) = √1 = 1
      have hsqrt_inv : Real.sqrt (2 / Real.pi) * Real.sqrt (Real.pi / 2) = 1 := by
        rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 / Real.pi)]
        have h : (2 / Real.pi) * (Real.pi / 2) = 1 := by field_simp
        rw [h, Real.sqrt_one]
      have hsqrt_inv' : Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi) = 1 := by
        rw [mul_comm]; exact hsqrt_inv
      -- Goal: √(2/π) * 4^n / √n = 4^n / (√(π/2) * √n)
      -- Since √(2/π) * √(π/2) = 1, we have √(2/π) = 1/√(π/2)
      have hsqrt_eq2 : Real.sqrt (2 / Real.pi) = 1 / Real.sqrt (Real.pi / 2) := by
        rw [eq_div_iff hsqrt_pi2_ne]
        exact hsqrt_inv
      rw [hsqrt_eq2, one_div, inv_mul_eq_div, div_div, mul_comm (Real.sqrt (Real.pi / 2)) (Real.sqrt n)]
    rw [← hsqrt_eq]
    apply div_le_div_of_nonneg_right _ (le_of_lt hsqrt_n_pos)
    apply mul_le_mul_of_nonneg_right hcoeff (le_of_lt h4n_pos)

  exact le_trans hratio_bound hfinal

/-- The binomial coefficient C(n, n/2 + k) for n even.
    When k = 0, this is the central binomial coefficient.
    Returns 0 if (n/2 : ℤ) + k is outside [0, n]. -/
noncomputable def centralBinomialShifted (n : ℕ) (k : ℤ) : ℕ :=
  let idx : ℤ := (n / 2 : ℤ) + k
  if 0 ≤ idx ∧ idx ≤ n then
    Nat.choose n idx.toNat
  else 0

/-- The Gaussian density at x with variance σ²:
    φ_σ(x) = (1/(σ√(2π))) exp(-x²/(2σ²)) -/
noncomputable def gaussianDensity (sigma : ℝ) (x : ℝ) : ℝ :=
  if sigma > 0 then
    (1 / (sigma * Real.sqrt (2 * Real.pi))) * Real.exp (-x^2 / (2 * sigma^2))
  else 0

/-- For a symmetric random walk with n steps, the standard deviation is √(n)/2. -/
noncomputable def walkStdDev (n : ℕ) : ℝ := Real.sqrt n / 2

/-! ## Local Central Limit Theorem

The main theorem: the binomial distribution converges locally to the Gaussian.
-/

/-- The Stirling ratio bounds: for n ≥ 1, √π ≤ stirlingSeq(n) ≤ e/√2.
    This gives: √π · √(2n) · (n/e)^n ≤ n! ≤ (e/√2) · √(2n) · (n/e)^n -/
theorem stirlingSeq_bounds (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt Real.pi ≤ Stirling.stirlingSeq n ∧ Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  constructor
  · exact Stirling.sqrt_pi_le_stirlingSeq hn0
  · exact stirlingSeq_le_one n hn

/-- For k in [1, n-1], we have the factorial ratio bound:
    n! / (k! (n-k)!) lies between explicit Stirling bounds.
    This is the key lemma for the local CLT. -/
theorem factorial_ratio_stirling_bounds (n k : ℕ) (hk_pos : 1 ≤ k) (hk_lt : k < n) :
    let nk := n - k
    let stirlingN := Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n
    let stirlingK := Real.sqrt (2 * Real.pi * k) * (k / Real.exp 1) ^ k
    let stirlingNK := Real.sqrt (2 * Real.pi * nk) * (nk / Real.exp 1) ^ nk
    -- Lower bound: n!/k!/(n-k)! ≥ (√π/stirlingSeq(1)²) · stirlingN / (stirlingK · stirlingNK)
    -- Upper bound: n!/k!/(n-k)! ≤ (stirlingSeq(1)/π) · stirlingN / (stirlingK · stirlingNK)
    stirlingN / (stirlingK * stirlingNK) / (Stirling.stirlingSeq 1)^2 * Real.pi ≤
      (n.factorial : ℝ) / (k.factorial * nk.factorial) ∧
    (n.factorial : ℝ) / (k.factorial * nk.factorial) ≤
      stirlingN / (stirlingK * stirlingNK) * (Stirling.stirlingSeq 1)^2 / Real.pi := by
  have hn : 1 ≤ n := Nat.one_le_of_lt hk_lt
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk_pos
  have hnk_pos : 1 ≤ n - k := by omega
  have hnk0 : n - k ≠ 0 := Nat.one_le_iff_ne_zero.mp hnk_pos
  -- Use factorial_eq_stirlingSeq for each factorial
  have hn_fact := factorial_eq_stirlingSeq n hn0
  have hk_fact := factorial_eq_stirlingSeq k hk0
  have hnk_fact := factorial_eq_stirlingSeq (n - k) hnk0
  -- The bounds follow from √π ≤ stirlingSeq ≤ stirlingSeq(1)
  have hn_bounds := stirlingSeq_bounds n hn
  have hk_bounds := stirlingSeq_bounds k hk_pos
  have hnk_bounds := stirlingSeq_bounds (n - k) hnk_pos
  -- Detailed calculation using the bounds
  have hk_pos' : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
  have hnk_pos' : (0 : ℝ) < (n - k : ℕ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hnk0)
  have hn_pos' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hsqrt_k : 0 < Real.sqrt (2 * k) := Real.sqrt_pos.mpr (by linarith)
  have hsqrt_nk : 0 < Real.sqrt (2 * (n - k : ℕ)) := Real.sqrt_pos.mpr (by positivity)
  have hsqrt_n : 0 < Real.sqrt (2 * n) := Real.sqrt_pos.mpr (by linarith)
  have hpow_k : 0 < (k / Real.exp 1) ^ k := by positivity
  have hpow_nk : 0 < ((n - k : ℕ) / Real.exp 1) ^ (n - k) := by positivity
  have hpow_n : 0 < (n / Real.exp 1) ^ n := by positivity
  have hseq_k_pos : 0 < Stirling.stirlingSeq k := lt_of_lt_of_le (Real.sqrt_pos.mpr Real.pi_pos) hk_bounds.1
  have hseq_nk_pos : 0 < Stirling.stirlingSeq (n - k) := lt_of_lt_of_le (Real.sqrt_pos.mpr Real.pi_pos) hnk_bounds.1
  have hseq_n_pos : 0 < Stirling.stirlingSeq n := lt_of_lt_of_le (Real.sqrt_pos.mpr Real.pi_pos) hn_bounds.1
  have hseq1_pos : 0 < Stirling.stirlingSeq 1 := lt_of_lt_of_le (Real.sqrt_pos.mpr Real.pi_pos) (stirlingSeq_bounds 1 le_rfl).1
  -- The proof involves substituting the factorial expressions and using the bounds
  -- n! = stirlingSeq(n) · √(2n) · (n/e)^n, etc.
  -- The ratio n!/(k!(n-k)!) = [stirlingSeq(n)/(stirlingSeq(k)·stirlingSeq(n-k))] ·
  --   [√(2n)/(√(2k)·√(2(n-k)))] · [(n/e)^n/((k/e)^k·((n-k)/e)^{n-k})]
  --
  -- Using stirlingApprox m = √(2πm)·(m/e)^m = √π · √(2m) · (m/e)^m,
  -- we have n! = (stirlingSeq(n)/√π) · stirlingApprox(n)
  --
  -- So the ratio becomes: √π · [stirlingSeq(n)/(stirlingSeq(k)·stirlingSeq(n-k))] ·
  --   [stirlingApprox(n)/(stirlingApprox(k)·stirlingApprox(n-k))]
  --
  -- The stirlingSeq ratio is bounded:
  -- √π/stirlingSeq(1)² ≤ stirlingSeq(n)/(stirlingSeq(k)·stirlingSeq(n-k)) ≤ stirlingSeq(1)/π
  --
  -- This gives the final bounds (with some loosening for simplicity)

  -- Relate stirlingN to stirlingApprox
  have hsqrt_pi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hpi_pos : 0 < Real.pi := Real.pi_pos

  -- stirlingK and stirlingNK are positive
  have hstirlingK_pos : 0 < Real.sqrt (2 * Real.pi * k) * (k / Real.exp 1) ^ k := by positivity
  have hstirlingNK_pos : 0 < Real.sqrt (2 * Real.pi * (n - k : ℕ)) * ((n - k : ℕ) / Real.exp 1) ^ (n - k) := by positivity
  have hstirlingN_pos : 0 < Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n := by positivity

  -- Rewrite stirlingN = √π · √(2n) · (n/e)^n (and similarly for K, NK)
  have hN_eq : Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n =
      Real.sqrt Real.pi * (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n) := by
    have h1 : Real.sqrt (2 * Real.pi * n) = Real.sqrt (2 * Real.pi) * Real.sqrt n :=
      Real.sqrt_mul (by positivity) n
    have h2 : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
      Real.sqrt_mul (by norm_num) Real.pi
    have h3 : Real.sqrt 2 * Real.sqrt n = Real.sqrt (2 * n) := (Real.sqrt_mul (by norm_num) n).symm
    rw [h1, h2]
    rw [mul_assoc (Real.sqrt 2) (Real.sqrt Real.pi) (Real.sqrt n)]
    rw [mul_comm (Real.sqrt Real.pi) (Real.sqrt n)]
    rw [← mul_assoc (Real.sqrt 2) (Real.sqrt n) (Real.sqrt Real.pi)]
    rw [h3, mul_comm (Real.sqrt (2 * n)) (Real.sqrt Real.pi), mul_assoc]
  have hK_eq : Real.sqrt (2 * Real.pi * k) * (k / Real.exp 1) ^ k =
      Real.sqrt Real.pi * (Real.sqrt (2 * k) * (k / Real.exp 1) ^ k) := by
    have h1 : Real.sqrt (2 * Real.pi * k) = Real.sqrt (2 * Real.pi) * Real.sqrt k :=
      Real.sqrt_mul (by positivity) k
    have h2 : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
      Real.sqrt_mul (by norm_num) Real.pi
    have h3 : Real.sqrt 2 * Real.sqrt k = Real.sqrt (2 * k) := (Real.sqrt_mul (by norm_num) k).symm
    rw [h1, h2]
    rw [mul_assoc (Real.sqrt 2) (Real.sqrt Real.pi) (Real.sqrt k)]
    rw [mul_comm (Real.sqrt Real.pi) (Real.sqrt k)]
    rw [← mul_assoc (Real.sqrt 2) (Real.sqrt k) (Real.sqrt Real.pi)]
    rw [h3, mul_comm (Real.sqrt (2 * k)) (Real.sqrt Real.pi), mul_assoc]
  have hNK_eq : Real.sqrt (2 * Real.pi * (n - k : ℕ)) * ((n - k : ℕ) / Real.exp 1) ^ (n - k) =
      Real.sqrt Real.pi * (Real.sqrt (2 * (n - k : ℕ)) * ((n - k : ℕ) / Real.exp 1) ^ (n - k)) := by
    have h1 : Real.sqrt (2 * Real.pi * (n - k : ℕ)) = Real.sqrt (2 * Real.pi) * Real.sqrt (n - k : ℕ) :=
      Real.sqrt_mul (by positivity) (n - k : ℕ)
    have h2 : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
      Real.sqrt_mul (by norm_num) Real.pi
    have h3 : Real.sqrt 2 * Real.sqrt (n - k : ℕ) = Real.sqrt (2 * (n - k : ℕ)) :=
      (Real.sqrt_mul (by norm_num) (n - k : ℕ)).symm
    rw [h1, h2]
    rw [mul_assoc (Real.sqrt 2) (Real.sqrt Real.pi) (Real.sqrt (n - k : ℕ))]
    rw [mul_comm (Real.sqrt Real.pi) (Real.sqrt (n - k : ℕ))]
    rw [← mul_assoc (Real.sqrt 2) (Real.sqrt (n - k : ℕ)) (Real.sqrt Real.pi)]
    rw [h3, mul_comm (Real.sqrt (2 * (n - k : ℕ))) (Real.sqrt Real.pi), mul_assoc]

  -- Define the denominator parts D_m = √(2m) · (m/e)^m
  set Dn := Real.sqrt (2 * n) * (n / Real.exp 1) ^ n with hDn_def
  set Dk := Real.sqrt (2 * k) * (k / Real.exp 1) ^ k with hDk_def
  set Dnk := Real.sqrt (2 * (n - k : ℕ)) * ((n - k : ℕ) / Real.exp 1) ^ (n - k) with hDnk_def

  -- Positivity of D terms
  have hDn_pos : 0 < Dn := by rw [hDn_def]; positivity
  have hDk_pos : 0 < Dk := by rw [hDk_def]; positivity
  have hDnk_pos : 0 < Dnk := by rw [hDnk_def]; positivity

  -- stirlingN = √π · D_n (from hN_eq)
  have hstirlingN_eq : Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n = Real.sqrt Real.pi * Dn := hN_eq
  have hstirlingK_eq : Real.sqrt (2 * Real.pi * k) * (k / Real.exp 1) ^ k = Real.sqrt Real.pi * Dk := hK_eq
  have hstirlingNK_eq : Real.sqrt (2 * Real.pi * (n - k : ℕ)) * ((n - k : ℕ) / Real.exp 1) ^ (n - k) =
      Real.sqrt Real.pi * Dnk := hNK_eq

  -- stirlingN/(stirlingK · stirlingNK) = (1/√π) · D_n/(D_k · D_{n-k})
  have hstirling_ratio : Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n /
      (Real.sqrt (2 * Real.pi * k) * (k / Real.exp 1) ^ k *
       (Real.sqrt (2 * Real.pi * (n - k : ℕ)) * ((n - k : ℕ) / Real.exp 1) ^ (n - k))) =
      (1 / Real.sqrt Real.pi) * (Dn / (Dk * Dnk)) := by
    rw [hstirlingN_eq, hstirlingK_eq, hstirlingNK_eq]
    have hsqrt_pi_ne : Real.sqrt Real.pi ≠ 0 := ne_of_gt hsqrt_pi_pos
    have hDk_ne : Dk ≠ 0 := ne_of_gt hDk_pos
    have hDnk_ne : Dnk ≠ 0 := ne_of_gt hDnk_pos
    field_simp

  -- The stirlingSeq ratio: R = stirlingSeq(n)/(stirlingSeq(k)·stirlingSeq(n-k))
  -- Bounds: √π/stirlingSeq(1)² ≤ R ≤ stirlingSeq(1)/π
  have hR_lower : Real.sqrt Real.pi / Stirling.stirlingSeq 1 ^ 2 ≤
      Stirling.stirlingSeq n / (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)) := by
    have h1 : Stirling.stirlingSeq k ≤ Stirling.stirlingSeq 1 := hk_bounds.2
    have h2 : Stirling.stirlingSeq (n - k) ≤ Stirling.stirlingSeq 1 := hnk_bounds.2
    have h3 : Real.sqrt Real.pi ≤ Stirling.stirlingSeq n := hn_bounds.1
    have hseq_k_ne : Stirling.stirlingSeq k ≠ 0 := ne_of_gt hseq_k_pos
    have hseq_nk_ne : Stirling.stirlingSeq (n - k) ≠ 0 := ne_of_gt hseq_nk_pos
    have hseq1_ne : Stirling.stirlingSeq 1 ≠ 0 := ne_of_gt hseq1_pos
    have hprod_bound : Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k) ≤ Stirling.stirlingSeq 1 ^ 2 := by
      calc Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)
          ≤ Stirling.stirlingSeq 1 * Stirling.stirlingSeq (n - k) := mul_le_mul_of_nonneg_right h1 (le_of_lt hseq_nk_pos)
        _ ≤ Stirling.stirlingSeq 1 * Stirling.stirlingSeq 1 := mul_le_mul_of_nonneg_left h2 (le_of_lt hseq1_pos)
        _ = Stirling.stirlingSeq 1 ^ 2 := (sq _).symm
    have hprod_pos : 0 < Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k) := mul_pos hseq_k_pos hseq_nk_pos
    rw [div_le_div_iff₀ (pow_pos hseq1_pos 2) hprod_pos]
    calc Real.sqrt Real.pi * (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k))
        ≤ Real.sqrt Real.pi * Stirling.stirlingSeq 1 ^ 2 := mul_le_mul_of_nonneg_left hprod_bound (le_of_lt hsqrt_pi_pos)
      _ ≤ Stirling.stirlingSeq n * Stirling.stirlingSeq 1 ^ 2 := mul_le_mul_of_nonneg_right h3 (pow_nonneg (le_of_lt hseq1_pos) 2)

  have hR_upper : Stirling.stirlingSeq n / (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)) ≤
      Stirling.stirlingSeq 1 / Real.pi := by
    have h1 : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := hn_bounds.2
    have h2 : Real.sqrt Real.pi ≤ Stirling.stirlingSeq k := hk_bounds.1
    have h3 : Real.sqrt Real.pi ≤ Stirling.stirlingSeq (n - k) := hnk_bounds.1
    have hseq_k_ne : Stirling.stirlingSeq k ≠ 0 := ne_of_gt hseq_k_pos
    have hseq_nk_ne : Stirling.stirlingSeq (n - k) ≠ 0 := ne_of_gt hseq_nk_pos
    have hprod_bound : Real.pi ≤ Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k) := by
      calc Real.pi = Real.sqrt Real.pi * Real.sqrt Real.pi := (Real.mul_self_sqrt (le_of_lt hpi_pos)).symm
        _ ≤ Stirling.stirlingSeq k * Real.sqrt Real.pi := mul_le_mul_of_nonneg_right h2 (le_of_lt hsqrt_pi_pos)
        _ ≤ Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k) := mul_le_mul_of_nonneg_left h3 (le_of_lt hseq_k_pos)
    have hprod_pos : 0 < Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k) := mul_pos hseq_k_pos hseq_nk_pos
    rw [div_le_div_iff₀ hprod_pos hpi_pos]
    calc Stirling.stirlingSeq n * Real.pi
        ≤ Stirling.stirlingSeq n * (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)) :=
            mul_le_mul_of_nonneg_left hprod_bound (le_of_lt hseq_n_pos)
      _ ≤ Stirling.stirlingSeq 1 * (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)) :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hprod_pos)

  -- Factorial ratio: n!/(k!(n-k)!) = R · D_n/(D_k · D_{n-k})
  have hfact_ratio : (n.factorial : ℝ) / (k.factorial * (n - k).factorial) =
      Stirling.stirlingSeq n / (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)) * (Dn / (Dk * Dnk)) := by
    rw [hn_fact, hk_fact, hnk_fact]
    have hseq_k_ne : Stirling.stirlingSeq k ≠ 0 := ne_of_gt hseq_k_pos
    have hseq_nk_ne : Stirling.stirlingSeq (n - k) ≠ 0 := ne_of_gt hseq_nk_pos
    have hDk_ne : Dk ≠ 0 := ne_of_gt hDk_pos
    have hDnk_ne : Dnk ≠ 0 := ne_of_gt hDnk_pos
    field_simp
    ring

  -- The bounds now follow from hR_lower, hR_upper and hstirling_ratio
  constructor
  · -- Lower bound: stirlingN/(stirlingK·stirlingNK) / stirlingSeq(1)² * π ≤ n!/(k!(n-k)!)
    rw [hfact_ratio, hstirling_ratio]
    -- LHS = (1/√π) · (D_n/(D_k·D_{n-k})) / stirlingSeq(1)² * π = (D_n/(D_k·D_{n-k})) · √π / stirlingSeq(1)²
    -- RHS = R · (D_n/(D_k·D_{n-k}))
    -- Need: (D_n/(D_k·D_{n-k})) · √π / stirlingSeq(1)² ≤ R · (D_n/(D_k·D_{n-k}))
    -- i.e., √π / stirlingSeq(1)² ≤ R (which is hR_lower)
    have hD_ratio_pos : 0 < Dn / (Dk * Dnk) := div_pos hDn_pos (mul_pos hDk_pos hDnk_pos)
    have hD_ratio_ne : Dn / (Dk * Dnk) ≠ 0 := ne_of_gt hD_ratio_pos
    have hsqrt_pi_ne : Real.sqrt Real.pi ≠ 0 := ne_of_gt hsqrt_pi_pos
    have hseq1_sq_pos : 0 < Stirling.stirlingSeq 1 ^ 2 := pow_pos hseq1_pos 2
    calc 1 / Real.sqrt Real.pi * (Dn / (Dk * Dnk)) / Stirling.stirlingSeq 1 ^ 2 * Real.pi
        = (Dn / (Dk * Dnk)) * (Real.pi / Real.sqrt Real.pi / Stirling.stirlingSeq 1 ^ 2) := by ring
      _ = (Dn / (Dk * Dnk)) * (Real.sqrt Real.pi / Stirling.stirlingSeq 1 ^ 2) := by
          congr 1
          have h := Real.mul_self_sqrt (le_of_lt hpi_pos)
          field_simp
          linarith
      _ ≤ (Dn / (Dk * Dnk)) * (Stirling.stirlingSeq n / (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k))) :=
          mul_le_mul_of_nonneg_left hR_lower (le_of_lt hD_ratio_pos)
      _ = Stirling.stirlingSeq n / (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)) * (Dn / (Dk * Dnk)) := by ring
  · -- Upper bound: n!/(k!(n-k)!) ≤ stirlingN/(stirlingK·stirlingNK) * stirlingSeq(1)² / π
    rw [hfact_ratio, hstirling_ratio]
    -- LHS = R · (D_n/(D_k·D_{n-k}))
    -- RHS = (1/√π) · (D_n/(D_k·D_{n-k})) * stirlingSeq(1)² / π = (D_n/(D_k·D_{n-k})) · stirlingSeq(1)² / (π√π)
    -- Need: R ≤ stirlingSeq(1)² / (π√π) = stirlingSeq(1)² / π^(3/2)
    -- But we only have R ≤ stirlingSeq(1)/π
    -- Need: stirlingSeq(1)/π ≤ stirlingSeq(1)²/(π√π) = stirlingSeq(1)²/π^(3/2)
    -- i.e., 1 ≤ stirlingSeq(1)/√π
    -- i.e., √π ≤ stirlingSeq(1) ✓ (since stirlingSeq(1) = e/√2 ≈ 1.92 > √π ≈ 1.77)
    have hD_ratio_pos : 0 < Dn / (Dk * Dnk) := div_pos hDn_pos (mul_pos hDk_pos hDnk_pos)
    have hseq1_sq_pos : 0 < Stirling.stirlingSeq 1 ^ 2 := pow_pos hseq1_pos 2
    have hsqrt_pi_ne : Real.sqrt Real.pi ≠ 0 := ne_of_gt hsqrt_pi_pos
    -- stirlingSeq(1)/π ≤ stirlingSeq(1)²/(π*√π)
    have hcoeff_bound : Stirling.stirlingSeq 1 / Real.pi ≤ Stirling.stirlingSeq 1 ^ 2 / (Real.pi * Real.sqrt Real.pi) := by
      rw [div_le_div_iff₀ hpi_pos (mul_pos hpi_pos hsqrt_pi_pos)]
      have hsqrt_pi_le : Real.sqrt Real.pi ≤ Stirling.stirlingSeq 1 := (stirlingSeq_bounds 1 le_rfl).1
      calc Stirling.stirlingSeq 1 * (Real.pi * Real.sqrt Real.pi)
          = Stirling.stirlingSeq 1 * Real.sqrt Real.pi * Real.pi := by ring
        _ ≤ Stirling.stirlingSeq 1 * Stirling.stirlingSeq 1 * Real.pi := by
            apply mul_le_mul_of_nonneg_right
            exact mul_le_mul_of_nonneg_left hsqrt_pi_le (le_of_lt hseq1_pos)
            exact le_of_lt hpi_pos
        _ = Stirling.stirlingSeq 1 ^ 2 * Real.pi := by ring
    calc Stirling.stirlingSeq n / (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)) * (Dn / (Dk * Dnk))
        ≤ (Stirling.stirlingSeq 1 / Real.pi) * (Dn / (Dk * Dnk)) :=
            mul_le_mul_of_nonneg_right hR_upper (le_of_lt hD_ratio_pos)
      _ ≤ (Stirling.stirlingSeq 1 ^ 2 / (Real.pi * Real.sqrt Real.pi)) * (Dn / (Dk * Dnk)) :=
            mul_le_mul_of_nonneg_right hcoeff_bound (le_of_lt hD_ratio_pos)
      _ = 1 / Real.sqrt Real.pi * (Dn / (Dk * Dnk)) * Stirling.stirlingSeq 1 ^ 2 / Real.pi := by
            field_simp

/-- For k = n/2 + j, the "exponential factor" (n/(2k))^k · (n/(2(n-k)))^{n-k} ≈ exp(-2j²/n).

    This is the key calculation for the local CLT. When k = n/2 + j and n-k = n/2 - j:
    - n/(2k) = 1/(1 + 2j/n)
    - n/(2(n-k)) = 1/(1 - 2j/n)

    Taking logs and using log(1+x) ≈ x - x²/2 + O(x³):
    log(exp_factor) = -(n/2+j)·log(1 + 2j/n) - (n/2-j)·log(1 - 2j/n)
                    ≈ -2j²/n + O(j⁴/n³)

    For |j| ≤ √n, the error is O(1/n).

    This lemma formalizes the bound: for n ≥ 4 and |j| ≤ √n, the ratio
    exp_factor / exp(-2j²/n) ∈ [1/2, 2]. -/
theorem exponential_factor_approx (n : ℕ) (j : ℤ) (hn : 4 ≤ n) (hj : |j| ≤ Real.sqrt n)
    (hj_lower : -(n/2 : ℤ) ≤ j) (hj_upper : j ≤ (n/2 : ℤ)) :
    let k := ((n : ℤ) / 2 + j).toNat
    let nk := n - k
    let exp_factor := (n / (2 * k : ℝ)) ^ k * (n / (2 * nk : ℝ)) ^ nk
    let gauss_factor := Real.exp (-2 * (j : ℝ)^2 / n)
    exp_factor / 2 ≤ gauss_factor ∧ gauss_factor ≤ 2 * exp_factor := by
  -- The proof requires Taylor expansion bounds on log(1 + 2j/n) and log(1 - 2j/n).
  -- For small |j|/n, log(1+x) ≈ x - x²/2, and the error is bounded.
  -- The key calculation is:
  -- log(exp_factor) = k·log(n/(2k)) + nk·log(n/(2·nk))
  --                 = -k·log(1 + 2j/n) - nk·log(1 - 2j/n)
  --                 ≈ -2j²/n
  sorry

/-- **Local CLT Statement**: For the symmetric random walk S_n:
    P(S_n = 2j) = C(n, (n+2j)/2)/2^n ≈ (2/√(πn)) exp(-2j²/n)

    More precisely, for the central values |j| ≤ n/2:
    |C(n,k)/2^n - (2/√(πn)) exp(-2j²/n)| = O(1/n) where k = (n/2 : ℤ) + j

    This gives pointwise convergence of the pmf to the Gaussian density.

    **Proof Strategy** (following Feller):
    1. Apply Stirling to C(n,k) = n!/(k!(n-k)!) with k = n/2 + j:
       - n! ≈ √(2πn)(n/e)^n
       - k! ≈ √(2πk)(k/e)^k where k = n/2 + j
       - (n-k)! ≈ √(2π(n-k))((n-k)/e)^{n-k} where n-k = n/2 - j

    2. The ratio gives:
       C(n,k)/2^n ≈ √(n/(2πk(n-k))) · (n/2k)^k · (n/2(n-k))^{n-k}

    3. For k = n/2 + j with small j:
       - log((n/2k)^k) = k·log(n/(n+2j)) ≈ -2j²/n + O(j⁴/n³)
       - log((n/2(n-k))^{n-k}) = (n-k)·log(n/(n-2j)) ≈ -2j²/n + O(j⁴/n³)

    4. Combining: C(n,k)/2^n ≈ (2/√(πn)) exp(-2j²/n) with O(1/n) error.
-/
theorem local_clt_error_bound (n : ℕ) (j : ℤ) (hn : 1 ≤ n)
    (hj_lower : -(n/2 : ℤ) ≤ j) (hj_upper : j ≤ (n/2 : ℤ)) :
    let idx : ℤ := (n / 2 : ℤ) + j
    let k := idx.toNat
    let binomProb := (Nat.choose n k : ℝ) / 2^n
    let gaussApprox := (2 / Real.sqrt (Real.pi * n)) * Real.exp (-2 * j^2 / n)
    |binomProb - gaussApprox| ≤ (10 : ℝ) / n := by
  -- The proof uses Stirling's approximation for the factorials in C(n,k)
  -- C(n,k) = n! / (k! (n-k)!)
  -- Apply Stirling to each factorial and simplify
  -- See the docstring above for the detailed proof strategy
  sorry

/-- For |j| < n/2 (strictly inside the central region), the binomial probability is close to Gaussian.
    This is the key bound for the local CLT. We require 1 ≤ k < n to apply Stirling.
    We require n ≥ 9 to ensure k, n-k ≥ 1 when |j| ≤ √n. -/
theorem local_clt_central_region (n : ℕ) (j : ℤ) (hn : 9 ≤ n)
    (hj : |j| ≤ Real.sqrt n)
    (hj_lower : -(n/2 : ℤ) ≤ j) (hj_upper : j ≤ (n/2 : ℤ)) :
    let idx : ℤ := (n / 2 : ℤ) + j
    let k := idx.toNat
    let binomProb := (Nat.choose n k : ℝ) / 2^n
    let gaussApprox := (2 / Real.sqrt (Real.pi * n)) * Real.exp (-2 * j^2 / n)
    binomProb ≥ gaussApprox / 2 ∧ binomProb ≤ 2 * gaussApprox := by
  -- Setup: k = (n/2 + j).toNat, with 1 ≤ k < n from bounds on j
  intro idx k binomProb gaussApprox

  -- For n ≥ 9 and |j| ≤ √n ≤ 3, we have:
  -- k = n/2 + j ≥ n/2 - √n ≥ 9/2 - 3 = 1.5 > 1
  -- n - k = n/2 - j ≥ n/2 - √n ≥ 1.5 > 1

  -- Basic positivity facts
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num : 0 < 9) hn)
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hexp_pos : 0 < Real.exp (-2 * (j : ℝ)^2 / n) := Real.exp_pos _

  -- The idx is nonnegative since j ≥ -n/2
  have hidx_nonneg : 0 ≤ idx := by
    simp only [idx]
    have h2 : -(n/2 : ℤ) ≤ j := hj_lower
    have h3 : (0 : ℤ) ≤ (n : ℤ) / 2 := Int.ediv_nonneg (Nat.cast_nonneg n) (by norm_num : (0 : ℤ) ≤ 2)
    linarith

  -- idx ≤ n since j ≤ n/2
  have hidx_le_n : idx ≤ n := by
    simp only [idx]
    have h1 : (n : ℤ) / 2 + j ≤ (n : ℤ) / 2 + (n : ℤ) / 2 := by linarith [hj_upper]
    calc (n : ℤ) / 2 + j ≤ (n : ℤ) / 2 + (n : ℤ) / 2 := h1
      _ ≤ (n : ℤ) := by omega

  have hk_eq : (k : ℤ) = idx := Int.toNat_of_nonneg hidx_nonneg
  have hk_le_n : k ≤ n := by
    have h1 : (k : ℤ) = idx := hk_eq
    have h2 : idx ≤ (n : ℤ) := hidx_le_n
    omega

  -- k ≥ 1: For n ≥ 9 and |j| ≤ √n, we have n/2 - √n ≥ 4.5 - 3 = 1.5 > 1
  -- So k = n/2 + j ≥ n/2 - |j| ≥ n/2 - √n > 1
  have hk_pos : 1 ≤ k := by
    -- The key inequality: for n ≥ 9, n/2 - √n ≥ 1
    -- Proof: Let x = √n. Need x²/2 - x ≥ 1, i.e., x² - 2x - 2 ≥ 0
    -- For x ≥ 3: (3)² - 2(3) - 2 = 9 - 6 - 2 = 1 ≥ 0 ✓
    have hidx_ge_1 : 1 ≤ idx := by
      simp only [idx]
      have hn9 : (9 : ℕ) ≤ n := hn
      -- For n ≥ 9: n/2 ≥ 4 (as integer division)
      have hn_div_2_ge : 4 ≤ (n : ℤ) / 2 := by omega
      -- |j| ≤ √n and j ≥ -|j|, so j ≥ -√n
      -- For integer j with |j| ≤ √n and n ≥ 9: |j| ≤ ⌊√n⌋
      -- n/2 + j ≥ n/2 - |j| ≥ 4 - ⌊√n⌋
      -- For n ≥ 9: ⌊√9⌋ = 3, so n/2 + j ≥ 4 - 3 = 1
      -- For larger n: √n grows slower than n/2, so still OK
      have h_sqrt_bound : Real.sqrt n < (n : ℝ) / 2 := by
        have hn_real : (9 : ℝ) ≤ n := Nat.cast_le.mpr hn9
        have hn_pos : (0 : ℝ) < n := by linarith
        -- √n < n/2 ⟺ 2√n < n
        -- We show (2√n)² < n² and use positivity
        have hsqrt_sq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by linarith)
        have h_sq_ineq : (2 * Real.sqrt n)^2 < (n : ℝ)^2 := by
          have h1 : (2 * Real.sqrt n)^2 = 4 * (Real.sqrt n)^2 := by ring
          rw [h1, hsqrt_sq]
          calc (4 : ℝ) * n < n * n := by nlinarith
            _ = (n : ℝ)^2 := by ring
        have h2sqrt_nonneg : 0 ≤ 2 * Real.sqrt n := by positivity
        have hn_nonneg : (0 : ℝ) ≤ n := by linarith
        -- From (2√n)² < n² and both nonneg, get 2√n < n
        have h3 : 2 * Real.sqrt n < n := (sq_lt_sq₀ h2sqrt_nonneg hn_nonneg).mp h_sq_ineq
        linarith
      -- j ≥ -|j| ≥ -√n (using neg_abs_le and transitivity with real to int)
      have hj_lower_real : -(Real.sqrt n) ≤ (j : ℝ) := by
        have h1 : -|j| ≤ j := neg_abs_le j
        have h2 : (|j| : ℝ) ≤ Real.sqrt n := by
          -- We have hj : (|j| : ℝ) ≤ √n (given), and ↑|j| = |↑j|
          simp only [Int.cast_abs] at hj ⊢
          exact hj
        calc -(Real.sqrt n) ≤ -(|j| : ℝ) := by linarith
          _ = ((-|j|) : ℤ) := by simp
          _ ≤ (j : ℝ) := by exact_mod_cast h1
      -- n/2 + j ≥ n/2 - √n as reals
      have h_idx_real : (1 : ℝ) < (n : ℝ) / 2 + (j : ℝ) := by
        have h1 : (n : ℝ) / 2 - Real.sqrt n > 1 := by
          have hn_real : (9 : ℝ) ≤ n := Nat.cast_le.mpr hn9
          -- n/2 - √n > 1 ⟺ n/2 - 1 > √n ⟺ (n/2 - 1)² > n (for n/2 > 1)
          have h2 : (1 : ℝ) < (n : ℝ) / 2 := by linarith
          have h3 : Real.sqrt n < (n : ℝ) / 2 - 1 := by
            have h4 : n < ((n : ℝ) / 2 - 1)^2 := by nlinarith
            have h5 : 0 < (n : ℝ) / 2 - 1 := by linarith
            have h6 : Real.sqrt n < Real.sqrt (((n : ℝ) / 2 - 1)^2) := Real.sqrt_lt_sqrt (by linarith) h4
            rwa [Real.sqrt_sq (le_of_lt h5)] at h6
          linarith
        calc (1 : ℝ) < (n : ℝ) / 2 - Real.sqrt n := h1
          _ ≤ (n : ℝ) / 2 + (j : ℝ) := by linarith [hj_lower_real]
      -- Convert to integer: 1 ≤ idx as integers using Arithmetic lemma
      have h_idx_int : 1 ≤ (n : ℤ) / 2 + j :=
        Arithmetic.int_div2_add_ge_one_of_real_gt_one n j hn hj_lower h_idx_real
      exact h_idx_int
    have hk_ge_1 : 1 ≤ k := by
      have h1 : (1 : ℤ) ≤ idx := hidx_ge_1
      have h2 : (k : ℤ) = idx := hk_eq
      omega
    exact hk_ge_1

  -- n - k ≥ 1 by symmetry: n - k = n - (n/2 + j) ≈ n/2 - j ≥ n/2 - |j| ≥ 1
  have hnk_pos : 1 ≤ n - k := by
    have hidx_le_nm1 : idx ≤ n - 1 := by
      simp only [idx]
      -- j ≤ |j| ≤ √n < n/2 - 1 for n ≥ 9
      have hn9 : (9 : ℕ) ≤ n := hn
      have hj_upper_real : (j : ℝ) ≤ Real.sqrt n := by
        have h1 : (j : ℝ) ≤ |(j : ℝ)| := le_abs_self (j : ℝ)
        -- hj : (|j| : ℝ) ≤ √n, and (|j| : ℝ) = |(j : ℝ)| by Int.cast_abs
        have h2 : |(j : ℝ)| ≤ Real.sqrt n := by
          have heq : ((|j| : ℤ) : ℝ) = |(j : ℝ)| := Int.cast_abs (R := ℝ)
          rw [← heq]
          exact hj
        linarith
      have h_sqrt_lt : Real.sqrt n < (n : ℝ) / 2 - 1 := by
        have hn_real : (9 : ℝ) ≤ n := Nat.cast_le.mpr hn9
        have h4 : n < ((n : ℝ) / 2 - 1)^2 := by nlinarith
        have h5 : 0 < (n : ℝ) / 2 - 1 := by linarith
        have h6 : Real.sqrt n < Real.sqrt (((n : ℝ) / 2 - 1)^2) := Real.sqrt_lt_sqrt (by linarith) h4
        rwa [Real.sqrt_sq (le_of_lt h5)] at h6
      have h_idx_real : (n : ℝ) / 2 + (j : ℝ) < (n : ℝ) - 1 := by
        calc (n : ℝ) / 2 + (j : ℝ)
            ≤ (n : ℝ) / 2 + Real.sqrt n := by linarith [hj_upper_real]
          _ < (n : ℝ) / 2 + ((n : ℝ) / 2 - 1) := by linarith [h_sqrt_lt]
          _ = (n : ℝ) - 1 := by ring
      -- Convert: (n : ℝ) / 2 + j < n - 1 ⟹ (n : ℤ) / 2 + j ≤ n - 1 using Arithmetic lemma
      have h_int : (n : ℤ) / 2 + j ≤ (n : ℤ) - 1 :=
        Arithmetic.int_div2_add_le_n_sub_one_of_real_lt n j h_idx_real
      exact h_int
    have hk_lt_n : k < n := by
      -- idx ≤ n - 1, so k = idx.toNat < n
      have h_n_pos : 0 < n := Nat.lt_of_lt_of_le (by norm_num : 0 < 9) hn
      -- k = idx.toNat and idx ≤ n - 1
      have hk_le_nm1 : k ≤ n - 1 := by
        have h1 : (k : ℤ) = idx := hk_eq
        have h2 : idx ≤ (n : ℤ) - 1 := hidx_le_nm1
        omega
      omega
    omega

  have hk_lt_n : k < n := by omega

  -- The binomProb and gaussApprox are positive
  have hbinom_pos : 0 < binomProb := by
    simp only [binomProb]
    apply div_pos
    · exact Nat.cast_pos.mpr (Nat.choose_pos hk_le_n)
    · positivity
  have hgauss_pos : 0 < gaussApprox := by
    simp only [gaussApprox]
    apply mul_pos
    · apply div_pos (by norm_num) (Real.sqrt_pos.mpr (mul_pos hpi_pos hn_pos))
    · exact hexp_pos

  -- Apply factorial_ratio_stirling_bounds to get Stirling bounds on C(n,k)
  have hStirling := factorial_ratio_stirling_bounds n k hk_pos hk_lt_n

  -- The core of the proof: connect Stirling bounds to Gaussian
  -- C(n,k)/2^n ≈ √(n/(2πk(n-k))) · (n/(2k))^k · (n/(2(n-k)))^{n-k}
  -- For k = n/2 + j:
  --   √(n/(2πk(n-k))) ≈ √(2/(πn)) when j is small
  --   (n/(2k))^k · (n/(2(n-k)))^{n-k} ≈ exp(-2j²/n)
  -- So C(n,k)/2^n ≈ √(2/(πn)) · exp(-2j²/n)
  -- And gaussApprox = (2/√(πn)) · exp(-2j²/n) = √(4/(πn)) · exp(-2j²/n)
  -- Ratio: √(2/(πn)) / √(4/(πn)) = √(1/2) = 1/√2 ≈ 0.707
  -- This is well within [1/2, 2]

  constructor
  · -- Lower bound: binomProb ≥ gaussApprox / 2
    sorry
  · -- Upper bound: binomProb ≤ 2 * gaussApprox
    sorry

/-! ## Tail Bounds

Outside the central region |j| > C√n, both binomial and Gaussian are exponentially small.
-/

/-- Sum of exp(l·boolToInt(b)) over b ∈ {true, false} is 2·cosh(l). -/
theorem sum_exp_boolToInt (l : ℝ) :
    (Finset.univ : Finset Bool).sum (fun b => Real.exp (l * boolToInt b)) = 2 * Real.cosh l := by
  -- Expand the sum over {true, false}
  have huniv : (Finset.univ : Finset Bool) = {true, false} := Fintype.univ_bool
  rw [huniv]
  simp only [Finset.sum_pair (by decide : true ≠ false)]
  -- boolToInt true = 1, boolToInt false = -1
  simp only [boolToInt_true, boolToInt_false]
  -- exp(l * 1) + exp(l * -1) = exp(l) + exp(-l) = 2 * cosh(l)
  -- Note: boolToInt returns ℤ, so we have casts
  simp only [Int.cast_one, Int.cast_neg]
  rw [mul_one, mul_neg_one, Real.cosh_eq]
  field_simp

/-! ## Exponential Moment for Random Walks

For Hoeffding's inequality, we need to compute the exponential moment:
Σ_flips exp(λ·S_n) = (2·cosh(λ))^n

This uses the product structure of the sum over all flip sequences.
-/

/-- Equivalence between (Fin (n+1) → α) and α × (Fin n → α) via Fin.cons.
    The first component is the value at 0, and the second is the restriction to Fin n. -/
def equivFinSuccFun (n : ℕ) (α : Type*) : (Fin (n+1) → α) ≃ α × (Fin n → α) where
  toFun := fun f => (f 0, fun i => f (Fin.succ i))
  invFun := fun ⟨a, g⟩ => Fin.cons a g
  left_inv := fun f => by
    ext i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · simp only [Fin.cons_zero]
    · simp only [Fin.cons_succ]
  right_inv := fun ⟨a, g⟩ => by
    simp only [Fin.cons_zero, Fin.cons_succ]

/-- The sum over all function values factors into products over coordinates.
    For f : Fin n → Bool → ℝ:
    ∑ flips : (Fin n → Bool), ∏ i, f i (flips i) = ∏ i, ∑ b, f i b

    Proof by induction on n using Fin.cons decomposition. -/
theorem sum_prod_function_eq_prod_sum (n : ℕ) (f : Fin n → Bool → ℝ) :
    (Finset.univ : Finset (Fin n → Bool)).sum (fun flips => Finset.univ.prod (fun i => f i (flips i))) =
    Finset.univ.prod (fun i => (Finset.univ : Finset Bool).sum (fun b => f i b)) := by
  induction n with
  | zero =>
    -- Empty product case: ∑ over singleton = 1 = ∏ over empty
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_const, Finset.card_univ]
    -- Fintype.card (Fin 0 → Bool) = 1 (unique function from empty type)
    have hcard : Fintype.card (Fin 0 → Bool) = 1 := by
      simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, pow_zero]
    simp only [hcard, one_smul]
  | succ n ih =>
    -- Use equivFinSuccFun to decompose: (Fin (n+1) → Bool) ≃ Bool × (Fin n → Bool)
    let equiv := equivFinSuccFun n Bool
    rw [← Equiv.sum_comp equiv.symm]
    rw [Fintype.sum_prod_type]
    -- For each (b, flips'), compute the product
    -- equiv.symm (b, flips') = Fin.cons b flips'
    have hsymm : ∀ (b : Bool) (flips' : Fin n → Bool),
        equiv.symm (b, flips') = Fin.cons b flips' := fun _ _ => rfl
    -- Product over Fin (n+1) = f 0 b * ∏ over Fin n
    have hprod_split : ∀ (b : Bool) (flips' : Fin n → Bool),
        Finset.univ.prod (fun i : Fin (n+1) => f i (equiv.symm (b, flips') i)) =
        f 0 b * Finset.univ.prod (fun i : Fin n => f (Fin.succ i) (flips' i)) := by
      intro b flips'
      rw [Fin.prod_univ_succ]
      -- equiv.symm (b, flips') = Fin.cons b flips'
      -- At index 0: Fin.cons b flips' 0 = b
      -- At index (succ i): Fin.cons b flips' (succ i) = flips' i
      simp only [hsymm, Fin.cons_zero, Fin.cons_succ]
    simp_rw [hprod_split]
    -- Sum over flips' and b
    -- ∑_b ∑_{flips'} f 0 b * ∏_{i<n} f (succ i) (flips' i)
    -- = ∑_b f 0 b * (∑_{flips'} ∏_{i<n} f (succ i) (flips' i))
    simp_rw [← Finset.mul_sum]
    -- By induction hypothesis: ∑_{flips'} ∏_{i<n} f (succ i) (flips' i) = ∏_{i<n} ∑_b f (succ i) b
    have hih := ih (fun i => f (Fin.succ i))
    simp_rw [hih]
    -- Now: ∑_b f 0 b * (∏_{i<n} ∑_{b'} f (succ i) b')
    -- = (∑_b f 0 b) * (∏_{i<n} ∑_{b'} f (succ i) b')
    rw [← Finset.sum_mul]
    -- The RHS is ∏_{i : Fin (n+1)} ∑_b f i b = (∑_b f 0 b) * ∏_{i : Fin n} (∑_b f (succ i) b)
    rw [Fin.prod_univ_succ]

/-- The exponential moment of the random walk:
    Σ_flips exp(λ·S_n) = (2·cosh(λ))^n

    This factorizes because exp(λ·S_n) = ∏ᵢ exp(λ·Xᵢ) and the sum over all
    flip sequences factors into a product of sums over each coordinate. -/
theorem exponential_moment_random_walk (n : ℕ) (l : ℝ) :
    (Finset.univ : Finset (Fin n → Bool)).sum
      (fun flips => Real.exp (l * (partialSumFin n flips n : ℝ))) = (2 * Real.cosh l) ^ n := by
  -- First, express partialSumFin n flips n as the full sum over Fin n
  have hfull : ∀ flips : Fin n → Bool,
      partialSumFin n flips n = Finset.univ.sum (fun i : Fin n => boolToInt (flips i)) := by
    intro flips
    exact partialSumFin_ge n flips n (le_refl n)
  simp_rw [hfull]
  -- exp(l * Σᵢ Xᵢ) = ∏ᵢ exp(l * Xᵢ)
  have hexp_sum : ∀ flips : Fin n → Bool,
      Real.exp (l * (Finset.univ.sum (fun i : Fin n => boolToInt (flips i)) : ℤ)) =
      Finset.univ.prod (fun i : Fin n => Real.exp (l * (boolToInt (flips i) : ℝ))) := by
    intro flips
    rw [Int.cast_sum]
    rw [mul_comm, Finset.sum_mul]
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [mul_comm]
  simp_rw [hexp_sum]
  -- Apply the factorization theorem
  have hfact := sum_prod_function_eq_prod_sum n (fun i b => Real.exp (l * (boolToInt b : ℝ)))
  rw [hfact]
  -- Now goal: ∏_i ∑_b exp(l * boolToInt b) = (2 * cosh l)^n
  -- Each factor ∑_b exp(l * boolToInt b) = 2 * cosh l
  have hfactor : ∀ i : Fin n, (Finset.univ : Finset Bool).sum (fun b => Real.exp (l * (boolToInt b : ℝ))) =
      2 * Real.cosh l := fun _ => sum_exp_boolToInt l
  conv_lhs => arg 2; ext i; rw [hfactor i]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The factorial inequality (2k)! ≥ 2^k · k! for all k ≥ 0.
    This follows from (2k)! = 2^k · k! · (2k-1)!! where (2k-1)!! = 1·3·5·...·(2k-1) ≥ 1.

    Proof: (2k)! = (1·3·5·...·(2k-1)) · (2·4·6·...·(2k)) = (2k-1)!! · 2^k · k! ≥ 2^k · k!
-/
theorem double_factorial_bound (k : ℕ) : 2^k * k.factorial ≤ (2 * k).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- (2(k+1))! = (2k+2)! = (2k+2)(2k+1)(2k)!
    -- 2^{k+1} (k+1)! = 2 · 2^k · (k+1) · k!
    -- Need: 2 · 2^k · (k+1) · k! ≤ (2k+2)(2k+1)(2k)!
    -- By IH: 2^k · k! ≤ (2k)!
    -- So: 2(k+1) · (2k)! ≤ (2k+2)(2k+1)(2k)!
    -- Need: 2(k+1) ≤ (2k+2)(2k+1) = 2(k+1)(2k+1)
    -- This is: 1 ≤ 2k+1, which is true for k ≥ 0.
    have hsucc_fact : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
    have h2k2_fact : (2 * (k + 1)).factorial = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
      have h1 : 2 * (k + 1) = 2 * k + 2 := by ring
      rw [h1]
      rw [Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k)]
      ring
    rw [pow_succ, hsucc_fact, h2k2_fact]
    -- Goal: 2^k * 2 * ((k+1) * k!) ≤ (2k+2)(2k+1)(2k)!
    -- Rewrite: 2 * (k+1) * (2^k * k!) ≤ (2k+2)(2k+1)(2k)!
    have hlhs : 2^k * 2 * ((k + 1) * k.factorial) = 2 * (k + 1) * (2^k * k.factorial) := by ring
    rw [hlhs]
    -- By ih: 2^k * k! ≤ (2k)!
    -- Need: 2(k+1) ≤ (2k+2)(2k+1)
    have hcoeff : 2 * (k + 1) ≤ (2 * k + 2) * (2 * k + 1) := by
      have h1 : 2 * k + 2 = 2 * (k + 1) := by ring
      rw [h1]
      calc 2 * (k + 1)
          = 2 * (k + 1) * 1 := by ring
        _ ≤ 2 * (k + 1) * (2 * k + 1) := by
            apply Nat.mul_le_mul_left
            omega
    calc 2 * (k + 1) * (2^k * k.factorial)
        ≤ 2 * (k + 1) * (2 * k).factorial := Nat.mul_le_mul_left _ ih
      _ ≤ (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := Nat.mul_le_mul_right _ hcoeff

/-- The key bound cosh(x) ≤ exp(x²/2) for all x ∈ ℝ.
    This is the sub-Gaussian property of the Rademacher distribution.

    **Proof**: By comparing Taylor series term by term.
    cosh(x) = Σ_{k=0}^∞ x^{2k} / (2k)!
    exp(x²/2) = Σ_{k=0}^∞ (x²/2)^k / k! = Σ_{k=0}^∞ x^{2k} / (2^k k!)

    By `double_factorial_bound`: (2k)! ≥ 2^k k!, so 1/(2k)! ≤ 1/(2^k k!).
    Summing term by term gives cosh(x) ≤ exp(x²/2).
-/
theorem cosh_le_exp_half_sq (x : ℝ) : Real.cosh x ≤ Real.exp (x^2 / 2) :=
  Real.cosh_le_exp_half_sq x

/-- Exponential Markov inequality for counting:
    If X is a real-valued function on a finite set S, then for λ > 0 and t > 0:
    #{x ∈ S | X(x) > t} ≤ exp(-λt) * Σ_{x ∈ S} exp(λ * X(x))

    Proof: For x with X(x) > t, we have exp(λt) < exp(λ*X(x)).
    So #{X > t} * exp(λt) ≤ Σ_{x : X(x)>t} exp(λ*X(x)) ≤ Σ_S exp(λ*X(x)). -/
theorem exp_markov_count {α : Type*} [DecidableEq α] (S : Finset α) (X : α → ℝ)
    (t : ℝ) (l : ℝ) (hl : 0 < l) (_ht : 0 < t) :
    ((S.filter (fun x => t < X x)).card : ℝ) ≤
      Real.exp (-l * t) * S.sum (fun x => Real.exp (l * X x)) := by
  -- Let T = {x ∈ S | X(x) > t}
  let T := S.filter (fun x => t < X x)
  -- For each x ∈ T: exp(λ*t) < exp(λ*X(x)) because t < X(x) and λ > 0
  have hexp_ineq : ∀ x ∈ T, Real.exp (l * t) < Real.exp (l * X x) := by
    intro x hx
    have hmem : x ∈ S ∧ t < X x := Finset.mem_filter.mp hx
    apply Real.exp_strictMono
    exact mul_lt_mul_of_pos_left hmem.2 hl
  -- So: |T| * exp(λt) ≤ Σ_{x∈T} exp(λ*X(x))
  have hcard_bound : (T.card : ℝ) * Real.exp (l * t) ≤ T.sum (fun x => Real.exp (l * X x)) := by
    calc (T.card : ℝ) * Real.exp (l * t)
        = T.sum (fun _ => Real.exp (l * t)) := by
          rw [Finset.sum_const]
          simp only [nsmul_eq_mul]
      _ ≤ T.sum (fun x => Real.exp (l * X x)) := by
          apply Finset.sum_le_sum
          intro x hx
          exact le_of_lt (hexp_ineq x hx)
  -- And: Σ_{x∈T} ≤ Σ_{x∈S} (since exp is nonneg)
  have hsubset : T.sum (fun x => Real.exp (l * X x)) ≤ S.sum (fun x => Real.exp (l * X x)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro x _ _
    exact le_of_lt (Real.exp_pos _)
  -- Combine: |T| * exp(λt) ≤ Σ_S exp(λX)
  have hcombined : (T.card : ℝ) * Real.exp (l * t) ≤ S.sum (fun x => Real.exp (l * X x)) :=
    le_trans hcard_bound hsubset
  -- Divide by exp(λt): |T| ≤ exp(-λt) * Σ_S exp(λX)
  have hexp_pos : 0 < Real.exp (l * t) := Real.exp_pos _
  calc (T.card : ℝ)
      = (T.card : ℝ) * Real.exp (l * t) / Real.exp (l * t) := by field_simp
    _ ≤ S.sum (fun x => Real.exp (l * X x)) / Real.exp (l * t) := by
        apply div_le_div_of_nonneg_right hcombined (le_of_lt hexp_pos)
    _ = Real.exp (-l * t) * S.sum (fun x => Real.exp (l * X x)) := by
        rw [div_eq_mul_inv, mul_comm, ← Real.exp_neg]
        ring_nf

/-- The random walk is symmetric: negating all flips negates the walk value. -/
theorem partialSumFin_neg_flips (n k : ℕ) (flips : Fin n → Bool) :
    partialSumFin n (fun i => !flips i) k = -partialSumFin n flips k := by
  unfold partialSumFin
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [boolToInt]
  rcases Bool.eq_false_or_eq_true (flips i) with hf | ht
  · simp [hf]
  · simp [ht]

/-- The negation map on flips is a bijection. -/
def flipNeg (n : ℕ) : Equiv.Perm (Fin n → Bool) where
  toFun := fun flips i => !flips i
  invFun := fun flips i => !flips i
  left_inv := by intro flips; ext i; simp
  right_inv := by intro flips; ext i; simp

/-- Hoeffding's inequality for the symmetric random walk:
    P(|S_n| > t) ≤ 2 exp(-t²/(2n))

    **Proof sketch** (Chernoff/Cramér method):
    1. For any λ > 0: #{S_n > t} ≤ exp(-λt) · Σ_flips exp(λ·S_n) (exponential Markov)
    2. Σ_flips exp(λ·S_n) = (2·cosh(λ))^n (independence + product structure)
    3. cosh(λ) ≤ exp(λ²/2) (cosh_le_exp_half_sq)
    4. So #{S_n > t} ≤ exp(-λt) · 2^n · exp(nλ²/2) = 2^n · exp(nλ²/2 - λt)
    5. Optimize: λ = t/n gives 2^n · exp(-t²/(2n))
    6. By symmetry, #{S_n < -t} also ≤ 2^n · exp(-t²/(2n))
    7. Union bound: #{|S_n| > t} ≤ 2 · 2^n · exp(-t²/(2n))
-/
theorem hoeffding_random_walk (n : ℕ) (t : ℝ) (ht : 0 < t) (hn : 0 < n) :
    (((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (t : ℝ) < |partialSumFin n flips n|)).card : ℝ) / 2^n ≤
    2 * Real.exp (-t^2 / (2 * n)) := by
  -- Step 1: Split |S_n| > t into S_n > t ∨ S_n < -t
  -- For this, we use |x| > t ↔ x > t ∨ x < -t for t > 0
  let S := Finset.univ (α := Fin n → Bool)
  let filterAbs := S.filter (fun flips => t < |partialSumFin n flips n|)
  let filterPos := S.filter (fun flips => t < (partialSumFin n flips n : ℝ))
  let filterNeg := S.filter (fun flips => (partialSumFin n flips n : ℝ) < -t)

  -- |S_n| > t ↔ S_n > t ∨ S_n < -t, so filterAbs ⊆ filterPos ∪ filterNeg
  have hsubset : filterAbs ⊆ filterPos ∪ filterNeg := by
    intro flips hflips
    simp only [Finset.mem_union] at hflips ⊢
    -- t < |S_n| means |S_n| > t, which is S_n > t ∨ S_n < -t
    have h := (Finset.mem_filter.mp hflips).2
    -- Use the fact that for t > 0: t < |x| ↔ t < x ∨ x < -t
    have hlt_abs : t < |partialSumFin n flips n| → (t < partialSumFin n flips n ∨ (partialSumFin n flips n : ℝ) < -t) := by
      intro habs
      rcases lt_or_ge (partialSumFin n flips n : ℝ) 0 with hneg | hpos
      · right
        have : (|partialSumFin n flips n| : ℝ) = -(partialSumFin n flips n : ℝ) := by
          rw [abs_of_neg]; exact hneg
        simp only [Int.cast_abs] at habs
        rw [abs_of_neg hneg] at habs
        linarith
      · left
        have : (|partialSumFin n flips n| : ℝ) = (partialSumFin n flips n : ℝ) := by
          rw [abs_of_nonneg]; exact hpos
        simp only [Int.cast_abs] at habs
        rw [abs_of_nonneg hpos] at habs
        exact habs
    rcases hlt_abs h with hpos | hneg
    · left
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hpos⟩
    · right
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hneg⟩

  -- Card bound via union
  have hcard : filterAbs.card ≤ filterPos.card + filterNeg.card := by
    calc filterAbs.card ≤ (filterPos ∪ filterNeg).card := Finset.card_le_card hsubset
      _ ≤ filterPos.card + filterNeg.card := Finset.card_union_le _ _

  -- Step 2: Bound #{S_n > t} using exponential Markov with λ = t/n
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hl : 0 < t / n := div_pos ht hn_pos

  -- Use exp_markov_count with λ = t/n
  have hmarkov_pos := exp_markov_count S (fun flips => (partialSumFin n flips n : ℝ)) t (t/n) hl ht

  -- The exponential moment: Σ exp((t/n)·S_n) = (2·cosh(t/n))^n
  have hexp_moment := exponential_moment_random_walk n (t/n)

  -- Bound using cosh ≤ exp
  have hcosh_bound := cosh_le_exp_half_sq (t/n)

  -- (2·cosh(t/n))^n ≤ (2·exp((t/n)²/2))^n = 2^n · exp(n·(t/n)²/2) = 2^n · exp(t²/(2n))
  have hcosh_exp : (2 * Real.cosh (t/n)) ^ n ≤ (2 * Real.exp ((t/n)^2 / 2)) ^ n := by
    have hle : 2 * Real.cosh (t/n) ≤ 2 * Real.exp ((t/n)^2 / 2) := by linarith [hcosh_bound]
    have hpos : 0 ≤ 2 * Real.cosh (t/n) := by positivity
    exact pow_le_pow_left₀ hpos hle n

  have hexp_simp : (2 * Real.exp ((t/n)^2 / 2)) ^ n = 2^n * Real.exp (t^2 / (2 * n)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    field_simp

  -- Combine: #{S_n > t} ≤ exp(-(t/n)·t) · (2·cosh(t/n))^n ≤ exp(-t²/n) · 2^n · exp(t²/(2n))
  --                     = 2^n · exp(-t²/n + t²/(2n)) = 2^n · exp(-t²/(2n))
  have hpos_bound : (filterPos.card : ℝ) ≤ 2^n * Real.exp (-t^2 / (2 * n)) := by
    calc (filterPos.card : ℝ)
        ≤ Real.exp (-(t/n) * t) * S.sum (fun flips => Real.exp ((t/n) * (partialSumFin n flips n : ℝ))) := hmarkov_pos
      _ = Real.exp (-(t/n) * t) * (2 * Real.cosh (t/n)) ^ n := by rw [hexp_moment]
      _ ≤ Real.exp (-(t/n) * t) * (2^n * Real.exp (t^2 / (2 * n))) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
          calc (2 * Real.cosh (t/n)) ^ n
              ≤ (2 * Real.exp ((t/n)^2 / 2)) ^ n := hcosh_exp
            _ = 2^n * Real.exp (t^2 / (2 * n)) := hexp_simp
      _ = 2^n * (Real.exp (-(t/n) * t) * Real.exp (t^2 / (2 * n))) := by ring
      _ = 2^n * Real.exp (-(t/n) * t + t^2 / (2 * n)) := by rw [← Real.exp_add]
      _ = 2^n * Real.exp (-t^2 / (2 * n)) := by
          congr 1
          field_simp
          ring

  -- Step 3: By symmetry, #{S_n < -t} also has the same bound
  -- Use the bijection flipNeg: flips ↦ !flips, which maps S_n to -S_n
  have hneg_bound : (filterNeg.card : ℝ) ≤ 2^n * Real.exp (-t^2 / (2 * n)) := by
    -- filterNeg = {flips | S_n(flips) < -t}
    -- For the bijection flipNeg: S_n(!flips) = -S_n(flips)
    -- So {S_n < -t} corresponds to {-S_n > t} = {S_n(!·) > t} under flipNeg
    -- This has the same cardinality as {S_n > t}
    have hbij : filterNeg.card = filterPos.card := by
      -- Define the bijection: negating flips maps filterNeg ↔ filterPos
      let negFlips : (Fin n → Bool) → (Fin n → Bool) := fun flips i => !flips i
      have hneg_invol : ∀ flips, negFlips (negFlips flips) = flips := by
        intro flips; ext i; simp [negFlips]
      -- negFlips maps filterNeg to filterPos
      have hneg_to_pos : ∀ flips ∈ filterNeg, negFlips flips ∈ filterPos := by
        intro flips hflips
        have hmem := Finset.mem_filter.mp hflips
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_univ _
        · have h := partialSumFin_neg_flips n n flips
          simp only [negFlips]
          rw [h, Int.cast_neg]
          linarith [hmem.2]
      -- negFlips maps filterPos to filterNeg
      have hpos_to_neg : ∀ flips ∈ filterPos, negFlips flips ∈ filterNeg := by
        intro flips hflips
        have hmem := Finset.mem_filter.mp hflips
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_univ _
        · have h := partialSumFin_neg_flips n n flips
          simp only [negFlips]
          rw [h, Int.cast_neg]
          linarith [hmem.2]
      -- negFlips is globally injective (it's an involution)
      have hinj : Function.Injective negFlips := by
        intro x y hxy
        have : negFlips (negFlips x) = negFlips (negFlips y) := by rw [hxy]
        simp only [hneg_invol] at this
        exact this
      -- Equal cardinalities via image
      have himage : filterNeg.image negFlips = filterPos := by
        ext flips
        constructor
        · intro hflips
          obtain ⟨flips', hflips', hflips'_eq⟩ := Finset.mem_image.mp hflips
          rw [← hflips'_eq]
          exact hneg_to_pos flips' hflips'
        · intro hflips
          apply Finset.mem_image.mpr
          use negFlips flips
          constructor
          · exact hpos_to_neg flips hflips
          · exact hneg_invol flips
      rw [← himage, Finset.card_image_of_injective _ hinj]
    rw [hbij]
    exact hpos_bound

  -- Step 4: Combine via union bound
  have htwo_pow_pos : (0 : ℝ) < 2^n := by positivity
  calc (filterAbs.card : ℝ) / 2^n
      ≤ ((filterPos.card : ℝ) + (filterNeg.card : ℝ)) / 2^n := by
        apply div_le_div_of_nonneg_right _ (le_of_lt htwo_pow_pos)
        exact_mod_cast hcard
    _ = (filterPos.card : ℝ) / 2^n + (filterNeg.card : ℝ) / 2^n := by
        rw [add_div]
    _ ≤ (2^n * Real.exp (-t^2 / (2 * n))) / 2^n + (2^n * Real.exp (-t^2 / (2 * n))) / 2^n := by
        apply add_le_add
        · apply div_le_div_of_nonneg_right hpos_bound (le_of_lt htwo_pow_pos)
        · apply div_le_div_of_nonneg_right hneg_bound (le_of_lt htwo_pow_pos)
    _ = Real.exp (-t^2 / (2 * n)) + Real.exp (-t^2 / (2 * n)) := by
        field_simp
    _ = 2 * Real.exp (-t^2 / (2 * n)) := by ring

/-- The Gaussian tail bound (Mill's ratio): ∫_{t}^∞ exp(-x²/2) dx ≤ exp(-t²/2)/t for t > 0.

    The proof uses a comparison argument:
    For x ≥ t > 0, exp(-x²/2) ≤ exp(-t²/2) · exp(-(x-t)·t) because x² - t² ≥ 2t(x-t).
    Integrating gives ∫_t^∞ exp(-x²/2) dx ≤ exp(-t²/2) · ∫_t^∞ exp(-(x-t)t) dx = exp(-t²/2)/t.
-/
theorem gaussian_tail_bound (t : ℝ) (ht : 0 < t) :
    ∫ x in Set.Ici t, Real.exp (-x^2/2) ≤ Real.exp (-t^2/2) / t := by
  -- The integral over Ici t equals integral over Ioi t (point has measure zero)
  have h_eq : ∫ x in Set.Ici t, Real.exp (-x^2/2) = ∫ x in Set.Ioi t, Real.exp (-x^2/2) := by
    rw [← MeasureTheory.integral_Ici_eq_integral_Ioi'
      (show MeasureTheory.volume ({t} : Set ℝ) = 0 by simp)]
  rw [h_eq]
  -- Use monotonicity: exp(-x²/2) ≤ exp(-t²/2) * exp(-(x-t)*t) for x ≥ t
  calc ∫ x in Set.Ioi t, Real.exp (-x^2/2)
      ≤ ∫ x in Set.Ioi t, Real.exp (-t^2/2) * Real.exp (-(x - t) * t) := by
        apply MeasureTheory.setIntegral_mono_on
        · -- LHS is integrable: exp(-x²/2) on Ioi t
          have hform : ∀ x : ℝ, -x^2/2 = -(1/2) * x^2 := fun x => by ring
          simp_rw [hform]
          exact (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).integrableOn
        · -- RHS is integrable: exp(const) * exp(-t*(x-t))
          -- This is essentially exp(const) * exp(-t*x + t²) which decays like exp(-t*x)
          -- exp(-(x-t)*t) = exp(-t*x + t²) = exp(t²) * exp(-t*x)
          have hform2 : ∀ x : ℝ, Real.exp (-(x - t) * t) = Real.exp (t^2) * Real.exp (-t * x) := by
            intro x
            rw [← Real.exp_add]
            congr 1
            ring
          simp_rw [hform2]
          -- Now we have exp(-t²/2) * (exp(t²) * exp(-tx)) which is const * exp(-tx)
          have hint2 := integrableOn_exp_mul_Ioi (by linarith : -t < 0) t
          exact (hint2.const_mul _).const_mul _
        · exact measurableSet_Ioi
        · intro x hx
          -- Need: exp(-x²/2) ≤ exp(-t²/2) * exp(-(x-t)*t)
          -- i.e., -x²/2 ≤ -t²/2 + (-(x-t)*t)
          -- i.e., -x²/2 + t²/2 + (x-t)*t ≤ 0
          -- Note: -x²/2 + t²/2 + xt - t² = -x²/2 - t²/2 + xt = -(x-t)²/2 ≤ 0 ✓
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have h : -x^2/2 ≤ -t^2/2 + (-(x - t) * t) := by
            have heq2 : -x^2/2 - (-t^2/2 + (-(x - t) * t)) = -(x - t)^2/2 := by ring
            linarith [sq_nonneg (x - t)]
          exact h
    _ = Real.exp (-t^2/2) * ∫ x in Set.Ioi t, Real.exp (-(x - t) * t) := by
        -- Factor out the constant: set integral is just integral on restricted measure
        rw [← MeasureTheory.integral_const_mul]
    _ = Real.exp (-t^2/2) * (1 / t) := by
        congr 1
        -- Evaluate ∫_t^∞ exp(-(x-t)t) dx = 1/t
        -- exp(-(x-t)*t) = exp(-t*x + t²) = exp(t²) * exp(-t*x)
        have hform2 : ∀ x : ℝ, Real.exp (-(x - t) * t) = Real.exp (t^2) * Real.exp (-t * x) := by
          intro x; rw [← Real.exp_add]; congr 1; ring
        simp_rw [hform2]
        -- Factor out exp(t²): ∫ exp(t²) * exp(-tx) = exp(t²) * ∫ exp(-tx)
        rw [MeasureTheory.integral_const_mul]
        -- Now use ∫_t^∞ exp(-tx) dx = exp(-t²)/t (from integral_exp_mul_Ioi)
        rw [integral_exp_mul_Ioi (by linarith : -t < 0) t]
        -- Result: exp(t²) * (-exp(-t*t) / (-t)) = exp(t²) * exp(-t²) / t = 1/t
        -- Note: integral_exp_mul_Ioi gives -exp(ac)/a for a < 0, here a = -t, c = t
        -- So we get -exp(-t*t)/(-t) = exp(-t²)/t
        have hcalc : Real.exp (t^2) * (-Real.exp (-t * t) / -t) = 1 / t := by
          field_simp
          rw [← Real.exp_add]
          ring_nf
          simp only [Real.exp_zero]
        exact hcalc
    _ = Real.exp (-t^2/2) / t := by ring

/-! ## Convergence of Cylinder Set Probabilities

For Anderson's theorem, we need the cylinder set probabilities to converge
to the corresponding Wiener measure probabilities.
-/

/-- For a single time constraint, the hyperfinite probability converges to Wiener measure.
    This is the key bridge between the nonstandard and standard worlds.

    If we have W_t ∈ [a, b] for Wiener measure, and the hyperfinite walk X_⌊tN⌋/√N at
    step ⌊tN⌋, rescaled, then:
    P_Loeb(X_⌊tN⌋/√N ∈ [a,b]) = Wiener(W_t ∈ [a,b]) + O(1/√N)
-/
theorem cylinder_prob_convergence (a b : ℝ) (t : ℝ) (ha : a < b) (ht : 0 < t) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      let k := Nat.floor (t * N)
      let scaledProb := ((Finset.univ : Finset (Fin N → Bool)).filter
        (fun flips =>
          let walk := (partialSumFin N flips k : ℝ) / Real.sqrt N
          a ≤ walk ∧ walk ≤ b)).card / (2^N : ℝ)
      let wienerProb := ∫ x in Set.Icc a b, gaussianDensity (Real.sqrt t) x
      |scaledProb - wienerProb| < ε := by
  -- This follows from the local CLT applied to each term in the sum
  -- scaledProb = Σ_{j : a√N ≤ 2j-k ≤ b√N} C(N, (k+j)/2) / 2^N
  -- Each term ≈ gaussianDensity evaluated at the corresponding point
  -- The sum approximates the integral
  sorry

/-! ## Summary

We have stated the main components needed for the local CLT:

1. **Stirling bounds** - Lower and upper bounds on n! via Stirling's formula
2. **Local CLT** - Pointwise convergence of binomial pmf to Gaussian density
3. **Tail bounds** - Hoeffding inequality and Gaussian tail bounds
4. **Cylinder convergence** - Hyperfinite probabilities converge to Wiener measure

These are the key ingredients for proving Anderson's theorem:
- The pushforward of Loeb measure under the standard part map equals Wiener measure.

The proofs are marked with `sorry` as they require substantial technical work:
- Stirling: Integral comparisons or Wallis product
- Local CLT: Careful application of Stirling to factorials
- Hoeffding: Exponential moment bounds
- Cylinder convergence: Riemann sum approximation of integrals

-/

end SPDE.Nonstandard
