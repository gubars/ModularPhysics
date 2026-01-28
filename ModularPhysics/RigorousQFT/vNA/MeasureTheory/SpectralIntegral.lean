/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Spectral Integrals

This file develops the theory of integration against projection-valued measures (spectral measures).
For a spectral measure P on ℝ and a bounded Borel function f : ℝ → ℂ, we define the spectral
integral ∫ f dP as a bounded linear operator.

## Main definitions

* `SpectralMeasure.toMeasure` - convert spectral measure to a scalar measure for a vector
* `SpectralMeasure.integral` - the spectral integral ∫ f dP

## Main results

* `SpectralMeasure.integral_mul` - ∫ fg dP = (∫ f dP) ∘ (∫ g dP)
* `SpectralMeasure.integral_star` - ∫ f̄ dP = (∫ f dP)*

## Implementation

The spectral integral is defined using the sesquilinear form approach:
For each x, y ∈ H, μ_{x,y}(E) = ⟨x, P(E)y⟩ defines a complex measure.
Then ⟨x, (∫ f dP) y⟩ = ∫ f dμ_{x,y}.

This approach uses Mathlib's measure theory and Bochner integration.

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I"
* Rudin, "Functional Analysis", Chapter 13
-/

noncomputable section

open scoped InnerProduct ComplexConjugate
open Filter Topology MeasureTheory

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Scalar measures from spectral measures -/

/-- The complex measure μ_{x,y}(E) = ⟨x, P(E)y⟩ associated to vectors x, y and a
    spectral measure P. This is σ-additive by the σ-additivity of P. -/
structure ComplexSpectralMeasure (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The set function -/
  toFun : Set ℝ → ℂ
  /-- Empty set has measure zero -/
  empty : toFun ∅ = 0
  /-- σ-additivity -/
  sigma_additive : ∀ (E : ℕ → Set ℝ), (∀ i j, i ≠ j → Disjoint (E i) (E j)) →
    Tendsto (fun n => ∑ i ∈ Finset.range n, toFun (E i)) atTop (nhds (toFun (⋃ i, E i)))
  /-- Finite total variation bound: for disjoint Eᵢ, Σᵢ |μ(Eᵢ)| ≤ C for some C.
      For spectral measures μ_{x,y}(E) = ⟨x, P(E)y⟩, this bound is C = ‖x‖·‖y‖. -/
  totalVar_bound : ℝ
  totalVar_bound_nonneg : totalVar_bound ≥ 0
  totalVar_finite : ∀ (E : ℕ → Set ℝ), (∀ i j, i ≠ j → Disjoint (E i) (E j)) →
    ∀ n, ∑ i ∈ Finset.range n, ‖toFun (E i)‖ ≤ totalVar_bound

namespace ComplexSpectralMeasure

variable (μ : ComplexSpectralMeasure H)

instance : CoeFun (ComplexSpectralMeasure H) (fun _ => Set ℝ → ℂ) := ⟨ComplexSpectralMeasure.toFun⟩

/-- The total variation of a complex spectral measure.
    This is defined as the supremum of ‖μ(E)‖ over all measurable sets E.
    For a spectral measure derived from P and vectors x, y, this is bounded by ‖x‖·‖y‖. -/
def totalVariation : ENNReal :=
  iSup fun n : ℕ => (‖μ (Set.Icc (-(n : ℝ)) n)‖₊ : ENNReal)

end ComplexSpectralMeasure

/-! ### Integration against complex spectral measures -/

/-- A simple function approximation on [-N, N] with n subdivision points.
    Represents f ≈ Σₖ f(k/n) χ_{[k/n, (k+1)/n)} for k from -Nn to Nn-1. -/
def simpleApprox (f : ℝ → ℂ) (N n : ℕ) : Fin (2 * N * n + 1) → (ℂ × Set ℝ) := fun i =>
  let k : ℤ := i.val - N * n
  (f (k / n), Set.Ico (k / n : ℝ) ((k + 1) / n))

/-- The integral of a simple function against a complex spectral measure.
    ∫ (Σᵢ cᵢ χ_{Eᵢ}) dμ = Σᵢ cᵢ μ(Eᵢ) -/
def simpleIntegral (μ : ComplexSpectralMeasure H) (N n : ℕ) (f : ℝ → ℂ) : ℂ :=
  ∑ i : Fin (2 * N * n + 1),
    let (c, E) := simpleApprox f N n i
    c * μ.toFun E

omit [CompleteSpace H] in
/-- Bound on a single simple integral: |simpleIntegral μ N n f| ≤ M · totalVar_bound
    for f with ‖f‖_∞ ≤ M. -/
theorem simpleIntegral_bound (μ : ComplexSpectralMeasure H) (f : ℝ → ℂ)
    (M : ℝ) (hM : ∀ x, ‖f x‖ ≤ M) (hM_pos : 0 ≤ M) (N n : ℕ) :
    ‖simpleIntegral μ N n f‖ ≤ M * μ.totalVar_bound := by
  -- |Σᵢ f(xᵢ) μ(Iᵢ)| ≤ Σᵢ |f(xᵢ)| |μ(Iᵢ)| ≤ M Σᵢ |μ(Iᵢ)| ≤ M · totalVar_bound
  unfold simpleIntegral
  have h1 : ‖∑ i : Fin (2 * N * n + 1), (simpleApprox f N n i).1 * μ.toFun (simpleApprox f N n i).2‖
      ≤ ∑ i : Fin (2 * N * n + 1), ‖(simpleApprox f N n i).1 * μ.toFun (simpleApprox f N n i).2‖ :=
    norm_sum_le _ _
  have h2 : ∀ i, ‖(simpleApprox f N n i).1 * μ.toFun (simpleApprox f N n i).2‖
      = ‖(simpleApprox f N n i).1‖ * ‖μ.toFun (simpleApprox f N n i).2‖ := fun i => norm_mul _ _
  have h3 : ∀ i, ‖(simpleApprox f N n i).1‖ ≤ M := by
    intro i
    simp only [simpleApprox]
    exact hM _
  calc ‖∑ i : Fin (2 * N * n + 1), (fun i => (simpleApprox f N n i).1 * μ.toFun (simpleApprox f N n i).2) i‖
      ≤ ∑ i : Fin (2 * N * n + 1), ‖(simpleApprox f N n i).1 * μ.toFun (simpleApprox f N n i).2‖ := h1
    _ = ∑ i : Fin (2 * N * n + 1), ‖(simpleApprox f N n i).1‖ * ‖μ.toFun (simpleApprox f N n i).2‖ := by
        congr 1; ext i; exact h2 i
    _ ≤ ∑ i : Fin (2 * N * n + 1), M * ‖μ.toFun (simpleApprox f N n i).2‖ := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (h3 i) (norm_nonneg _)
    _ = M * ∑ i : Fin (2 * N * n + 1), ‖μ.toFun (simpleApprox f N n i).2‖ := by rw [Finset.mul_sum]
    _ ≤ M * μ.totalVar_bound := by
        apply mul_le_mul_of_nonneg_left _ hM_pos
        -- The intervals (simpleApprox f N n i).2 are disjoint Ico intervals [k/n, (k+1)/n)
        -- By totalVar_finite, sum of norms is bounded by totalVar_bound
        -- Define E : ℕ → Set ℝ extending the Fin-indexed intervals
        let E : ℕ → Set ℝ := fun i =>
          if h : i < 2 * N * n + 1 then (simpleApprox f N n ⟨i, h⟩).2 else ∅
        -- The intervals are disjoint: [k₁/n, (k₁+1)/n) ∩ [k₂/n, (k₂+1)/n) = ∅ for k₁ ≠ k₂
        have hE_disj : ∀ i j, i ≠ j → Disjoint (E i) (E j) := by
          intro i j hij
          simp only [E]
          split_ifs with hi hj hj
          · -- Both in range: the Ico intervals [kᵢ/n, (kᵢ+1)/n) are disjoint for i ≠ j
            simp only [simpleApprox, Set.disjoint_iff]
            intro x ⟨hxi, hxj⟩
            -- x ∈ [kᵢ/n, (kᵢ+1)/n) ∩ [kⱼ/n, (kⱼ+1)/n) with i ≠ j is impossible
            -- The intervals are consecutive and non-overlapping
            have hk_neq : (↑i : ℤ) - ↑N * ↑n ≠ (↑j : ℤ) - ↑N * ↑n := by omega
            -- Standard Ico disjointness for integer endpoints
            by_cases hn : n = 0
            · simp [hn] at hxi
            · -- For n > 0, Ico intervals with different integer offsets are disjoint
              have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
              -- From hxi: ki/n ≤ x < (ki+1)/n, from hxj: kj/n ≤ x < (kj+1)/n
              -- This means ki ≤ nx < ki+1 and kj ≤ nx < kj+1
              -- So ki and kj differ by < 1 in each direction, meaning ki = kj
              have h1 := hxi.1  -- (i - Nn)/n ≤ x
              have h2 := hxi.2  -- x < (i - Nn + 1)/n
              have h3 := hxj.1  -- (j - Nn)/n ≤ x
              have h4 := hxj.2  -- x < (j - Nn + 1)/n
              have hlt1 : (↑i : ℤ) - ↑N * ↑n < (↑j : ℤ) - ↑N * ↑n + 1 := by
                have := lt_of_le_of_lt h1 h4
                rw [div_lt_div_iff_of_pos_right hn_pos] at this
                exact_mod_cast this
              have hlt2 : (↑j : ℤ) - ↑N * ↑n < (↑i : ℤ) - ↑N * ↑n + 1 := by
                have := lt_of_le_of_lt h3 h2
                rw [div_lt_div_iff_of_pos_right hn_pos] at this
                exact_mod_cast this
              omega
          · exact Set.disjoint_empty _
          · exact Set.empty_disjoint _
          · exact Set.disjoint_empty _
        -- Apply totalVar_finite
        have hbound := μ.totalVar_finite E hE_disj (2 * N * n + 1)
        -- Convert Fin sum to Finset.range sum
        have heq : ∑ i : Fin (2 * N * n + 1), ‖μ.toFun (simpleApprox f N n i).2‖
            = ∑ i ∈ Finset.range (2 * N * n + 1), ‖μ.toFun (E i)‖ := by
          rw [Finset.sum_fin_eq_sum_range]
          apply Finset.sum_congr rfl
          intro i hi
          simp only [Finset.mem_range] at hi
          simp only [E, hi, dif_pos]
        rw [heq]
        exact hbound

/-- For a bounded series of nonnegative terms, the partial sums are monotone increasing
    and bounded, hence the tail goes to 0.

    Given: ∀ n, ∑ᵢ<n aᵢ ≤ C (where aᵢ ≥ 0)
    Then: ∀ ε > 0, ∃ N₀, ∀ m > n ≥ N₀, ∑ᵢ∈[n,m) aᵢ < ε

    This is the Cauchy property for the partial sums of a bounded nonneg series. -/
theorem bounded_nonneg_series_cauchy {a : ℕ → ℝ} (ha_nonneg : ∀ i, 0 ≤ a i)
    (C : ℝ) (hC : ∀ n, ∑ i ∈ Finset.range n, a i ≤ C) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ m n : ℕ, N₀ ≤ n → n ≤ m →
      ∑ i ∈ Finset.Ico n m, a i < ε := by
  intro ε hε
  -- The partial sums form a bounded monotone sequence, hence convergent
  let S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, a i
  have h_mono : Monotone S := by
    intro n m hnm
    simp only [S]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi; exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hnm)
    · intro i _ _; exact ha_nonneg i
  have h_bdd : BddAbove (Set.range S) := by
    use C
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact hC n
  -- Monotone bounded sequence converges, hence is Cauchy
  have h_conv : ∃ L, Tendsto S atTop (nhds L) := by
    use ⨆ n, S n
    exact tendsto_atTop_ciSup h_mono h_bdd
  obtain ⟨L, hL⟩ := h_conv
  rw [Metric.tendsto_atTop] at hL
  obtain ⟨N₀, hN₀⟩ := hL (ε / 2) (by linarith)
  use N₀
  intro m n hn_ge hn_le
  -- The sum over [n, m) equals S(m) - S(n)
  have hdiff : ∑ i ∈ Finset.Ico n m, a i = S m - S n := by
    simp only [S]
    have hsub : Finset.range n ⊆ Finset.range m := Finset.range_mono hn_le
    have hsdiff : Finset.range m \ Finset.range n = Finset.Ico n m := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [← Finset.sum_sdiff hsub, hsdiff, add_sub_cancel_right]
  rw [hdiff]
  have h1 := hN₀ m (le_trans hn_ge hn_le)
  have h2 := hN₀ n hn_ge
  rw [dist_eq_norm, Real.norm_eq_abs] at h1 h2
  -- S m - S n ≤ |S m - L| + |S n - L| by triangle inequality
  have h_tri : S m - S n ≤ |S m - L| + |S n - L| := by
    have heq : S m - S n = (S m - L) + (L - S n) := by ring
    calc S m - S n = (S m - L) + (L - S n) := heq
      _ ≤ |S m - L| + |L - S n| := add_le_add (le_abs_self _) (le_abs_self _)
      _ = |S m - L| + |S n - L| := by rw [abs_sub_comm L (S n)]
  calc S m - S n ≤ |S m - L| + |S n - L| := h_tri
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

/-- Annulus variation: the total variation of μ on the annulus [k, k+1) ∪ [-k-1, -k).
    This is used to show tail decay for spectral integrals. -/
def annulusVariation (μ : ComplexSpectralMeasure H) (k : ℕ) : ℝ :=
  ‖μ.toFun (Set.Ico (k : ℝ) (k + 1))‖ + ‖μ.toFun (Set.Ico (-(k + 1 : ℝ)) (-k))‖

omit [CompleteSpace H] in
theorem annulusVariation_nonneg (μ : ComplexSpectralMeasure H) (k : ℕ) :
    0 ≤ annulusVariation μ k := by
  unfold annulusVariation
  apply add_nonneg <;> exact norm_nonneg _

omit [CompleteSpace H] in
theorem annulusVariation_sum_bounded (μ : ComplexSpectralMeasure H) :
    ∀ n, ∑ k ∈ Finset.range n, annulusVariation μ k ≤ μ.totalVar_bound := by
  intro n
  unfold annulusVariation
  -- The intervals [k, k+1) and [-k-1, -k) for k = 0, 1, ..., n-1 are all disjoint
  -- and their total variation is bounded by totalVar_bound
  -- We construct the disjoint sequence E_i that covers all these intervals
  let E : ℕ → Set ℝ := fun i =>
    if i < n then Set.Ico (i : ℝ) (i + 1)
    else if i < 2 * n then Set.Ico (-(i - n + 1 : ℝ)) (-(i - n : ℝ))
    else ∅
  have hE_disj : ∀ i j, i ≠ j → Disjoint (E i) (E j) := by
    intro i j hij
    simp only [E]
    split_ifs with hi hj hj' hi' hj'' hj'''
    · -- Both in [0, n): intervals [i, i+1) and [j, j+1) for i ≠ j
      apply Set.disjoint_iff.mpr
      intro x ⟨hxi, hxj⟩
      have h1 := hxi.1; have h2 := hxi.2; have h3 := hxj.1; have h4 := hxj.2
      have : (i : ℤ) = j := by
        have hi' : (i : ℝ) ≤ x := h1
        have hi'' : x < i + 1 := h2
        have hj' : (j : ℝ) ≤ x := h3
        have hj'' : x < j + 1 := h4
        have h5 : (i : ℝ) < j + 1 := lt_of_le_of_lt hi' hj''
        have h6 : (j : ℝ) < i + 1 := lt_of_le_of_lt hj' hi''
        have h7 : (i : ℤ) < j + 1 := by exact_mod_cast h5
        have h8 : (j : ℤ) < i + 1 := by exact_mod_cast h6
        omega
      exact hij (Nat.cast_injective this)
    · -- i in [0, n), j in [n, 2n): [i, i+1) ∩ [-(j-n+1), -(j-n)) = ∅
      -- because [i, i+1) ⊂ [0, ∞) and [-(j-n+1), -(j-n)) ⊂ (-∞, 0]
      apply Set.disjoint_iff.mpr
      intro x ⟨hxi, hxj⟩
      have h1 := hxi.1  -- i ≤ x
      have h4 := hxj.2  -- x < -(j - n)
      have hi_nn : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      have hj_ge_n : j ≥ n := Nat.not_lt.mp hj
      have hj_n_nn : (0 : ℝ) ≤ j - n := by
        have : (n : ℝ) ≤ j := by exact_mod_cast hj_ge_n
        linarith
      have h5 : x < 0 := by linarith
      have h6 : x ≥ 0 := le_trans hi_nn h1
      linarith
    · exact Set.disjoint_empty _
    · -- i in [n, 2n), j in [0, n): symmetric to case 2
      apply Set.disjoint_iff.mpr
      intro x ⟨hxi, hxj⟩
      have h3 := hxj.1  -- j ≤ x
      have h2 := hxi.2  -- x < -(i - n)
      have hj_nn : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hi_ge_n : i ≥ n := Nat.not_lt.mp hi
      have hi_n_nn : (0 : ℝ) ≤ i - n := by
        have : (n : ℝ) ≤ i := by exact_mod_cast hi_ge_n
        linarith
      have h5 : x < 0 := by linarith
      have h6 : x ≥ 0 := le_trans hj_nn h3
      linarith
    · -- Both in [n, 2n): intervals [-(i-n+1), -(i-n)) and [-(j-n+1), -(j-n)) for i ≠ j
      apply Set.disjoint_iff.mpr
      intro x ⟨hxi, hxj⟩
      have h1 := hxi.1; have h2 := hxi.2; have h3 := hxj.1; have h4 := hxj.2
      -- -(i-n+1) ≤ x < -(i-n) and -(j-n+1) ≤ x < -(j-n)
      -- This means i-n ≤ -x-1 < i-n+1 and j-n ≤ -x-1 < j-n+1
      -- So i-n = floor(-x-1) = j-n, hence i = j
      have h5 : -(i - n + 1 : ℝ) < -(j - n : ℝ) := lt_of_le_of_lt h1 h4
      have h6 : -(j - n + 1 : ℝ) < -(i - n : ℝ) := lt_of_le_of_lt h3 h2
      have h7 : (i : ℝ) - n - 1 < j - n := by linarith
      have h8 : (j : ℝ) - n - 1 < i - n := by linarith
      have h9 : (i : ℝ) < j + 1 := by linarith
      have h10 : (j : ℝ) < i + 1 := by linarith
      have h11 : i < j + 1 := by exact_mod_cast h9
      have h12 : j < i + 1 := by exact_mod_cast h10
      have h13 : i = j := by omega
      exact hij h13
    · exact Set.disjoint_empty _
    · exact Set.empty_disjoint _
    · exact Set.empty_disjoint _
    · exact Set.disjoint_empty _
  -- The sum splits into positive and negative parts
  have heq : ∑ k ∈ Finset.range n, (‖μ.toFun (Set.Ico (k : ℝ) (k + 1))‖ +
      ‖μ.toFun (Set.Ico (-(k + 1 : ℝ)) (-k))‖) =
      ∑ i ∈ Finset.range (2 * n), ‖μ.toFun (E i)‖ := by
    rw [Finset.sum_add_distrib]
    have h1 : ∑ k ∈ Finset.range n, ‖μ.toFun (Set.Ico (k : ℝ) (k + 1))‖ =
        ∑ i ∈ Finset.range n, ‖μ.toFun (E i)‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [E, Finset.mem_range] at hk ⊢
      simp only [hk, ↓reduceIte]
    have h2 : ∑ k ∈ Finset.range n, ‖μ.toFun (Set.Ico (-(k + 1 : ℝ)) (-k))‖ =
        ∑ i ∈ Finset.Ico n (2 * n), ‖μ.toFun (E i)‖ := by
      rw [Finset.sum_Ico_eq_sum_range]
      have hrng : 2 * n - n = n := by omega
      rw [hrng]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [E, Finset.mem_range] at hk ⊢
      have h_lt : n + k < 2 * n := by omega
      have h_ge : ¬(n + k < n) := by omega
      rw [if_neg h_ge, if_pos h_lt]
      -- Show the sets are equal: -(k+1) = -((n+k) - n + 1) and -k = -((n+k) - n)
      have hset : Set.Ico (-(k + 1 : ℝ)) (-(k : ℝ)) =
          Set.Ico (-((n + k : ℕ) - (n : ℕ) + 1 : ℝ)) (-((n + k : ℕ) - (n : ℕ) : ℝ)) := by
        have h1 : ((n + k : ℕ) - (n : ℕ) : ℝ) = (k : ℝ) := by
          simp only [Nat.cast_add, add_sub_cancel_left]
        rw [h1]
      rw [hset]
    rw [h1, h2]
    have hrange : Finset.range (2 * n) = Finset.range n ∪ Finset.Ico n (2 * n) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
      omega
    have hdisj : Disjoint (Finset.range n) (Finset.Ico n (2 * n)) := by
      simp only [Finset.disjoint_iff_ne]
      intro a ha b hb hab
      simp only [Finset.mem_range] at ha
      simp only [Finset.mem_Ico] at hb
      omega
    rw [hrange, Finset.sum_union hdisj]
  rw [heq]
  have hbound := μ.totalVar_finite E hE_disj (2 * n)
  exact hbound

/-! ### Spectral integral for operators

Note: The Cauchy sequence approach to spectral integrals (simpleIntegral_diagonal_cauchy
and complexSpectralIntegral) has been moved to SpectralIntegralCauchy.lean to keep
this file sorry-free. Those definitions are NOT needed for the RMK-based spectral
theorem approach - only sesquilinearToOperator below is needed.
-/

/-- A bounded linear operator defined by a sesquilinear form.
    Given a bounded sesquilinear form B : H × H → ℂ with |B(x,y)| ≤ C‖x‖‖y‖,
    there exists a unique T ∈ B(H) such that B(x,y) = ⟨x, Ty⟩.

    This is the Riesz representation theorem for bounded sesquilinear forms.
    The proof uses Mathlib's Fréchet-Riesz theorem:
    1. For each y, B(·, y) is a bounded conjugate-linear functional
    2. By Fréchet-Riesz, B(x, y) = ⟨z_y, x⟩ for unique z_y
    3. The map y ↦ z_y is the desired operator T (after taking adjoint) -/
theorem sesquilinear_to_operator (B : H → H → ℂ)
    (hB_linear_right : ∀ x, IsLinearMap ℂ (B x))
    (hB_conj_linear_left : ∀ y c x₁ x₂, B (c • x₁ + x₂) y = starRingEnd ℂ c * B x₁ y + B x₂ y)
    (hB_bounded : ∃ C : ℝ, ∀ x y, ‖B x y‖ ≤ C * ‖x‖ * ‖y‖) :
    ∃! T : H →L[ℂ] H, ∀ x y, B x y = @inner ℂ H _ x (T y) := by
  /-
  PROOF using Fréchet-Riesz theorem (Mathlib's InnerProductSpace.toDual):

  **Construction:**
  1. For each y ∈ H, the map x ↦ conj(B(x, y)) is linear in x (by hB_conj_linear_left).
  2. It is bounded: |conj(B(x, y))| = |B(x, y)| ≤ C‖x‖‖y‖.
  3. By Fréchet-Riesz, there exists unique T(y) with conj(B(x, y)) = ⟨T(y), x⟩ = conj(⟨x, T(y)⟩).
  4. Therefore B(x, y) = ⟨x, T(y)⟩.
  5. The map y ↦ T(y) is linear (from linearity of B in y) and bounded.

  **Uniqueness:**
  If ⟨x, T₁y⟩ = ⟨x, T₂y⟩ for all x, y, then T₁ = T₂.
  -/
  obtain ⟨C_bound, hC⟩ := hB_bounded
  -- Step 1: For each y, construct the bounded linear functional ℓ_y(x) = star(B(x, y))
  -- This is linear because B is conjugate-linear in x.
  -- Define ℓ_y as a CLM
  have hℓ_exists : ∀ y : H, ∃ ℓ : H →L[ℂ] ℂ, ∀ x, ℓ x = star (B x y) := by
    intro y
    -- The map x ↦ star(B(x, y)) is linear
    let ℓ_fun : H → ℂ := fun x => star (B x y)
    have hℓ_add : ∀ x₁ x₂, ℓ_fun (x₁ + x₂) = ℓ_fun x₁ + ℓ_fun x₂ := by
      intro x₁ x₂
      simp only [ℓ_fun]
      have h := hB_conj_linear_left y 1 x₁ x₂
      simp only [one_smul, starRingEnd_apply, star_one, one_mul] at h
      rw [h, star_add]
    have hℓ_smul : ∀ (c : ℂ) (x : H), ℓ_fun (c • x) = c • ℓ_fun x := by
      intro c x
      show star (B (c • x) y) = (c : ℂ) * star (B x y)
      have h := hB_conj_linear_left y c x 0
      simp only [add_zero] at h
      have hB0 : B 0 y = 0 := by
        -- Use: B(1·0 + 0) = star(1)·B(0) + B(0) = 2·B(0)
        -- But  B(1·0 + 0) = B(0)
        -- So B(0) = 2·B(0), hence B(0) = 0
        have h1 := hB_conj_linear_left y 1 0 0
        simp only [one_smul, add_zero, starRingEnd_apply, star_one, one_mul] at h1
        -- h1 : B 0 y = B 0 y + B 0 y, i.e., a = a + a, so a = 0
        have : B 0 y + B 0 y = B 0 y := h1.symm
        calc B 0 y = B 0 y + 0 := (add_zero _).symm
          _ = B 0 y + (B 0 y - B 0 y) := by ring
          _ = (B 0 y + B 0 y) - B 0 y := by ring
          _ = B 0 y - B 0 y := by rw [this]
          _ = 0 := sub_self _
      rw [hB0, add_zero] at h
      rw [h]
      simp only [starRingEnd_apply, star_mul', star_star]
    let ℓ_lin : H →ₗ[ℂ] ℂ := {
      toFun := ℓ_fun
      map_add' := hℓ_add
      map_smul' := hℓ_smul
    }
    -- Show bounded
    have hℓ_bdd : ∃ M : ℝ, ∀ x, ‖ℓ_lin x‖ ≤ M * ‖x‖ := by
      use max C_bound 0 * ‖y‖
      intro x
      -- ℓ_lin x = ℓ_fun x = star (B x y)
      show ‖star (B x y)‖ ≤ _
      rw [norm_star]
      calc ‖B x y‖ ≤ C_bound * ‖x‖ * ‖y‖ := hC x y
        _ ≤ max C_bound 0 * ‖x‖ * ‖y‖ := by
            apply mul_le_mul_of_nonneg_right
            apply mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
            exact norm_nonneg _
        _ = (max C_bound 0 * ‖y‖) * ‖x‖ := by ring
    obtain ⟨M, hM⟩ := hℓ_bdd
    -- Convert to CLM
    have hcont : Continuous ℓ_lin := by
      apply AddMonoidHomClass.continuous_of_bound ℓ_lin M
      intro x
      exact hM x
    exact ⟨⟨ℓ_lin, hcont⟩, fun x => rfl⟩
  -- Step 2: Apply Fréchet-Riesz to get T(y) for each y
  -- For functional ℓ, we have (toDual ℂ H).symm ℓ is the vector z with ⟨z, x⟩ = ℓ x
  let T_fun : H → H := fun y =>
    let ℓ := (hℓ_exists y).choose
    (InnerProductSpace.toDual ℂ H).symm ℓ
  -- Step 3: Show B(x, y) = ⟨x, T_fun y⟩
  have hB_eq : ∀ x y, B x y = @inner ℂ H _ x (T_fun y) := by
    intro x y
    simp only [T_fun]
    let ℓ := (hℓ_exists y).choose
    have hℓ_spec := (hℓ_exists y).choose_spec
    -- ⟨(toDual).symm ℓ, x⟩ = ℓ x = star(B(x, y))
    have h1 : @inner ℂ H _ ((InnerProductSpace.toDual ℂ H).symm ℓ) x = ℓ x :=
      InnerProductSpace.toDual_symm_apply
    have h2 : ℓ x = star (B x y) := hℓ_spec x
    -- ⟨z, x⟩ = star(B(x, y)) means B(x, y) = star(⟨z, x⟩) = ⟨x, z⟩
    have h3 : star (star (B x y)) = B x y := star_star _
    calc B x y = star (star (B x y)) := h3.symm
      _ = star (ℓ x) := by rw [h2]
      _ = star (@inner ℂ H _ ((InnerProductSpace.toDual ℂ H).symm ℓ) x) := by rw [h1]
      _ = @inner ℂ H _ x ((InnerProductSpace.toDual ℂ H).symm ℓ) := inner_conj_symm _ _
  -- Step 4: Show T_fun is linear
  have hT_add : ∀ y₁ y₂, T_fun (y₁ + y₂) = T_fun y₁ + T_fun y₂ := by
    intro y₁ y₂
    -- Use that inner product separates points
    apply ext_inner_left ℂ
    intro x
    -- ⟨x, T(y₁+y₂)⟩ = B(x, y₁+y₂) = B(x,y₁) + B(x,y₂) = ⟨x, Ty₁⟩ + ⟨x, Ty₂⟩ = ⟨x, Ty₁+Ty₂⟩
    have hlin := hB_linear_right x
    calc @inner ℂ H _ x (T_fun (y₁ + y₂)) = B x (y₁ + y₂) := (hB_eq x (y₁ + y₂)).symm
      _ = B x y₁ + B x y₂ := hlin.map_add y₁ y₂
      _ = @inner ℂ H _ x (T_fun y₁) + @inner ℂ H _ x (T_fun y₂) := by rw [hB_eq x y₁, hB_eq x y₂]
      _ = @inner ℂ H _ x (T_fun y₁ + T_fun y₂) := (inner_add_right _ _ _).symm
  have hT_smul : ∀ (c : ℂ) (y : H), T_fun (c • y) = c • T_fun y := by
    intro c y
    apply ext_inner_left ℂ
    intro x
    have hlin := hB_linear_right x
    calc @inner ℂ H _ x (T_fun (c • y)) = B x (c • y) := (hB_eq x (c • y)).symm
      _ = c • B x y := hlin.map_smul c y
      _ = c * @inner ℂ H _ x (T_fun y) := by rw [hB_eq x y]; rfl
      _ = @inner ℂ H _ x (c • T_fun y) := (inner_smul_right _ _ _).symm
  -- Step 5: Show T_fun is bounded
  have hT_bdd : ∃ M : ℝ, ∀ y, ‖T_fun y‖ ≤ M * ‖y‖ := by
    use max C_bound 0
    intro y
    by_cases hy : T_fun y = 0
    · rw [hy, norm_zero]; positivity
    · -- Use ‖z‖ = sup_{‖x‖=1} |⟨x, z⟩|
      -- We have |⟨x, T_fun y⟩| = |B(x, y)| ≤ C‖x‖‖y‖
      -- So ‖T_fun y‖ ≤ C‖y‖
      have h : ∀ x, ‖@inner ℂ H _ x (T_fun y)‖ ≤ max C_bound 0 * ‖x‖ * ‖y‖ := by
        intro x
        rw [← hB_eq x y]
        calc ‖B x y‖ ≤ C_bound * ‖x‖ * ‖y‖ := hC x y
          _ ≤ max C_bound 0 * ‖x‖ * ‖y‖ := by
              apply mul_le_mul_of_nonneg_right
              apply mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
              exact norm_nonneg _
      -- Use x = T_fun y to get ‖T_fun y‖² ≤ C‖T_fun y‖‖y‖
      have hself : ‖@inner ℂ H _ (T_fun y) (T_fun y)‖ ≤ max C_bound 0 * ‖T_fun y‖ * ‖y‖ :=
        h (T_fun y)
      have hnorm_sq : ‖@inner ℂ H _ (T_fun y) (T_fun y)‖ = ‖T_fun y‖^2 := by
        rw [inner_self_eq_norm_sq_to_K]
        -- Goal: ‖(↑‖T_fun y‖)^2‖ = ‖T_fun y‖^2
        -- (↑‖T_fun y‖)^2 = ↑(‖T_fun y‖^2) as real numbers
        rw [← RCLike.ofReal_pow]
        rw [RCLike.norm_ofReal, abs_of_nonneg (sq_nonneg _)]
      rw [hnorm_sq] at hself
      -- ‖T_fun y‖² ≤ C‖T_fun y‖‖y‖, and T_fun y ≠ 0, so ‖T_fun y‖ ≤ C‖y‖
      have hpos : 0 < ‖T_fun y‖ := norm_pos_iff.mpr hy
      calc ‖T_fun y‖ = ‖T_fun y‖^2 / ‖T_fun y‖ := by field_simp
        _ ≤ (max C_bound 0 * ‖T_fun y‖ * ‖y‖) / ‖T_fun y‖ := by
            apply div_le_div_of_nonneg_right hself hpos.le
        _ = max C_bound 0 * ‖y‖ := by field_simp
  -- Step 6: Construct T as a CLM
  obtain ⟨M, hM⟩ := hT_bdd
  let T_lin : H →ₗ[ℂ] H := {
    toFun := T_fun
    map_add' := hT_add
    map_smul' := hT_smul
  }
  have hT_cont : Continuous T_lin := by
    apply AddMonoidHomClass.continuous_of_bound T_lin M
    intro y
    exact hM y
  let T : H →L[ℂ] H := ⟨T_lin, hT_cont⟩
  -- Existence
  use T
  constructor
  · -- T satisfies the property
    intro x y
    exact hB_eq x y
  · -- Uniqueness
    intro T' hT'
    ext y
    apply ext_inner_left ℂ
    intro x
    have h1 : @inner ℂ H _ x (T y) = B x y := (hB_eq x y).symm
    have h2 : @inner ℂ H _ x (T' y) = B x y := (hT' x y).symm
    rw [h1, h2]

/-- Direct construction of an operator from a bounded sesquilinear form.

    This function directly constructs the unique operator T such that
    B(x, y) = ⟨x, T y⟩ for all x, y, WITHOUT using Classical.choose on an
    existential statement.

    **Construction via Fréchet-Riesz:**
    1. For each y, define ℓ_y : x ↦ conj(B(x, y)) (a continuous linear functional)
    2. Apply (toDual ℂ H).symm to get T y
    3. Then B(x, y) = ⟨x, T y⟩

    The uniqueness is guaranteed by the fact that inner products separate points. -/
noncomputable def sesquilinearToOperator (B : H → H → ℂ)
    (hB_linear_right : ∀ x, IsLinearMap ℂ (B x))
    (hB_conj_linear_left : ∀ y c x₁ x₂, B (c • x₁ + x₂) y = starRingEnd ℂ c * B x₁ y + B x₂ y)
    (hB_bounded : ∃ C : ℝ, ∀ x y, ‖B x y‖ ≤ C * ‖x‖ * ‖y‖) : H →L[ℂ] H :=
  -- Extract the bound
  let C_bound := hB_bounded.choose
  let hC := hB_bounded.choose_spec
  -- For each y, construct the continuous linear functional ℓ_y : x ↦ conj(B(x, y))
  -- Then T y = (toDual ℂ H).symm ℓ_y
  let T_fun : H → H := fun y =>
    -- The functional x ↦ conj(B(x, y)) is linear (conjugate of conjugate-linear = linear)
    let ℓ_lin : H →ₗ[ℂ] ℂ := {
      toFun := fun x => star (B x y)
      map_add' := fun x₁ x₂ => by
        have h := hB_conj_linear_left y 1 x₁ x₂
        simp only [one_smul, map_one, one_mul] at h
        simp only [h, star_add]
      map_smul' := fun c x => by
        have h := hB_conj_linear_left y c x 0
        simp only [add_zero] at h
        -- B 0 y = 0 from conjugate-linearity: B(1·0 + 0) y = 1·B(0)y + B(0)y implies B(0)y = 0
        have hB0 : B 0 y = 0 := by
          have h0 := hB_conj_linear_left y 1 0 0
          simp only [one_smul, add_zero, map_one, one_mul] at h0
          -- h0 : B 0 y = B 0 y + B 0 y, so B 0 y = 0
          have : B 0 y + B 0 y = B 0 y + 0 := by rw [add_zero]; exact h0.symm
          exact add_left_cancel this
        rw [h, hB0, add_zero, star_mul', starRingEnd_apply, star_star]
        rfl
    }
    -- Show ℓ_lin is bounded
    have hℓ_bdd : ∃ M : ℝ, ∀ x, ‖ℓ_lin x‖ ≤ M * ‖x‖ := by
      use max C_bound 0 * ‖y‖
      intro x
      calc ‖star (B x y)‖ = ‖B x y‖ := by rw [norm_star]
        _ ≤ C_bound * ‖x‖ * ‖y‖ := hC x y
        _ ≤ max C_bound 0 * ‖x‖ * ‖y‖ := by
            apply mul_le_mul_of_nonneg_right
            apply mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
            exact norm_nonneg _
        _ = (max C_bound 0 * ‖y‖) * ‖x‖ := by ring
    let M := hℓ_bdd.choose
    let hM := hℓ_bdd.choose_spec
    let ℓ : H →L[ℂ] ℂ := ⟨ℓ_lin, AddMonoidHomClass.continuous_of_bound ℓ_lin M hM⟩
    -- Apply Fréchet-Riesz: get the unique z with ⟨z, x⟩ = ℓ x
    (InnerProductSpace.toDual ℂ H).symm ℓ
  -- Helper: compute ⟨x, T_fun y⟩ = B x y
  have hT_inner : ∀ x y, @inner ℂ H _ x (T_fun y) = B x y := by
    intro x y
    -- T_fun y = (toDual).symm ℓ where ℓ x = star(B x y)
    -- We need: ⟨x, T_fun y⟩ = B x y
    -- toDual_symm_apply: ⟨(toDual).symm ℓ, x⟩ = ℓ x = star(B x y)
    -- So: ⟨x, T_fun y⟩ = star(⟨T_fun y, x⟩) = star(star(B x y)) = B x y
    have h1 : @inner ℂ H _ (T_fun y) x = star (B x y) := by
      simp only [T_fun]
      exact InnerProductSpace.toDual_symm_apply
    calc @inner ℂ H _ x (T_fun y)
        = star (@inner ℂ H _ (T_fun y) x) := (inner_conj_symm _ _).symm
      _ = star (star (B x y)) := by rw [h1]
      _ = B x y := star_star _
  -- Show T_fun is linear
  have hT_add : ∀ y₁ y₂, T_fun (y₁ + y₂) = T_fun y₁ + T_fun y₂ := by
    intro y₁ y₂
    apply ext_inner_left ℂ
    intro x
    rw [hT_inner, inner_add_right, hT_inner, hT_inner]
    exact (hB_linear_right x).map_add y₁ y₂
  have hT_smul : ∀ (c : ℂ) (y : H), T_fun (c • y) = c • T_fun y := by
    intro c y
    apply ext_inner_left ℂ
    intro x
    rw [hT_inner, inner_smul_right, hT_inner]
    exact (hB_linear_right x).map_smul c y
  -- Show T_fun is bounded
  have hT_bdd : ∃ M : ℝ, ∀ y, ‖T_fun y‖ ≤ M * ‖y‖ := by
    use max C_bound 0
    intro y
    by_cases hy : T_fun y = 0
    · rw [hy, norm_zero]; positivity
    · have h : ∀ x, ‖@inner ℂ H _ x (T_fun y)‖ ≤ max C_bound 0 * ‖x‖ * ‖y‖ := by
        intro x
        rw [hT_inner]
        calc ‖B x y‖ ≤ C_bound * ‖x‖ * ‖y‖ := hC x y
          _ ≤ max C_bound 0 * ‖x‖ * ‖y‖ := by
              apply mul_le_mul_of_nonneg_right
              apply mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
              exact norm_nonneg _
      have hself : ‖@inner ℂ H _ (T_fun y) (T_fun y)‖ ≤ max C_bound 0 * ‖T_fun y‖ * ‖y‖ :=
        h (T_fun y)
      have hnorm_sq : ‖@inner ℂ H _ (T_fun y) (T_fun y)‖ = ‖T_fun y‖^2 := by
        rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.norm_ofReal, abs_of_nonneg (sq_nonneg _)]
      rw [hnorm_sq] at hself
      have hpos : 0 < ‖T_fun y‖ := norm_pos_iff.mpr hy
      calc ‖T_fun y‖ = ‖T_fun y‖^2 / ‖T_fun y‖ := by field_simp
        _ ≤ (max C_bound 0 * ‖T_fun y‖ * ‖y‖) / ‖T_fun y‖ := by
            apply div_le_div_of_nonneg_right hself hpos.le
        _ = max C_bound 0 * ‖y‖ := by field_simp
  -- Construct as CLM
  let M := hT_bdd.choose
  let hM := hT_bdd.choose_spec
  let T_lin : H →ₗ[ℂ] H := {
    toFun := T_fun
    map_add' := hT_add
    map_smul' := hT_smul
  }
  ⟨T_lin, AddMonoidHomClass.continuous_of_bound T_lin M hM⟩

/-- The direct construction satisfies B(x, y) = ⟨x, T y⟩. -/
theorem sesquilinearToOperator_inner (B : H → H → ℂ)
    (hB_linear_right : ∀ x, IsLinearMap ℂ (B x))
    (hB_conj_linear_left : ∀ y c x₁ x₂, B (c • x₁ + x₂) y = starRingEnd ℂ c * B x₁ y + B x₂ y)
    (hB_bounded : ∃ C : ℝ, ∀ x y, ‖B x y‖ ≤ C * ‖x‖ * ‖y‖)
    (x y : H) :
    B x y = @inner ℂ H _ x (sesquilinearToOperator B hB_linear_right hB_conj_linear_left hB_bounded y) := by
  -- Use the existing sesquilinear_to_operator uniqueness
  have hexists := sesquilinear_to_operator B hB_linear_right hB_conj_linear_left hB_bounded
  -- The operator we construct also satisfies the defining property
  -- So by uniqueness, it equals the Classical.choose, which has the property
  have hT_prop := hexists.choose_spec.1
  -- sesquilinearToOperator equals Classical.choose by uniqueness
  have heq : sesquilinearToOperator B hB_linear_right hB_conj_linear_left hB_bounded =
      hexists.choose := by
    apply hexists.choose_spec.2
    intro a b
    -- Need: B a b = ⟨a, sesquilinearToOperator ... b⟩
    unfold sesquilinearToOperator
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
    -- Goal: B a b = ⟨a, (toDual).symm ℓ⟩ where ℓ x = star(B x b)
    -- inner_conj_symm says: star (inner x y) = inner y x
    -- So: inner a z = star (inner z a)
    -- And: inner ((toDual).symm ℓ) a = ℓ a = star(B a b) by toDual_symm_apply
    -- Thus: inner a ((toDual).symm ℓ) = star(star(B a b)) = B a b
    symm
    calc @inner ℂ H _ a ((InnerProductSpace.toDual ℂ H).symm _)
        = star (@inner ℂ H _ ((InnerProductSpace.toDual ℂ H).symm _) a) := (inner_conj_symm _ _).symm
      _ = star (star (B a b)) := by
          simp only [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.coe_mk',
                     LinearMap.coe_mk, AddHom.coe_mk]
      _ = B a b := star_star _
  rw [heq]
  exact hT_prop x y

end
