/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.vNA.MeasureTheory.SpectralIntegral

/-!
# Spectral Integral via Cauchy Sequences

This file contains the Cauchy sequence approach to defining spectral integrals.
The main theorem `simpleIntegral_diagonal_cauchy` has ONE SORRY in the refined
analysis branch (when the crude bound doesn't work).

## Main definitions

* `complexSpectralIntegral` - the spectral integral ∫ f dμ defined as a limit

## Main results

* `simpleIntegral_diagonal_cauchy` - the diagonal Riemann sums form a Cauchy sequence

## Status

This file is separated from SpectralIntegral.lean to keep the latter sorry-free.
The sorry here requires decomposition infrastructure (splitting integrals into
core and tail parts) which is documented in /test/proofideas.lean.

Note: This machinery is NOT needed for the RMK-based spectral theorem approach
in SpectralTheoremViaRMK.lean, which only uses `sesquilinearToOperator`.
-/

noncomputable section

open scoped InnerProduct ComplexConjugate
open Filter Topology MeasureTheory

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For the diagonal sequence u(k) = simpleIntegral μ k k f, the sequence is Cauchy.
    This is the key step for defining the spectral integral.

    The proof uses the standard Riemann-Stieltjes argument:
    For bounded continuous f and measure μ with finite total variation,
    the Riemann sums converge because:
    1. f is uniformly continuous on compact sets (Heine-Cantor)
    2. The total variation bounds the approximation error
    3. Tail contributions decay due to finite total variation -/
theorem simpleIntegral_diagonal_cauchy (μ : ComplexSpectralMeasure H) (f : ℝ → ℂ)
    (hf_bdd : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M)
    (hf_cont : Continuous f) :
    CauchySeq (fun k => simpleIntegral μ k k f) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨M, hM⟩ := hf_bdd
  have hM_nonneg : 0 ≤ M := le_trans (norm_nonneg (f 0)) (hM 0)
  let M' := max M 1
  have hM'_pos : M' > 0 := lt_max_of_lt_right (by norm_num : (0 : ℝ) < 1)
  have hM_le_M' : M ≤ M' := le_max_left M 1
  have hbound := simpleIntegral_bound μ f M' (fun x => le_trans (hM x) hM_le_M') (le_of_lt hM'_pos)

  -- Get tail decay from annulusVariation
  have h_tail_decay := bounded_nonneg_series_cauchy (annulusVariation_nonneg μ)
      μ.totalVar_bound (annulusVariation_sum_bounded μ)

  -- Choose K for tail decay: tail annulusVariation sum < ε/(8M')
  have hε_tail : ε / (8 * M' + 8) > 0 := by positivity
  obtain ⟨K₁, hK₁⟩ := h_tail_decay (ε / (8 * M' + 8)) hε_tail

  -- Get uniform continuity modulus for f on [-K₁-1, K₁+1]
  have hcompact : IsCompact (Set.Icc (-(K₁ + 1 : ℝ)) (K₁ + 1)) := isCompact_Icc
  have hf_unif : UniformContinuousOn f (Set.Icc (-(K₁ + 1 : ℝ)) (K₁ + 1)) :=
    hcompact.uniformContinuousOn_of_continuous hf_cont.continuousOn

  -- Get δ from uniform continuity for ε/(4*totalVar+4)
  rw [Metric.uniformContinuousOn_iff] at hf_unif
  have hε_core : ε / (4 * (μ.totalVar_bound + 1)) > 0 := by
    apply div_pos hε
    linarith [μ.totalVar_bound_nonneg]
  obtain ⟨δ, hδ_pos, hδ⟩ := hf_unif (ε / (4 * (μ.totalVar_bound + 1))) hε_core

  -- Get K₂ such that mesh 1/K₂ < δ
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt δ⁻¹
  let K₂ := n₀ + 1
  have hK₂_pos : 0 < K₂ := Nat.succ_pos n₀
  have hK₂_mesh : (K₂ : ℝ)⁻¹ < δ := by
    have h1 : (0 : ℝ) < K₂ := Nat.cast_pos.mpr hK₂_pos
    rw [inv_lt_comm₀ h1 hδ_pos]
    have : (K₂ : ℝ) = n₀ + 1 := by simp [K₂]
    rw [this]
    calc δ⁻¹ < n₀ := hn₀
      _ < n₀ + 1 := by linarith

  -- Use N₀ = max K₁ K₂
  use max K₁ K₂
  intro m hm n hn
  simp only [dist_eq_norm]

  have hm_ge_K₁ : m ≥ K₁ := le_trans (le_max_left K₁ K₂) hm
  have hn_ge_K₁ : n ≥ K₁ := le_trans (le_max_left K₁ K₂) hn
  have hm_ge_K₂ : m ≥ K₂ := le_trans (le_max_right K₁ K₂) hm
  have hn_ge_K₂ : n ≥ K₂ := le_trans (le_max_right K₁ K₂) hn

  have hm_pos : 0 < m := lt_of_lt_of_le hK₂_pos hm_ge_K₂
  have hn_pos : 0 < n := lt_of_lt_of_le hK₂_pos hn_ge_K₂

  -- Tail bounds using annulusVariation decay
  have htail_m : ∑ k ∈ Finset.Ico K₁ m, annulusVariation μ k < ε / (8 * M' + 8) :=
    hK₁ m K₁ (le_refl K₁) hm_ge_K₁
  have htail_n : ∑ k ∈ Finset.Ico K₁ n, annulusVariation μ k < ε / (8 * M' + 8) :=
    hK₁ n K₁ (le_refl K₁) hn_ge_K₁

  -- The M'-weighted tail contributions
  have htail_m_weighted : M' * ∑ k ∈ Finset.Ico K₁ m, annulusVariation μ k < ε / 8 := by
    have h1 : M' * (ε / (8 * M' + 8)) ≤ ε / 8 := by
      have hne : 8 * M' + 8 ≠ 0 := by linarith
      have h8ne : (8 : ℝ) ≠ 0 := by norm_num
      have h2 : M' / (8 * M' + 8) ≤ 1 / 8 := by
        have h3 : 8 * M' ≤ 8 * M' + 8 := by linarith
        calc M' / (8 * M' + 8) ≤ M' / (8 * M') := by
              apply div_le_div_of_nonneg_left (le_of_lt hM'_pos) (by linarith) h3
          _ = 1 / 8 := by field_simp
      calc M' * (ε / (8 * M' + 8)) = ε * (M' / (8 * M' + 8)) := by ring
        _ ≤ ε * (1 / 8) := by apply mul_le_mul_of_nonneg_left h2 (le_of_lt hε)
        _ = ε / 8 := by ring
    calc M' * ∑ k ∈ Finset.Ico K₁ m, annulusVariation μ k
        < M' * (ε / (8 * M' + 8)) := by apply mul_lt_mul_of_pos_left htail_m hM'_pos
      _ ≤ ε / 8 := h1

  have htail_n_weighted : M' * ∑ k ∈ Finset.Ico K₁ n, annulusVariation μ k < ε / 8 := by
    have h1 : M' * (ε / (8 * M' + 8)) ≤ ε / 8 := by
      have hne : 8 * M' + 8 ≠ 0 := by linarith
      have h8ne : (8 : ℝ) ≠ 0 := by norm_num
      have h2 : M' / (8 * M' + 8) ≤ 1 / 8 := by
        have h3 : 8 * M' ≤ 8 * M' + 8 := by linarith
        calc M' / (8 * M' + 8) ≤ M' / (8 * M') := by
              apply div_le_div_of_nonneg_left (le_of_lt hM'_pos) (by linarith) h3
          _ = 1 / 8 := by field_simp
      calc M' * (ε / (8 * M' + 8)) = ε * (M' / (8 * M' + 8)) := by ring
        _ ≤ ε * (1 / 8) := by apply mul_le_mul_of_nonneg_left h2 (le_of_lt hε)
        _ = ε / 8 := by ring
    calc M' * ∑ k ∈ Finset.Ico K₁ n, annulusVariation μ k
        < M' * (ε / (8 * M' + 8)) := by apply mul_lt_mul_of_pos_left htail_n hM'_pos
      _ ≤ ε / 8 := h1

  -- Core bound using uniform continuity: on [-K₁, K₁], mesh < δ gives small f-differences
  -- The core contribution difference is bounded by (uniform continuity modulus) × totalVar
  -- For mesh 1/m, 1/n < δ, the core difference is < ε/(4*(totalVar+1)) × totalVar < ε/4
  have hcore_bound : ε / (4 * (μ.totalVar_bound + 1)) * μ.totalVar_bound < ε / 4 := by
    by_cases htv : μ.totalVar_bound = 0
    · simp [htv]; linarith
    · have htv_pos : μ.totalVar_bound > 0 := lt_of_le_of_ne μ.totalVar_bound_nonneg (Ne.symm htv)
      have h1 : μ.totalVar_bound / (μ.totalVar_bound + 1) < 1 := by
        rw [div_lt_one (by linarith : μ.totalVar_bound + 1 > 0)]
        linarith
      have hne : 4 * (μ.totalVar_bound + 1) ≠ 0 := by linarith
      have hne2 : μ.totalVar_bound + 1 ≠ 0 := by linarith
      calc ε / (4 * (μ.totalVar_bound + 1)) * μ.totalVar_bound
          = ε / 4 * (μ.totalVar_bound / (μ.totalVar_bound + 1)) := by field_simp
        _ < ε / 4 * 1 := by apply mul_lt_mul_of_pos_left h1 (by linarith : ε / 4 > 0)
        _ = ε / 4 := by ring

  -- When totalVar_bound = 0, all μ(E) = 0, so both integrals are 0 and the difference is trivially < ε
  by_cases htv : μ.totalVar_bound = 0
  · have hμ_zero : ∀ E, μ.toFun E = 0 := by
      intro E
      by_contra hne
      have hpos : 0 < ‖μ.toFun E‖ := norm_pos_iff.mpr hne
      let F : ℕ → Set ℝ := fun i => if i = 0 then E else ∅
      have hF_disj : ∀ i j, i ≠ j → Disjoint (F i) (F j) := by
        intro i j hij
        simp only [F]
        by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj, Set.disjoint_empty]
        · exact absurd (hi.trans hj.symm) hij
      have hbound' := μ.totalVar_finite F hF_disj 1
      simp only [F, Finset.range_one, Finset.sum_singleton, ↓reduceIte] at hbound'
      rw [htv] at hbound'
      linarith
    have h1 : simpleIntegral μ m m f = 0 := by
      unfold simpleIntegral
      apply Finset.sum_eq_zero
      intro i _
      simp only [simpleApprox]
      rw [hμ_zero, mul_zero]
    have h2 : simpleIntegral μ n n f = 0 := by
      unfold simpleIntegral
      apply Finset.sum_eq_zero
      intro i _
      simp only [simpleApprox]
      rw [hμ_zero, mul_zero]
    rw [h1, h2, sub_self, norm_zero]
    exact hε
  -- When totalVar_bound > 0, use the crude bound (which works when totalVar is small enough)
  -- or the refined analysis (which always works)
  · have htv_pos : μ.totalVar_bound > 0 := lt_of_le_of_ne μ.totalVar_bound_nonneg (Ne.symm htv)
    -- The key insight: the Riemann sums u(m) and u(n) both approximate the same limit (the integral).
    -- The difference |u(m) - u(n)| is bounded by the sum of their approximation errors.
    -- Each error decomposes into: core error (mesh refinement) + tail error (domain truncation).
    --
    -- For the diagonal sequence with m, n ≥ max K₁ K₂:
    -- - Core [-K₁, K₁]: mesh 1/m, 1/n < 1/K₂ < δ, so f-oscillation < ε/(4*totalVar+4)
    --   Core contribution to error: < ε/(4*totalVar+4) * totalVar < ε/4 for each, total < ε/2
    -- - Tail beyond K₁: bounded by M' * Σ annulusVar < M' * ε/(8M'+8) < ε/8 for each, total < ε/4
    -- Combined: < ε/2 + ε/4 = 3ε/4 < ε
    --
    -- For the formal proof, we use the crude bound when it works, otherwise refine.
    by_cases h_crude : 2 * M' * μ.totalVar_bound < ε
    · calc ‖simpleIntegral μ m m f - simpleIntegral μ n n f‖
          ≤ ‖simpleIntegral μ m m f‖ + ‖simpleIntegral μ n n f‖ := norm_sub_le _ _
        _ ≤ M' * μ.totalVar_bound + M' * μ.totalVar_bound := add_le_add (hbound m m) (hbound n n)
        _ = 2 * M' * μ.totalVar_bound := by ring
        _ < ε := h_crude
    · -- When crude bound doesn't work: ε ≤ 2*M'*totalVar
      -- We need the REFINED analysis using domain decomposition.
      --
      -- The key insight: ‖u(m) - u(n)‖ is NOT bounded by ‖u(m)‖ + ‖u(n)‖ (too crude).
      -- Instead, we decompose into core and tail contributions:
      --
      --   u(m) - u(n) = [u(m)|_core - u(n)|_core] + [u(m)|_tail - u(n)|_tail]
      --
      -- where core = [-K₁, K₁] and tail = complement.
      --
      -- For m, n ≥ max K₁ K₂:
      -- 1. Core difference: both use mesh < 1/K₂ < δ, so f-oscillation < ε/(4*totalVar+4)
      --    ‖u(m)|_core - u(n)|_core‖ < ε/4 (uniform continuity + small mesh)
      -- 2. Tail contribution: ‖u(m)|_tail‖ < ε/8 and ‖u(n)|_tail‖ < ε/8
      --    These follow from the annular variation decay in hK₁.
      --
      -- Total: ‖u(m) - u(n)‖ ≤ ε/4 + ε/8 + ε/8 = ε/2 < ε
      --
      -- The formal proof requires splitting simpleIntegral into core and tail parts:
      --   simpleIntegral μ m m f = simpleIntegral_core μ m m f K₁ + simpleIntegral_tail μ m m f K₁
      -- This decomposition lemma is not yet formalized.
      --
      -- MATHEMATICAL CORRECTNESS: The argument above is sound and standard in analysis.
      -- FORMALIZATION STATUS: Requires decomposition infrastructure.
      sorry

/-- For a bounded continuous function f and a complex spectral measure μ,
    the integral ∫ f dμ is defined as the limit of simple function approximations.

    The construction:
    1. Approximate f by step functions fₙ on [-N, N] with partition size n
    2. Define ∫ fₙ dμ = Σₖ f(xₖ) μ(Eₖ) where Eₖ = [k/n, (k+1)/n)
    3. The sequence is Cauchy: |∫ fₙ dμ - ∫ fₘ dμ| ≤ ‖fₙ - fₘ‖_∞ · |μ|(ℝ)
    4. Take the limit in ℂ (which is complete)

    The integral satisfies the standard properties:
    - Linearity: ∫ (αf + g) dμ = α∫ f dμ + ∫ g dμ
    - Indicator: ∫ χ_E dμ = μ(E)
    - Bound: |∫ f dμ| ≤ ‖f‖_∞ · |μ|(ℝ) -/
def complexSpectralIntegral (μ : ComplexSpectralMeasure H) (f : ℝ → ℂ)
    (hf_bdd : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) (hf_cont : Continuous f) : ℂ :=
  -- The limit of the diagonal simple function approximations u(k) = simpleIntegral μ k k f
  -- We use Classical.choose to select the limit value.
  -- The existence is guaranteed by:
  -- 1. The diagonal sequence is Cauchy (simpleIntegral_diagonal_cauchy)
  -- 2. ℂ is complete
  Classical.choose <| cauchySeq_tendsto_of_complete
    (simpleIntegral_diagonal_cauchy μ f hf_bdd hf_cont)

end
