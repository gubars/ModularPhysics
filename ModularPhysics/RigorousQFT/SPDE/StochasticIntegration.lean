/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.BrownianMotion
import ModularPhysics.RigorousQFT.SPDE.Probability.IndependenceHelpers
import ModularPhysics.RigorousQFT.SPDE.Helpers.L2LimitInfrastructure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Stochastic Integration (Itô Calculus)

This file develops stochastic integration with respect to Brownian motion
and more general semimartingales.

## Main Definitions

* `StochasticIntegral` - The Itô integral ∫₀ᵗ H_s dW_s
* `ItoProcess` - Processes of the form dX = μ dt + σ dW
* `ItoFormula` - Itô's formula for C² functions

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus"
* Revuz, Yor, "Continuous Martingales and Brownian Motion"
-/

namespace SPDE

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Simple Processes -/

/-- A simple (step) process defined by a finite partition -/
structure SimpleProcess (F : Filtration Ω ℝ) where
  /-- Number of partition points -/
  n : ℕ
  /-- The partition times (as a function) -/
  times : Fin n → ℝ
  /-- The values at each interval -/
  values : Fin n → Ω → ℝ
  /-- Partition is increasing -/
  increasing : ∀ i j : Fin n, i < j → times i < times j
  /-- Values are predictable (F_{t_{i-1}}-measurable) -/
  adapted : ∀ i : Fin n, (i : ℕ) > 0 →
    @Measurable Ω ℝ (F.σ_algebra (times ⟨i - 1, by omega⟩)) _ (values i)

namespace SimpleProcess

variable {F : Filtration Ω ℝ}

/-- The stochastic integral of a simple process w.r.t. Brownian motion -/
noncomputable def stochasticIntegral (H : SimpleProcess F) (W : BrownianMotion Ω μ) : Ω → ℝ :=
  fun ω =>
    ∑ i : Fin H.n, if h : (i : ℕ) + 1 < H.n then
      H.values i ω * (W.process (H.times ⟨i + 1, h⟩) ω - W.process (H.times i) ω)
    else 0

/-- The time-parameterized stochastic integral of a simple process.
    At time t, this includes:
    - Full summands Hᵢ · (W_{t_{i+1}} - W_{t_i}) for completed intervals [t_i, t_{i+1}] ⊂ [0, t]
    - Partial summand H_k · (W_t - W_{t_k}) for the interval containing t

    When t is past the last partition time, this equals `stochasticIntegral`.
    This is needed for the martingale property and L² limit characterization. -/
noncomputable def stochasticIntegral_at (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    (t : ℝ) : Ω → ℝ :=
  fun ω =>
    ∑ i : Fin H.n, if h : (i : ℕ) + 1 < H.n then
      if H.times ⟨i + 1, h⟩ ≤ t then
        H.values i ω * (W.process (H.times ⟨i + 1, h⟩) ω - W.process (H.times i) ω)
      else if H.times i ≤ t then
        H.values i ω * (W.process t ω - W.process (H.times i) ω)
      else 0
    else 0

/-! ### Helper lemmas for the Itô isometry -/

/-- Helper: for i-1 < j in a simple process, times (i-1) < times j -/
private theorem times_pred_lt_times (H : SimpleProcess F) {i j : Fin H.n}
    (hi0 : (i : ℕ) > 0) (hij : (i : ℕ) ≤ (j : ℕ)) :
    H.times ⟨(i : ℕ) - 1, by omega⟩ < H.times j := by
  apply H.increasing ⟨(i : ℕ) - 1, by omega⟩ j
  simp only [Fin.lt_def]; omega

/-- Cross-term vanishing: for i < j, E[Hᵢ·ΔWᵢ · Hⱼ·ΔWⱼ] = 0.

    Proof: regroup as E[(Hᵢ·ΔWᵢ·Hⱼ) · ΔWⱼ], show the first factor is
    F_{tⱼ}-measurable, ΔWⱼ is independent of F_{tⱼ} with zero mean,
    then apply integral factorization. -/
theorem cross_term_zero (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    [IsProbabilityMeasure μ]
    (hH_adapted_all : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (i j : Fin H.n)
    (hi : (i : ℕ) + 1 < H.n) (hj : (j : ℕ) + 1 < H.n)
    (hij : (i : ℕ) < (j : ℕ)) :
    ∫ ω, (H.values i ω * (W.process (H.times ⟨i + 1, hi⟩) ω - W.process (H.times i) ω)) *
         (H.values j ω * (W.process (H.times ⟨j + 1, hj⟩) ω - W.process (H.times j) ω)) ∂μ = 0 := by
  -- Regroup: (Hᵢ·ΔWᵢ) · (Hⱼ·ΔWⱼ) = (Hᵢ·ΔWᵢ·Hⱼ) · ΔWⱼ
  have hregroup : ∀ ω,
      (H.values i ω * (W.process (H.times ⟨i + 1, hi⟩) ω - W.process (H.times i) ω)) *
      (H.values j ω * (W.process (H.times ⟨j + 1, hj⟩) ω - W.process (H.times j) ω)) =
      (H.values i ω * (W.process (H.times ⟨i + 1, hi⟩) ω - W.process (H.times i) ω) * H.values j ω) *
      (W.process (H.times ⟨j + 1, hj⟩) ω - W.process (H.times j) ω) := by
    intro ω; ring
  simp_rw [hregroup]
  -- Ordering helper
  have hjj1 : H.times j < H.times ⟨(j : ℕ) + 1, hj⟩ :=
    H.increasing j ⟨(j : ℕ) + 1, hj⟩ (by simp [Fin.lt_def])
  have hii1 : H.times i < H.times ⟨(i : ℕ) + 1, hi⟩ :=
    H.increasing i ⟨(i : ℕ) + 1, hi⟩ (by simp [Fin.lt_def])
  have hij_times : H.times ⟨(i : ℕ) + 1, hi⟩ ≤ H.times j := by
    by_cases h : (i : ℕ) + 1 = (j : ℕ)
    · have : (⟨(i : ℕ) + 1, hi⟩ : Fin H.n) = j := by ext; exact h
      rw [this]
    · exact le_of_lt (H.increasing ⟨(i : ℕ) + 1, hi⟩ j (by
        simp only [Fin.lt_def]; omega))
  -- ΔWⱼ has zero mean
  have hΔW_mean : ∫ ω, (W.process (H.times ⟨(j : ℕ) + 1, hj⟩) ω -
      W.process (H.times j) ω) ∂μ = 0 :=
    W.increment_mean_zero _ _ (hH_times_nn j) (le_of_lt hjj1)
  -- ΔWⱼ is integrable
  have hΔW_int : Integrable (fun ω => W.process (H.times ⟨(j : ℕ) + 1, hj⟩) ω -
      W.process (H.times j) ω) μ :=
    W.increment_integrable _ _ (hH_times_nn j) (le_of_lt hjj1)
  -- Independence: ΔWⱼ is independent of F_{tⱼ}
  have hindep : Indep (W.F.σ_algebra (H.times j))
    (MeasurableSpace.comap (fun ω => W.process (H.times ⟨(j : ℕ) + 1, hj⟩) ω -
      W.process (H.times j) ω) inferInstance) μ :=
    W.independent_increments _ _ (hH_times_nn j) (le_of_lt hjj1)
  -- Show (Hᵢ·ΔWᵢ·Hⱼ) is F_{tⱼ}-measurable
  have hX_meas : @Measurable Ω ℝ (W.F.σ_algebra (H.times j)) _
      (fun ω => H.values i ω *
        (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω) *
        H.values j ω) := by
    apply Measurable.mul
    apply Measurable.mul
    · -- Hᵢ is F_{tᵢ}-measurable ≤ F_{tⱼ}
      have hij_fin : i < j := Fin.lt_def.mpr hij
      exact (hH_adapted_all i).mono (W.F.mono _ _ (le_of_lt (H.increasing i j hij_fin))) le_rfl
    · -- ΔWᵢ is F_{tⱼ}-measurable
      have hij_fin : i < j := Fin.lt_def.mpr hij
      apply Measurable.sub
      · exact (W.toAdapted.adapted _).mono (W.F.mono _ _ hij_times) le_rfl
      · exact (W.toAdapted.adapted _).mono (W.F.mono _ _ (le_of_lt
          (H.increasing i j hij_fin))) le_rfl
    · -- Hⱼ is F_{tⱼ}-measurable
      exact hH_adapted_all j
  -- X is integrable (bounded × integrable = integrable)
  have hX_int : Integrable (fun ω => H.values i ω *
      (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω) *
      H.values j ω) μ := by
    -- Regroup as (Hi * Hj) * ΔWi
    have hregroup' : (fun ω => H.values i ω *
        (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω) *
        H.values j ω) =
        (fun ω => (H.values i ω * H.values j ω) *
          (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω)) := by
      ext ω; ring
    rw [hregroup']
    -- ΔWi is integrable
    have hΔWi_int := W.increment_integrable _ _ (hH_times_nn i) (le_of_lt hii1)
    -- Hi * Hj is bounded and AEStronglyMeasurable
    obtain ⟨Ci, hCi⟩ := hH_bdd i
    obtain ⟨Cj, hCj⟩ := hH_bdd j
    apply Integrable.bdd_mul hΔWi_int
    · exact (((hH_adapted_all i).mono (W.F.le_ambient _) le_rfl).mul
        ((hH_adapted_all j).mono (W.F.le_ambient _) le_rfl)).aestronglyMeasurable
    · filter_upwards with ω
      simp only [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hCi ω) (hCj ω) (abs_nonneg _) (le_trans (abs_nonneg _) (hCi ω))
  -- Apply the key lemma
  exact SPDE.Probability.integral_mul_zero_of_indep_zero_mean
    (W.F.le_ambient _) hX_meas hX_int hΔW_int hindep hΔW_mean

/-- Diagonal term: E[Hᵢ²·(ΔWᵢ)²] = E[Hᵢ²]·Δtᵢ.

    Proof: Hᵢ² is F_{tᵢ}-measurable and ΔWᵢ is independent of F_{tᵢ},
    so E[Hᵢ²·(ΔWᵢ)²] = E[Hᵢ²]·E[(ΔWᵢ)²] = E[Hᵢ²]·Δtᵢ. -/
theorem diagonal_term (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    [IsProbabilityMeasure μ]
    (hH_adapted_all : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_sq_int : ∀ i : Fin H.n, Integrable (fun ω => (H.values i ω)^2) μ)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (i : Fin H.n) (hi : (i : ℕ) + 1 < H.n) :
    ∫ ω, (H.values i ω)^2 * (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω -
      W.process (H.times i) ω)^2 ∂μ =
    (∫ ω, (H.values i ω)^2 ∂μ) * (H.times ⟨(i : ℕ) + 1, hi⟩ - H.times i) := by
  -- Ordering
  have hii1 : H.times i < H.times ⟨(i : ℕ) + 1, hi⟩ :=
    H.increasing i ⟨(i : ℕ) + 1, hi⟩ (by simp [Fin.lt_def])
  -- Hᵢ² is F_{tᵢ}-measurable
  have hHsq_meas : @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _
      (fun ω => (H.values i ω)^2) := by
    have hm := hH_adapted_all i
    have : (fun ω => (H.values i ω)^2) = (fun ω => H.values i ω * H.values i ω) := by
      ext ω; ring
    rw [this]; exact hm.mul hm
  -- Independence: ΔWᵢ is independent of F_{tᵢ}
  have hindep : Indep (W.F.σ_algebra (H.times i))
    (MeasurableSpace.comap (fun ω => W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω -
      W.process (H.times i) ω) inferInstance) μ :=
    W.independent_increments _ _ (hH_times_nn i) (le_of_lt hii1)
  -- Integrability
  have hHsq_int := hH_sq_int i
  have hDWsq_int : Integrable (fun ω => (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω -
      W.process (H.times i) ω)^2) μ :=
    W.increment_sq_integrable _ _ (hH_times_nn i) (le_of_lt hii1)
  -- Build IndepFun for Hᵢ² and (ΔWᵢ)²
  have hIndepFun : IndepFun (fun ω => (H.values i ω)^2)
      (fun ω => (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω)^2) μ := by
    rw [IndepFun_iff_Indep]
    -- comap(Hᵢ²) ≤ F_{tᵢ}
    have hle1 : MeasurableSpace.comap (fun ω => (H.values i ω)^2) inferInstance ≤
        W.F.σ_algebra (H.times i) :=
      MeasurableSpace.comap_le_iff_le_map.mpr (fun _ hs => hHsq_meas hs)
    -- comap((ΔWᵢ)²) ≤ comap(ΔWᵢ)
    have hle2 : MeasurableSpace.comap
        (fun ω => (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω)^2)
        inferInstance ≤
        MeasurableSpace.comap (fun ω => W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω -
          W.process (H.times i) ω) inferInstance := by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := hs
      exact ⟨(fun x => x ^ 2) ⁻¹' t, (measurable_id.pow_const 2) ht, rfl⟩
    exact indep_of_indep_of_le_left (indep_of_indep_of_le_right hindep hle2) hle1
  -- Factor: E[Hᵢ²·(ΔWᵢ)²] = E[Hᵢ²]·E[(ΔWᵢ)²]
  have hfactor := hIndepFun.integral_mul_eq_mul_integral
    hHsq_int.aestronglyMeasurable hDWsq_int.aestronglyMeasurable
  -- Use E[(ΔWᵢ)²] = Δtᵢ
  have hvar : ∫ ω, (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω -
      W.process (H.times i) ω)^2 ∂μ = H.times ⟨(i : ℕ) + 1, hi⟩ - H.times i :=
    W.increment_variance _ _ (hH_times_nn i) (le_of_lt hii1)
  -- Combine: rewrite integral using factorization then variance
  rw [show (fun ω => (H.values i ω) ^ 2 *
      (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω) ^ 2) =
      (fun ω => (H.values i ω) ^ 2) * (fun ω =>
        (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω) ^ 2)
    from funext (fun ω => by simp [Pi.mul_apply])]
  rw [hfactor, hvar]

/-- Pythagoras for orthogonal sums: if E[aᵢ·aⱼ] = 0 for i ≠ j, then
    E[(Σ aᵢ)²] = Σ E[aᵢ²].

    This is the L² Pythagorean theorem, the algebraic core of the Itô isometry. -/
private theorem sum_sq_integral_eq_sum_integral_sq {n : ℕ}
    (a : Fin n → Ω → ℝ)
    (h_cross_int : ∀ i j : Fin n, Integrable (fun ω => a i ω * a j ω) μ)
    (h_orthog : ∀ i j : Fin n, i ≠ j → ∫ ω, a i ω * a j ω ∂μ = 0) :
    ∫ ω, (∑ i : Fin n, a i ω) ^ 2 ∂μ =
    ∑ i : Fin n, ∫ ω, (a i ω) ^ 2 ∂μ := by
  -- Step 1: (Σ aᵢ)² = Σᵢ Σⱼ aᵢ·aⱼ
  have hexpand : ∀ ω, (∑ i : Fin n, a i ω) ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, a i ω * a j ω := by
    intro ω; simp [sq, Finset.sum_mul_sum]
  simp_rw [hexpand]
  -- Step 2: Pull integral inside the double sum
  have h_inner_int : ∀ i : Fin n,
      Integrable (fun ω => ∑ j : Fin n, a i ω * a j ω) μ :=
    fun i => integrable_finset_sum _ (fun j _ => h_cross_int i j)
  rw [integral_finset_sum _ (fun i _ => h_inner_int i)]
  simp_rw [integral_finset_sum _ (fun j _ => h_cross_int _ j)]
  -- Step 3: Extract diagonal, zero out cross terms
  -- Now goal: Σᵢ Σⱼ ∫ aᵢ·aⱼ = Σᵢ ∫ aᵢ²
  congr 1; ext i
  -- Split: Σⱼ ∫ aᵢ·aⱼ = ∫ aᵢ·aᵢ + Σⱼ≠ᵢ ∫ aᵢ·aⱼ
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  -- Off-diagonal terms vanish
  have hoff : ∑ j ∈ Finset.univ.erase i, ∫ ω, a i ω * a j ω ∂μ = 0 :=
    Finset.sum_eq_zero (fun j hj => h_orthog i j (Finset.ne_of_mem_erase hj).symm)
  rw [hoff, add_zero]
  -- aᵢ · aᵢ = aᵢ²
  congr 1; ext ω; ring

/-- The Itô isometry for simple processes:

    E[(∫H dW)²] = Σᵢ E[Hᵢ²] * (tᵢ₊₁ - tᵢ)

    Proved using:
    1. Pythagoras (cross terms vanish by `cross_term_zero`)
    2. Diagonal factorization by `diagonal_term` -/
theorem isometry (H : SimpleProcess F) (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (hH_adapted_all : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i) :
    ∫ ω, (H.stochasticIntegral W ω)^2 ∂μ =
    ∑ i : Fin H.n, if h : (i : ℕ) + 1 < H.n then
      (∫ ω, (H.values i ω)^2 ∂μ) * (H.times ⟨i + 1, h⟩ - H.times i)
    else 0 := by
  -- Define the summand a_i(ω) = dite(i+1 < n, H_i · ΔW_i, 0)
  set a : Fin H.n → Ω → ℝ := fun i ω =>
    if h : (i : ℕ) + 1 < H.n then
      H.values i ω * (W.process (H.times ⟨i + 1, h⟩) ω - W.process (H.times i) ω)
    else 0 with ha_def
  -- The stochastic integral is Σ a_i
  have hI : ∀ ω, H.stochasticIntegral W ω = ∑ i, a i ω := by
    intro ω; simp [stochasticIntegral, a]
  simp_rw [hI]
  -- Apply Pythagoras: E[(Σ aᵢ)²] = Σ E[aᵢ²]
  -- Need: cross-product integrability and orthogonality
  have h_cross_int : ∀ i j : Fin H.n,
      Integrable (fun ω => a i ω * a j ω) μ := by
    intro i j
    simp only [ha_def]
    split_ifs with hi hj hj
    · -- Both valid: bounded × integrable products
      obtain ⟨Ci, hCi⟩ := hH_bdd i
      obtain ⟨Cj, hCj⟩ := hH_bdd j
      -- Regroup as (Hi * Hj) * (ΔWi * ΔWj)
      have hregroup_ij : (fun ω =>
          (H.values i ω * (W.process (H.times ⟨↑i + 1, hi⟩) ω - W.process (H.times i) ω)) *
          (H.values j ω * (W.process (H.times ⟨↑j + 1, hj⟩) ω - W.process (H.times j) ω))) =
          (fun ω => (H.values i ω * H.values j ω) *
            ((W.process (H.times ⟨↑i + 1, hi⟩) ω - W.process (H.times i) ω) *
             (W.process (H.times ⟨↑j + 1, hj⟩) ω - W.process (H.times j) ω))) := by
        ext ω; ring
      rw [hregroup_ij]
      -- Increments are square-integrable
      have hΔWi_sq := W.increment_sq_integrable _ _ (hH_times_nn i)
        (le_of_lt (H.increasing i ⟨(i : ℕ) + 1, hi⟩ (by simp [Fin.lt_def])))
      have hΔWj_sq := W.increment_sq_integrable _ _ (hH_times_nn j)
        (le_of_lt (H.increasing j ⟨(j : ℕ) + 1, hj⟩ (by simp [Fin.lt_def])))
      -- Product of increments is integrable by AM-GM: |a*b| ≤ a² + b²
      have hΔW_prod_int : Integrable (fun ω =>
          (W.process (H.times ⟨↑i + 1, hi⟩) ω - W.process (H.times i) ω) *
          (W.process (H.times ⟨↑j + 1, hj⟩) ω - W.process (H.times j) ω)) μ := by
        apply Integrable.mono' (hΔWi_sq.add hΔWj_sq)
        · exact (((W.toAdapted.adapted _).mono (W.F.le_ambient _) le_rfl).sub
            ((W.toAdapted.adapted _).mono (W.F.le_ambient _) le_rfl)).mul
            (((W.toAdapted.adapted _).mono (W.F.le_ambient _) le_rfl).sub
            ((W.toAdapted.adapted _).mono (W.F.le_ambient _) le_rfl))
            |>.aestronglyMeasurable
        · filter_upwards with ω
          simp only [Real.norm_eq_abs, BrownianMotion.process, Pi.add_apply]
          -- |a*b| ≤ a² + b² by AM-GM: (|a| - |b|)² ≥ 0
          set u := W.toAdapted.process (H.times ⟨↑i + 1, hi⟩) ω -
            W.toAdapted.process (H.times i) ω
          set v := W.toAdapted.process (H.times ⟨↑j + 1, hj⟩) ω -
            W.toAdapted.process (H.times j) ω
          rw [abs_mul]
          nlinarith [sq_abs u, sq_abs v, sq_nonneg (|u| - |v|),
            mul_nonneg (abs_nonneg u) (abs_nonneg v)]
      -- Bounded × integrable = integrable
      apply Integrable.bdd_mul hΔW_prod_int
      · exact (((hH_adapted_all i).mono (W.F.le_ambient _) le_rfl).mul
          ((hH_adapted_all j).mono (W.F.le_ambient _) le_rfl)).aestronglyMeasurable
      · filter_upwards with ω
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hCi ω) (hCj ω) (abs_nonneg _) (le_trans (abs_nonneg _) (hCi ω))
    all_goals simp [integrable_zero _ _ μ]
  have h_orthog : ∀ i j : Fin H.n, i ≠ j →
      ∫ ω, a i ω * a j ω ∂μ = 0 := by
    intro i j hij
    simp only [ha_def]
    split_ifs with hi hj hj
    · -- Both valid indices, i ≠ j. Use cross_term_zero.
      -- Need i < j or j < i
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
      · exact cross_term_zero H W hH_adapted_all hH_bdd hH_times_nn i j hi hj h
      · -- j < i: swap and use commutativity
        have hcomm : ∀ ω, a i ω * a j ω = a j ω * a i ω := fun ω => mul_comm _ _
        simp_rw [ha_def, dif_pos hi, dif_pos hj] at hcomm ⊢
        simp_rw [show ∀ ω, (H.values i ω *
            (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω)) *
            (H.values j ω *
            (W.process (H.times ⟨(j : ℕ) + 1, hj⟩) ω - W.process (H.times j) ω)) =
            (H.values j ω *
            (W.process (H.times ⟨(j : ℕ) + 1, hj⟩) ω - W.process (H.times j) ω)) *
            (H.values i ω *
            (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω))
          from fun ω => by ring]
        exact cross_term_zero H W hH_adapted_all hH_bdd hH_times_nn j i hj hi h
    all_goals simp
  -- Apply Pythagoras
  rw [sum_sq_integral_eq_sum_integral_sq a h_cross_int h_orthog]
  -- Now: Σᵢ ∫ (a_i)² = Σᵢ dite(...)
  congr 1; ext i
  simp only [ha_def]
  split_ifs with hi
  · -- Valid index: ∫ (H_i · ΔW_i)² = E[H_i²] · Δt_i
    have hsq : ∀ ω, (H.values i ω *
        (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω)) ^ 2 =
        (H.values i ω) ^ 2 *
        (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω) ^ 2 := by
      intro ω; ring
    simp_rw [hsq]
    -- Helper: derive square-integrability from boundedness
    have hH_sq_int_of_bdd : ∀ k : Fin H.n,
        Integrable (fun ω => (H.values k ω) ^ 2) μ := by
      intro k
      obtain ⟨Ck, hCk⟩ := hH_bdd k
      exact Integrable.of_bound
        (((hH_adapted_all k).mono (W.F.le_ambient _) le_rfl).pow_const 2).aestronglyMeasurable
        (Ck ^ 2)
        (ae_of_all μ (fun ω => by
          simp only [Real.norm_eq_abs]
          calc |H.values k ω ^ 2| = |H.values k ω| ^ 2 := by rw [abs_pow]
            _ ≤ Ck ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hCk ω) 2))
    exact diagonal_term H W hH_adapted_all hH_sq_int_of_bdd hH_times_nn i hi
  · -- Invalid index: both sides are 0
    simp [sq]

end SimpleProcess

/-! ## Itô Integral -/

/-- The space of Itô integrable processes.
    H is integrable if E[∫₀ᵀ H²_s ds] < ∞ -/
structure ItoIntegrableProcess (F : Filtration Ω ℝ) (μ : Measure Ω) (T : ℝ) where
  /-- The process -/
  process : ℝ → Ω → ℝ
  /-- Adapted to F -/
  adapted : ∀ t : ℝ, t ≤ T → @Measurable Ω ℝ (F.σ_algebra t) _ (process t)
  /-- Square-integrable condition: E[∫₀ᵀ H²_s ds] < ∞ -/
  square_integrable : ∃ (bound : ℝ),
    ∫ ω, (∫ t in Set.Icc 0 T, (process t ω)^2 ∂volume) ∂μ ≤ bound

/-- The Itô integral ∫₀ᵗ H_s dW_s, defined as the L² limit of simple process integrals.

    This structure carries the data of the integral process. The key properties
    (martingale, isometry) are proved as theorems, NOT bundled as fields. -/
structure ItoIntegral (F : Filtration Ω ℝ) (μ : Measure Ω) (T : ℝ) where
  /-- The integrand -/
  integrand : ItoIntegrableProcess F μ T
  /-- The driving Brownian motion -/
  BM : BrownianMotion Ω μ
  /-- The resulting process -/
  integral : ℝ → Ω → ℝ
  /-- The integral is adapted to F -/
  adapted : ∀ t : ℝ, t ≤ T → @Measurable Ω ℝ (F.σ_algebra t) _ (integral t)
  /-- The integral at time 0 is 0 -/
  initial : ∀ᵐ ω ∂μ, integral 0 ω = 0
  /-- The integral is the L² limit of simple process integrals:
      there exist simple processes Hₙ → H in L² such that
      ∫₀ᵗ Hₙ dW → ∫₀ᵗ H dW in L² for all t ∈ [0, T].
      This is the defining property (not isometry, which is proved from this).
      The time-parameterized version is needed for the martingale property.

      The approximating processes are adapted to the BM filtration, bounded,
      and have nonnegative partition times — these are standard properties
      guaranteed by the construction of the Itô integral. -/
  is_L2_limit : ∃ (approx : ℕ → SimpleProcess F),
    -- Adapted to BM filtration at partition times
    (∀ n, ∀ i : Fin (approx n).n,
      @Measurable Ω ℝ (BM.F.σ_algebra ((approx n).times i)) _ ((approx n).values i)) ∧
    -- Each value function is bounded
    (∀ n, ∀ i : Fin (approx n).n, ∃ C : ℝ, ∀ ω, |(approx n).values i ω| ≤ C) ∧
    -- Partition times are nonnegative
    (∀ n, ∀ i : Fin (approx n).n, 0 ≤ (approx n).times i) ∧
    -- L² convergence at each time
    (∀ t : ℝ, 0 ≤ t → t ≤ T →
    Filter.Tendsto (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx n) BM t ω -
                                     integral t ω)^2 ∂μ)
      Filter.atTop (nhds 0))
  /-- The integral is integrable at each time in [0, T].
      This is a defining property: the Itô integral is the L² limit of simple process
      integrals, so it is in L² (hence L¹) by construction. -/
  integrable_limit : ∀ t : ℝ, 0 ≤ t → t ≤ T → Integrable (integral t) μ
  /-- The integral is square-integrable at each time in [0, T].
      As the L² limit of L² processes, the integral is in L² by construction. -/
  sq_integrable_limit : ∀ t : ℝ, 0 ≤ t → t ≤ T →
    Integrable (fun ω => (integral t ω) ^ 2) μ

namespace ItoIntegral

variable {F : Filtration Ω ℝ} {μ : Measure Ω} {T : ℝ}

/-- Linearity of Itô integral in the integrand -/
theorem linear (I₁ I₂ : ItoIntegral F μ T) (_h : I₁.BM = I₂.BM) (a b : ℝ) :
    ∃ I : ItoIntegral F μ T,
      I.BM = I₁.BM ∧
      ∀ t : ℝ, ∀ᵐ ω ∂μ, I.integral t ω = a * I₁.integral t ω + b * I₂.integral t ω := by
  sorry

/-- Itô isometry: E[(∫₀ᵗ H dW)²] = E[∫₀ᵗ H² ds].
    This is a theorem proved from the L² limit definition, not a structure field. -/
theorem ito_isometry (I : ItoIntegral F μ T) [IsProbabilityMeasure μ] (t : ℝ) (ht : t ≤ T) :
    ∫ ω, (I.integral t ω)^2 ∂μ =
    ∫ ω, (∫ (s : ℝ) in Set.Icc 0 t, (I.integrand.process s ω)^2 ∂volume) ∂μ := by
  sorry -- Proof: pass through L² limit using SimpleProcess.isometry for each approximant

/-- The Itô integral satisfies the martingale set-integral property on [0, T]:
    for 0 ≤ s ≤ t ≤ T and A ∈ F_s, ∫_A I(t) dμ = ∫_A I(s) dμ.

    This is the mathematical content of "the Itô integral is a martingale".
    Fully proved in `Helpers/ItoIntegralProperties.lean` as
    `ItoIntegral.is_martingale_proof`. The sorry here is due to import limitations
    (the proof uses infrastructure from files that import this one). -/
theorem is_martingale (I : ItoIntegral F μ T) [IsProbabilityMeasure μ]
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    {A : Set Ω} (hA : MeasurableSet[I.BM.F.σ_algebra s] A) :
    ∫ ω in A, I.integral t ω ∂μ = ∫ ω in A, I.integral s ω ∂μ := by
  sorry -- Proved in Helpers/ItoIntegralProperties.lean as ItoIntegral.is_martingale_proof

/-- Burkholder-Davis-Gundy inequality: E[sup|M_t|^p] ≤ C_p E[⟨M⟩_T^{p/2}] -/
theorem bdg_inequality (I : ItoIntegral F μ T) (p : ℝ) (_hp : 1 ≤ p) :
    ∃ (Cp : ℝ), Cp > 0 ∧
      ∫ ω, (⨆ (t : Set.Icc 0 T), |I.integral t ω|)^p ∂μ ≤
      Cp * ∫ ω, ((∫ (s : ℝ) in Set.Icc 0 T, (I.integrand.process s ω)^2 ∂volume))^(p/2) ∂μ := by
  sorry

end ItoIntegral

/-! ## Itô Processes -/

/-- An Itô process: dX_t = μ_t dt + σ_t dW_t

    The stochastic integral ∫₀ᵗ σ_s dW_s is represented as a process field,
    characterized as an L² limit of simple process integrals. -/
structure ItoProcess (F : Filtration Ω ℝ) (μ : Measure Ω) where
  /-- The process X -/
  process : ℝ → Ω → ℝ
  /-- The drift coefficient μ -/
  drift : ℝ → Ω → ℝ
  /-- The diffusion coefficient σ -/
  diffusion : ℝ → Ω → ℝ
  /-- The driving Brownian motion -/
  BM : BrownianMotion Ω μ
  /-- The stochastic integral process ∫₀ᵗ σ_s dW_s -/
  stoch_integral : ℝ → Ω → ℝ
  /-- The stochastic integral is the L² limit of simple process approximations
      of the diffusion coefficient. This connects `stoch_integral` to `diffusion` and `BM`.
      Convergence holds at all times t ≥ 0.

      The approximating processes are adapted, bounded, with nonneg partition times. -/
  stoch_integral_is_L2_limit : ∃ (approx : ℕ → SimpleProcess F),
    (∀ n, ∀ i : Fin (approx n).n,
      @Measurable Ω ℝ (BM.F.σ_algebra ((approx n).times i)) _ ((approx n).values i)) ∧
    (∀ n, ∀ i : Fin (approx n).n, ∃ C : ℝ, ∀ ω, |(approx n).values i ω| ≤ C) ∧
    (∀ n, ∀ i : Fin (approx n).n, 0 ≤ (approx n).times i) ∧
    (∀ t : ℝ, t ≥ 0 →
    Filter.Tendsto (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx n) BM t ω -
                                     stoch_integral t ω)^2 ∂μ)
      Filter.atTop (nhds 0))
  /-- Integral form: X_t = X_0 + ∫₀ᵗ μ_s ds + ∫₀ᵗ σ_s dW_s -/
  integral_form : ∀ t : ℝ, t ≥ 0 → ∀ᵐ ω ∂μ,
    process t ω = process 0 ω +
      (∫ (s : ℝ) in Set.Icc 0 t, drift s ω ∂volume) +
      stoch_integral t ω

namespace ItoProcess

variable {F : Filtration Ω ℝ} {μ : Measure Ω}

/-- The quadratic variation of an Itô process is ∫₀ᵗ σ²_s ds -/
theorem quadratic_variation (X : ItoProcess F μ) :
    ∃ qv : QuadraticVariation F,
      qv.process = X.process ∧
      (∀ t : ℝ, t ≥ 0 → ∀ᵐ ω ∂μ,
        qv.variation t ω = ∫ (s : ℝ) in Set.Icc 0 t, (X.diffusion s ω)^2 ∂volume) := by
  sorry

/-- Itô processes are semimartingales -/
theorem is_semimartingale (X : ItoProcess F μ) :
    ∃ (M : LocalMartingale F μ ℝ) (A : ℝ → Ω → ℝ),
      ∀ t : ℝ, ∀ᵐ ω ∂μ, X.process t ω = M.process t ω + A t ω := by
  sorry

end ItoProcess

/-! ## Itô's Formula -/

/-- Itô's formula for a C² function f applied to an Itô process.

    f(t, X_t) = f(0, X_0) + ∫₀ᵗ ∂_t f(s, X_s) ds + ∫₀ᵗ ∂_x f(s, X_s) dX_s
                + (1/2)∫₀ᵗ ∂²_x f(s, X_s) σ²_s ds

    The three integral terms are:
    - drift_term: ∫₀ᵗ [∂_t f(s, X_s) + ∂_x f(s, X_s) μ_s + (1/2) ∂²_x f(s, X_s) σ²_s] ds
    - diffusion_term: ∫₀ᵗ ∂_x f(s, X_s) σ_s dW_s (stochastic integral)

    We express the drift terms explicitly and the stochastic integral
    as a process (which is characterised elsewhere via L² limits). -/
theorem ito_formula {F : Filtration Ω ℝ} {μ : Measure Ω}
    (X : ItoProcess F μ)
    (f : ℝ → ℝ → ℝ)
    (hf_t : ∀ x, Differentiable ℝ (fun t => f t x))
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x)) :
    ∃ (stoch_int : ℝ → Ω → ℝ),
    ∀ t : ℝ, t ≥ 0 → ∀ᵐ ω ∂μ,
      f t (X.process t ω) = f 0 (X.process 0 ω) +
        (∫ (s : ℝ) in Set.Icc 0 t,
          (deriv (fun u => f u (X.process s ω)) s +
           deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
           (1/2) * deriv (deriv (fun x => f s x)) (X.process s ω) * (X.diffusion s ω)^2)
          ∂volume) +
        stoch_int t ω := by
  sorry

/-! ## Stochastic Differential Equations -/

/-- An SDE: dX_t = b(t, X_t) dt + σ(t, X_t) dW_t -/
structure SDE (F : Filtration Ω ℝ) (μ : Measure Ω) where
  /-- Drift coefficient b(t, x) -/
  drift : ℝ → ℝ → ℝ
  /-- Diffusion coefficient σ(t, x) -/
  diffusion : ℝ → ℝ → ℝ
  /-- Lipschitz condition in x -/
  lipschitz : ∃ K : ℝ, K > 0 ∧ ∀ t x y : ℝ,
    |drift t x - drift t y| + |diffusion t x - diffusion t y| ≤ K * |x - y|
  /-- Linear growth condition -/
  linear_growth : ∃ K : ℝ, K > 0 ∧ ∀ t x : ℝ,
    |drift t x|^2 + |diffusion t x|^2 ≤ K^2 * (1 + |x|^2)

/-- A strong solution to an SDE -/
structure SDESolution (F : Filtration Ω ℝ) (μ : Measure Ω) (sde : SDE F μ) where
  /-- The solution process -/
  solution : ItoProcess F μ
  /-- Initial condition -/
  initial : Ω → ℝ
  /-- Initial value matches -/
  initial_matches : ∀ᵐ ω ∂μ, solution.process 0 ω = initial ω
  /-- The drift matches -/
  drift_matches : ∀ t : ℝ, ∀ᵐ ω ∂μ,
    solution.drift t ω = sde.drift t (solution.process t ω)
  /-- The diffusion matches -/
  diffusion_matches : ∀ t : ℝ, ∀ᵐ ω ∂μ,
    solution.diffusion t ω = sde.diffusion t (solution.process t ω)

/-- Existence and uniqueness theorem for SDEs (Picard-Lindelöf) -/
theorem sde_existence_uniqueness {F : Filtration Ω ℝ} {μ : Measure Ω}
    (sde : SDE F μ) (W : BrownianMotion Ω μ) (initial : Ω → ℝ)
    (h_initial : Integrable (fun ω => (initial ω)^2) μ) :
    ∃ sol : SDESolution F μ sde, sol.initial = initial ∧ sol.solution.BM = W := by
  sorry

/-- Uniqueness in law for SDE solutions -/
theorem sde_uniqueness_law {F : Filtration Ω ℝ} {μ : Measure Ω}
    (sde : SDE F μ) (sol₁ sol₂ : SDESolution F μ sde)
    (h : ∀ᵐ ω ∂μ, sol₁.initial ω = sol₂.initial ω) :
    ∀ t : ℝ, ∀ᵐ ω ∂μ, sol₁.solution.process t ω = sol₂.solution.process t ω := by
  sorry

/-! ## Stratonovich Integral -/

/-- The Stratonovich integral ∫₀ᵗ H_s ∘ dW_s.
    Related to Itô by: ∫ H ∘ dW = ∫ H dW + (1/2)⟨H, W⟩_t

    The correction term (1/2)⟨H, W⟩_t is a deterministic integral when H is
    a smooth function of W. -/
structure StratonovichIntegral (F : Filtration Ω ℝ) (μ : Measure Ω) (T : ℝ) where
  /-- The integrand -/
  integrand : ItoIntegrableProcess F μ T
  /-- The driving Brownian motion -/
  BM : BrownianMotion Ω μ
  /-- The corresponding Itô integral -/
  ito_integral : ItoIntegral F μ T
  /-- The Itô-Stratonovich correction process (1/2)⟨H, W⟩_t -/
  correction : ℝ → Ω → ℝ
  /-- The correction is adapted -/
  correction_adapted : ∀ t : ℝ, t ≤ T →
    @Measurable Ω ℝ (F.σ_algebra t) _ (correction t)
  /-- The result: Stratonovich integral = Itô integral + correction -/
  integral : ℝ → Ω → ℝ
  /-- Relation to Itô integral with correction term -/
  ito_correction : ∀ t : ℝ, t ≤ T → ∀ᵐ ω ∂μ,
    integral t ω = ito_integral.integral t ω + correction t ω

/-- Stratonovich calculus follows the ordinary chain rule -/
theorem stratonovich_chain_rule {F : Filtration Ω ℝ} {μ : Measure Ω} {T : ℝ}
    (I : StratonovichIntegral F μ T)
    (f : ℝ → ℝ)
    (_hf : ContDiff ℝ 1 f) :
    ∀ t : ℝ, t ≤ T → ∀ᵐ ω ∂μ,
      f (I.integral t ω) = f (I.integral 0 ω) +
        ∫ (s : ℝ) in Set.Icc 0 t, deriv f (I.integral s ω) * I.integrand.process s ω ∂volume := by
  sorry

/-! ## Finite Variation Processes -/

/-- A partition of [0, T] is an increasing list of times.
    We represent this as a list with the property that consecutive elements are ordered. -/
structure Partition (T : ℝ) where
  /-- The partition points -/
  points : List ℝ
  /-- Non-empty with 0 at start -/
  starts_zero : points.head? = some 0
  /-- Ends at T -/
  ends_T : points.getLast? = some T
  /-- Strictly increasing -/
  increasing : points.IsChain (· < ·)

/-- The total variation of a function over a partition -/
noncomputable def totalVariationOver (A : ℝ → ℝ) (π : Partition T) : ℝ :=
  (π.points.zip π.points.tail).foldl
    (fun acc (pair : ℝ × ℝ) => acc + |A pair.2 - A pair.1|) 0

/-- A function A : ℝ → ℝ has finite variation on [0, T] if the total variation
    over all partitions is bounded. -/
def HasFiniteVariation (A : ℝ → ℝ) (T : ℝ) : Prop :=
  ∃ V : ℝ, V ≥ 0 ∧ ∀ π : Partition T, totalVariationOver A π ≤ V

/-- The total variation of A on [0, T] (as a sup over partitions) -/
noncomputable def totalVariation (A : ℝ → ℝ) (T : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ π : Partition T, v = totalVariationOver A π}

/-! ## Semimartingales -/

/-- A semimartingale is X = M + A where M is a local martingale and A has finite variation.

    This is the fundamental decomposition for stochastic calculus.
    Key examples:
    - Brownian motion: M = W, A = 0
    - Itô process: M = ∫σ dW, A = ∫μ dt -/
structure Semimartingale (F : Filtration Ω ℝ) (μ : Measure Ω) where
  /-- The local martingale part M -/
  martingale_part : LocalMartingale F μ ℝ
  /-- The finite variation part A -/
  finite_variation_part : ℝ → Ω → ℝ
  /-- A has finite variation on [0, T] for each ω and T ≥ 0.
      CORRECT DEFINITION: The variation is computed as the supremum of
      Σᵢ |A(tᵢ₊₁, ω) - A(tᵢ, ω)| over all partitions {t₀ < t₁ < ... < tₙ} of [0, T]. -/
  finite_variation : ∀ ω : Ω, ∀ T : ℝ, T ≥ 0 →
    HasFiniteVariation (fun t => finite_variation_part t ω) T
  /-- A(0) = 0 (canonical starting point) -/
  fv_initial : ∀ ω : Ω, finite_variation_part 0 ω = 0
  /-- A is right-continuous (càdlàg) -/
  fv_right_continuous : ∀ ω : Ω, ∀ t : ℝ,
    Filter.Tendsto (fun s => finite_variation_part s ω) (nhdsWithin t (Set.Ioi t))
      (nhds (finite_variation_part t ω))
  /-- The process X = M + A -/
  process : ℝ → Ω → ℝ
  /-- Decomposition X = M + A -/
  decomposition : ∀ t : ℝ, ∀ ω : Ω,
    process t ω = martingale_part.process t ω + finite_variation_part t ω

namespace Semimartingale

variable {F : Filtration Ω ℝ} {μ : Measure Ω}

/-- The variation process: V_t(ω) = total variation of A on [0, t] -/
noncomputable def variation_process (X : Semimartingale F μ) : ℝ → Ω → ℝ :=
  fun t ω => if t ≥ 0 then totalVariation (fun s => X.finite_variation_part s ω) t else 0

/-- Decomposition of A into increasing parts: A = A⁺ - A⁻ (Jordan decomposition) -/
noncomputable def positive_variation (X : Semimartingale F μ) : ℝ → Ω → ℝ :=
  fun t ω => (X.variation_process t ω + X.finite_variation_part t ω) / 2

noncomputable def negative_variation (X : Semimartingale F μ) : ℝ → Ω → ℝ :=
  fun t ω => (X.variation_process t ω - X.finite_variation_part t ω) / 2

end Semimartingale

/-- Lebesgue-Stieltjes integral ∫₀ᵗ H dA for finite variation A.

    This is defined via the associated measure: the increment A(b) - A(a)
    determines a signed measure, and we integrate H against it.

    For continuous H and A, this equals lim_{‖π‖→0} Σᵢ H(tᵢ)(A(tᵢ₊₁) - A(tᵢ)). -/
structure LebesgueStieltjesIntegral {F : Filtration Ω ℝ}
    (H : PredictableProcess F ℝ) (A : ℝ → Ω → ℝ) (T : ℝ) where
  /-- The integral process -/
  integral : Ω → ℝ
  /-- A has finite variation -/
  fv : ∀ ω : Ω, HasFiniteVariation (fun t => A t ω) T
  /-- The integral is the limit of Riemann-Stieltjes sums:
      lim Σᵢ H(tᵢ, ω)(A(tᵢ₊₁, ω) - A(tᵢ, ω)) as mesh → 0 -/
  is_limit : ∀ ω : Ω, ∀ ε > 0, ∃ δ > 0,
    ∀ π : Partition T,
    (∀ i : Fin (π.points.length - 1),
      π.points.get ⟨i.val + 1, by omega⟩ - π.points.get ⟨i.val, by omega⟩ < δ) →
    |integral ω - (π.points.zip π.points.tail).foldl
      (fun acc (pair : ℝ × ℝ) => acc + H.process pair.1 ω * (A pair.2 ω - A pair.1 ω)) 0| < ε

/-- Stochastic integral w.r.t. semimartingale: ∫₀ᵗ H dX = ∫₀ᵗ H dM + ∫₀ᵗ H dA

    The first term is the Itô integral (against local martingale).
    The second term is the Lebesgue-Stieltjes integral (against finite variation).

    **Mathematical Definition**:
    For a predictable process H and semimartingale X = M + A:
    - The Itô integral ∫₀ᵗ H dM is defined as the L²-limit of simple process integrals
    - The LS integral ∫₀ᵗ H dA is defined via the associated Lebesgue-Stieltjes measure

    **Structure**:
    This structure witnesses the existence of the integral and provides the result.
    The existence requires:
    1. H is predictable (F_{t-}-measurable)
    2. H satisfies integrability: E[∫₀ᵀ H² d⟨M⟩] < ∞ for the martingale part
    3. H is integrable w.r.t. |dA| for the finite variation part -/
structure SemimartingaleIntegral
    {F : Filtration Ω ℝ} {μ : Measure Ω}
    (H : PredictableProcess F ℝ)
    (X : Semimartingale F μ)
    (T : ℝ) where
  /-- The resulting integral process -/
  integral : ℝ → Ω → ℝ
  /-- The martingale part of the integral: ∫₀ᵗ H dM -/
  martingale_integral : ℝ → Ω → ℝ
  /-- The Lebesgue-Stieltjes part of the integral: ∫₀ᵗ H dA -/
  ls_integral : ℝ → Ω → ℝ
  /-- The integral at time 0 is 0 -/
  initial : ∀ ω, integral 0 ω = 0
  /-- The integral is adapted to F -/
  adapted : ∀ t : ℝ, t ≤ T → @Measurable Ω ℝ (F.σ_algebra t) _ (integral t)
  /-- The integral decomposes as martingale + LS integral.
      ∫₀ᵗ H dX = ∫₀ᵗ H dM + ∫₀ᵗ H dA for each ω and t. -/
  decomposition : ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ᵐ ω ∂μ,
    integral t ω = martingale_integral t ω + ls_integral t ω
  /-- The martingale part is a local martingale -/
  martingale_integral_is_local_martingale :
    ∃ M : LocalMartingale F μ ℝ, M.process = martingale_integral
  /-- The LS part has finite variation -/
  ls_integral_finite_variation : ∀ ω : Ω,
    HasFiniteVariation (fun t => ls_integral t ω) T

/-- Existence of semimartingale integral for bounded predictable processes.
    For H bounded and X a semimartingale, ∫ H dX exists. -/
theorem semimartingale_integral_exists
    {F : Filtration Ω ℝ} {μ : Measure Ω}
    (H : PredictableProcess F ℝ)
    (X : Semimartingale F μ)
    (T : ℝ) (hT : T ≥ 0)
    (hH_bounded : ∃ C : ℝ, ∀ t : ℝ, ∀ ω : Ω, |H.process t ω| ≤ C) :
    ∃ I : SemimartingaleIntegral H X T, True := by
  sorry  -- Requires full construction of stochastic integral

/-- For simple predictable processes, the semimartingale integral
    is the Riemann sum Σᵢ Hᵢ (X_{tᵢ₊₁} - X_{tᵢ}). -/
noncomputable def semimartingale_integral_simple
    {F : Filtration Ω ℝ} {μ : Measure Ω}
    (H : SimpleProcess F)
    (X : Semimartingale F μ) : ℝ → Ω → ℝ :=
  fun t ω =>
    ∑ i : Fin H.n, if h : (i : ℕ) + 1 < H.n then
      if H.times ⟨i + 1, h⟩ ≤ t then
        H.values i ω * (X.process (H.times ⟨i + 1, h⟩) ω - X.process (H.times i) ω)
      else if H.times i ≤ t then
        H.values i ω * (X.process t ω - X.process (H.times i) ω)
      else 0
    else 0

/-! ## Girsanov's Theorem -/

/-- Girsanov's theorem: under change of measure, BM becomes BM with drift.
    If dQ/dP = exp(∫θ dW - (1/2)∫θ² dt), then W̃_t = W_t - ∫₀ᵗ θ_s ds is Q-BM. -/
theorem girsanov {F : Filtration Ω ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (W : BrownianMotion Ω μ)
    (θ : ℝ → Ω → ℝ)
    (T : ℝ)
    (_novikov : ∃ (bound : ℝ),
      ∫ ω, Real.exp ((1/2) * ∫ (t : ℝ) in Set.Icc 0 T, (θ t ω)^2 ∂volume) ∂μ ≤ bound) :
    ∃ (ν : Measure Ω) (W' : BrownianMotion Ω ν),
      ∀ t : ℝ, ∀ᵐ ω ∂μ,
        W'.process t ω = W.process t ω - ∫ (s : ℝ) in Set.Icc 0 t, θ s ω ∂volume := by
  sorry

/-! ## Martingale Representation Theorem -/

/-- Every square-integrable martingale adapted to the Brownian filtration
    can be represented as a stochastic integral:
    M_t = M_0 + ∫₀ᵗ H_s dW_s

    The integrand H is predictable and the stochastic integral is the L² limit
    of simple process approximations. -/
theorem martingale_representation {F : Filtration Ω ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (W : BrownianMotion Ω μ)
    (M : Martingale F μ ℝ)
    (hM : ∀ t : ℝ, Integrable (fun ω => (M.process t ω)^2) μ) :
    ∃ (H : ℝ → Ω → ℝ) (stoch_int : ℝ → Ω → ℝ),
      -- H is adapted (predictable)
      (∀ t : ℝ, @Measurable Ω ℝ (F.σ_algebra t) _ (H t)) ∧
      -- stoch_int is the L² limit of simple process integrals of H w.r.t. W
      (∃ (approx : ℕ → SimpleProcess F),
        ∀ t : ℝ, t ≥ 0 →
        Filter.Tendsto (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx n) W t ω -
                                         stoch_int t ω)^2 ∂μ)
          Filter.atTop (nhds 0)) ∧
      -- M = M_0 + stochastic integral
      (∀ t : ℝ, ∀ᵐ ω ∂μ, M.process t ω = M.process 0 ω + stoch_int t ω) := by
  sorry

end SPDE
