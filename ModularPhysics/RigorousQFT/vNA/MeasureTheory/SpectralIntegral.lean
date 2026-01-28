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

/-- The step approximations form a Cauchy sequence for bounded f.
    |∫ fₙ dμ - ∫ fₘ dμ| ≤ ‖fₙ - fₘ‖_∞ · |μ|(ℝ)
    Since the simple functions converge uniformly, the integrals converge. -/
theorem simpleIntegral_cauchy (μ : ComplexSpectralMeasure H) (f : ℝ → ℂ)
    (_hf_bdd : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N₁ N₂ n₁ n₂ : ℕ, N₁ ≥ N₀ → N₂ ≥ N₀ → n₁ ≥ N₀ → n₂ ≥ N₀ →
      ‖simpleIntegral μ N₁ n₁ f - simpleIntegral μ N₂ n₂ f‖ < ε := by
  sorry

/-- For a bounded measurable function f and a complex spectral measure μ,
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
def complexSpectralIntegral (μ : ComplexSpectralMeasure H) (f : ℝ → ℂ) : ℂ :=
  -- The limit of simple function approximations as N, n → ∞
  -- We use Classical.choose to select the limit value.
  -- The existence is guaranteed by:
  -- 1. Simple integrals form a Cauchy sequence (for bounded f)
  -- 2. ℂ is complete
  Classical.choose <| by
    have h_exists : ∃ L : ℂ, ∀ ε > 0, ∃ N₀ : ℕ, ∀ N n : ℕ, N ≥ N₀ → n ≥ N₀ →
        ‖simpleIntegral μ N n f - L‖ < ε := by
      -- The simple integrals form a Cauchy net, and ℂ is complete.
      -- Therefore the limit exists.
      sorry
    exact h_exists

/-! ### Spectral integral for operators -/

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

/-- The spectral integral ∫ f dP for a spectral measure P and bounded Borel function f.
    This is defined as the unique operator T such that ⟨x, Ty⟩ = ∫ f dμ_{x,y}
    where μ_{x,y}(E) = ⟨x, P(E)y⟩.

    Properties:
    - ∫ 1 dP = I (identity)
    - ∫ χ_E dP = P(E) (projection)
    - ∫ fg dP = (∫ f dP)(∫ g dP) (multiplicativity)
    - ∫ f̄ dP = (∫ f dP)* (adjoint)
    - ‖∫ f dP‖ ≤ sup|f| on supp(P) (norm bound) -/
structure SpectralIntegral (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The spectral measure -/
  measure : Set ℝ → (H →L[ℂ] H)
  /-- The integral map from bounded Borel functions to operators -/
  integral : (ℝ → ℂ) → (H →L[ℂ] H)
  /-- Integral of indicator function gives projection -/
  integral_indicator : ∀ E : Set ℝ, integral (Set.indicator E (fun _ => 1)) = measure E
  /-- Integral of 1 is identity -/
  integral_one : integral (fun _ => 1) = 1
  /-- Multiplicativity -/
  integral_mul : ∀ f g, integral (f * g) = integral f ∘L integral g
  /-- Adjoint property -/
  integral_star : ∀ f, ContinuousLinearMap.adjoint (integral f) = integral (star ∘ f)
  /-- P(∅) = 0 -/
  measure_empty : measure ∅ = 0
  /-- σ-additivity of the measure -/
  measure_sigma_additive : ∀ (E : ℕ → Set ℝ), (∀ i j, i ≠ j → Disjoint (E i) (E j)) →
    ∀ x : H, Tendsto (fun n => ∑ i ∈ Finset.range n, measure (E i) x)
      atTop (nhds (measure (⋃ i, E i) x))

namespace SpectralIntegral

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (I : SpectralIntegral H)

/-- The complex measure μ_{x,y}(E) = ⟨x, P(E)y⟩ derived from the spectral integral -/
def complexMeasureOf (x y : H) : ComplexSpectralMeasure H where
  toFun E := @inner ℂ H _ x (I.measure E y)
  empty := by simp only [I.measure_empty, ContinuousLinearMap.zero_apply, inner_zero_right]
  sigma_additive E hdisj := by
    -- σ-additivity follows from σ-additivity of measure and continuity of inner product
    -- ⟨x, Σ P(Eᵢ)y⟩ = Σ ⟨x, P(Eᵢ)y⟩ → ⟨x, P(⋃ Eᵢ)y⟩
    -- The inner product is continuous, so it preserves limits
    have hmeas := I.measure_sigma_additive E hdisj y
    -- hmeas : Tendsto (fun n => Σᵢ P(Eᵢ)y) atTop (nhds (P(⋃ Eᵢ)y))
    -- We need: Tendsto (fun n => Σᵢ ⟨x, P(Eᵢ)y⟩) atTop (nhds ⟨x, P(⋃ Eᵢ)y⟩)
    -- This follows from continuity of inner product in the second argument
    -- The map z ↦ ⟨x, z⟩ is continuous
    have hcont : Continuous (fun z : H => @inner ℂ H _ x z) :=
      continuous_inner.comp (continuous_const.prodMk continuous_id)
    -- Apply the continuous map to the convergent sequence
    have hconv := hcont.continuousAt.tendsto.comp hmeas
    -- Convert the sum of inner products to inner of sums
    convert hconv using 1
    ext n
    simp only [Function.comp_apply]
    rw [inner_sum]

/-- The defining sesquilinear property: ⟨x, (∫ f dP) y⟩ = ∫ f dμ_{x,y} -/
theorem integral_inner (f : ℝ → ℂ) (x y : H) :
    @inner ℂ H _ x (I.integral f y) = complexSpectralIntegral (I.complexMeasureOf x y) f := by
  -- This is the defining property of the spectral integral
  sorry

end SpectralIntegral

/-- Existence of the spectral integral for any spectral measure -/
theorem spectralIntegral_exists (P : Set ℝ → (H →L[ℂ] H))
    (hP_empty : P ∅ = 0) (hP_univ : P Set.univ = 1)
    (hP_idem : ∀ E, P E ∘L P E = P E)
    (hP_sa : ∀ E, ContinuousLinearMap.adjoint (P E) = P E)
    (hP_inter : ∀ E F, P (E ∩ F) = P E ∘L P F) :
    ∃ I : SpectralIntegral H, I.measure = P := by
  -- Construction of the spectral integral
  sorry

end
