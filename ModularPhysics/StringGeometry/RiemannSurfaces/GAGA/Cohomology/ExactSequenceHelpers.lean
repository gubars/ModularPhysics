import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-!
# Exact Sequence Dimension Lemmas

This file proves helper lemmas about dimensions in exact sequences of finite-dimensional
vector spaces. The main result is that the alternating sum of dimensions in an exact
sequence is zero.

## Main Results

* `alternatingSum_exactSeq_eq_zero` - For a six-term exact sequence of f.d. vector spaces,
  the alternating sum of dimensions is zero.
* `eulerChar_additive_of_exactSeq` - Euler characteristic is additive on short exact sequences.

## Mathematical Background

For an exact sequence of finite-dimensional vector spaces:
  0 → V₁ → V₂ → V₃ → V₄ → V₅ → V₆ → 0

By rank-nullity at each map, and using exactness (ker = im of previous map):
  dim V₁ - dim V₂ + dim V₃ - dim V₄ + dim V₅ - dim V₆ = 0

Applied to the long exact sequence in cohomology:
  0 → H⁰(F') → H⁰(F) → H⁰(F'') → H¹(F') → H¹(F) → H¹(F'') → 0

gives the additivity of Euler characteristic:
  χ(F) = χ(F') + χ(F'')
-/

namespace ExactSequenceHelpers

open Module LinearMap

universe u

variable {K : Type*} [DivisionRing K]

/-!
## Four-term Exact Sequence

For 0 → V₁ →^f V₂ →^g V₃ → 0 exact:
  dim V₂ = dim V₁ + dim V₃
-/

/-- In a short exact sequence 0 → V₁ → V₂ → V₃ → 0, dim V₂ = dim V₁ + dim V₃ -/
theorem finrank_middle_of_shortExact
    {V₁ V₂ V₃ : Type u} [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃]
    [Module K V₁] [Module K V₂] [Module K V₃]
    [Module.Finite K V₁] [Module.Finite K V₂] [Module.Finite K V₃]
    (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃)
    (hf_inj : Function.Injective f)
    (hg_surj : Function.Surjective g)
    (hexact : ker g = range f) :
    finrank K V₂ = finrank K V₁ + finrank K V₃ := by
  -- By rank-nullity: dim V₂ = dim ker g + dim range g
  -- ker g = range f, and dim range f = dim V₁ (since f is injective)
  -- range g = V₃ (since g is surjective)
  have h1 : finrank K (range f) = finrank K V₁ := by
    exact LinearMap.finrank_range_of_inj hf_inj
  have h2 : finrank K (range g) = finrank K V₃ := by
    rw [range_eq_top.mpr hg_surj]
    simp
  have h3 : finrank K (ker g) = finrank K (range f) := by
    rw [hexact]
  -- rank-nullity: dim V₂ = dim ker g + dim range g
  have rn := Submodule.finrank_quotient_add_finrank (ker g)
  rw [LinearEquiv.finrank_eq g.quotKerEquivRange] at rn
  -- rn : finrank K (range g) + finrank K (ker g) = finrank K V₂
  omega

/-- Alternative form: dim V₁ + dim V₃ = dim V₂ for short exact sequence -/
theorem finrank_sum_of_shortExact
    {V₁ V₂ V₃ : Type u} [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃]
    [Module K V₁] [Module K V₂] [Module K V₃]
    [Module.Finite K V₁] [Module.Finite K V₂] [Module.Finite K V₃]
    (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃)
    (hf_inj : Function.Injective f)
    (hg_surj : Function.Surjective g)
    (hexact : ker g = range f) :
    finrank K V₁ + finrank K V₃ = finrank K V₂ :=
  (finrank_middle_of_shortExact f g hf_inj hg_surj hexact).symm

/-!
## Six-term Exact Sequence

For the long exact sequence in cohomology:
  0 → H⁰(F') → H⁰(F) → H⁰(F'') → H¹(F') → H¹(F) → H¹(F'') → 0

we prove the alternating sum formula.
-/

/-- Given maps between consecutive terms of a six-term exact sequence,
    the alternating sum of dimensions is zero. -/
theorem alternatingSum_sixTerm_exact
    {V₁ V₂ V₃ V₄ V₅ V₆ : Type u}
    [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃]
    [AddCommGroup V₄] [AddCommGroup V₅] [AddCommGroup V₆]
    [Module K V₁] [Module K V₂] [Module K V₃]
    [Module K V₄] [Module K V₅] [Module K V₆]
    [Module.Finite K V₁] [Module.Finite K V₂] [Module.Finite K V₃]
    [Module.Finite K V₄] [Module.Finite K V₅] [Module.Finite K V₆]
    (f₁ : V₁ →ₗ[K] V₂) (f₂ : V₂ →ₗ[K] V₃) (f₃ : V₃ →ₗ[K] V₄)
    (f₄ : V₄ →ₗ[K] V₅) (f₅ : V₅ →ₗ[K] V₆)
    (hf₁_inj : Function.Injective f₁)
    (hf₅_surj : Function.Surjective f₅)
    (hexact₂ : ker f₂ = range f₁)
    (hexact₃ : ker f₃ = range f₂)
    (hexact₄ : ker f₄ = range f₃)
    (hexact₅ : ker f₅ = range f₄) :
    (finrank K V₁ : ℤ) - finrank K V₂ + finrank K V₃ -
    finrank K V₄ + finrank K V₅ - finrank K V₆ = 0 := by
  -- Strategy: use rank-nullity at each step
  -- For each map fᵢ : Vᵢ → Vᵢ₊₁:
  --   dim Vᵢ = dim ker fᵢ + dim range fᵢ
  -- By exactness: ker fᵢ = range fᵢ₋₁

  -- Helper: dimension of range equals codomain finrank minus kernel finrank
  have rn1 := Submodule.finrank_quotient_add_finrank (ker f₁)
  have rn2 := Submodule.finrank_quotient_add_finrank (ker f₂)
  have rn3 := Submodule.finrank_quotient_add_finrank (ker f₃)
  have rn4 := Submodule.finrank_quotient_add_finrank (ker f₄)
  have rn5 := Submodule.finrank_quotient_add_finrank (ker f₅)

  -- Use quotKerEquivRange to relate quotient to range
  rw [LinearEquiv.finrank_eq f₁.quotKerEquivRange] at rn1
  rw [LinearEquiv.finrank_eq f₂.quotKerEquivRange] at rn2
  rw [LinearEquiv.finrank_eq f₃.quotKerEquivRange] at rn3
  rw [LinearEquiv.finrank_eq f₄.quotKerEquivRange] at rn4
  rw [LinearEquiv.finrank_eq f₅.quotKerEquivRange] at rn5

  -- For f₁ injective: ker f₁ = 0, so dim range f₁ = dim V₁
  have hk1 : finrank K (ker f₁) = 0 := by
    rw [ker_eq_bot.mpr hf₁_inj]
    simp
  have hr1 : finrank K (range f₁) = finrank K V₁ := by
    omega

  -- For f₅ surjective: range f₅ = V₆
  have hr5 : finrank K (range f₅) = finrank K V₆ := by
    rw [range_eq_top.mpr hf₅_surj]
    simp

  -- By exactness: ker fᵢ = range fᵢ₋₁, so their dimensions match
  have hk2 : finrank K (ker f₂) = finrank K (range f₁) := by
    rw [hexact₂]
  have hk3 : finrank K (ker f₃) = finrank K (range f₂) := by
    rw [hexact₃]
  have hk4 : finrank K (ker f₄) = finrank K (range f₃) := by
    rw [hexact₄]
  have hk5 : finrank K (ker f₅) = finrank K (range f₄) := by
    rw [hexact₅]

  -- Now the computation
  -- dim V₁ = dim range f₁ (since ker f₁ = 0)
  -- dim V₂ = dim ker f₂ + dim range f₂ = dim range f₁ + dim range f₂
  -- dim V₃ = dim ker f₃ + dim range f₃ = dim range f₂ + dim range f₃
  -- dim V₄ = dim ker f₄ + dim range f₄ = dim range f₃ + dim range f₄
  -- dim V₅ = dim ker f₅ + dim range f₅ = dim range f₄ + dim range f₅
  -- dim V₆ = dim range f₅ (since f₅ is surjective)

  -- Substituting:
  -- V₁ - V₂ + V₃ - V₄ + V₅ - V₆
  -- = r₁ - (r₁ + r₂) + (r₂ + r₃) - (r₃ + r₄) + (r₄ + r₅) - r₅
  -- = 0

  omega

/-- Euler characteristic additivity: χ(middle) = χ(left) + χ(right) in an exact sequence.

    For a six-term exact sequence of ℂ-vector spaces:
      0 → V'₀ → V₀ → V''₀ → V'₁ → V₁ → V''₁ → 0

    with:
      χ(F') = dim V'₀ - dim V'₁
      χ(F) = dim V₀ - dim V₁
      χ(F'') = dim V''₀ - dim V''₁

    We have: χ(F) = χ(F') + χ(F'') -/
theorem eulerChar_additive_of_sixTermExact
    {V'₀ V₀ V''₀ V'₁ V₁ V''₁ : Type u}
    [AddCommGroup V'₀] [AddCommGroup V₀] [AddCommGroup V''₀]
    [AddCommGroup V'₁] [AddCommGroup V₁] [AddCommGroup V''₁]
    [Module K V'₀] [Module K V₀] [Module K V''₀]
    [Module K V'₁] [Module K V₁] [Module K V''₁]
    [Module.Finite K V'₀] [Module.Finite K V₀] [Module.Finite K V''₀]
    [Module.Finite K V'₁] [Module.Finite K V₁] [Module.Finite K V''₁]
    (ι₀ : V'₀ →ₗ[K] V₀) (π₀ : V₀ →ₗ[K] V''₀) (δ : V''₀ →ₗ[K] V'₁)
    (ι₁ : V'₁ →ₗ[K] V₁) (π₁ : V₁ →ₗ[K] V''₁)
    (hι₀_inj : Function.Injective ι₀)
    (hπ₁_surj : Function.Surjective π₁)
    (hexact_V₀ : ker π₀ = range ι₀)
    (hexact_V''₀ : ker δ = range π₀)
    (hexact_V'₁ : ker ι₁ = range δ)
    (hexact_V₁ : ker π₁ = range ι₁) :
    (finrank K V₀ : ℤ) - finrank K V₁ =
    ((finrank K V'₀ : ℤ) - finrank K V'₁) + ((finrank K V''₀ : ℤ) - finrank K V''₁) := by
  -- The alternating sum is zero:
  -- V'₀ - V₀ + V''₀ - V'₁ + V₁ - V''₁ = 0
  -- Rearranging: V₀ - V₁ = V'₀ + V''₀ - V'₁ - V''₁ = (V'₀ - V'₁) + (V''₀ - V''₁)
  have h := alternatingSum_sixTerm_exact ι₀ π₀ δ ι₁ π₁
    hι₀_inj hπ₁_surj hexact_V₀ hexact_V''₀ hexact_V'₁ hexact_V₁
  omega

end ExactSequenceHelpers
