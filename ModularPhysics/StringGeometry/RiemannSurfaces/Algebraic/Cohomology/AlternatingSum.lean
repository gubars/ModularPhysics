import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Alternating Sum Formula for Exact Sequences

This file proves the alternating sum formula for exact sequences of finite-dimensional
vector spaces: in any exact sequence, the alternating sum of dimensions is zero.

This is the key tool for the Riemann-Roch theorem - it gives χ(D) - χ(D-p) = 1 directly
from the exactness of the long exact sequence, without any case analysis.

## Main Results

* `alternating_sum_exact_three` - For 0 → V₁ → V₂ → V₃ → 0
* `alternating_sum_exact_five` - For 0 → V₁ → V₂ → V₃ → V₄ → V₅ → 0
-/

open scoped Classical

namespace AlternatingSum

-- We work over ℂ since that's what we need for Riemann-Roch
-- Using Module.Finite instead of FiniteDimensional to avoid binder annotation issues

section Basic

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
variable {W : Type*} [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]

/-- Rank-nullity theorem in the form we need -/
theorem rank_nullity_finrank (f : V →ₗ[ℂ] W) :
    Module.finrank ℂ V = Module.finrank ℂ (LinearMap.ker f) + Module.finrank ℂ (LinearMap.range f) := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
  rw [LinearEquiv.finrank_eq f.quotKerEquivRange] at h
  omega

/-- For an injective linear map, range has the same dimension as the domain -/
theorem finrank_range_of_injective (f : V →ₗ[ℂ] W) (hf : Function.Injective f) :
    Module.finrank ℂ (LinearMap.range f) = Module.finrank ℂ V := by
  have hker : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr hf
  have h := rank_nullity_finrank f
  rw [hker] at h
  simp at h
  omega

/-- For a surjective linear map, range has the same dimension as the codomain -/
theorem finrank_range_of_surjective (f : V →ₗ[ℂ] W) (hf : Function.Surjective f) :
    Module.finrank ℂ (LinearMap.range f) = Module.finrank ℂ W := by
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hf
  rw [hrange]
  simp

end Basic

section ThreeTerm

variable {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [Module.Finite ℂ V₁]
variable {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂] [Module.Finite ℂ V₂]
variable {V₃ : Type*} [AddCommGroup V₃] [Module ℂ V₃] [Module.Finite ℂ V₃]

/-- **Alternating sum formula for 3-term exact sequences**

    For an exact sequence 0 → V₁ →^{f₁} V₂ →^{f₂} V₃ → 0:
    dim(V₁) - dim(V₂) + dim(V₃) = 0 -/
theorem alternating_sum_exact_three
    (f₁ : V₁ →ₗ[ℂ] V₂) (f₂ : V₂ →ₗ[ℂ] V₃)
    (hf₁_inj : Function.Injective f₁)
    (hf₂_surj : Function.Surjective f₂)
    (hex : LinearMap.ker f₂ = LinearMap.range f₁) :
    (Module.finrank ℂ V₁ : ℤ) - Module.finrank ℂ V₂ + Module.finrank ℂ V₃ = 0 := by
  -- By rank-nullity: dim(V₂) = dim(ker f₂) + dim(range f₂)
  have h_rn := rank_nullity_finrank f₂
  -- Since f₂ is surjective: dim(range f₂) = dim(V₃)
  have h_range := finrank_range_of_surjective f₂ hf₂_surj
  -- By exactness: ker f₂ = range f₁
  -- Since f₁ is injective: dim(range f₁) = dim(V₁)
  have h_ker : Module.finrank ℂ (LinearMap.ker f₂) = Module.finrank ℂ V₁ := by
    rw [hex]
    exact finrank_range_of_injective f₁ hf₁_inj
  -- Combine: dim(V₂) = dim(V₁) + dim(V₃)
  omega

end ThreeTerm

section FiveTerm

variable {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [Module.Finite ℂ V₁]
variable {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂] [Module.Finite ℂ V₂]
variable {V₃ : Type*} [AddCommGroup V₃] [Module ℂ V₃] [Module.Finite ℂ V₃]
variable {V₄ : Type*} [AddCommGroup V₄] [Module ℂ V₄] [Module.Finite ℂ V₄]
variable {V₅ : Type*} [AddCommGroup V₅] [Module ℂ V₅] [Module.Finite ℂ V₅]

/-- **Alternating sum formula for 5-term exact sequences**

    For an exact sequence 0 → V₁ →^{f₁} V₂ →^{f₂} V₃ →^{f₃} V₄ →^{f₄} V₅ → 0:
    dim(V₁) - dim(V₂) + dim(V₃) - dim(V₄) + dim(V₅) = 0

    This is the key formula for Riemann-Roch. Applied to the cohomology long exact sequence
    0 → L(D-p) → L(D) → ℂ → H¹(D-p) → H¹(D) → 0
    it gives: h⁰(D-p) - h⁰(D) + 1 - h¹(D-p) + h¹(D) = 0
    which rearranges to χ(D) - χ(D-p) = 1. -/
theorem alternating_sum_exact_five
    (f₁ : V₁ →ₗ[ℂ] V₂) (f₂ : V₂ →ₗ[ℂ] V₃) (f₃ : V₃ →ₗ[ℂ] V₄) (f₄ : V₄ →ₗ[ℂ] V₅)
    (hf₁_inj : Function.Injective f₁)
    (hf₄_surj : Function.Surjective f₄)
    (hex₂ : LinearMap.ker f₂ = LinearMap.range f₁)
    (hex₃ : LinearMap.ker f₃ = LinearMap.range f₂)
    (hex₄ : LinearMap.ker f₄ = LinearMap.range f₃) :
    (Module.finrank ℂ V₁ : ℤ) - Module.finrank ℂ V₂ + Module.finrank ℂ V₃ -
    Module.finrank ℂ V₄ + Module.finrank ℂ V₅ = 0 := by
  -- Rank-nullity at each map
  have rn₂ := rank_nullity_finrank f₂
  have rn₃ := rank_nullity_finrank f₃
  have rn₄ := rank_nullity_finrank f₄

  -- f₁ is injective: dim(range f₁) = dim(V₁)
  have h_range_f₁ := finrank_range_of_injective f₁ hf₁_inj

  -- f₄ is surjective: dim(range f₄) = dim(V₅)
  have h_range_f₄ := finrank_range_of_surjective f₄ hf₄_surj

  -- By exactness: ker fᵢ = range fᵢ₋₁
  have h_ker₂ : Module.finrank ℂ (LinearMap.ker f₂) = Module.finrank ℂ (LinearMap.range f₁) := by
    rw [hex₂]
  have h_ker₃ : Module.finrank ℂ (LinearMap.ker f₃) = Module.finrank ℂ (LinearMap.range f₂) := by
    rw [hex₃]
  have h_ker₄ : Module.finrank ℂ (LinearMap.ker f₄) = Module.finrank ℂ (LinearMap.range f₃) := by
    rw [hex₄]

  -- Telescoping sum gives 0
  omega

/-- Corollary: The formula in the form used for Riemann-Roch -/
theorem alternating_sum_exact_five'
    (f₁ : V₁ →ₗ[ℂ] V₂) (f₂ : V₂ →ₗ[ℂ] V₃) (f₃ : V₃ →ₗ[ℂ] V₄) (f₄ : V₄ →ₗ[ℂ] V₅)
    (hf₁_inj : Function.Injective f₁)
    (hf₄_surj : Function.Surjective f₄)
    (hex₂ : LinearMap.ker f₂ = LinearMap.range f₁)
    (hex₃ : LinearMap.ker f₃ = LinearMap.range f₂)
    (hex₄ : LinearMap.ker f₄ = LinearMap.range f₃) :
    (Module.finrank ℂ V₂ : ℤ) - Module.finrank ℂ V₁ +
    Module.finrank ℂ V₄ - Module.finrank ℂ V₅ = Module.finrank ℂ V₃ := by
  have h := alternating_sum_exact_five f₁ f₂ f₃ f₄ hf₁_inj hf₄_surj hex₂ hex₃ hex₄
  omega

end FiveTerm

end AlternatingSum
