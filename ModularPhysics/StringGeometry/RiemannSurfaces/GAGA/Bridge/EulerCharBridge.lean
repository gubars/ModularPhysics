/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Euler Characteristic Bridge for Exact Sequences

This file proves the key property needed for the (0,0) case in PointExactSequence:
the alternating sum of dimensions in an exact sequence of finite-dimensional
vector spaces is zero.

## Main Results

* `alternating_sum_exact_five` - For a 5-term exact sequence 0 → V₁ → V₂ → V₃ → V₄ → V₅ → 0,
  we have dim V₁ - dim V₂ + dim V₃ - dim V₄ + dim V₅ = 0

This is the core linear algebra fact that, combined with the exactness of the
point exact sequence and dim V₃ = 1, gives a + b = 1, ruling out the (0,0) case.

## Mathematical Background

For any exact sequence of finite-dimensional vector spaces:
  0 → V₁ → V₂ → ... → Vₙ → 0

The alternating sum Σᵢ (-1)ⁱ dim(Vᵢ) = 0.

This follows from the rank-nullity theorem applied at each step.

## References

* Weibel "An Introduction to Homological Algebra" Section 1.1
-/

namespace RiemannSurfaces.GAGA.Bridge

open Module FiniteDimensional

variable {k : Type*} [DivisionRing k]
variable {V₁ V₂ V₃ V₄ V₅ : Type*}
variable [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄] [AddCommGroup V₅]
variable [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄] [Module k V₅]
variable [FiniteDimensional k V₁] [FiniteDimensional k V₂] [FiniteDimensional k V₃]
variable [FiniteDimensional k V₄] [FiniteDimensional k V₅]

/-!
## Exact Sequence Properties

An exact sequence at a position means: kernel of outgoing map = image of incoming map.
-/

/-!
## The Main Alternating Sum Theorem

For a 5-term exact sequence:
  0 → V₁ →[f₁] V₂ →[f₂] V₃ →[f₃] V₄ →[f₄] V₅ → 0

with:
  - f₁ injective
  - ker(f₂) = im(f₁)
  - ker(f₃) = im(f₂)
  - ker(f₄) = im(f₃)
  - f₄ surjective

The alternating sum dim V₁ - dim V₂ + dim V₃ - dim V₄ + dim V₅ = 0.
-/

/-- The alternating sum of dimensions in a 5-term exact sequence is zero. -/
theorem alternating_sum_exact_five
    (f₁ : V₁ →ₗ[k] V₂) (f₂ : V₂ →ₗ[k] V₃) (f₃ : V₃ →ₗ[k] V₄) (f₄ : V₄ →ₗ[k] V₅)
    (inj_f₁ : Function.Injective f₁)
    (exact_V₂ : LinearMap.ker f₂ = LinearMap.range f₁)
    (exact_V₃ : LinearMap.ker f₃ = LinearMap.range f₂)
    (exact_V₄ : LinearMap.ker f₄ = LinearMap.range f₃)
    (surj_f₄ : Function.Surjective f₄) :
    (finrank k V₁ : ℤ) - finrank k V₂ + finrank k V₃ - finrank k V₄ + finrank k V₅ = 0 := by
  -- Step 1: dim(im f₁) = dim V₁ (from injectivity)
  have h1 : finrank k (LinearMap.range f₁) = finrank k V₁ :=
    LinearMap.finrank_range_of_inj inj_f₁
  -- Step 2: dim(ker f₂) = dim V₁ (from exactness at V₂)
  have h2 : finrank k (LinearMap.ker f₂) = finrank k V₁ := by
    rw [exact_V₂, h1]
  -- Step 3: Rank-nullity for f₂: dim V₂ = dim(ker f₂) + dim(im f₂)
  have rn2 : finrank k V₂ = finrank k (LinearMap.ker f₂) + finrank k (LinearMap.range f₂) := by
    have h := LinearMap.finrank_range_add_finrank_ker f₂
    omega
  -- Step 4: dim(im f₂) = dim V₂ - dim V₁
  have h3 : finrank k (LinearMap.range f₂) = finrank k V₂ - finrank k V₁ := by
    rw [h2] at rn2; omega
  -- Step 5: dim(ker f₃) = dim V₂ - dim V₁ (from exactness at V₃)
  have h4 : finrank k (LinearMap.ker f₃) = finrank k V₂ - finrank k V₁ := by
    rw [exact_V₃, h3]
  -- Step 6: Rank-nullity for f₃
  have rn3 : finrank k V₃ = finrank k (LinearMap.ker f₃) + finrank k (LinearMap.range f₃) := by
    have h := LinearMap.finrank_range_add_finrank_ker f₃
    omega
  -- Step 7: We need dim V₁ ≤ dim V₂ for the subtraction to be valid
  have h_le : finrank k V₁ ≤ finrank k V₂ := by
    calc finrank k V₁ = finrank k (LinearMap.range f₁) := h1.symm
      _ ≤ finrank k V₂ := Submodule.finrank_le (LinearMap.range f₁)
  -- Step 8: dim(im f₃) = dim V₃ - (dim V₂ - dim V₁)
  have h5 : finrank k (LinearMap.range f₃) = finrank k V₃ - (finrank k V₂ - finrank k V₁) := by
    rw [h4] at rn3; omega
  -- Step 9: dim(ker f₄) = dim V₃ - dim V₂ + dim V₁ (from exactness at V₄)
  have h6 : finrank k (LinearMap.ker f₄) = finrank k V₃ - (finrank k V₂ - finrank k V₁) := by
    rw [exact_V₄, h5]
  -- Step 10: dim(im f₄) = dim V₅ (from surjectivity)
  have h7 : finrank k (LinearMap.range f₄) = finrank k V₅ := by
    rw [LinearMap.range_eq_top.mpr surj_f₄]
    exact finrank_top k V₅
  -- Step 11: Rank-nullity for f₄
  have rn4 : finrank k V₄ = finrank k (LinearMap.ker f₄) + finrank k (LinearMap.range f₄) := by
    have h := LinearMap.finrank_range_add_finrank_ker f₄
    omega
  -- Step 12: We need dim V₂ - dim V₁ ≤ dim V₃
  have h_le2 : finrank k V₂ - finrank k V₁ ≤ finrank k V₃ := by
    calc finrank k V₂ - finrank k V₁ = finrank k (LinearMap.range f₂) := h3.symm
      _ ≤ finrank k V₃ := Submodule.finrank_le (LinearMap.range f₂)
  -- Step 13: dim V₄ = (dim V₃ - dim V₂ + dim V₁) + dim V₅
  have h8 : finrank k V₄ = finrank k V₃ - (finrank k V₂ - finrank k V₁) + finrank k V₅ := by
    rw [h6, h7] at rn4
    exact rn4
  -- Step 14: The alternating sum is zero
  omega

/-- Rearranged form: (dim V₂ - dim V₁) + (dim V₄ - dim V₅) = dim V₃

    This is the form used in PointExactSequence:
    a + b = 1 where a = dim L(D) - dim L(D-p), b = dim L(K-D+p) - dim L(K-D), dim V₃ = 1 -/
theorem alternating_sum_exact_five'
    (f₁ : V₁ →ₗ[k] V₂) (f₂ : V₂ →ₗ[k] V₃) (f₃ : V₃ →ₗ[k] V₄) (f₄ : V₄ →ₗ[k] V₅)
    (inj_f₁ : Function.Injective f₁)
    (exact_V₂ : LinearMap.ker f₂ = LinearMap.range f₁)
    (exact_V₃ : LinearMap.ker f₃ = LinearMap.range f₂)
    (exact_V₄ : LinearMap.ker f₄ = LinearMap.range f₃)
    (surj_f₄ : Function.Surjective f₄) :
    (finrank k V₂ - finrank k V₁) + (finrank k V₄ - finrank k V₅) = finrank k V₃ := by
  -- First establish the needed inequalities
  have h1 : finrank k (LinearMap.range f₁) = finrank k V₁ :=
    LinearMap.finrank_range_of_inj inj_f₁
  have h_le1 : finrank k V₁ ≤ finrank k V₂ := by
    calc finrank k V₁ = finrank k (LinearMap.range f₁) := h1.symm
      _ ≤ finrank k V₂ := Submodule.finrank_le (LinearMap.range f₁)
  have h_le2 : finrank k V₅ ≤ finrank k V₄ := by
    have rn := LinearMap.finrank_range_add_finrank_ker f₄
    have hrange : finrank k (LinearMap.range f₄) = finrank k V₅ := by
      rw [LinearMap.range_eq_top.mpr surj_f₄]
      exact finrank_top k V₅
    omega
  -- Now use the main theorem
  have h := alternating_sum_exact_five f₁ f₂ f₃ f₄ inj_f₁ exact_V₂ exact_V₃ exact_V₄ surj_f₄
  omega

/-!
## Application to Point Exact Sequence

The point exact sequence has the form:
  0 → L(D-p) → L(D) → ℂ → L(K-D+p)* → L(K-D)* → 0

where dim V₃ = dim ℂ = 1. The alternating sum theorem gives:
  (dim L(D) - dim L(D-p)) + (dim L(K-D+p) - dim L(K-D)) = 1
  i.e., a + b = 1

This rules out the (0,0) case where a = 0 and b = 0.
-/

/-- For a 5-term exact sequence with dim V₃ = 1, we have a + b = 1 -/
theorem a_plus_b_eq_one
    (f₁ : V₁ →ₗ[k] V₂) (f₂ : V₂ →ₗ[k] V₃) (f₃ : V₃ →ₗ[k] V₄) (f₄ : V₄ →ₗ[k] V₅)
    (inj_f₁ : Function.Injective f₁)
    (exact_V₂ : LinearMap.ker f₂ = LinearMap.range f₁)
    (exact_V₃ : LinearMap.ker f₃ = LinearMap.range f₂)
    (exact_V₄ : LinearMap.ker f₄ = LinearMap.range f₃)
    (surj_f₄ : Function.Surjective f₄)
    (hV₃ : finrank k V₃ = 1) :
    (finrank k V₂ - finrank k V₁) + (finrank k V₄ - finrank k V₅) = 1 := by
  rw [alternating_sum_exact_five' f₁ f₂ f₃ f₄ inj_f₁ exact_V₂ exact_V₃ exact_V₄ surj_f₄, hV₃]

/-- The (0,0) case is impossible for a 5-term exact sequence with dim V₃ = 1 -/
theorem impossible_zero_zero
    (f₁ : V₁ →ₗ[k] V₂) (f₂ : V₂ →ₗ[k] V₃) (f₃ : V₃ →ₗ[k] V₄) (f₄ : V₄ →ₗ[k] V₅)
    (inj_f₁ : Function.Injective f₁)
    (exact_V₂ : LinearMap.ker f₂ = LinearMap.range f₁)
    (exact_V₃ : LinearMap.ker f₃ = LinearMap.range f₂)
    (exact_V₄ : LinearMap.ker f₄ = LinearMap.range f₃)
    (surj_f₄ : Function.Surjective f₄)
    (hV₃ : finrank k V₃ = 1)
    (ha : finrank k V₂ - finrank k V₁ = 0)
    (hb : finrank k V₄ - finrank k V₅ = 0) : False := by
  have h := a_plus_b_eq_one f₁ f₂ f₃ f₄ inj_f₁ exact_V₂ exact_V₃ exact_V₄ surj_f₄ hV₃
  omega

end RiemannSurfaces.GAGA.Bridge
