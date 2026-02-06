/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.LocalRings
import Mathlib.Data.Finsupp.BigOperators

/-!
# Weil Divisors on Algebraic Curves

This file defines Weil divisors on algebraic curves in a purely scheme-theoretic way.

## Main Definitions

* `Divisor` - A Weil divisor: formal ℤ-linear combination of closed points
* `Divisor.degree` - The degree of a divisor (sum of coefficients)
* `principalDivisor` - The divisor of a rational function
* `Divisor.effective` - A divisor with non-negative coefficients

## Main Results

* `principalDivisor_degree_zero` - Principal divisors have degree zero (Argument Principle)

## Scheme-Theoretic Approach

Divisors are defined purely in terms of:
- Closed points of the scheme (C.PointType)
- Valuations at points (from DVR structure of stalks)
- Finite support condition

## References

* Hartshorne, "Algebraic Geometry", Chapter II.6 (Divisors)
* Stacks Project, Tag 01WO (Weil Divisors)
-/

open AlgebraicGeometry Finsupp BigOperators

namespace RiemannSurfaces.SchemeTheoretic

variable (C : AlgebraicCurve)

/-!
## Weil Divisors

A Weil divisor on a curve is a formal ℤ-linear combination of closed points.
-/

/-- A Weil divisor on an algebraic curve: a formal ℤ-linear combination of closed points
    with finite support.

    **Scheme-theoretic definition:**
    D = Σ_p n_p · [p] where n_p ∈ ℤ and only finitely many n_p ≠ 0.

    We use `Finsupp` to automatically handle the finite support condition. -/
def Divisor : Type _ := C.PointType →₀ ℤ

namespace Divisor

variable {C}

noncomputable instance : Zero (Divisor C) := inferInstanceAs (Zero (C.PointType →₀ ℤ))
noncomputable instance : Add (Divisor C) := inferInstanceAs (Add (C.PointType →₀ ℤ))
noncomputable instance : Neg (Divisor C) := inferInstanceAs (Neg (C.PointType →₀ ℤ))
noncomputable instance : Sub (Divisor C) := inferInstanceAs (Sub (C.PointType →₀ ℤ))
noncomputable instance : AddCommGroup (Divisor C) := inferInstanceAs (AddCommGroup (C.PointType →₀ ℤ))

/-- Coercion to get the coefficient function. -/
instance : CoeFun (Divisor C) (fun _ => C.PointType → ℤ) := inferInstanceAs (CoeFun (C.PointType →₀ ℤ) _)

/-- Extensionality for divisors. -/
@[ext]
theorem ext {D E : Divisor C} (h : ∀ p, D p = E p) : D = E := Finsupp.ext h

/-- The coefficient of a divisor at a point. -/
def coeff (D : Divisor C) (p : C.PointType) : ℤ := D p

/-- The support of a divisor: points with nonzero coefficient. -/
def supp (D : Divisor C) : Finset C.PointType := Finsupp.support D

/-- A single point as a divisor: [p]. -/
noncomputable def point (p : C.PointType) : Divisor C := Finsupp.single p 1

/-- The degree of a divisor: sum of all coefficients.

    deg(D) = Σ_p n_p -/
noncomputable def degree (D : Divisor C) : ℤ := Finsupp.sum D (fun _ n => n)

/-- Degree is a group homomorphism. -/
theorem degree_zero : degree (0 : Divisor C) = 0 := by
  simp only [degree, Finsupp.sum_zero_index]

theorem degree_add (D E : Divisor C) : degree (D + E) = degree D + degree E := by
  simp only [degree]
  rw [Finsupp.sum_add_index']
  · intro _; rfl
  · intro _ _ _; ring

theorem degree_neg (D : Divisor C) : degree (-D) = -degree D := by
  simp only [degree]
  rw [Finsupp.sum_neg_index]
  simp only [Finsupp.sum, Finset.sum_neg_distrib]
  intro _; rfl

/-- Degree of a single point divisor is 1. -/
theorem degree_point (p : C.PointType) : degree (point p) = 1 := by
  simp only [degree, point, Finsupp.sum_single_index]

/-- A divisor is effective if all coefficients are non-negative. -/
def effective (D : Divisor C) : Prop := ∀ p, 0 ≤ D.coeff p

/-- Notation: D ≥ E means D - E is effective. -/
instance : LE (Divisor C) where
  le D E := (D - E).effective

/-- The cardinality of the support. -/
noncomputable def supportCard (D : Divisor C) : ℕ := D.supp.card

/-- Zero divisor has empty support. -/
theorem supp_zero : (0 : Divisor C).supp = ∅ := Finsupp.support_zero

/-- Zero divisor has support cardinality 0. -/
theorem supportCard_zero : (0 : Divisor C).supportCard = 0 := by
  simp only [supportCard, supp_zero, Finset.card_empty]

/-- A nonzero divisor has nonempty support. -/
theorem exists_mem_support_of_ne_zero (D : Divisor C) (hD : D ≠ 0) :
    ∃ p, p ∈ D.supp := by
  have hne : D.supp.Nonempty := Finsupp.support_nonempty_iff.mpr hD
  exact hne

/-- Degree of (D - point p) when p ∈ supp(D). -/
theorem degree_sub_point (D : Divisor C) (p : C.PointType) :
    degree (D - point p) = degree D - 1 := by
  rw [sub_eq_add_neg, degree_add, degree_neg, degree_point]
  ring

/-- Degree of (D + point p). -/
theorem degree_add_point (D : Divisor C) (p : C.PointType) :
    degree (D + point p) = degree D + 1 := by
  rw [degree_add, degree_point]

end Divisor

/-!
## Principal Divisors

The divisor of a nonzero rational function, using valuations from DVR structure.
-/

variable {C}

/-- The principal divisor of a nonzero rational function f ∈ K(C)*.

    **Scheme-theoretic definition:**
    div(f) = Σ_p v_p(f) · [p]
    where v_p is the discrete valuation at p (from DVR structure of stalk).

    Uses `SmoothProjectiveCurve.valuationAt` from LocalRings.lean. -/
noncomputable def principalDivisor (C : SmoothProjectiveCurve) (f : C.FunctionFieldType) (hf : f ≠ 0) :
    Divisor C.toAlgebraicCurve :=
  -- The support is finite by valuationAt_finiteSupport
  -- We use Finsupp.ofSupportFinite
  Finsupp.ofSupportFinite (fun p => C.valuationAt p f) (C.valuationAt_finiteSupport f hf)

namespace PrincipalDivisor

variable (C : SmoothProjectiveCurve)

/-- The coefficient of div(f) at p equals v_p(f). -/
theorem coeff_eq_valuation (f : C.FunctionFieldType) (hf : f ≠ 0) (p : C.PointType) :
    (principalDivisor C f hf).coeff p = C.valuationAt p f := by
  simp only [principalDivisor, Divisor.coeff, Finsupp.ofSupportFinite_coe]

/-- div(fg) = div(f) + div(g).

    **Proof:** Follows from multiplicativity of valuations. -/
theorem mul (f g : C.FunctionFieldType) (hf : f ≠ 0) (hg : g ≠ 0) :
    principalDivisor C (f * g) (mul_ne_zero hf hg) =
    principalDivisor C f hf + principalDivisor C g hg := by
  ext p
  simp only [principalDivisor, Finsupp.ofSupportFinite_coe]
  rw [Finsupp.add_apply]
  exact C.valuationAt_mul p f g hf hg

/-- div(f⁻¹) = -div(f).

    **Proof:** Follows from v_p(f⁻¹) = -v_p(f). -/
theorem inv (f : C.FunctionFieldType) (hf : f ≠ 0) :
    principalDivisor C f⁻¹ (inv_ne_zero hf) = -principalDivisor C f hf := by
  ext p
  simp only [principalDivisor, Finsupp.ofSupportFinite_coe]
  rw [Finsupp.neg_apply]
  exact C.valuationAt_inv p f hf

end PrincipalDivisor

/-!
## Argument Principle

The degree of a principal divisor is zero. This is the algebraic form
of the "argument principle" from complex analysis.
-/

/-- **Argument Principle (Algebraic Form):**
    The degree of a principal divisor is zero.

    deg(div(f)) = Σ_p v_p(f) = 0

    **Proof outline:**
    For a proper curve, this follows from:
    1. f defines a morphism f : C → ℙ¹
    2. The degree of the pullback of any point is constant (properness)
    3. deg(div(f)) = deg(f⁻¹(0)) - deg(f⁻¹(∞)) = n - n = 0

    Alternatively, use the fact that on a proper curve,
    the global regular functions are constants (Liouville). -/
theorem principalDivisor_degree_zero (C : SmoothProjectiveCurve) (f : C.FunctionFieldType) (hf : f ≠ 0) :
    (principalDivisor C f hf).degree = 0 := by
  -- This is a deep theorem requiring properness
  sorry

/-!
## Linear Equivalence

Two divisors are linearly equivalent if they differ by a principal divisor.
-/

/-- Two divisors are linearly equivalent if D - E = div(f) for some f ∈ K(C)*. -/
def linearlyEquivalent (C : SmoothProjectiveCurve) (D E : Divisor C.toAlgebraicCurve) : Prop :=
  ∃ (f : C.FunctionFieldType) (hf : f ≠ 0), D - E = principalDivisor C f hf

/-- Linear equivalence is an equivalence relation. -/
theorem linearlyEquivalent_refl (C : SmoothProjectiveCurve) (D : Divisor C.toAlgebraicCurve) :
    linearlyEquivalent C D D := by
  use 1, one_ne_zero
  simp only [sub_self]
  ext p
  simp only [Finsupp.coe_zero, Pi.zero_apply, principalDivisor, Finsupp.ofSupportFinite_coe]
  exact (C.valuationAt_one p).symm

/-- Linearly equivalent divisors have the same degree. -/
theorem degree_eq_of_linearlyEquivalent (C : SmoothProjectiveCurve)
    (D E : Divisor C.toAlgebraicCurve) (h : linearlyEquivalent C D E) :
    D.degree = E.degree := by
  obtain ⟨f, hf, heq⟩ := h
  have hdeg : (D - E).degree = 0 := by
    rw [heq]
    exact principalDivisor_degree_zero C f hf
  -- D - E = D + (-E), so degree(D - E) = degree(D) + degree(-E) = degree(D) - degree(E)
  rw [sub_eq_add_neg] at hdeg
  have h1 : (D + -E).degree = D.degree + (-E).degree := Divisor.degree_add D (-E)
  have h2 : (-E).degree = -E.degree := Divisor.degree_neg E
  rw [h1, h2] at hdeg
  linarith

end RiemannSurfaces.SchemeTheoretic
