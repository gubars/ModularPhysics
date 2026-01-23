/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Algebra.Basic

/-!
# Formal Power Series - Basic Theory

This file develops the basic theory of formal power series over a commutative ring,
following the treatment in the Waterloo C&O 430 notes (Section 7).

## Main Theorems

* `FPSBasic.invertible_iff_constantTerm_invertible` - Proposition 7.5 from Waterloo notes:
  A formal power series f(x) = Σ aₙxⁿ is invertible in R[[x]] iff a₀ is invertible in R.

## Mathematical Background

The ring R[[x]] of formal power series has elements of the form
  f(x) = a₀ + a₁x + a₂x² + ⋯ + aₙxⁿ + ⋯
where aₙ ∈ R for all n ∈ ℕ.

The key insight (Proposition 7.5) is that f(x) is invertible iff a₀ is invertible.

## References

* Waterloo C&O 430 notes, Section 7: Formal Power Series
* Mathlib documentation on PowerSeries
-/

namespace FPSBasic

open PowerSeries

variable {R : Type*} [CommRing R]

/-! ### Invertibility Criterion (Proposition 7.5) -/

/-- **Proposition 7.5 (Waterloo Notes)**: Forward direction.
    If f(x) is invertible in R[[x]], then a₀ is invertible in R. -/
theorem constantTerm_invertible_of_invertible (f : R⟦X⟧)
    (hf : IsUnit f) : IsUnit (constantCoeff f) :=
  isUnit_iff_constantCoeff.mp hf

/-- **Proposition 7.5 (Waterloo Notes)**: Backward direction.
    If a₀ is invertible in R, then f(x) is invertible in R[[x]]. -/
theorem invertible_of_constantTerm_invertible (f : R⟦X⟧)
    (hf : IsUnit (constantCoeff f)) : IsUnit f :=
  isUnit_iff_constantCoeff.mpr hf

/-- **Proposition 7.5 (Waterloo Notes)**: Complete characterization.
    A formal power series f(x) is invertible in R[[x]] if and only if
    its constant term a₀ is invertible in R. -/
theorem invertible_iff_constantTerm_invertible (f : R⟦X⟧) :
    IsUnit f ↔ IsUnit (constantCoeff f) :=
  ⟨constantTerm_invertible_of_invertible f, invertible_of_constantTerm_invertible f⟩

/-! ### Power Series with Positive Index -/

/-- A power series f(x) has positive index iff its constant term is zero.
    Such series are of the form f(x) = x · g(x) for some g(x). -/
def hasPositiveIndex (f : R⟦X⟧) : Prop :=
  constantCoeff f = 0

theorem X_hasPositiveIndex : hasPositiveIndex (X : R⟦X⟧) :=
  constantCoeff_X

/-! ### Geometric Series -/

/-- The geometric series 1/(1-x) = 1 + x + x² + ⋯ in R[[x]]. -/
noncomputable def geometricSeries : R⟦X⟧ :=
  invOfUnit (1 - X) 1

end FPSBasic
