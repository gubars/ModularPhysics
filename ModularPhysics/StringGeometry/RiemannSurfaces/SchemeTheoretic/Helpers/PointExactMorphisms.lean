/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Sheaves.LineBundles
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Sheaves.Skyscraper
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.LocalRings

/-!
# Morphisms for the Point Exact Sequence

This file provides infrastructure for constructing the morphisms in the fundamental
point exact sequence:

  0 → O(D - [p]) → O(D) → k_p → 0

## Main Definitions

* `uniformizerAt` - A uniformizer (local parameter) at point p with v_p(t) = 1
* `inclusionMorphism` - The inclusion O(D-[p]) ↪ O(D) (multiplication by uniformizer)
* `evaluationMorphism` - The evaluation O(D) → k_p (restriction to residue field)

## Mathematical Construction

**Uniformizers:**
  - From `LocalRings.exists_localParameter`: ∃ t, v_p(t) = 1
  - We use `Classical.choose` to pick one such element

**Inclusion morphism O(D - [p]) → O(D):**
  - Defined by f ↦ t_p · f where t_p is a uniformizer at p
  - If f ∈ O(D-[p])(U), then v_q(f) ≥ -(D-[p])(q) for all q ∈ U
  - v_p(f) ≥ -(D-[p])(p) = -D(p) + 1
  - v_p(t_p · f) = 1 + v_p(f) ≥ 1 + (-D(p) + 1) = -D(p) + 2 ≥ -D(p) ✓

**Evaluation morphism O(D) → k_p:**
  - Defined by restricting a section to its value at p
  - For f ∈ O(D)(U) with p ∈ U, we have v_p(f) ≥ -D(p)
  - The residue class in κ(p) is well-defined

**Exactness:**
  - ker(eval) = { f ∈ O(D)(U) : f(p) = 0 } = { f : v_p(f) ≥ 1 - D(p) } = O(D-[p])(U)
  - This shows exactness at the middle term

## References

* Hartshorne, "Algebraic Geometry", Chapter IV.1 (Riemann-Roch)
-/

open AlgebraicGeometry CategoryTheory

namespace RiemannSurfaces.SchemeTheoretic

variable (C : SmoothProjectiveCurve)

/-!
## Uniformizers

A uniformizer at a point p is a local parameter: an element t_p ∈ K(C) with v_p(t_p) = 1.
On a smooth curve, such elements exist because the stalks are DVRs.

We use `Classical.choose` on `exists_localParameter` to obtain a canonical choice.
-/

/-- A uniformizer at a point p is an element t ∈ K(C) with v_p(t) = 1.

    **Existence:** Uses `SmoothProjectiveCurve.exists_localParameter` from LocalRings.lean,
    which derives uniformizer existence from the DVR structure of stalks.

    **Construction:** `Classical.choose` picks a witness from the existence theorem. -/
noncomputable def uniformizerAt (p : C.PointType) : C.FunctionFieldType :=
  Classical.choose (C.exists_localParameter p)

/-- The uniformizer has valuation 1 at p.

    **Proof:** Follows directly from `Classical.choose_spec` on `exists_localParameter`. -/
theorem uniformizer_valuation (p : C.PointType) :
    C.valuationAt p (uniformizerAt C p) = 1 :=
  Classical.choose_spec (C.exists_localParameter p)

/-- The uniformizer is nonzero.

    **Proof:** If t_p = 0, then v_p(0) = 0 ≠ 1 by `valuationAt_zero`. -/
theorem uniformizer_ne_zero (p : C.PointType) : uniformizerAt C p ≠ 0 := by
  intro h
  have hval := uniformizer_valuation C p
  rw [h, C.valuationAt_zero] at hval
  exact one_ne_zero hval.symm

/-- The uniformizer has finite support (only finitely many points with nonzero valuation).

    **Proof:** Follows from `valuationAt_finiteSupport` in LocalRings.lean. -/
theorem uniformizer_finiteSupport (p : C.PointType) :
    Set.Finite { q : C.PointType | C.valuationAt q (uniformizerAt C p) ≠ 0 } :=
  C.valuationAt_finiteSupport (uniformizerAt C p) (uniformizer_ne_zero C p)

/-- The principal divisor of a uniformizer has degree 0.

    **Note:** v_p(t_p) = 1, so by the argument principle, the sum of valuations
    at other points is -1. This means there must be some pole(s) elsewhere. -/
theorem uniformizer_degree_zero (p : C.PointType) :
    (principalDivisor C (uniformizerAt C p) (uniformizer_ne_zero C p)).degree = 0 :=
  principalDivisor_degree_zero C (uniformizerAt C p) (uniformizer_ne_zero C p)

/-!
## The Inclusion Morphism

The inclusion O(D-[p]) → O(D) is the natural inclusion of subsheaves.

**Key insight:**
O(D-[p]) and O(D) are both subsheaves of the constant sheaf K(C).
For a section f, we have:
- f ∈ O(D-[p])(U) ⟺ v_q(f) ≥ -(D-[p])(q) for all q ∈ U
- f ∈ O(D)(U) ⟺ v_q(f) ≥ -D(q) for all q ∈ U

Since (D-[p])(q) = D(q) - [p](q):
- For q ≠ p: (D-[p])(q) = D(q), so conditions are the same
- For q = p: (D-[p])(p) = D(p) - 1, so v_p(f) ≥ -D(p)+1 > -D(p)

Therefore O(D-[p])(U) ⊆ O(D)(U), and the inclusion is just the natural embedding.
-/

/-- The inclusion morphism O(D - [p]) → O(D).

    **Mathematical definition:**
    The natural inclusion of subsheaves of K(C). For each open U:
      O(D-[p])(U) → O(D)(U)
      f ↦ f

    **Why this is well-defined:**
    If f ∈ O(D-[p])(U), then v_q(f) ≥ -(D-[p])(q) for all q ∈ U.
    - For q ≠ p: -(D-[p])(q) = -D(q), so v_q(f) ≥ -D(q) ✓
    - For q = p: -(D-[p])(p) = -D(p)+1 > -D(p), so v_p(f) ≥ -D(p) ✓
    Therefore f ∈ O(D)(U). -/
noncomputable def inclusionMorphism (D : Divisor C.toAlgebraicCurve) (p : C.PointType) :
    (divisorSheaf C (D - Divisor.point p)).toModule ⟶ (divisorSheaf C D).toModule := sorry

/-- The inclusion morphism is a monomorphism.

    **Proof:**
    The natural inclusion of a subsheaf is always injective on stalks.
    Since it's the identity on the underlying sets, it's clearly mono. -/
theorem inclusionMorphism_mono (D : Divisor C.toAlgebraicCurve) (p : C.PointType) :
    Mono (inclusionMorphism C D p) := by
  sorry

/-!
## The Evaluation Morphism

The evaluation O(D) → k_p is given by restricting a section to its value at p.
-/

/-- The evaluation morphism O(D) → k_p.

    **Mathematical definition:**
    For f ∈ O(D)(U) with p ∈ U, map f to its "value" at p.

    More precisely:
    - The stalk O_{C,p} has maximal ideal m_p
    - κ(p) = O_{C,p} / m_p is the residue field
    - For f with v_p(f) ≥ -D(p), the element t_p^{D(p)} · f is regular at p
    - Its image in κ(p) gives the evaluation

    **Type-theoretic definition:**
    A morphism in X.Modules = SheafOfModules X.ringCatSheaf from
    divisorModule C D to skyscraperModule C.toAlgebraicCurve p. -/
noncomputable def evaluationMorphism (D : Divisor C.toAlgebraicCurve) (p : C.PointType) :
    (divisorSheaf C D).toModule ⟶ skyscraperModule C.toAlgebraicCurve p := sorry

/-- The evaluation morphism is an epimorphism.

    **Proof:**
    For any element v ∈ κ(p), there exists f ∈ K(C) with f(p) = v
    (this uses that κ(p) = ℂ and global functions include constants).

    More precisely, if D(p) ≥ 0, then constant functions in O(D) surject onto κ(p).
    If D(p) < 0, we can multiply by t_p^{-D(p)} to get an element in O(D) with
    any prescribed residue class at p. -/
theorem evaluationMorphism_epi (D : Divisor C.toAlgebraicCurve) (p : C.PointType) :
    Epi (evaluationMorphism C D p) := by
  sorry

/-!
## Exactness of the Point Sequence
-/

/-- The composition i ≫ p = 0.

    **Proof:**
    For f ∈ O(D-[p])(U), the inclusion gives f ∈ O(D)(U) (same function).
    But f satisfies v_p(f) ≥ -(D-[p])(p) = -D(p) + 1 ≥ 1 - D(p).

    The evaluation at p of a function f with v_p(f) ≥ 1 gives zero in the
    residue field κ(p), because f vanishes at p (has positive valuation
    after accounting for poles allowed by D).

    More precisely: the evaluation map sends f to its residue class in κ(p).
    Functions with v_p(f) ≥ 1 - D(p) and D(p) ≥ 0 vanish at p.
    For D(p) < 0, the normalization t_p^{D(p)} · f is in m_p, hence vanishes. -/
theorem composition_zero (D : Divisor C.toAlgebraicCurve) (p : C.PointType) :
    inclusionMorphism C D p ≫ evaluationMorphism C D p = 0 := by
  sorry

/-- The sequence 0 → O(D-[p]) → O(D) → k_p → 0 is exact at the middle term.

    **Proof:**
    ker(eval) = { f ∈ O(D)(U) : f(p) = 0 in κ(p) }
             = { f ∈ K(C) : v_q(f) ≥ -D(q) for all q ∈ U, and f "vanishes at p" }

    For f ∈ O(D)(U), "f vanishes at p" means:
    - If D(p) ≥ 0: f is regular at p and f(p) = 0, i.e., v_p(f) ≥ 1
    - If D(p) < 0: t_p^{D(p)} · f is regular at p and vanishes, i.e., v_p(f) ≥ 1 - D(p)

    In both cases: v_p(f) ≥ 1 - D(p) = -(D-[p])(p)

    Combined with v_q(f) ≥ -D(q) = -(D-[p])(q) for q ≠ p, this gives f ∈ O(D-[p])(U).

    Therefore ker(eval) = O(D-[p])(U) = im(incl). -/
theorem pointSequence_exact (D : Divisor C.toAlgebraicCurve) (p : C.PointType) :
    (CategoryTheory.ShortComplex.mk
      (inclusionMorphism C D p)
      (evaluationMorphism C D p)
      (composition_zero C D p)).Exact := by
  sorry

end RiemannSurfaces.SchemeTheoretic
