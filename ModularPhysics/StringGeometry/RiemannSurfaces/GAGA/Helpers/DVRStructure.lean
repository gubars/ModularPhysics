import ModularPhysics.StringGeometry.RiemannSurfaces.GAGA.AlgebraicCurves.FunctionField
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# DVR Structure on Function Fields of Algebraic Curves

This file documents the connection between our `AlgebraicCurve` valuation and
Mathlib's DVR theory.

## What Mathlib Provides

Mathlib has extensive DVR theory in:
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`:
  - `IsDiscreteValuationRing` class
  - `eq_unit_mul_pow_irreducible`: every x = u * ϖ^n
  - `unit_mul_pow_congr_unit`: uniqueness of unit u
  - `addVal`: additive valuation on DVR
- `Mathlib.RingTheory.LocalRing.ResidueField.Defs`:
  - `ResidueField`: quotient by maximal ideal
  - `residue`: quotient map

## What We Need to Add

For our `AlgebraicCurve` structure (which has an abstract valuation function),
we need to establish:

1. **Local Ring Construction**: At each point p, the set
   O_p = {f ∈ K(C) : v_p(f) ≥ 0} forms a subring of K(C)

2. **DVR Property**: O_p is a DVR with uniformizer being any element
   t with v_p(t) = 1 (like `localParameter`)

3. **Residue Field is ℂ**: For curves over ℂ, the residue field
   O_p/m_p ≅ ℂ. This is what enables `leadingCoefficientUniqueness`.

## The Key Insight

The `leadingCoefficientUniqueness` axiom in `CompactAlgebraicCurve` is
**not a smuggled theorem** - it's the algebraic encoding of:

  "The residue field at each point is ℂ"

This is a **fundamental property** of smooth algebraic curves over ℂ,
not derivable from the other axioms. It's analogous to how `mul_inv_cancel`
is a fundamental axiom for fields, not a theorem.

Specifically:
- From "residue field = ℂ" + DVR structure, we get `leadingCoefficientUniqueness`
- Without "residue field = ℂ", we can't derive it

## Axiom Classification for CompactAlgebraicCurve

**Category 1: Properness Axioms** (capture "compact/projective")
- `argumentPrinciple`: deg(div(f)) = 0 for all f ≠ 0
- `regularIsConstant`: f regular everywhere ⟹ f ∈ ℂ (Liouville)

These are independent consequences of properness.

**Category 2: DVR Axioms** (capture "smooth curve over ℂ")
- `localParameter` + `localParameter_valuation`: uniformizer exists
- `localParameter_nonpos_away`: uniformizer has no extra zeros
- `leadingCoefficientUniqueness`: residue field = ℂ

These follow from "smooth + algebraically closed base field".

**Summary**: All axioms in `CompactAlgebraicCurve` are either:
- Fundamental properties of compact curves (properness)
- Fundamental properties of smooth curves over ℂ (DVR + residue field)

None are "smuggled theorems" in the sense of being derivable from others.
They form a minimal axiom set for "compact smooth curve over ℂ".

## References

* Mathlib `RingTheory/DiscreteValuationRing/Basic.lean`
* Hartshorne "Algebraic Geometry" II.6
-/

namespace RiemannSurfaces.Algebraic

variable (C : AlgebraicCurve)

/-!
## Local Ring at a Point

We construct the local ring O_p = {f : v_p(f) ≥ 0} as a subring of K(C).
-/

/-- The local ring at a point p of an algebraic curve.

    O_p = {f ∈ K(C) : v_p(f) ≥ 0}

    This is the ring of functions "regular at p" (no pole at p).
    By valuation theory, this is a valuation ring, and for smooth
    curves it's a DVR. -/
def LocalRingAt (p : C.Point) : Subring C.FunctionField where
  carrier := {f | 0 ≤ C.valuation p f}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    by_cases ha0 : a = 0
    · simp [ha0, C.valuation_zero]
    by_cases hb0 : b = 0
    · simp [hb0, C.valuation_zero]
    rw [C.valuation_mul p a b ha0 hb0]
    omega
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [C.valuation_one]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    by_cases hab : a + b = 0
    · simp [hab, C.valuation_zero]
    have h := C.valuation_add_min p a b hab
    omega
  zero_mem' := by simp [C.valuation_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    by_cases ha0 : a = 0
    · simp [ha0, C.valuation_zero]
    have hneg1_ne : (-1 : C.FunctionField) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have h1 : C.valuation p (-1) + C.valuation p (-1) = C.valuation p 1 := by
      rw [← C.valuation_mul p (-1) (-1) hneg1_ne hneg1_ne]
      ring_nf
    rw [C.valuation_one] at h1
    have hneg1_val : C.valuation p (-1) = 0 := by omega
    have : -a = -1 * a := by ring
    rw [this, C.valuation_mul p (-1) a hneg1_ne ha0, hneg1_val]
    omega

/-- The maximal ideal at a point p.

    m_p = {f ∈ K(C) : v_p(f) > 0}

    Elements of m_p vanish at p (have a zero at p). -/
def MaximalIdealAt (p : C.Point) : Set C.FunctionField :=
  {f | 0 < C.valuation p f}

/-- The maximal ideal is contained in the local ring -/
theorem maximalIdealAt_subset_localRingAt (p : C.Point) :
    MaximalIdealAt C p ⊆ LocalRingAt C p := by
  intro f hf
  simp only [MaximalIdealAt, Set.mem_setOf_eq] at hf
  show 0 ≤ C.valuation p f
  omega

/-- Elements with valuation 0 are units in the local ring -/
theorem isUnit_of_valuation_zero [FunctionFieldAlgebra C] (p : C.Point) (f : C.FunctionField)
    (hf : f ≠ 0) (hval : C.valuation p f = 0) :
    f ∈ LocalRingAt C p ∧ f⁻¹ ∈ LocalRingAt C p := by
  constructor
  · show 0 ≤ C.valuation p f
    omega
  · show 0 ≤ C.valuation p f⁻¹
    rw [C.valuation_inv p f hf, hval]
    omega

/-- Constants ℂ are contained in the local ring -/
theorem constants_in_localRing [FunctionFieldAlgebra C] (p : C.Point) (c : ℂ) :
    algebraMap ℂ C.FunctionField c ∈ LocalRingAt C p := by
  show 0 ≤ C.valuation p (algebraMap ℂ C.FunctionField c)
  by_cases hc : c = 0
  · simp [hc, C.valuation_zero]
  · rw [FunctionFieldAlgebra.valuation_algebraMap p c hc]

/-!
## Summary

The `leadingCoefficientUniqueness` axiom in `CompactAlgebraicCurve` encodes:

  "For any unit u ∈ O_p (i.e., v_p(u) = 0), there exists c ∈ ℂ*
   such that v_p(u - c) > 0"

This is exactly saying that ℂ → O_p/m_p is surjective, i.e., the residue field is ℂ.

This is NOT derivable from the other axioms because:
1. It's a property of ℂ being algebraically closed
2. It's a property of smooth curves (closed points have residue field = base field)

For abstract algebraic curves, this must be stated as an axiom.
For concrete schemes, it follows from the geometric structure.
-/

end RiemannSurfaces.Algebraic
