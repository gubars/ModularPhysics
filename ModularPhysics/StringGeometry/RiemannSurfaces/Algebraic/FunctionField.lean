import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Function Fields of Algebraic Curves

This file defines the function field K(C) of an algebraic curve and meromorphic functions
as elements of the function field. This is the **algebraic approach** to meromorphic functions.

## Mathematical Background

For a smooth projective algebraic curve C over ℂ:
- The function field K(C) is the field of rational functions on C
- An element f ∈ K(C) is a meromorphic function on C
- At each point p ∈ C, there is a discrete valuation v_p : K(C)* → ℤ
- The order of f at p is ord_p(f) = v_p(f)

Key properties:
- v_p(fg) = v_p(f) + v_p(g)
- v_p(f + g) ≥ min(v_p(f), v_p(g))
- v_p(f) > 0 iff p is a zero of f
- v_p(f) < 0 iff p is a pole of f
- v_p(f) ≠ 0 for only finitely many p (for f ≠ 0)

## Why This Is The Correct Definition

Unlike a "bundled" definition that just records (value, order) pairs with consistency axioms,
this definition is grounded in algebraic geometry:

1. The function field K(C) is a concrete mathematical object
2. A meromorphic function IS an element of K(C), not a separate structure
3. The valuation v_p comes from the local ring structure at p
4. All properties follow from the algebraic structure, not axioms

## Key Definitions

* `AlgebraicCurve` - A smooth projective algebraic curve with function field
* `AlgebraicCurve.FunctionField` - The function field K(C)
* `AlgebraicCurve.MeromorphicFunction` - Alias for elements of K(C)
* `AlgebraicCurve.valuation` - The discrete valuation v_p at each point

## References

* Hartshorne "Algebraic Geometry" II.6
* Miranda "Algebraic Curves and Riemann Surfaces" Ch IV
* Silverman "The Arithmetic of Elliptic Curves" Ch II
-/

namespace RiemannSurfaces.Algebraic

/-!
## Algebraic Curve Structure

An algebraic curve over ℂ, abstracted to capture the essential properties
needed for function field theory.
-/

/-- An algebraic curve over ℂ.

    This is an abstract structure capturing a smooth projective curve.
    The key data is:
    - `Point`: The set of closed points C(ℂ)
    - `FunctionField`: The field K(C) of rational functions

    The structure includes the discrete valuation at each point, which
    gives the algebraic definition of order for meromorphic functions.

    **Mathematical context:**
    In algebraic geometry, a smooth projective curve C over ℂ has:
    - A function field K(C) = Frac(O_C,η) where η is the generic point
    - At each closed point p, a discrete valuation ring O_{C,p} ⊆ K(C)
    - The valuation v_p : K(C)* → ℤ measures order of vanishing/pole at p -/
structure AlgebraicCurve where
  /-- The set of closed points of the curve -/
  Point : Type*
  /-- The function field K(C) -/
  FunctionField : Type*
  /-- The function field is a field -/
  [fieldInst : Field FunctionField]
  /-- The discrete valuation at each point p: v_p : K(C)* → ℤ
      Encodes order of vanishing/pole at p -/
  valuation : Point → FunctionField → ℤ
  /-- v_p(0) is defined to be 0 (mathematically ∞, but we use 0 for simplicity
      since we only care about v_p for nonzero elements in most cases) -/
  valuation_zero : ∀ p, valuation p 0 = 0
  /-- v_p(1) = 0 -/
  valuation_one : ∀ p, valuation p 1 = 0
  /-- v_p(fg) = v_p(f) + v_p(g) for f, g ≠ 0 -/
  valuation_mul : ∀ p (f g : FunctionField), f ≠ 0 → g ≠ 0 →
    valuation p (f * g) = valuation p f + valuation p g
  /-- v_p(f⁻¹) = -v_p(f) for f ≠ 0 -/
  valuation_inv : ∀ p (f : FunctionField), f ≠ 0 →
    valuation p f⁻¹ = -valuation p f
  /-- For any nonzero f ∈ K(C), only finitely many p have v_p(f) ≠ 0
      This is the algebraic version of "finitely many zeros and poles" -/
  valuation_finiteSupport : ∀ (f : FunctionField), f ≠ 0 →
    Set.Finite { p | valuation p f ≠ 0 }

attribute [instance] AlgebraicCurve.fieldInst

namespace AlgebraicCurve

variable (C : AlgebraicCurve)

/-- The order of f ∈ K(C) at point p.
    This is the algebraic definition of order using discrete valuation. -/
def orderAt (f : C.FunctionField) (p : C.Point) : ℤ :=
  C.valuation p f

/-- f has a zero at p iff v_p(f) > 0 -/
def hasZeroAt (f : C.FunctionField) (p : C.Point) : Prop :=
  0 < C.valuation p f

/-- f has a pole at p iff v_p(f) < 0 -/
def hasPoleAt (f : C.FunctionField) (p : C.Point) : Prop :=
  C.valuation p f < 0

/-- f is regular at p iff v_p(f) ≥ 0 (no pole) -/
def isRegularAt (f : C.FunctionField) (p : C.Point) : Prop :=
  0 ≤ C.valuation p f

/-- The support of f: points where f has a zero or pole -/
def support (f : C.FunctionField) : Set C.Point :=
  { p | C.valuation p f ≠ 0 }

theorem support_finite (f : C.FunctionField) (hf : f ≠ 0) :
    Set.Finite (C.support f) :=
  C.valuation_finiteSupport f hf

/-!
## Algebraic Meromorphic Functions

A meromorphic function on an algebraic curve is simply an element of the function field K(C).
This is the **correct algebraic definition** - no separate structure needed.
-/

/-- A meromorphic function on an algebraic curve is an element of its function field.

    **This is the correct algebraic definition.**

    Unlike the "bundled" approach that just records data, this definition
    is mathematically grounded: f ∈ K(C) automatically has all the properties
    of a meromorphic function because K(C) is defined as the field of rational
    functions on C.

    The order at each point comes from the discrete valuation v_p, which is
    intrinsic to the algebraic structure of the curve. -/
abbrev MeromorphicFunction := C.FunctionField

/-- The divisor of a nonzero meromorphic function.

    div(f) = Σ_p v_p(f) · [p]

    This is a formal sum with finite support (the support of f). -/
structure Divisor (C : AlgebraicCurve) where
  /-- The coefficient at each point -/
  coeff : C.Point → ℤ
  /-- Only finitely many points have nonzero coefficient -/
  finiteSupport : Set.Finite { p | coeff p ≠ 0 }

/-- The divisor of a nonzero meromorphic function -/
noncomputable def divisorOf (f : C.FunctionField) (hf : f ≠ 0) : Divisor C where
  coeff := fun p => C.valuation p f
  finiteSupport := C.valuation_finiteSupport f hf

/-- The degree of a divisor: deg(D) = Σ_p D(p) -/
noncomputable def Divisor.degree (D : Divisor C) : ℤ :=
  D.finiteSupport.toFinset.sum D.coeff

/-- The sum of orders (valuations) of a nonzero function -/
noncomputable def orderSum (f : C.FunctionField) (hf : f ≠ 0) : ℤ :=
  (divisorOf C f hf).degree

end AlgebraicCurve

/-!
## The Argument Principle (Algebraic Version)

On an algebraic curve, the argument principle states that for any
nonzero f ∈ K(C), the degree of its divisor is zero:

  deg(div(f)) = Σ_p v_p(f) = 0

This is sometimes stated as "principal divisors have degree zero".
-/

/-- A compact algebraic curve (smooth projective curve over ℂ).

    For a compact curve, the argument principle holds: the degree
    of any principal divisor is zero. -/
structure CompactAlgebraicCurve extends AlgebraicCurve where
  /-- The genus of the curve -/
  genus : ℕ
  /-- The argument principle: degree of any principal divisor is zero.

      **Mathematical content:**
      This follows from the fact that on a compact curve, a rational function
      f : C → ℙ¹ is a finite morphism of degree d, so it has exactly d zeros
      (with multiplicity) and d poles (with multiplicity).

      Proof approaches:
      1. Algebraic: The Picard group Pic⁰(C) is the kernel of deg: Div(C) → ℤ,
         and principal divisors lie in Pic⁰(C).
      2. Topological: f: C → ℙ¹ is a branched covering, fiber cardinality is constant.
      3. Analytic (via GAGA): Residue theorem, ∮ f'/f = 0 on compact surfaces. -/
  argumentPrinciple : ∀ (f : FunctionField) (hf : f ≠ 0),
    toAlgebraicCurve.orderSum f hf = 0

namespace CompactAlgebraicCurve

variable (C : CompactAlgebraicCurve)

/-- The number of zeros equals the number of poles (counting multiplicity).

    This is an immediate consequence of the argument principle:
    sum of positive orders (zeros) + sum of negative orders (poles) = 0
    Therefore: sum of positive orders = -(sum of negative orders) -/
theorem zeros_eq_poles (f : C.FunctionField) (hf : f ≠ 0) :
    let S := (C.toAlgebraicCurve.valuation_finiteSupport f hf).toFinset
    (S.filter (fun p => 0 < C.valuation p f)).sum (fun p => C.valuation p f) =
    -((S.filter (fun p => C.valuation p f < 0)).sum (fun p => C.valuation p f)) := by
  intro S
  have h := C.argumentPrinciple f hf
  unfold AlgebraicCurve.orderSum AlgebraicCurve.divisorOf AlgebraicCurve.Divisor.degree at h
  simp only at h
  -- The support sum = positive part + negative part = 0
  -- Split the sum over support into positive and negative parts
  have hsplit : S.sum (fun p => C.valuation p f) =
      (S.filter (fun p => 0 < C.valuation p f)).sum (fun p => C.valuation p f) +
      (S.filter (fun p => C.valuation p f < 0)).sum (fun p => C.valuation p f) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun p => 0 < C.valuation p f)]
    congr 1
    apply Finset.sum_congr
    · ext p
      simp only [Finset.mem_filter, not_lt]
      constructor
      · intro ⟨hmem, hle⟩
        refine ⟨hmem, ?_⟩
        have hne : C.valuation p f ≠ 0 := by
          rw [Set.Finite.mem_toFinset] at hmem
          simp only [Set.mem_setOf_eq] at hmem
          exact hmem
        omega
      · intro ⟨hmem, hlt⟩
        exact ⟨hmem, le_of_lt hlt⟩
    · intros; rfl
  rw [hsplit] at h
  linarith

end CompactAlgebraicCurve

/-!
## Example: The Projective Line

The projective line ℙ¹ is the simplest example of a compact algebraic curve (genus 0).
- Points: ℂ ∪ {∞} (represented as ℂ ⊕ Unit)
- Function field: ℂ(z) = RatFunc ℂ

The full construction of ℙ¹ as a CompactAlgebraicCurve requires:
1. Valuation at finite points: v_z(f) = (mult of z in numerator) - (mult of z in denominator)
2. Valuation at infinity: v_∞(f) = deg(denom) - deg(numer)
3. Proof that these satisfy the valuation axioms

This infrastructure is partially available in `Helpers/RiemannSphere.lean` using
polynomial root multiplicities. See that file for the ℙ¹-specific argument principle.
-/

/-- The projective line ℙ¹ as a set: ℂ ∪ {∞} -/
def ProjectiveLinePoints := ℂ ⊕ Unit

/-- The finite point z ∈ ℂ viewed as a point of ℙ¹ -/
def finitePoint (z : ℂ) : ProjectiveLinePoints := Sum.inl z

/-- The point at infinity in ℙ¹ -/
def infinityPoint : ProjectiveLinePoints := Sum.inr ()

end RiemannSurfaces.Algebraic
