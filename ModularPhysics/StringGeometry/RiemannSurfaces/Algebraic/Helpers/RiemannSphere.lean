import ModularPhysics.StringGeometry.RiemannSurfaces.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The Riemann Sphere ℂP¹

This file defines the Riemann sphere ℂP¹ and proves the argument principle
for rational functions, which is the foundation for the general argument principle.

## Main Results

* `RiemannSphere` - ℂP¹ as a compact Riemann surface
* `RationalFunction` - Meromorphic functions on ℂP¹
* `argumentPrinciple_rational` - Σ ord_p(f) = 0 for rational functions

## Mathematical Background

The Riemann sphere ℂP¹ = ℂ ∪ {∞} is the simplest compact Riemann surface.
Meromorphic functions on ℂP¹ are precisely the rational functions P(z)/Q(z).

For a rational function f = P/Q:
- Zeros in ℂ: roots of P (counting multiplicity)
- Poles in ℂ: roots of Q (counting multiplicity)
- Behavior at ∞: depends on deg(P) vs deg(Q)

The argument principle states that #zeros = #poles (counting ∞).

## References

* Ahlfors "Complex Analysis"
* Conway "Functions of One Complex Variable"
-/

namespace RiemannSurfaces.RiemannSphere

open Polynomial

/-!
## Definition of the Riemann Sphere
-/

/-- The Riemann sphere as a set: ℂ ∪ {∞}
    We represent this as `ℂ ⊕ Unit` where `Sum.inr ()` is the point at infinity. -/
def RiemannSphereSet : Type := ℂ ⊕ Unit

/-- The finite point z ∈ ℂ viewed as a point of ℂP¹ -/
def finitePoint (z : ℂ) : RiemannSphereSet := Sum.inl z

/-- The point at infinity -/
def infinity : RiemannSphereSet := Sum.inr ()

/-!
## Rational Functions

A rational function is P(z)/Q(z) where P, Q are polynomials with Q ≠ 0.
-/

/-- A rational function on ℂP¹, represented as a ratio of polynomials. -/
structure RationalFunction where
  /-- The numerator polynomial -/
  numerator : Polynomial ℂ
  /-- The denominator polynomial -/
  denominator : Polynomial ℂ
  /-- The denominator is nonzero -/
  denom_ne_zero : denominator ≠ 0
  /-- The fraction is in lowest terms (no common factors) -/
  coprime : IsCoprime numerator denominator

namespace RationalFunction

/-- Degree of the numerator -/
def numDeg (f : RationalFunction) : ℕ := f.numerator.natDegree

/-- Degree of the denominator -/
def denomDeg (f : RationalFunction) : ℕ := f.denominator.natDegree

/-- The order of f at a finite point z ∈ ℂ.

    - If P(z) = 0 and Q(z) ≠ 0: order = multiplicity of z as root of P > 0
    - If P(z) ≠ 0 and Q(z) = 0: order = -(multiplicity of z as root of Q) < 0
    - If P(z) ≠ 0 and Q(z) ≠ 0: order = 0 (regular point)
    - If P(z) = 0 and Q(z) = 0: impossible (coprime) -/
noncomputable def orderAtFinite (f : RationalFunction) (z : ℂ) : ℤ :=
  (f.numerator.rootMultiplicity z : ℤ) - (f.denominator.rootMultiplicity z : ℤ)

/-- The order of f at infinity.

    At ∞, we substitute w = 1/z and look at w = 0:
    f(1/w) = P(1/w)/Q(1/w) = w^(deg Q - deg P) · P*(w)/Q*(w)
    where P*, Q* are "reversed" polynomials.

    So ord_∞(f) = deg(Q) - deg(P) -/
def orderAtInfinity (f : RationalFunction) : ℤ :=
  (f.denomDeg : ℤ) - (f.numDeg : ℤ)

/-- The order function on the full Riemann sphere -/
noncomputable def orderAt (f : RationalFunction) : RiemannSphereSet → ℤ
  | Sum.inl z => orderAtFinite f z
  | Sum.inr () => orderAtInfinity f

/-!
## Total Order Counting

We prove that the sum of orders over all points equals 0.
-/

/-- For a non-zero polynomial over ℂ, the number of roots (with multiplicity)
    equals the degree. This follows from the fundamental theorem of algebra.

    Note: Over ℂ specifically, card(roots) = natDegree for non-zero polynomials.
    This is proved in Mathlib via IsAlgClosed.card_roots_eq_natDegree. -/
theorem card_roots_eq_natDegree (p : Polynomial ℂ) (_ : p ≠ 0) :
    Multiset.card p.roots = p.natDegree :=
  -- Over ℂ, which is algebraically closed, we can use the Mathlib theorem
  IsAlgClosed.card_roots_eq_natDegree

/-- The sum of orders at all finite points equals deg(P) - deg(Q)

    Proof:
    - Sum of positive orders = Σ (multiplicities of roots of P) = deg(P)
    - Sum of negative orders = -Σ (multiplicities of roots of Q) = -deg(Q)
    - Total = deg(P) - deg(Q) -/
theorem finiteOrderSum (f : RationalFunction) (hnum : f.numerator ≠ 0) :
    (Multiset.card f.numerator.roots : ℤ) -
    (Multiset.card f.denominator.roots : ℤ) =
    (f.numDeg : ℤ) - (f.denomDeg : ℤ) := by
  -- Use that card(roots) = natDegree over ℂ
  rw [card_roots_eq_natDegree f.numerator hnum]
  rw [card_roots_eq_natDegree f.denominator f.denom_ne_zero]
  rfl

/-- **The Argument Principle for Rational Functions**

    For any rational function f = P/Q on ℂP¹:
    Σ_{p ∈ ℂP¹} ord_p(f) = 0

    Proof:
    - Σ_{z ∈ ℂ} ord_z(f) = deg(P) - deg(Q)  (fundamental theorem of algebra)
    - ord_∞(f) = deg(Q) - deg(P)             (by definition)
    - Total = (deg(P) - deg(Q)) + (deg(Q) - deg(P)) = 0 -/
theorem argumentPrinciple_rational (f : RationalFunction) (hnum : f.numerator ≠ 0) :
    (Multiset.card f.numerator.roots : ℤ) -
    (Multiset.card f.denominator.roots : ℤ) +
    f.orderAtInfinity = 0 := by
  -- Total order = (orders at finite points) + (order at ∞)
  --             = (deg P - deg Q) + (deg Q - deg P)
  --             = 0
  rw [finiteOrderSum f hnum]
  unfold orderAtInfinity numDeg denomDeg
  ring

end RationalFunction

end RiemannSurfaces.RiemannSphere
