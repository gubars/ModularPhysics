import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.AlgebraicStructure
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Meromorphic Functions on Riemann Surfaces

This file provides meromorphic functions on Riemann surfaces using the **algebraic approach**:
a meromorphic function is an element of the function field K(Σ).

## Mathematical Background

For a Riemann surface Σ with algebraic structure A:
- The function field K(Σ) = A.FunctionField contains all meromorphic functions
- A meromorphic function f ∈ K(Σ) has a well-defined order v_p(f) at each point
- v_p(f) > 0: f has a zero of order v_p(f) at p
- v_p(f) < 0: f has a pole of order -v_p(f) at p
- v_p(f) = 0: f is regular and nonzero at p

## Key Definitions

* `MeromorphicFunction A` - Element of the function field (with algebraic structure A)
* `orderAt A f p` - The order v_p(f)
* `orderSum A f` - Sum of orders over the support
* `argumentPrinciple` - For compact surfaces: orderSum = 0

## Why This Definition Is Correct

The function field K(Σ) is a mathematically well-defined object:
- For algebraic curves: K(C) = Frac(coordinate ring)
- For Riemann surfaces (via GAGA): Field of globally meromorphic functions

Being an element of K(Σ) automatically ensures meromorphy - no separate axioms needed.

## References

* Hartshorne "Algebraic Geometry" II.6
* Miranda "Algebraic Curves and Riemann Surfaces" Ch IV
-/

namespace RiemannSurfaces

open RiemannSurfaces.Algebraic

/-!
## Meromorphic Functions via Algebraic Structure

A meromorphic function on a Riemann surface RS with algebraic structure A
is simply an element of A.FunctionField.
-/

/-- A meromorphic function on a Riemann surface with algebraic structure.

    **This is the correct definition**: f ∈ K(Σ) where K(Σ) is the function field.

    Being in the function field automatically ensures:
    - f is holomorphic except at isolated poles
    - The order v_p(f) is well-defined at each point
    - Only finitely many points have nonzero order -/
abbrev MeromorphicFunction {RS : RiemannSurface} (A : AlgebraicStructureOn RS) :=
  A.FunctionField

namespace MeromorphicFunction

variable {RS : RiemannSurface} {A : AlgebraicStructureOn RS}

/-- The order of f at point p -/
def orderAt (f : MeromorphicFunction A) (p : RS.carrier) : ℤ :=
  A.valuation p f

/-- f is regular (holomorphic and nonzero) at p iff orderAt = 0 -/
def isRegularAt (f : MeromorphicFunction A) (p : RS.carrier) : Prop :=
  orderAt f p = 0

/-- f has a zero at p iff orderAt > 0 -/
def hasZeroAt (f : MeromorphicFunction A) (p : RS.carrier) : Prop :=
  0 < orderAt f p

/-- f has a pole at p iff orderAt < 0 -/
def hasPoleAt (f : MeromorphicFunction A) (p : RS.carrier) : Prop :=
  orderAt f p < 0

/-- The support of f: points where f has a zero or pole -/
def support (f : MeromorphicFunction A) : Set RS.carrier :=
  { p | orderAt f p ≠ 0 }

/-- Support is finite for nonzero f -/
theorem support_finite (f : MeromorphicFunction A) (hf : f ≠ 0) :
    Set.Finite (support f) :=
  A.valuation_finiteSupport f hf

/-!
## Order Properties

These follow directly from the valuation axioms.
-/

/-- Order of 1 is 0 everywhere -/
theorem orderAt_one (p : RS.carrier) : orderAt (1 : MeromorphicFunction A) p = 0 :=
  A.valuation_one p

/-- Order is additive: v_p(fg) = v_p(f) + v_p(g) -/
theorem orderAt_mul (f g : MeromorphicFunction A) (p : RS.carrier)
    (hf : f ≠ 0) (hg : g ≠ 0) :
    orderAt (f * g) p = orderAt f p + orderAt g p :=
  A.valuation_mul p f g hf hg

/-- Order of inverse: v_p(f⁻¹) = -v_p(f) -/
theorem orderAt_inv (f : MeromorphicFunction A) (p : RS.carrier) (hf : f ≠ 0) :
    orderAt f⁻¹ p = -orderAt f p :=
  A.valuation_inv p f hf

end MeromorphicFunction

/-!
## Sum of Orders and Argument Principle

For compact Riemann surfaces, the argument principle holds: Σ_p v_p(f) = 0.
-/

/-- Sum of orders of a nonzero meromorphic function over its support -/
noncomputable def orderSum {RS : RiemannSurface} (A : AlgebraicStructureOn RS)
    (f : MeromorphicFunction A) (hf : f ≠ 0) : ℤ :=
  (A.valuation_finiteSupport f hf).toFinset.sum (fun p => A.valuation p f)

/-- The order sum for 1 is 0 (trivially, since 1 has no zeros or poles) -/
theorem orderSum_one {RS : RiemannSurface} (A : AlgebraicStructureOn RS)
    (h : (1 : MeromorphicFunction A) ≠ 0) : orderSum A 1 h = 0 := by
  unfold orderSum
  have h_empty : ∀ p : RS.carrier, A.valuation p 1 = 0 := A.valuation_one
  convert Finset.sum_empty (f := fun p => A.valuation p (1 : A.FunctionField))
  rw [Set.Finite.toFinset_eq_empty]
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
  exact h_empty p

/-!
## Argument Principle for Compact Surfaces
-/

/-- The Argument Principle: Sum of orders is zero on compact Riemann surfaces.

    For any nonzero meromorphic function f on a compact Riemann surface Σ:
      Σ_p ord_p(f) = 0

    This is equivalent to: #zeros = #poles (counting multiplicities).

    **Proof approaches:**
    1. Residue calculus: ∮ f'/f dz = 2πi · Σ_p ord_p(f) = 0 (no boundary)
    2. Topological degree: f: Σ → ℂP¹ has |f⁻¹(0)| = |f⁻¹(∞)| = deg(f)
    3. Algebraic: Principal divisors have degree zero in the Picard group -/
theorem argumentPrinciple {CRS : CompactRiemannSurface}
    (CA : CompactAlgebraicStructureOn CRS)
    (f : MeromorphicFunction CA.toAlgebraicStructureOn) (hf : f ≠ 0) :
    orderSum CA.toAlgebraicStructureOn f hf = 0 :=
  CA.argumentPrinciple f hf

/-!
## Compatibility with Old API

The following definitions provide backward compatibility for code that
used the old `MeromorphicFunction RS` structure.
-/

/-- For backward compatibility: order function on the support -/
noncomputable def order_finiteSupport {RS : RiemannSurface} (A : AlgebraicStructureOn RS)
    (f : MeromorphicFunction A) (hf : f ≠ 0) :
    Set.Finite { p | A.valuation p f ≠ 0 } :=
  A.valuation_finiteSupport f hf

end RiemannSurfaces
