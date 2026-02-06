import ModularPhysics.StringGeometry.RiemannSurfaces.GAGA.AlgebraicCurves.FunctionField
import ModularPhysics.StringGeometry.RiemannSurfaces.GAGA.AlgebraicCurves.Core.Divisors
import ModularPhysics.StringGeometry.RiemannSurfaces.GAGA.AlgebraicCurves.Cohomology.AlgebraicCech

/-!
# Algebraic Residue Theory for Compact Algebraic Curves

This file develops algebraic residue theory for compact algebraic curves.
The main results show how products of functions in quotient spaces L(D)/L(D-p)
behave under valuation.

## Main Results

* `product_valuation_at_p`: If f ∈ L(D)\L(D-p) and g ∈ L(K-D+p)\L(K-D), then
  v_p(fg) = -(K(p)+1), i.e., fg has a simple pole at p.
* `product_valuation_away`: For q ≠ p, v_q(fg) ≥ -K(q).
* `product_in_Kp`: The product fg lies in L(K + point(p)).

These lemmas support the Serre pairing argument: if both f and g have exact
valuations at p, their product has a simple pole at p, and by the residue
theorem, the residue (product of leading coefficients) must be 0.
-/

namespace RiemannSurfaces.Algebraic

open CompactAlgebraicCurve

variable (C : CompactAlgebraicCurve)

/-!
## Auxiliary Definitions

We use Core.Divisor for divisors, as it has all the arithmetic operations we need.
-/

/-- The valuation of a function at a point -/
abbrev val (p : C.Point) (f : C.FunctionField) : ℤ := C.valuation p f

/-- A function f is in L(D) if v_p(f) + D(p) ≥ 0 for all p -/
def inRiemannRochSpace (f : C.FunctionField) (D : Core.Divisor C.toAlgebraicCurve) : Prop :=
  f = 0 ∨ ∀ p : C.Point, val C p f + D.coeff p ≥ 0

/-- f ∈ L(D) \ L(D-p) means f ∈ L(D) with v_p(f) = -D(p) exactly -/
def inQuotient (f : C.FunctionField) (D : Core.Divisor C.toAlgebraicCurve)
    (p : C.Point) : Prop :=
  f ≠ 0 ∧ inRiemannRochSpace C f D ∧ val C p f = -D.coeff p

/-!
## Key Technical Lemmas
-/

/-- If f ∈ L(D) with v_p(f) = -D(p), and g ∈ L(K-D+point(p)) with v_p(g) = -(K-D+point(p))(p),
    then fg ∈ L(K+point(p)) with v_p(fg) = -(K(p)+1). -/
theorem product_valuation_at_p {D K : Core.Divisor C.toAlgebraicCurve}
    {p : C.Point} {f g : C.FunctionField}
    (hf : inQuotient C f D p)
    (hg : inQuotient C g (K - D + Core.Divisor.point p) p) :
    val C p (f * g) = -(K.coeff p + 1) := by
  obtain ⟨hf_ne, _, hvf⟩ := hf
  obtain ⟨hg_ne, _, hvg⟩ := hg
  have hfg_ne : f * g ≠ 0 := mul_ne_zero hf_ne hg_ne
  simp only [val] at hvf hvg ⊢
  rw [C.valuation_mul p f g hf_ne hg_ne]
  rw [hvf, hvg]
  simp only [Core.Divisor.sub_coeff, Core.Divisor.add_coeff, Core.Divisor.point, ite_true]
  ring

/-- If f ∈ L(D) with v_p(f) = -D(p), and g ∈ L(K-D+point(p)) with v_p(g) = -(K-D+point(p))(p),
    then v_q(fg) ≥ -K(q) for all q ≠ p. -/
theorem product_valuation_away {D K : Core.Divisor C.toAlgebraicCurve}
    {p : C.Point} {f g : C.FunctionField}
    (hf : inQuotient C f D p)
    (hg : inQuotient C g (K - D + Core.Divisor.point p) p)
    {q : C.Point} (hqp : q ≠ p) :
    val C q (f * g) ≥ -K.coeff q := by
  obtain ⟨hf_ne, hf_in, _⟩ := hf
  obtain ⟨hg_ne, hg_in, _⟩ := hg
  have hfg_ne : f * g ≠ 0 := mul_ne_zero hf_ne hg_ne
  simp only [val]
  rw [C.valuation_mul q f g hf_ne hg_ne]
  -- f ∈ L(D) means v_q(f) ≥ -D(q)
  have hvf : C.valuation q f ≥ -D.coeff q := by
    rcases hf_in with rfl | hf_in
    · exact absurd rfl hf_ne
    · have := hf_in q; simp only [val] at this; linarith
  -- g ∈ L(K-D+point(p)) means v_q(g) ≥ -(K-D+point(p))(q) = -K(q) + D(q) for q ≠ p
  have hvg : C.valuation q g ≥ -K.coeff q + D.coeff q := by
    rcases hg_in with rfl | hg_in
    · exact absurd rfl hg_ne
    · have := hg_in q
      simp only [val, Core.Divisor.sub_coeff, Core.Divisor.add_coeff,
                 Core.Divisor.point, if_neg hqp, add_zero] at this
      linarith
  linarith

/-- The product fg lies in L(K + point(p)) -/
theorem product_in_Kp {D K : Core.Divisor C.toAlgebraicCurve}
    {p : C.Point} {f g : C.FunctionField}
    (hf : inQuotient C f D p)
    (hg : inQuotient C g (K - D + Core.Divisor.point p) p) :
    inRiemannRochSpace C (f * g) (K + Core.Divisor.point p) := by
  obtain ⟨hf_ne, hf_in, hvf⟩ := hf
  obtain ⟨hg_ne, hg_in, hvg⟩ := hg
  have hfg_ne : f * g ≠ 0 := mul_ne_zero hf_ne hg_ne
  right
  intro q
  simp only [Core.Divisor.add_coeff, Core.Divisor.point]
  by_cases hqp : q = p
  · -- At p: v_p(fg) + K(p) + 1 = -(K(p)+1) + K(p) + 1 = 0
    subst hqp
    simp only [ite_true]
    have hvfg := product_valuation_at_p C ⟨hf_ne, hf_in, hvf⟩ ⟨hg_ne, hg_in, hvg⟩
    simp only [val] at hvfg
    linarith
  · -- At q ≠ p: v_q(fg) + K(q) ≥ 0
    simp only [if_neg hqp, add_zero]
    have hvfg := product_valuation_away C ⟨hf_ne, hf_in, hvf⟩ ⟨hg_ne, hg_in, hvg⟩ hqp
    simp only [val] at hvfg
    linarith

end RiemannSurfaces.Algebraic
