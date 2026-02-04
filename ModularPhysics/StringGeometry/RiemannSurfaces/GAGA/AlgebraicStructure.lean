import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.FunctionField
import ModularPhysics.StringGeometry.RiemannSurfaces.Basic

/-!
# Algebraic Structure on Riemann Surfaces

This file provides the bridge between the analytic `RiemannSurface` and the
algebraic `AlgebraicCurve` structures.

## Mathematical Background

For a compact Riemann surface Σ, GAGA establishes that:
- Σ has a unique structure as a smooth projective algebraic curve C over ℂ
- The function field K(C) equals the field of meromorphic functions on Σ
- The analytic and algebraic viewpoints are equivalent

This file provides:
1. `AlgebraicStructureOn` - algebraic structure (function field, valuations) on a Riemann surface
2. Compatibility lemmas showing the structures agree

## Key Definitions

* `AlgebraicStructureOn RS` - Function field and valuations for a Riemann surface
* `compactAlgebraicStructure` - Every compact Riemann surface has algebraic structure

## References

* Serre "GAGA"
* Griffiths, Harris "Principles of Algebraic Geometry" Ch 1
-/

namespace RiemannSurfaces.Algebraic

open RiemannSurfaces

/-!
## Algebraic Structure on a Riemann Surface

For a Riemann surface RS, we provide its algebraic structure: function field and valuations.
-/

/-- Algebraic structure on a Riemann surface.

    This equips a Riemann surface with its function field K(Σ) and the
    discrete valuation v_p at each point.

    **GAGA principle**: For compact Riemann surfaces, this structure
    always exists and is unique up to canonical isomorphism.

    The function field K(Σ) consists of all meromorphic functions on Σ,
    and forms a field under pointwise operations. -/
structure AlgebraicStructureOn (RS : RiemannSurface) where
  /-- The function field K(Σ) of meromorphic functions -/
  FunctionField : Type*
  /-- The function field is a field -/
  [fieldInst : Field FunctionField]
  /-- The discrete valuation at each point -/
  valuation : RS.carrier → FunctionField → ℤ
  /-- v_p(0) = 0 (by convention) -/
  valuation_zero : ∀ p, valuation p 0 = 0
  /-- v_p(fg) = v_p(f) + v_p(g) for f, g ≠ 0 -/
  valuation_mul : ∀ p (f g : FunctionField), f ≠ 0 → g ≠ 0 →
    valuation p (f * g) = valuation p f + valuation p g
  /-- Ultrametric inequality: v_p(f + g) ≥ min(v_p(f), v_p(g)) when f + g ≠ 0 -/
  valuation_add_min : ∀ p (f g : FunctionField), f + g ≠ 0 →
    valuation p (f + g) ≥ min (valuation p f) (valuation p g)
  /-- Finite support: only finitely many points have nonzero valuation -/
  valuation_finiteSupport : ∀ (f : FunctionField), f ≠ 0 →
    Set.Finite { p | valuation p f ≠ 0 }

attribute [instance] AlgebraicStructureOn.fieldInst

namespace AlgebraicStructureOn

variable {RS : RiemannSurface} (A : AlgebraicStructureOn RS)

/-- A meromorphic function on RS (with algebraic structure) is an element of K(Σ) -/
abbrev MeromorphicFunction := A.FunctionField

/-- The order of f at point p -/
def orderAt (f : A.FunctionField) (p : RS.carrier) : ℤ :=
  A.valuation p f

/-- f has a zero at p -/
def hasZeroAt (f : A.FunctionField) (p : RS.carrier) : Prop :=
  0 < A.valuation p f

/-- f has a pole at p -/
def hasPoleAt (f : A.FunctionField) (p : RS.carrier) : Prop :=
  A.valuation p f < 0

/-- The support of f (zeros and poles) -/
def support (f : A.FunctionField) : Set RS.carrier :=
  { p | A.valuation p f ≠ 0 }

theorem support_finite (f : A.FunctionField) (hf : f ≠ 0) :
    Set.Finite (A.support f) :=
  A.valuation_finiteSupport f hf

/-- v_p(1) = 0. DERIVED from valuation_mul. -/
theorem valuation_one (p : RS.carrier) : A.valuation p 1 = 0 := by
  have h1_ne : (1 : A.FunctionField) ≠ 0 := one_ne_zero
  have h := A.valuation_mul p 1 1 h1_ne h1_ne
  simp only [mul_one] at h
  omega

/-- v_p(f⁻¹) = -v_p(f) for f ≠ 0. DERIVED from valuation_mul + valuation_one. -/
theorem valuation_inv (p : RS.carrier) (f : A.FunctionField) (hf : f ≠ 0) :
    A.valuation p f⁻¹ = -A.valuation p f := by
  have hf_inv_ne : f⁻¹ ≠ 0 := inv_ne_zero hf
  have h := A.valuation_mul p f f⁻¹ hf hf_inv_ne
  rw [mul_inv_cancel₀ hf, A.valuation_one] at h
  omega

/-- Convert to AlgebraicCurve structure -/
def toAlgebraicCurve : AlgebraicCurve where
  Point := RS.carrier
  FunctionField := A.FunctionField
  valuation := A.valuation
  valuation_zero := A.valuation_zero
  valuation_mul := A.valuation_mul
  valuation_add_min := A.valuation_add_min
  valuation_finiteSupport := A.valuation_finiteSupport

end AlgebraicStructureOn

/-!
## Compact Riemann Surfaces with Algebraic Structure

For compact Riemann surfaces, we additionally have the argument principle.
-/

/-- Algebraic structure on a compact Riemann surface.

    Includes the genus and the argument principle. -/
structure CompactAlgebraicStructureOn (CRS : CompactRiemannSurface) extends
    AlgebraicStructureOn CRS.toRiemannSurface where
  /-- The argument principle: degree of any principal divisor is zero -/
  argumentPrinciple : ∀ (f : FunctionField) (hf : f ≠ 0),
    (toAlgebraicStructureOn.valuation_finiteSupport f hf).toFinset.sum
      (fun p => toAlgebraicStructureOn.valuation p f) = 0

namespace CompactAlgebraicStructureOn

variable {CRS : CompactRiemannSurface} (CA : CompactAlgebraicStructureOn CRS)

/-- The sum of orders of a nonzero function is zero -/
theorem orderSum_eq_zero (f : CA.FunctionField) (hf : f ≠ 0) :
    (CA.toAlgebraicStructureOn.valuation_finiteSupport f hf).toFinset.sum
      (fun p => CA.valuation p f) = 0 :=
  CA.argumentPrinciple f hf

/-- The total order of zeros equals the total order of poles -/
theorem zeros_eq_poles (f : CA.FunctionField) (hf : f ≠ 0) :
    let S := (CA.toAlgebraicStructureOn.valuation_finiteSupport f hf).toFinset
    (S.filter (fun p => 0 < CA.valuation p f)).sum (fun p => CA.valuation p f) =
    -((S.filter (fun p => CA.valuation p f < 0)).sum (fun p => CA.valuation p f)) := by
  intro S
  have h := CA.argumentPrinciple f hf
  -- Split the sum into positive and negative parts
  have hsplit : S.sum (fun p => CA.valuation p f) =
      (S.filter (fun p => 0 < CA.valuation p f)).sum (fun p => CA.valuation p f) +
      (S.filter (fun p => CA.valuation p f < 0)).sum (fun p => CA.valuation p f) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun p => 0 < CA.valuation p f)]
    congr 1
    apply Finset.sum_congr
    · ext p
      simp only [Finset.mem_filter, not_lt]
      constructor
      · intro ⟨hmem, hle⟩
        refine ⟨hmem, ?_⟩
        have hne : CA.valuation p f ≠ 0 := by
          rw [Set.Finite.mem_toFinset] at hmem
          simp only [Set.mem_setOf_eq] at hmem
          exact hmem
        omega
      · intro ⟨hmem, hlt⟩
        exact ⟨hmem, le_of_lt hlt⟩
    · intros; rfl
  rw [hsplit] at h
  linarith

-- Note: Full conversion to CompactAlgebraicCurve requires additional fields
-- (algebraInst, regularIsConstant, localParameter, etc.) that are not in this
-- minimal structure. Use Algebraic.CompactAlgebraicStructureOn for the complete version.

end CompactAlgebraicStructureOn

/-!
## Existence of Algebraic Structure (GAGA)

For compact Riemann surfaces, algebraic structure always exists.
This is a consequence of the GAGA principle.
-/

/-- GAGA: Every compact Riemann surface admits a unique algebraic structure.

    This is a deep theorem of complex algebraic geometry:
    - Existence: Riemann's existence theorem / Chow's theorem
    - Uniqueness: Up to isomorphism

    The algebraic structure provides:
    - The function field K(Σ)
    - Discrete valuations at each point
    - The argument principle -/
theorem compact_admits_algebraic_structure (CRS : CompactRiemannSurface) :
    Nonempty (CompactAlgebraicStructureOn CRS) := by
  -- This is the GAGA principle for curves.
  -- The proof requires showing:
  -- 1. CRS can be embedded as a projective algebraic curve
  -- 2. The meromorphic functions form a function field
  -- 3. The discrete valuations satisfy the required properties
  --
  -- This is a deep theorem that we take as axiomatic at this level.
  sorry

end RiemannSurfaces.Algebraic
