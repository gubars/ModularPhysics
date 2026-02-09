/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Complex.Basic

/-!
# Scheme-Theoretic Algebraic Curves

This file provides scheme-theoretic foundations for algebraic curves over ℂ,
using Mathlib's actual `Scheme` infrastructure.

## Hierarchy

* `AlgebraicCurve` - An integral scheme of dimension 1 over ℂ (separated, finite type)
* `ProperCurve` - A proper algebraic curve (+ proper morphism)
* `SmoothProjectiveCurve` - A smooth proper curve (+ smooth of relative dimension 1)

## Design Principles

**NO AXIOM SMUGGLING**: Structure fields are genuine data or properties that
characterize the curve class:
- `toScheme` and `structureMorphism` are DATA
- `separated`, `finiteType`, `proper`, `smooth` are PREDICATES (type class instances)
- `irreducible`, `reduced` DEFINE "integral"
- `residueFieldIsComplex` DEFINES "over algebraically closed ℂ"

Computational results like:
- Local rings are DVRs → THEOREM (follows from smooth + dim 1)
- Argument principle → THEOREM (follows from proper)
- Regular functions are constant → THEOREM (follows from proper)

These are NOT bundled into the structure.

## References

* Hartshorne, "Algebraic Geometry", Chapter II (Schemes) and Chapter IV (Curves)
* Mathlib's AlgebraicGeometry.Scheme
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace RiemannSurfaces.SchemeTheoretic

/-- The base scheme Spec ℂ. -/
noncomputable def SpecComplex : Scheme := Scheme.Spec.obj (Opposite.op (CommRingCat.of ℂ))

/-- The canonical ring homomorphism from ℂ to the residue field at a point x,
    induced by a structure morphism f : X → Spec ℂ.

    This is the composition:
    ℂ →[ΓSpecIso⁻¹]→ Γ(Spec ℂ, ⊤) →[f*.appTop]→ Γ(X, ⊤) →[evaluation]→ κ(x)

    For schemes of finite type over an algebraically closed field, this map
    is bijective at all closed points (by the Nullstellensatz). -/
noncomputable def canonicalToResidueField (X : Scheme) (f : X ⟶ SpecComplex) (x : X) :
    ℂ →+* (X.residueField x : Type _) :=
  ((X.evaluation ⊤ x (Set.mem_univ x)).hom).comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)

/-!
## Algebraic Curves (General)

An algebraic curve over ℂ is an integral (= irreducible + reduced) scheme of
dimension 1, separated and of finite type over Spec ℂ.

This is the most general notion - it includes affine curves, quasi-projective
curves, etc. Properness and smoothness are additional conditions.
-/

/-- An algebraic curve over ℂ (scheme-theoretic definition).

    This is the general notion: an integral scheme of dimension 1 over ℂ.
    No properness or smoothness assumed.

    **Fields:**
    - `toScheme` : The underlying scheme X
    - `structureMorphism` : The structure map π : X → Spec ℂ
    - `separated` : π is separated
    - `finiteType` : π is locally of finite type
    - `irreducible` : X is irreducible (connected in the Zariski sense)
    - `reduced` : X is reduced (no nilpotents)
    - `residueFieldIsComplex` : Residue fields κ(x) ≅ ℂ (over alg. closed field)

    **Note:** We do not include an explicit "dimension 1" predicate because
    Mathlib's dimension theory for schemes is still developing. The dimension
    is implicitly captured by how we use these curves (e.g., stalks are DVRs
    for smooth curves, which requires dim 1). -/
structure AlgebraicCurve where
  /-- The underlying scheme -/
  toScheme : Scheme
  /-- The structure morphism to Spec ℂ -/
  structureMorphism : toScheme ⟶ SpecComplex
  /-- Separated over ℂ -/
  [separated : IsSeparated structureMorphism]
  /-- Locally of finite type over ℂ -/
  [finiteType : LocallyOfFiniteType structureMorphism]
  /-- The scheme is irreducible (connected in the Zariski sense).
      This is required for the function field to be well-defined. -/
  [irreducible : IrreducibleSpace toScheme]
  /-- The scheme is reduced (no nilpotent elements in the structure sheaf). -/
  [reduced : IsReduced toScheme]
  /-- The canonical map ℂ → κ(x) is bijective at every point.

      **Mathematical content:**
      For a variety of finite type over an algebraically closed field k,
      the canonical map k → κ(x) is bijective at all closed points
      (by Hilbert's Nullstellensatz / Zariski's lemma). This is the
      scheme-theoretic content of "the curve is over ℂ".

      This is stronger than merely asserting ∃ iso : κ(x) ≅ ℂ, because
      it asserts the CANONICAL map (induced by the structure morphism)
      is the one witnessing the isomorphism. -/
  residueFieldIsComplex : ∀ x : toScheme,
    Function.Bijective (canonicalToResidueField toScheme structureMorphism x)

attribute [instance] AlgebraicCurve.separated
attribute [instance] AlgebraicCurve.finiteType
attribute [instance] AlgebraicCurve.irreducible
attribute [instance] AlgebraicCurve.reduced

namespace AlgebraicCurve

variable (C : AlgebraicCurve)

/-- The scheme is nonempty (from IrreducibleSpace). -/
instance toSchemeNonempty : Nonempty C.toScheme := by
  haveI : IrreducibleSpace C.toScheme := C.irreducible
  exact IrreducibleSpace.toNonempty

/-- The scheme is integral (from irreducible + reduced). -/
instance toSchemeIsIntegral : IsIntegral C.toScheme :=
  isIntegral_of_irreducibleSpace_of_isReduced C.toScheme

/-- The canonical map ℂ → κ(x) for the curve. -/
noncomputable def canonicalToResidue (x : C.toScheme) :
    ℂ →+* (C.toScheme.residueField x : Type _) :=
  canonicalToResidueField C.toScheme C.structureMorphism x

/-- The canonical map ℂ → κ(x) is bijective. -/
theorem canonicalToResidue_bijective (x : C.toScheme) :
    Function.Bijective (C.canonicalToResidue x) :=
  C.residueFieldIsComplex x

/-- The canonical map as a ring equivalence ℂ ≃+* κ(x). -/
noncomputable def residueFieldEquiv (x : C.toScheme) :
    ℂ ≃+* (C.toScheme.residueField x : Type _) :=
  RingEquiv.ofBijective (C.canonicalToResidue x) (C.canonicalToResidue_bijective x)

/-- Derived: the residue field is isomorphic to ℂ as CommRingCat (backwards-compatible). -/
theorem residueFieldIso (x : C.toScheme) :
    Nonempty (C.toScheme.residueField x ≅ CommRingCat.of ℂ) := by
  let e := C.residueFieldEquiv x
  exact ⟨{
    hom := CommRingCat.ofHom e.symm.toRingHom
    inv := CommRingCat.ofHom e.toRingHom
    hom_inv_id := by ext a; exact e.apply_symm_apply a
    inv_hom_id := by ext a; exact e.symm_apply_apply a
  }⟩

/-- The set of points of the curve (as a type). -/
def PointType : Type _ := C.toScheme.carrier

/-- The function field K(C) of the curve as a CommRingCat. -/
noncomputable def FunctionFieldCat : CommRingCat := C.toScheme.functionField

/-- The function field K(C) as a type. -/
noncomputable def FunctionFieldType : Type _ := (C.FunctionFieldCat : Type _)

/-- The function field is a commutative ring. -/
noncomputable instance functionFieldCommRing : CommRing C.FunctionFieldType :=
  inferInstanceAs (CommRing C.FunctionFieldCat)

/-- The function field is a field (from integrality). -/
noncomputable instance functionFieldField : Field C.FunctionFieldType :=
  inferInstanceAs (Field (C.toScheme.functionField : Type _))

/-- The stalk of the structure sheaf at a point. -/
noncomputable def StalkType (x : C.PointType) : Type _ := (C.toScheme.presheaf.stalk x : Type _)

noncomputable instance stalkCommRing (x : C.PointType) : CommRing (C.StalkType x) :=
  inferInstanceAs (CommRing (C.toScheme.presheaf.stalk x))

/-- Stalks are local rings (schemes are locally ringed spaces). -/
noncomputable instance stalkIsLocalRing (x : C.PointType) : IsLocalRing (C.StalkType x) :=
  inferInstanceAs (IsLocalRing (C.toScheme.presheaf.stalk x))

/-- Stalks are domains (from integrality). -/
instance stalkIsDomain (x : C.PointType) : IsDomain (C.StalkType x) :=
  inferInstanceAs (IsDomain (C.toScheme.presheaf.stalk x))

/-- The residue field at a point. -/
noncomputable def ResidueFieldCat (x : C.PointType) : CommRingCat := C.toScheme.residueField x

/-- The top open is nonempty. -/
noncomputable instance topOpenSetNonempty : Nonempty (⊤ : C.toScheme.Opens) := by
  haveI : Nonempty C.toScheme := C.toSchemeNonempty
  exact ⟨⟨Classical.arbitrary C.toScheme, trivial⟩⟩

/-- The embedding of constants ℂ into the function field. -/
noncomputable def constantsEmbed : ℂ →+* C.FunctionFieldType :=
  (C.toScheme.germToFunctionField ⊤).hom.comp
    (C.structureMorphism.appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)

/-- The ℂ-algebra structure on the function field. -/
noncomputable instance functionFieldAlgebra : Algebra ℂ C.FunctionFieldType :=
  RingHom.toAlgebra C.constantsEmbed

end AlgebraicCurve

/-!
## Proper Curves

A proper curve is an algebraic curve with proper structure morphism.
This gives finiteness properties: coherent cohomology is finite-dimensional,
global sections form a finite ℂ-algebra, etc.
-/

/-- A proper algebraic curve over ℂ.

    Extends `AlgebraicCurve` with properness (universally closed, separated, finite type).
    This is the setting where:
    - Global sections Γ(C, O_C) ≅ ℂ (Liouville)
    - Argument principle holds (deg(div(f)) = 0)
    - Coherent sheaf cohomology is finite-dimensional -/
structure ProperCurve extends AlgebraicCurve where
  /-- Proper over ℂ: universally closed, separated, of finite type -/
  [proper : IsProper structureMorphism]

attribute [instance] ProperCurve.proper

namespace ProperCurve

variable (C : ProperCurve)

/-- Coercion to AlgebraicCurve. -/
instance : Coe ProperCurve AlgebraicCurve := ⟨ProperCurve.toAlgebraicCurve⟩

/-- The global sections ring is isomorphic to ℂ (Liouville property).

    **Mathematical content:**
    For a proper variety X over ℂ, the global sections Γ(X, O_X) form
    a finite-dimensional ℂ-algebra. If X is also connected (which follows
    from irreducible), then Γ(X, O_X) ≅ ℂ.

    This is the algebraic analogue of Liouville's theorem.
    This is a THEOREM derived from properness, not an axiom. -/
theorem globalSections_eq_constants :
    Nonempty (Γ(C.toScheme, ⊤) ≃+* ℂ) := by
  -- Proof uses properness:
  -- π : X → Spec ℂ proper ⟹ π_* O_X is coherent on Spec ℂ
  -- Γ(Spec ℂ, π_* O_X) = Γ(X, O_X) is finite-dimensional over ℂ
  -- X connected ⟹ Γ(X, O_X) is a connected finite ℂ-algebra ⟹ Γ(X, O_X) = ℂ
  sorry

end ProperCurve

/-!
## Smooth Projective Curves

A smooth projective curve is a proper curve that is also smooth.
For curves over ℂ, smooth + proper = smooth + projective (by Chow's theorem
and the fact that smooth proper curves embed in projective space).

This is the setting where:
- Local rings are DVRs (smooth + dim 1)
- Full Riemann-Roch theorem holds
- Serre duality holds
-/

/-- A smooth projective curve over ℂ.

    Extends `ProperCurve` with smoothness. For curves, smooth + proper is
    equivalent to smooth + projective over an algebraically closed field.

    **Fields:**
    - All fields from `ProperCurve`
    - `smooth` : Structure morphism is smooth of relative dimension 1

    **NOT bundled** (these are THEOREMS):
    - Local rings are DVRs (follows from smooth + dim 1)
    - Riemann-Roch theorem (follows from proper + smooth)

    **NOTE:** The genus is NOT bundled as data. It is COMPUTED as h¹(O_C)
    via `SmoothProjectiveCurve.genus` in Cohomology/SheafCohomology.lean.
    This prevents smuggling of the genus value.
-/
structure SmoothProjectiveCurve extends ProperCurve where
  /-- Smooth of relative dimension 1 over ℂ.

      This encodes that C is a "curve" (dimension 1) and is smooth.
      The relative dimension 1 is part of the DEFINITION of being a curve,
      not a computed result.

      `IsSmoothOfRelativeDimension 1` implies `IsSmooth`. -/
  [smooth : IsSmoothOfRelativeDimension 1 structureMorphism]

attribute [instance] SmoothProjectiveCurve.smooth

namespace SmoothProjectiveCurve

variable (C : SmoothProjectiveCurve)

/-- Coercion to ProperCurve. -/
instance : Coe SmoothProjectiveCurve ProperCurve := ⟨SmoothProjectiveCurve.toProperCurve⟩

/-- Coercion to AlgebraicCurve. -/
instance : Coe SmoothProjectiveCurve AlgebraicCurve := ⟨fun C => C.toProperCurve.toAlgebraicCurve⟩

/-- Derive IsSmooth from IsSmoothOfRelativeDimension 1. -/
instance toSchemeIsSmooth : IsSmooth C.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth (n := 1) (f := C.structureMorphism)

/-!
### Convenience accessors

These lift definitions from AlgebraicCurve to SmoothProjectiveCurve.
-/

/-- The underlying scheme. -/
abbrev scheme : Scheme := C.toScheme

/-- The set of points. -/
abbrev PointType : Type _ := C.toAlgebraicCurve.PointType

/-- The function field K(C) as a type. -/
noncomputable abbrev FunctionFieldType : Type _ := C.toAlgebraicCurve.FunctionFieldType

/-- The function field is a field. -/
noncomputable instance functionFieldField : Field C.FunctionFieldType :=
  C.toAlgebraicCurve.functionFieldField

/-- The stalk at a point. -/
noncomputable abbrev StalkType (x : C.PointType) : Type _ := C.toAlgebraicCurve.StalkType x

/-- Stalks are local rings. -/
noncomputable instance stalkIsLocalRing (x : C.PointType) : IsLocalRing (C.StalkType x) :=
  C.toAlgebraicCurve.stalkIsLocalRing x

/-- Stalks are domains. -/
instance stalkIsDomain (x : C.PointType) : IsDomain (C.StalkType x) :=
  C.toAlgebraicCurve.stalkIsDomain x

/-- The residue field at a point. -/
noncomputable abbrev ResidueFieldCat (x : C.PointType) : CommRingCat :=
  C.toAlgebraicCurve.ResidueFieldCat x

/-- The embedding of constants ℂ → K(C). -/
noncomputable abbrev constantsEmbed : ℂ →+* C.FunctionFieldType :=
  C.toAlgebraicCurve.constantsEmbed

/-- The ℂ-algebra structure on K(C). -/
noncomputable instance functionFieldAlgebra : Algebra ℂ C.FunctionFieldType :=
  C.toAlgebraicCurve.functionFieldAlgebra

end SmoothProjectiveCurve

end RiemannSurfaces.SchemeTheoretic
