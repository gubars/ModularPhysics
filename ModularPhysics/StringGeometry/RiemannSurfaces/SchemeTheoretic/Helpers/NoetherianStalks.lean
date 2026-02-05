/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Basic

/-!
# Noetherian Stalks for Smooth Projective Curves

This file proves that stalks of smooth projective curves over ℂ are Noetherian rings.

## Main Results

* `SmoothProjectiveCurve.stalkIsNoetherianRing` - Stalks are Noetherian rings

## Proof Strategy

The proof uses the following chain:
1. ℂ is a Noetherian ring (it's a field)
2. `Spec ℂ` is locally Noetherian
3. Smooth morphisms are locally of finite type
4. If `f : X ⟶ Y` is locally of finite type and `Y` is locally Noetherian, then `X` is locally Noetherian
5. Therefore `C` is locally Noetherian
6. Stalks of locally Noetherian schemes are Noetherian rings

## References

* Mathlib.AlgebraicGeometry.Noetherian
* Hartshorne, "Algebraic Geometry", Chapter II.3
-/

open AlgebraicGeometry CategoryTheory

namespace RiemannSurfaces.SchemeTheoretic

/-!
## ℂ is Noetherian

ℂ is a field, hence a Noetherian ring.
-/

/-- ℂ is a Noetherian ring (as a field, every ideal is finitely generated). -/
instance complexIsNoetherianRing : IsNoetherianRing ℂ :=
  inferInstance  -- Fields are Noetherian rings

/-- `CommRingCat.of ℂ` has `IsNoetherianRing` instance. -/
instance complexCommRingCatIsNoetherianRing : IsNoetherianRing (CommRingCat.of ℂ) :=
  complexIsNoetherianRing

/-!
## Spec ℂ is Locally Noetherian

By Mathlib's instance `instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier`,
Spec of a Noetherian ring is locally Noetherian.
-/

/-- `Spec ℂ` is locally Noetherian.

    We show this by noting that `SpecComplex = Spec (CommRingCat.of ℂ)` definitionally,
    and Mathlib provides an instance for `IsLocallyNoetherian (Spec R)` when `R` is Noetherian. -/
instance specComplexIsLocallyNoetherian : IsLocallyNoetherian SpecComplex := by
  -- SpecComplex = Scheme.Spec.obj (Opposite.op (CommRingCat.of ℂ))
  --             = Spec (unop (op (CommRingCat.of ℂ)))
  --             = Spec (CommRingCat.of ℂ)
  -- The instance for IsLocallyNoetherian (Spec R) when [IsNoetherianRing R] should apply
  show IsLocallyNoetherian (Spec (CommRingCat.of ℂ))
  infer_instance

/-!
## Smooth Morphisms are Locally of Finite Type

Smooth morphisms are locally of finite type by definition.
-/

namespace SmoothProjectiveCurve

variable (C : SmoothProjectiveCurve)

/-- The structure morphism is locally of finite type (follows from smoothness).

    **Mathematical content:**
    Smooth morphisms are locally of finite presentation, which implies locally of finite type. -/
instance structureMorphismLocallyOfFiniteType : LocallyOfFiniteType C.structureMorphism := by
  -- IsSmooth implies LocallyOfFinitePresentation implies LocallyOfFiniteType
  -- IsSmoothOfRelativeDimension 1 implies IsSmooth (via C.toSchemeIsSmooth)
  infer_instance

/-!
## C is Locally Noetherian

By `LocallyOfFiniteType.isLocallyNoetherian`, if `f : X ⟶ Y` is locally of finite type
and `Y` is locally Noetherian, then `X` is locally Noetherian.
-/

/-- The curve C is locally Noetherian.

    **Mathematical content:**
    - The structure morphism `C → Spec ℂ` is locally of finite type (from smoothness)
    - `Spec ℂ` is locally Noetherian (ℂ is a Noetherian ring)
    - A finite type algebra over a Noetherian ring is Noetherian (Hilbert basis theorem)
    - Therefore the coordinate rings of affine opens are Noetherian, making `C` locally Noetherian

    **Proof:**
    Use `isLocallyNoetherian_iff_of_affine_openCover` with the affine cover of C.
    Each affine piece has Noetherian sections because:
    1. LocallyOfFiniteType means the map ℂ → Γ(V) has RingHom.FiniteType
    2. RingHom.FiniteType gives Algebra.FiniteType
    3. By `Algebra.FiniteType.isNoetherianRing`, finitely generated ℂ-algebras are Noetherian -/
instance toSchemeIsLocallyNoetherian : IsLocallyNoetherian C.toScheme := by
  -- Use the affine cover of the scheme
  rw [isLocallyNoetherian_iff_of_affine_openCover (C.toScheme.affineCover)]
  intro i
  -- Need: IsNoetherianRing Γ(affineCover.X i, ⊤)
  haveI : IsAffine (C.toScheme.affineCover.X i) := Scheme.isAffine_affineCover _ _
  -- The coordinate ring of the affine piece
  let Ai := Γ(C.toScheme.affineCover.X i, ⊤)
  -- The structure morphism is locally of finite type (from smoothness)
  haveI hLFT : LocallyOfFiniteType C.structureMorphism := C.structureMorphismLocallyOfFiniteType
  -- The affine cover map: affineCover.X i → C
  let fi := C.toScheme.affineCover.f i
  -- Spec ℂ has ⊤ as an affine open with sections ℂ
  haveI hSpecAffine : IsAffine SpecComplex := isAffine_Spec _
  let specTop : SpecComplex.affineOpens := ⟨⊤, isAffineOpen_top SpecComplex⟩
  -- The preimage of ⊤ under structureMorphism is all of C
  have hpreimg : fi.opensRange.1 ≤ C.structureMorphism ⁻¹ᵁ specTop.1 := by
    intro x _
    trivial
  -- The affine open in C
  let Vi : C.toScheme.affineOpens := ⟨fi.opensRange, isAffineOpen_opensRange fi⟩
  -- LocallyOfFiniteType gives us that the map Γ(Spec ℂ, ⊤) → Γ(C, Vi) has FiniteType
  have hFT := LocallyOfFiniteType.finiteType_of_affine_subset (f := C.structureMorphism)
    specTop Vi hpreimg
  -- Γ(affineCover.X i, ⊤) ≅ Γ(C, Vi) via IsOpenImmersion.ΓIsoTop
  have hIso : Ai ≅ Γ(C.toScheme, Vi.1) := IsOpenImmersion.ΓIsoTop fi
  -- Γ(C, Vi) is Noetherian using Hilbert basis theorem
  -- The map Γ(Spec ℂ, ⊤) → Γ(C, Vi) has FiniteType by hFT
  -- Γ(Spec ℂ, ⊤) is Noetherian (it's ℂ)
  haveI hNoethSpec : IsNoetherianRing Γ(SpecComplex, specTop.1) := by
    apply isNoetherianRing_of_ringEquiv (R := ℂ)
    exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv
  -- hFT says the ring map Γ(Spec ℂ, ⊤) → Γ(C, Vi) has FiniteType
  -- By RingHom.FiniteType definition, this means Γ(C, Vi) is a finitely generated
  -- Γ(Spec ℂ, ⊤)-algebra. Since Γ(Spec ℂ, ⊤) is Noetherian, so is Γ(C, Vi).
  let appMap := C.structureMorphism.appLE specTop Vi hpreimg
  haveI hNoethVi : IsNoetherianRing Γ(C.toScheme, Vi.1) := by
    -- appMap.hom has RingHom.FiniteType
    -- This means Γ(C, Vi) is a finitely generated Γ(Spec ℂ, ⊤)-algebra
    -- Apply Hilbert basis theorem
    -- Use algebraize to set up the algebra structure from the ring homomorphism
    algebraize [appMap.hom]
    -- hFT gives RingHom.FiniteType appMap.hom, which by definition is
    -- @Algebra.FiniteType _ _ _ _ appMap.hom.toAlgebra
    -- After algebraize, this should be Algebra.FiniteType _ _
    exact Algebra.FiniteType.isNoetherianRing Γ(SpecComplex, specTop.1) Γ(C.toScheme, Vi.1)
  -- Transfer through the isomorphism to Γ(affineCover.X i, ⊤)
  exact isNoetherianRing_of_ringEquiv (R := Γ(C.toScheme, Vi.1))
    hIso.symm.commRingCatIsoToRingEquiv

/-!
## Stalks are Noetherian

By Mathlib's instance for locally Noetherian schemes, stalks are Noetherian rings.
-/

/-- Stalks of the curve are Noetherian rings.

    **Proof:** Uses Mathlib's `instIsNoetherianRingCarrierStalkCommRingCatPresheafOfIsLocallyNoetherian`
    which states that stalks of locally Noetherian schemes are Noetherian rings.

    This is a PROPER DEFINITION (no sorry), using Mathlib's infrastructure. -/
instance stalkIsNoetherianRing (x : C.PointType) : IsNoetherianRing (C.StalkType x) :=
  inferInstanceAs (IsNoetherianRing (C.toScheme.presheaf.stalk x))

end SmoothProjectiveCurve

end RiemannSurfaces.SchemeTheoretic
