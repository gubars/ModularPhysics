/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.LocalRings
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Constants Have Valuation Zero

This file proves that constants (elements from ℂ embedded into the function field)
have valuation 0 at every point.

## Main Results

* `SmoothProjectiveCurve.constantsEmbed_eq_algebraMap_unit` - Constants are algebraMap of units
* `SmoothProjectiveCurve.valuationAt_constant'` - Constants have valuation 0

## Proof Strategy

For a constant c = constantsEmbed z with z ≠ 0:
1. The scalar tower Γ(C, ⊤) → O_{C,x} → K(C) shows c = algebraMap(germ_x(s))
   where s is the global section corresponding to z
2. By residueFieldIsComplex, κ(x) ≅ ℂ, so nonzero constants map to nonzero
   elements in the residue field
3. An element not in the maximal ideal is a unit in a local ring
4. Units in a DVR have addVal = 0, hence extendedVal = 0

## References

* Mathlib.AlgebraicGeometry.FunctionField
* Hartshorne, "Algebraic Geometry", Chapter II.6
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace RiemannSurfaces.SchemeTheoretic

namespace SmoothProjectiveCurve

variable (C : SmoothProjectiveCurve)

/-!
## Helper Definitions and Lemmas

Infrastructure for factoring constantsEmbed through stalks.
-/

/-- The global section on C corresponding to a constant z ∈ ℂ.

    This is the pullback of the constant section on Spec ℂ. -/
noncomputable def constantGlobalSection (z : ℂ) : Γ(C.toScheme, ⊤) :=
  C.structureMorphism.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom z)

/-- The germ of a constant global section at a point.

    This is the stalk element whose algebraMap to K(C) gives constantsEmbed z. -/
noncomputable def constantGerm (x : C.PointType) (z : ℂ) : C.toScheme.presheaf.stalk x :=
  (C.toScheme.presheaf.germ ⊤ x trivial).hom (C.constantGlobalSection z)

/-- constantsEmbed factors through stalks via the scalar tower.

    **Mathematical content:**
    By Mathlib's functionField_isScalarTower, we have a scalar tower:
      Γ(C, ⊤) → O_{C,x} → K(C)
    The constantsEmbed map factors as:
      ℂ → Γ(C, ⊤) → K(C) = ℂ → Γ(C, ⊤) → O_{C,x} → K(C)

    Therefore constantsEmbed z = algebraMap (stalk x) K(C) (constantGerm x z). -/
theorem constantsEmbed_eq_algebraMap_germ (x : C.PointType) (z : ℂ) :
    C.constantsEmbed z = algebraMap (C.toScheme.presheaf.stalk x) (C.toScheme.functionField)
      (C.constantGerm x z) := by
  -- Direct proof using the definitions
  simp only [constantsEmbed, constantGlobalSection, constantGerm]
  haveI : Nonempty (⊤ : C.toScheme.Opens) := C.topOpenSetNonempty
  -- The specialization from generic point to x
  have hspec : (genericPoint C.toScheme) ⤳ x := (genericPoint_spec C.toScheme).specializes trivial
  have hx : x ∈ (⊤ : C.toScheme.Opens) := trivial
  have hgen : (genericPoint C.toScheme) ∈ (⊤ : C.toScheme.Opens) :=
    hspec.mem_open (⊤ : C.toScheme.Opens).isOpen hx
  -- germ_stalkSpecializes: germ ⊤ x hx ≫ stalkSpecializes hspec = germ ⊤ genericPoint hgen
  have heq := C.toScheme.presheaf.germ_stalkSpecializes (U := ⊤) hx hspec
  -- The algebraMap from stalk x to functionField is stalkSpecializes
  -- germToFunctionField is germ at genericPoint
  -- So: germToFunctionField s = (germ x ≫ stalkSpecializes) s = algebraMap (germ s)
  conv_lhs => rw [show (C.toScheme.germToFunctionField ⊤) =
    C.toScheme.presheaf.germ ⊤ x hx ≫ C.toScheme.presheaf.stalkSpecializes hspec from heq.symm]
  rfl

/-- The residue of a constant germ is nonzero when z ≠ 0.

    **Proof outline:**
    1. The structure morphism π : C → Spec ℂ induces a map on residue fields:
       π.residueFieldMap x : κ(π(x)) → κ(x)
    2. κ(π(x)) ≅ ℂ (Spec ℂ has one point with residue field ℂ)
    3. κ(x) ≅ ℂ (by residueFieldIsComplex)
    4. The residue of constantGerm x z is π.residueFieldMap x (evaluation of z on Spec ℂ)
    5. Since the residue field map is a ring homomorphism between fields, it's injective
    6. Therefore nonzero z maps to nonzero residue -/
theorem constantGerm_residue_ne_zero (x : C.PointType) (z : ℂ) (hz : z ≠ 0) :
    C.toScheme.residue x (C.constantGerm x z) ≠ 0 := by
  -- The composition ℂ → Γ(Spec ℂ, ⊤) → Γ(C, ⊤) → O_{C,x} → κ(x)
  -- is a ring homomorphism. Ring homomorphisms from a field are injective.
  -- Therefore nonzero z maps to nonzero residue.
  --
  -- Using residueFieldIsComplex, κ(x) ≅ ℂ, we can compose with this isomorphism
  -- to get a ring homomorphism ℂ → ℂ, which is injective.

  -- Get the residue field isomorphism from the structure
  obtain ⟨iso⟩ := C.residueFieldIsComplex x

  -- Construct the ring homomorphism from ℂ to the residue field κ(x)
  -- This is: ℂ → Γ(Spec ℂ) → Γ(C) → O_{C,x} → κ(x)
  let evalAtX : Γ(C.toScheme, ⊤) →+* C.toScheme.residueField x :=
    (C.toScheme.Γevaluation x).hom
  let globalSectionMap : ℂ →+* Γ(C.toScheme, ⊤) :=
    C.structureMorphism.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let toResidueField : ℂ →+* C.toScheme.residueField x := evalAtX.comp globalSectionMap

  -- The full map ℂ → ℂ (via the residue field iso)
  let φ : ℂ →+* ℂ := iso.hom.hom.comp toResidueField

  -- Key observation: φ is injective (ring hom from a field)
  have hφ_inj : Function.Injective φ := RingHom.injective φ

  -- The residue of constantGerm equals the image under toResidueField
  -- residue (constantGerm x z) = evaluation (constantGlobalSection z) = toResidueField z
  have heval : (C.toScheme.residue x).hom (C.constantGerm x z) = toResidueField z := by
    simp only [constantGerm, constantGlobalSection, toResidueField, evalAtX, globalSectionMap]
    rfl

  -- If residue = 0, then toResidueField z = 0, hence φ z = φ 0 = 0, hence z = 0
  intro h
  have h' : toResidueField z = 0 := by
    rw [← heval]
    exact h
  have hφz : φ z = φ 0 := by simp only [φ, RingHom.comp_apply, h', map_zero]
  exact hz (hφ_inj hφz)

/-- A stalk element with nonzero residue is a unit. -/
theorem stalk_isUnit_of_residue_ne_zero (x : C.PointType) (s : C.toScheme.presheaf.stalk x)
    (hs : C.toScheme.residue x s ≠ 0) : IsUnit s := by
  -- s ∉ maximalIdeal ↔ IsUnit s (by IsLocalRing.notMem_maximalIdeal)
  -- s ∈ maximalIdeal ↔ residue s = 0 (by definition of residue field)
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hmem
  -- If s ∈ maximalIdeal, then residue s = 0
  -- The residue map is IsLocalRing.residue, and residue_eq_zero_iff gives the equivalence
  apply hs
  -- Need to show: C.toScheme.residue x s = 0
  -- Scheme.residue x is CommRingCat.ofHom (IsLocalRing.residue _)
  -- The underlying function is IsLocalRing.residue
  have h : IsLocalRing.residue (C.toScheme.presheaf.stalk x) s = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hmem
  -- Now connect Scheme.residue to IsLocalRing.residue
  -- Scheme.residue is defined as CommRingCat.ofHom (IsLocalRing.residue)
  show (C.toScheme.residue x).hom s = 0
  simp only [Scheme.residue]
  exact h

/-!
## Constants are Units in Stalks

The key theorem: nonzero constants embed as units in stalks.
-/

/-- Nonzero constants embed as algebraMap of units in stalks.

    **Mathematical content:**
    For z : ℂ with z ≠ 0:
    1. constantsEmbed z ∈ K(C) factors through the stalk O_{C,x}
    2. The preimage in O_{C,x} is a unit (by residue field argument)
    3. Therefore constantsEmbed z = algebraMap(u) for some unit u

    **Proof approach:**
    - Γ(C, ⊤) → O_{C,x} → K(C) is the scalar tower from Mathlib
    - The germ of a constant global section at x is in O_{C,x}
    - Nonzero constants are units in O_{C,x} because:
      * O_{C,x} → κ(x) ≅ ℂ (by residueFieldIsComplex)
      * A nonzero constant maps to nonzero in κ(x)
      * Hence it's not in the maximal ideal, hence it's a unit -/
theorem constantsEmbed_eq_algebraMap_unit (x : C.PointType) (z : ℂ) (hz : z ≠ 0) :
    ∃ u : (C.toScheme.presheaf.stalk x)ˣ,
      algebraMap (C.toScheme.presheaf.stalk x) (C.toScheme.functionField) u =
      C.constantsEmbed z := by
  -- Step 1: Get the stalk element (the germ of the constant section)
  let s := C.constantGerm x z
  -- Step 2: Show constantsEmbed z = algebraMap s
  have heq := C.constantsEmbed_eq_algebraMap_germ x z
  -- Step 3: Show s has nonzero residue
  have hres : C.toScheme.residue x s ≠ 0 := C.constantGerm_residue_ne_zero x z hz
  -- Step 4: Therefore s is a unit
  have hunit : IsUnit s := C.stalk_isUnit_of_residue_ne_zero x s hres
  -- Step 5: Extract the unit
  obtain ⟨u, hu⟩ := hunit
  use u
  rw [heq, hu]

/-- Constants have valuation 0 (using unit representation).

    This is the key theorem: if constantsEmbed z is algebraMap of a unit,
    then by extendedVal_unit, its valuation is 0. -/
theorem valuationAt_constant' (x : C.PointType) (z : ℂ) (hz : z ≠ 0) :
    C.valuationAt x (C.constantsEmbed z) = 0 := by
  -- Get the unit representation
  obtain ⟨u, hu⟩ := C.constantsEmbed_eq_algebraMap_unit x z hz
  -- Rewrite using the unit representation
  rw [← hu]
  -- Apply extendedVal_unit
  unfold valuationAt
  exact @DVRValuation.extendedVal_unit
    (C.toScheme.presheaf.stalk x)
    (C.toScheme.functionField)
    _ _ (C.stalkIsDVR x) _ _ _ u

end SmoothProjectiveCurve

end RiemannSurfaces.SchemeTheoretic
