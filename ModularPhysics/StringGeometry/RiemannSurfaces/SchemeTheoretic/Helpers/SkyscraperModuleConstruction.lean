/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Module.PUnit
import Mathlib.Topology.Sheaves.Skyscraper
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Helpers.SkyscraperInfrastructure

/-!
# Skyscraper Module Construction

This file constructs the skyscraper O_X-module at a point p on a scheme X.

The skyscraper sheaf k_p is the O_X-module with:
- Sections k_p(U) = κ(p) if p ∈ U, else PUnit (trivial = zero module)
- Module action: f · v = evalAtPoint(f)(p) · v for f ∈ O_X(U), v ∈ κ(p)
- Restriction: identity on κ(p) when p is in both opens, zero otherwise
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Classical

namespace RiemannSurfaces.SchemeTheoretic.SkyscraperConstruction

variable {X : Scheme}

/-!
## Type compatibility

The carrier type `↑(X.ringCatSheaf.val.obj U)` equals `Γ(X, U.unop)` definitionally.
We establish this and use it to transfer module instances.
-/

/-- The underlying type of ringCatSheaf sections agrees with the presheaf sections type.
    This follows from `forgetToRingCat_obj` in Mathlib. -/
theorem ringCatSheaf_carrier_eq (U : (Opens X.carrier)ᵒᵖ) :
    (X.ringCatSheaf.val.obj U : Type _) = (X.presheaf.obj U : Type _) := rfl

/-- Module instance on κ(p) over the ringCatSheaf ring of sections.
    Uses the fact that the carrier types are definitionally equal. -/
noncomputable def residueFieldModuleRCS (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (hp : (p : X.carrier) ∈ U.unop) :
    Module ↑(X.ringCatSheaf.val.obj U) (X.residueField p) :=
  residueFieldModule p U.unop hp

/-!
## Evaluation-Restriction Compatibility
-/

/-- Evaluation at p commutes with restriction of sections. -/
theorem evalAtPoint_comp_restriction (p : X) (U V : Opens X.carrier)
    (hpU : (p : X.carrier) ∈ U) (hpV : (p : X.carrier) ∈ V) (hUV : U ≤ V)
    (r : Γ(X, V)) :
    (evalAtPoint p U hpU) ((X.presheaf.map (homOfLE hUV).op).hom r) =
    (evalAtPoint p V hpV) r := by
  simp only [evalAtPoint]
  show ((X.presheaf.map (homOfLE hUV).op ≫ X.presheaf.germ U (↑p) hpU) ≫
    X.residue (↑p)).hom r = (X.presheaf.germ V (↑p) hpV ≫ X.residue (↑p)).hom r
  rw [X.presheaf.germ_res (homOfLE hUV) (↑p) hpU]

/-!
## Object Definition
-/

/-- The module of sections of the skyscraper sheaf at p over U.
    Returns κ(p) when p ∈ U, and PUnit (zero module) otherwise. -/
noncomputable def skyscraperObj (p : X) (U : (Opens X.carrier)ᵒᵖ) :
    ModuleCat ↑(X.ringCatSheaf.val.obj U) :=
  if h : (p : X.carrier) ∈ U.unop then
    letI := residueFieldModuleRCS p U h
    ModuleCat.of ↑(X.ringCatSheaf.val.obj U) (X.residueField p)
  else
    ModuleCat.of ↑(X.ringCatSheaf.val.obj U) PUnit

/-- When p ∈ U, the skyscraper sections are κ(p). -/
theorem skyscraperObj_pos (p : X) (U : (Opens X.carrier)ᵒᵖ) (h : (p : X.carrier) ∈ U.unop) :
    skyscraperObj p U = (
      letI := residueFieldModuleRCS p U h
      ModuleCat.of ↑(X.ringCatSheaf.val.obj U) (X.residueField p) :
        ModuleCat ↑(X.ringCatSheaf.val.obj U)) := by
  simp only [skyscraperObj, dif_pos h]

/-- When p ∉ U, the skyscraper sections are PUnit. -/
theorem skyscraperObj_neg (p : X) (U : (Opens X.carrier)ᵒᵖ) (h : (p : X.carrier) ∉ U.unop) :
    skyscraperObj p U = (ModuleCat.of ↑(X.ringCatSheaf.val.obj U) PUnit) := by
  simp only [skyscraperObj, dif_neg h]

/-!
## Restriction Maps
-/

/-- The restriction map for the skyscraper presheaf of modules. -/
noncomputable def skyscraperMap (p : X) {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V) :
    skyscraperObj p U ⟶
      (ModuleCat.restrictScalars (X.ringCatSheaf.val.map f).hom).obj (skyscraperObj p V) := by
  by_cases hV : (p : X.carrier) ∈ V.unop
  · -- p ∈ V, hence p ∈ U
    have hU : (p : X.carrier) ∈ U.unop := f.unop.le hV
    -- Cast source and target to concrete forms
    refine eqToHom (skyscraperObj_pos p U hU) ≫ ?_ ≫
      (ModuleCat.restrictScalars (X.ringCatSheaf.val.map f).hom).map
        (eqToHom (skyscraperObj_pos p V hV).symm)
    -- The identity map κ(p) → κ(p) as semilinear map
    letI := residueFieldModuleRCS p U hU
    letI := residueFieldModuleRCS p V hV
    exact ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.val.map f).hom).obj
        (ModuleCat.of ↑(X.ringCatSheaf.val.obj V) (X.residueField p)))
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun r v => by
          simp only [RingHom.id_apply]
          change (evalAtPoint p U.unop hU) r • v =
                 (evalAtPoint p V.unop hV) ((X.ringCatSheaf.val.map f).hom r) • v
          congr 1
          symm
          exact evalAtPoint_comp_restriction p V.unop U.unop hV hU f.unop.le r }
  · -- p ∉ V, target has PUnit carrier
    rw [show skyscraperObj p V = ModuleCat.of _ PUnit from skyscraperObj_neg p V hV]
    exact 0

/-!
## Presheaf of Modules
-/

/-- The skyscraper presheaf of modules at point p on scheme X. -/
noncomputable def skyscraperPresheafOfModules (p : X) :
    PresheafOfModules X.ringCatSheaf.val where
  obj := skyscraperObj p
  map f := skyscraperMap p f
  map_id U := by
    -- Both sides are the identity on elements:
    -- LHS: skyscraperMap p (𝟙 U) = id on κ(p) or 0 on PUnit
    -- RHS: (restrictScalarsId' ...).inv.app _ = id (by restrictScalarsId'App_inv_apply)
    sorry
  map_comp f g := by
    -- Both sides compose restriction maps:
    -- LHS: skyscraperMap p (f ≫ g) = id on κ(p) or 0
    -- RHS: skyscraperMap p f ≫ restrictScalars.map(skyscraperMap p g) ≫ comp_iso
    sorry

/-- The skyscraper presheaf of modules satisfies the sheaf condition. -/
theorem skyscraper_isSheaf (p : X) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X.carrier)
      (skyscraperPresheafOfModules p).presheaf :=
  sorry

/-- The skyscraper O_X-module at point p. -/
noncomputable def constructSkyscraperModule (p : X) :
    SheafOfModules X.ringCatSheaf where
  val := skyscraperPresheafOfModules p
  isSheaf := skyscraper_isSheaf p

/-- When p ∉ U, the carrier of skyscraperObj is a subsingleton (it's PUnit). -/
instance skyscraperObj_subsingleton (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∉ U.unop) :
    Subsingleton ↑(skyscraperObj p U) := by
  rw [skyscraperObj_neg p U h]
  exact instSubsingletonPUnit

/-- The carrier type of skyscraperObj is the same as that of the restrictScalars variant. -/
theorem skyscraperObj_restrictScalars_carrier (p : X) (U : (Opens X.carrier)ᵒᵖ)
    {V : (Opens X.carrier)ᵒᵖ} (f : V ⟶ U) :
    (↑((ModuleCat.restrictScalars (X.ringCatSheaf.val.map f).hom).obj (skyscraperObj p U)) : Type _) =
    (↑(skyscraperObj p U) : Type _) := rfl

/-- When p ∉ U, the restrictScalars variant is also a subsingleton. -/
instance skyscraperObj_restrictScalars_subsingleton (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∉ U.unop)
    {V : (Opens X.carrier)ᵒᵖ} (f : V ⟶ U) :
    Subsingleton ↑((ModuleCat.restrictScalars (X.ringCatSheaf.val.map f).hom).obj (skyscraperObj p U)) := by
  rw [show (↑((ModuleCat.restrictScalars (X.ringCatSheaf.val.map f).hom).obj
    (skyscraperObj p U)) : Type _) = ↑(skyscraperObj p U) from rfl]
  exact skyscraperObj_subsingleton p U h

/-- eqToHom followed by its inverse is identity on elements (using .hom). -/
theorem eqToHom_hom_symm_comp {R : Type*} [Ring R] {A B : ModuleCat R}
    (h : A = B) (x : ↑A) :
    (eqToHom h.symm).hom ((eqToHom h).hom x) = x := by
  subst h; rfl

/-- eqToHom inverse followed by eqToHom is identity on elements (using .hom). -/
theorem eqToHom_hom_comp_symm {R : Type*} [Ring R] {A B : ModuleCat R}
    (h : A = B) (y : ↑B) :
    (eqToHom h).hom ((eqToHom h.symm).hom y) = y := by
  subst h; rfl

/-- The restriction map of the skyscraper presheaf is surjective. -/
theorem skyscraperMap_surjective (p : X) {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V) :
    Function.Surjective (skyscraperMap p f) := by
  intro y
  by_cases hV : (p : X.carrier) ∈ V.unop
  · -- p ∈ V (hence p ∈ U): map is eqToHom ≫ id ≫ restrictScalars.map(eqToHom)
    have hU : (p : X.carrier) ∈ U.unop := f.unop.le hV
    -- Cast y to κ(p) via eqToHom (carrier of restrictScalars = carrier of original)
    let y_kp : X.residueField p := (eqToHom (skyscraperObj_pos p V hV)).hom y
    -- Cast back to source type
    let x : ↑(skyscraperObj p U) := (eqToHom (skyscraperObj_pos p U hU).symm).hom y_kp
    exact ⟨x, by
      -- skyscraperMap p f x = y
      -- After unfolding, the goal has 4 eqToHom applications to y.
      -- They cancel pairwise: eqToHom(h) ∘ eqToHom(h.symm) = id.
      simp only [skyscraperMap, dif_pos hV, x, y_kp]
      -- Normalize all coercion paths to use .hom (ConcreteCategory.hom = .hom defeq)
      change (eqToHom (skyscraperObj_pos p V hV).symm).hom
        ((eqToHom (skyscraperObj_pos p U hU)).hom
          ((eqToHom (skyscraperObj_pos p U hU).symm).hom
            ((eqToHom (skyscraperObj_pos p V hV)).hom y))) = y
      rw [eqToHom_hom_comp_symm (skyscraperObj_pos p U hU)]
      rw [eqToHom_hom_symm_comp (skyscraperObj_pos p V hV)]⟩
  · -- p ∉ V: target is PUnit (subsingleton), any preimage works
    have hsub : Subsingleton ↑((ModuleCat.restrictScalars
        (X.ringCatSheaf.val.map f).hom).obj (skyscraperObj p V)) :=
      skyscraperObj_restrictScalars_subsingleton p V hV f
    exact ⟨0, hsub.elim _ _⟩

/-- Global sections of the skyscraper module are κ(p). -/
theorem skyscraper_globalSections_eq (p : X) :
    skyscraperObj p (op ⊤) = (
      letI := residueFieldModuleRCS p (op ⊤) (Set.mem_univ (↑p))
      ModuleCat.of _ (X.residueField p) :
        ModuleCat ↑(X.ringCatSheaf.val.obj (op ⊤))) :=
  skyscraperObj_pos p (op ⊤) (Set.mem_univ _)

end RiemannSurfaces.SchemeTheoretic.SkyscraperConstruction
