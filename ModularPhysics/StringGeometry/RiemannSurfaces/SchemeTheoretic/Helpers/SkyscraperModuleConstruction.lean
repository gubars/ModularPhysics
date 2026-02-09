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

/-- When p ∉ U, the carrier of skyscraperObj is a subsingleton (it's PUnit). -/
instance skyscraperObj_subsingleton' (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∉ U.unop) :
    Subsingleton ↑(skyscraperObj p U) := by
  rw [skyscraperObj_neg p U h]
  exact instSubsingletonPUnit

/-- The carrier type of restrictScalars.obj equals the original carrier. -/
theorem skyscraperObj_restrictScalars_carrier' (p : X) (U : (Opens X.carrier)ᵒᵖ)
    {V : (Opens X.carrier)ᵒᵖ} (f : V ⟶ U) :
    (↑((ModuleCat.restrictScalars (X.ringCatSheaf.val.map f).hom).obj (skyscraperObj p U)) : Type _) =
    (↑(skyscraperObj p U) : Type _) := rfl

/-- When p ∉ U, the restrictScalars variant is also a subsingleton. -/
instance skyscraperObj_restrictScalars_subsingleton' (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∉ U.unop)
    {V : (Opens X.carrier)ᵒᵖ} (f : V ⟶ U) :
    Subsingleton ↑((ModuleCat.restrictScalars (X.ringCatSheaf.val.map f).hom).obj (skyscraperObj p U)) := by
  rw [show (↑((ModuleCat.restrictScalars (X.ringCatSheaf.val.map f).hom).obj
    (skyscraperObj p U)) : Type _) = ↑(skyscraperObj p U) from rfl]
  exact skyscraperObj_subsingleton' p U h

/-- eqToHom followed by its inverse is identity on elements (using .hom). -/
@[simp] theorem eqToHom_hom_symm_comp' {R : Type*} [Ring R] {A B : ModuleCat R}
    (h : A = B) (x : ↑A) :
    (eqToHom h.symm).hom ((eqToHom h).hom x) = x := by
  subst h; rfl

/-- eqToHom inverse followed by eqToHom is identity on elements (using .hom). -/
@[simp] theorem eqToHom_hom_comp_symm' {R : Type*} [Ring R] {A B : ModuleCat R}
    (h : A = B) (y : ↑B) :
    (eqToHom h).hom ((eqToHom h.symm).hom y) = y := by
  subst h; rfl

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
    by_cases h : (p : X.carrier) ∈ U.unop
    · -- p ∈ U: both sides are identity on κ(p) through type-level casts
      ext; apply DFunLike.ext; intro x
      -- RHS: restrictScalarsId'App.inv acts as identity on elements
      simp only [ModuleCat.restrictScalarsId'_inv_app,
        ModuleCat.restrictScalarsId'App_inv_apply]
      -- Now goal is: (skyscraperMap p (𝟙 U)).hom x = x
      -- LHS: unfold skyscraperMap and simplify the eqToHom chain
      simp only [skyscraperMap, dif_pos h, ModuleCat.comp_apply]
      -- Goal: eqToHom(pos.symm).hom (eqToHom(pos).hom x) = x
      exact eqToHom_hom_symm_comp' (skyscraperObj_pos p U h) x
    · -- p ∉ U: both source and target have PUnit carrier (subsingleton)
      ext; apply DFunLike.ext; intro x
      exact (skyscraperObj_restrictScalars_subsingleton' p U h (𝟙 U)).elim _ _
  map_comp {U V W} f g := by
    -- Work around instance diamond for restrictScalarsComp' (cf. Mathlib Pushforward.lean)
    refine ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
    by_cases hW : (p : X.carrier) ∈ W.unop
    · -- p ∈ W (hence p ∈ V and p ∈ U): all maps are identity on κ(p)
      have hV : (p : X.carrier) ∈ V.unop := g.unop.le hW
      -- Unfold skyscraperMap and comp iso to expose the eqToHom chains
      simp only [ModuleCat.restrictScalarsComp'_inv_app,
        ModuleCat.restrictScalarsComp'App_inv_apply,
        skyscraperMap, dif_pos hW, dif_pos hV,
        ModuleCat.comp_apply]
      -- The goal has ConcreteCategory.hom wrappers; normalize coercions
      -- Both sides are identity on κ(p) through eqToHom chains.
      -- Show both sides equal the same cast of x.
      -- LHS: eqToHom(W.symm).hom (id (eqToHom(U).hom x))
      -- RHS: eqToHom(W.symm).hom (eqToHom(V).hom (eqToHom(V.symm).hom (id (eqToHom(U).hom x))))
      -- The intermediate V pair cancels, making both sides equal.
      change (eqToHom (skyscraperObj_pos p W hW).symm).hom
            (id ((eqToHom (skyscraperObj_pos p U _)).hom x)) =
          (eqToHom (skyscraperObj_pos p W hW).symm).hom
            ((eqToHom (skyscraperObj_pos p V hV)).hom
              ((eqToHom (skyscraperObj_pos p V hV).symm).hom
                (id ((eqToHom (skyscraperObj_pos p U _)).hom x))))
      rw [eqToHom_hom_comp_symm' (skyscraperObj_pos p V hV)]
    · -- p ∉ W: target module has PUnit carrier (subsingleton)
      exact (skyscraperObj_restrictScalars_subsingleton' p W hW (f ≫ g)).elim _ _

/-!
## Helper Lemmas for Sheaf Condition

Key properties of the skyscraper presheaf restriction maps:
1. On elements, the presheaf map equals the skyscraperMap (by presheaf_map_apply_coe)
2. When both opens contain p, restriction acts as identity on κ(p)
3. The projection to κ(p) via eqToHom is injective
-/

/-- The projection from skyscraperObj sections to κ(p) via eqToHom. -/
noncomputable def toKappa (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∈ U.unop) :
    ↑(skyscraperObj p U) → X.residueField p :=
  (eqToHom (skyscraperObj_pos p U h)).hom

/-- The embedding from κ(p) to skyscraperObj sections. -/
noncomputable def fromKappa (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∈ U.unop) :
    X.residueField p → ↑(skyscraperObj p U) :=
  (eqToHom (skyscraperObj_pos p U h).symm).hom

@[simp] theorem toKappa_fromKappa (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∈ U.unop) (v : X.residueField p) :
    toKappa p U h (fromKappa p U h v) = v :=
  eqToHom_hom_comp_symm' (skyscraperObj_pos p U h) v

@[simp] theorem fromKappa_toKappa (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∈ U.unop) (x : ↑(skyscraperObj p U)) :
    fromKappa p U h (toKappa p U h x) = x :=
  eqToHom_hom_symm_comp' (skyscraperObj_pos p U h) x

/-- toKappa is injective. -/
theorem toKappa_injective (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∈ U.unop) :
    Function.Injective (toKappa p U h) := by
  intro a b hab
  have := congr_arg (fromKappa p U h) hab
  simp only [fromKappa_toKappa] at this
  exact this

/-- fromKappa is injective. -/
theorem fromKappa_injective (p : X) (U : (Opens X.carrier)ᵒᵖ)
    (h : (p : X.carrier) ∈ U.unop) :
    Function.Injective (fromKappa p U h) := by
  intro a b hab
  have := congr_arg (toKappa p U h) hab
  simp only [toKappa_fromKappa] at this
  exact this

/-- eqToHom applied to an element equals cast of the carrier equality. -/
theorem eqToHom_apply_eq_cast' {R : Type*} [Ring R] {A B : ModuleCat R}
    (h : A = B) (x : ↑A) :
    (eqToHom h).hom x = cast (congrArg (↑·) h) x := by
  cases h; rfl

/-- toKappa commutes with cast between carrier types.
    All casts through κ(p) give the same result by proof irrelevance. -/
theorem toKappa_cast (p : X) (U V : (Opens X.carrier)ᵒᵖ)
    (hU : (p : X.carrier) ∈ U.unop) (hV : (p : X.carrier) ∈ V.unop)
    (heq : (↑(skyscraperObj p U) : Type _) = ↑(skyscraperObj p V))
    (x : ↑(skyscraperObj p U)) :
    toKappa p V hV (cast heq x) = toKappa p U hU x := by
  simp only [toKappa]
  -- Convert eqToHom applications to cast
  rw [eqToHom_apply_eq_cast' (skyscraperObj_pos p V hV) (cast heq x),
      eqToHom_apply_eq_cast' (skyscraperObj_pos p U hU) x]
  -- Goal: cast _ (cast heq x) = cast _ x
  -- Both are casts of x to the same target type. Use HEq transitivity.
  exact eq_of_heq ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))

/-- The skyscraper presheaf of modules satisfies the sheaf condition.

    **Proof:** We prove the sheaf condition directly using the unique gluing
    characterization. The skyscraper presheaf assigns κ(p) to opens containing p
    and PUnit to opens not containing p, with identity restriction maps.
    Unique gluing follows because all sections at opens containing p must agree,
    and sections at opens not containing p are trivially unique (PUnit). -/
theorem skyscraper_isSheaf (p : X) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X.carrier)
      (skyscraperPresheafOfModules p).presheaf := by
  classical
  let F := (skyscraperPresheafOfModules p).presheaf
  -- Reduce to unique gluing characterization for concrete categories
  show TopCat.Presheaf.IsSheaf F
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hcompat
  -- Case split on whether p is in the union
  by_cases hp : (p : ↥X.carrier) ∈ (iSup U : Opens ↥X.carrier)
  · -- p ∈ iSup U: there exists i₀ with p ∈ U i₀
    obtain ⟨i₀, hi₀⟩ := Opens.mem_iSup.mp hp
    have hp_sup : (p : ↥X.carrier) ∈ (iSup U : Opens ↥X.carrier) :=
      Opens.mem_iSup.mpr ⟨i₀, hi₀⟩
    -- All F.obj carriers when p ∈ U are κ(p). Cast sf i₀ to the union type.
    have carrier_eq : (↑(skyscraperObj p (op (U i₀))) : Type _) =
                       (↑(skyscraperObj p (op (iSup U))) : Type _) := by
      simp only [iSup, skyscraperObj_pos p _ hi₀, skyscraperObj_pos p _ hp_sup]
    let s : ↑(F.obj (op (iSup U))) := cast carrier_eq (sf i₀)
    -- Helper: presheaf map on elements equals skyscraperMap (from presheaf_map_apply_coe)
    -- The restriction map preserves κ(p) value: toKappa(res x) = toKappa(x)
    have res_toKappa : ∀ {U' V' : (Opens X.carrier)ᵒᵖ} (f' : U' ⟶ V')
        (hU' : (p : X.carrier) ∈ U'.unop) (hV' : (p : X.carrier) ∈ V'.unop)
        (x' : ↑(F.obj U')),
        toKappa p V' hV' (F.map f' x') = toKappa p U' hU' x' := by
      intro U' V' f' hU' hV' x'
      -- Strategy: show F.map f' acts as fromKappa ∘ toKappa, then cancel
      suffices key : (F.map f').hom x' = fromKappa p V' hV' (toKappa p U' hU' x') by
        rw [show F.map f' x' = (F.map f').hom x' from rfl, key, toKappa_fromKappa]
      -- F.map on elements = skyscraperMap (definitionally through presheaf construction)
      change (skyscraperMap p f').hom x' = fromKappa p V' hV' (toKappa p U' hU' x')
      -- Unfold skyscraperMap in positive case and fromKappa/toKappa
      simp only [skyscraperMap, dif_pos hV', fromKappa, toKappa]
      -- The whole expression should be definitionally equal:
      -- Both sides compose eqToHom's and identity, ending up as the same cast
      rfl
    refine ⟨s, fun i => ?_, fun s' hs' => ?_⟩
    · -- Gluing: F.map (leSupr U i).op s = sf i
      by_cases hi : (p : ↥X.carrier) ∈ U i
      · -- p ∈ U i: show both sides project to the same κ(p) element
        apply toKappa_injective p (op (U i)) hi
        -- LHS: toKappa (F.map ... s) = toKappa s = toKappa (cast carrier_eq (sf i₀))
        --     = toKappa (sf i₀) (by toKappa_cast)
        rw [res_toKappa (Opens.leSupr U i).op hp_sup hi]
        -- Now goal: toKappa (iSup U) hp_sup s = toKappa (U i) hi (sf i)
        -- s = cast carrier_eq (sf i₀)
        rw [show (s : ↑(F.obj (op (iSup U)))) = cast carrier_eq (sf i₀) from rfl]
        rw [toKappa_cast p (op (U i₀)) (op (iSup U)) hi₀ hp_sup carrier_eq (sf i₀)]
        -- Now goal: toKappa (U i₀) hi₀ (sf i₀) = toKappa (U i) hi (sf i)
        -- Use compatibility to show sf i and sf i₀ have same κ(p) value
        have hp_inf : (p : ↥X.carrier) ∈ (U i ⊓ U i₀ : Opens ↥X.carrier) := ⟨hi, hi₀⟩
        have hcompat_ii₀ := hcompat i i₀
        -- Apply toKappa to both sides of compatibility
        have hk := congr_arg (toKappa p (op (U i ⊓ U i₀)) hp_inf) hcompat_ii₀
        rw [res_toKappa _ hi hp_inf, res_toKappa _ hi₀ hp_inf] at hk
        -- hk : toKappa (sf i) = toKappa (sf i₀)
        exact hk.symm
      · -- p ∉ U i: target is PUnit (subsingleton)
        haveI : Subsingleton ↑(F.obj (op (U i))) := by
          show Subsingleton ↑(skyscraperObj p (op (U i)))
          exact skyscraperObj_subsingleton' p _ hi
        exact Subsingleton.elim _ _
    · -- Uniqueness: show s' = s
      apply toKappa_injective p (op (iSup U)) hp_sup
      -- toKappa s' = toKappa (sf i₀) from hs' i₀ and res_toKappa
      have h_s' := hs' i₀
      have hk1 : toKappa p (op (U i₀)) hi₀ (F.map (Opens.leSupr U i₀).op s') =
                  toKappa p (op (U i₀)) hi₀ (sf i₀) := congr_arg _ h_s'
      rw [res_toKappa (Opens.leSupr U i₀).op hp_sup hi₀] at hk1
      -- hk1 : toKappa hp_sup s' = toKappa hi₀ (sf i₀)
      rw [hk1]
      -- Goal: toKappa hi₀ (sf i₀) = toKappa hp_sup s
      exact (toKappa_cast p (op (U i₀)) (op (iSup U)) hi₀ hp_sup carrier_eq (sf i₀)).symm
  · -- p ∉ iSup U: F(iSup U) has carrier PUnit, trivial
    haveI : Subsingleton ↑(F.obj (op (iSup U))) := by
      show Subsingleton ↑(skyscraperObj p (op (iSup U)))
      exact skyscraperObj_subsingleton' p _ hp
    haveI : Inhabited ↑(F.obj (op (iSup U))) := by
      show Inhabited ↑(skyscraperObj p (op (iSup U)))
      simp only [skyscraperObj, dif_neg hp]; exact ⟨PUnit.unit⟩
    refine ⟨default, fun i => ?_, fun s _ => Subsingleton.elim _ _⟩
    haveI : Subsingleton ↑(F.obj (op (U i))) := by
      show Subsingleton ↑(skyscraperObj p (op (U i)))
      exact skyscraperObj_subsingleton' p _ (fun h => hp (Opens.mem_iSup.mpr ⟨i, h⟩))
    exact Subsingleton.elim _ _

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

/-- The restriction map of the skyscraper presheaf preserves the κ(p) value.

    For the skyscraper presheaf F at point p, when p ∈ U' and p ∈ V',
    the presheaf restriction map F.map f' : F(U') → F(V') acts as identity
    on κ(p) (i.e., toKappa(F.map f' x) = toKappa(x)). -/
theorem res_toKappa (p : X) {U' V' : (Opens X.carrier)ᵒᵖ} (f' : U' ⟶ V')
    (hU' : (p : X.carrier) ∈ U'.unop) (hV' : (p : X.carrier) ∈ V'.unop)
    (x' : ↑((skyscraperPresheafOfModules p).presheaf.obj U')) :
    toKappa p V' hV' ((skyscraperPresheafOfModules p).presheaf.map f' x') =
    toKappa p U' hU' x' := by
  suffices key : ((skyscraperPresheafOfModules p).presheaf.map f').hom x' =
      fromKappa p V' hV' (toKappa p U' hU' x') by
    rw [show (skyscraperPresheafOfModules p).presheaf.map f' x' =
        ((skyscraperPresheafOfModules p).presheaf.map f').hom x' from rfl, key, toKappa_fromKappa]
  change (skyscraperMap p f').hom x' = fromKappa p V' hV' (toKappa p U' hU' x')
  simp only [skyscraperMap, dif_pos hV', fromKappa, toKappa]
  rfl

end RiemannSurfaces.SchemeTheoretic.SkyscraperConstruction
