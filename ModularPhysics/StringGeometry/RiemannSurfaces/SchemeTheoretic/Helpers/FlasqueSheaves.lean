/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Cohomology.CechComplex
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Flasque Sheaves

This file develops the theory of flasque (flabby) sheaves, which are
sheaves for which all restriction maps are surjective.

## Main Definitions

* `IsFlasque` - A sheaf is flasque if restriction maps are surjective

## Main Results

* `flasque_H1_zero` - Flasque sheaves have H¹ = 0

## Application

The main application is proving that skyscraper sheaves k_p are flasque,
which implies h¹(k_p) = 0 - a key ingredient in the Riemann-Roch proof.

## References

* Hartshorne, "Algebraic Geometry", Chapter III, Exercise 2.3
* Stacks Project, Tag 01EW (Flasque Sheaves)
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace RiemannSurfaces.SchemeTheoretic

variable {X : Scheme}

/-!
## Open Cover Lemmas
-/

/-- The union of all opens in a cover equals the whole space. -/
theorem OpenCover.iSup_eq_top (𝒰 : OpenCover X) : ⨆ i : 𝒰.I, 𝒰.U i = ⊤ := by
  ext x
  constructor
  · intro _; trivial
  · intro _; exact Opens.mem_iSup.mpr (𝒰.covers x)

/-- Restriction maps compose: restricting from W to V then to U is the same as
    restricting directly from W to U. Works at the element level. -/
theorem OModule.map_comp_apply {X : Scheme} (F : OModule X) {U V W : Opens X.carrier}
    (h₁ : U ≤ V) (h₂ : V ≤ W) (s : F.val.obj (Opposite.op W)) :
    F.val.map (homOfLE h₁).op (F.val.map (homOfLE h₂).op s) =
    F.val.map (homOfLE (le_trans h₁ h₂)).op s := by
  -- Work at the presheaf (AddCommGrpCat) level via .hom where composition is rfl:
  -- presheaf_map_apply_coe : (M.presheaf.map f).hom x = M.map f x := rfl
  -- AddCommGrpCat.hom_comp : (f ≫ g).hom = g.hom.comp f.hom := rfl
  -- Together: g.hom (f.hom x) = (f ≫ g).hom x (all rfl)
  show (F.val.presheaf.map (homOfLE h₂).op ≫ F.val.presheaf.map (homOfLE h₁).op).hom s =
    (F.val.presheaf.map (homOfLE (le_trans h₁ h₂)).op).hom s
  rw [← F.val.presheaf.map_comp]
  exact congrArg (fun m => (F.val.presheaf.map m).hom s) (Subsingleton.elim _ _)

/-- In a thin category (like Opens), any two parallel morphisms are equal,
    so the resulting restriction maps agree on elements. -/
theorem OModule.map_eq {X : Scheme} (F : OModule X) {U V : Opens X.carrier}
    (f g : (Opposite.op V) ⟶ (Opposite.op U)) (s : F.val.obj (Opposite.op V)) :
    F.val.map f s = F.val.map g s := by
  show (F.val.presheaf.map f).hom s = (F.val.presheaf.map g).hom s
  exact congrArg (fun m => (F.val.presheaf.map m).hom s) (Subsingleton.elim f g)

/-!
## Flasque Sheaves

A sheaf F is flasque (or flabby) if for every open U ⊆ V, the restriction
map F(V) → F(U) is surjective. Equivalently, every section over an open
set can be extended to the whole space.
-/

/-- A presheaf is flasque if all restriction maps are surjective.

    **Flasque sheaves have trivial Čech cohomology in positive degrees.**
    This is because any cocycle can be "extended" step by step to become
    a coboundary. -/
class IsFlasque (F : OModule X) : Prop where
  /-- Restriction maps are surjective. -/
  restriction_surjective : ∀ (U V : Opens X.carrier) (hUV : U ≤ V),
    Function.Surjective (F.val.map (homOfLE hUV).op)

/-- A flasque sheaf has sections that extend.
    Given a section s ∈ F(U), there exists a section t ∈ F(V) with t|_U = s. -/
theorem IsFlasque.extend_section (F : OModule X) [IsFlasque F]
    (U V : Opens X.carrier) (hUV : U ≤ V) (s : F.val.obj (Opposite.op U)) :
    ∃ t : F.val.obj (Opposite.op V), F.val.map (homOfLE hUV).op t = s :=
  IsFlasque.restriction_surjective U V hUV s

/-!
## Flasque Sheaves are Acyclic

The main theorem: flasque sheaves have trivial Čech cohomology in positive degrees.
-/

/-!
### Cocycle Condition

The cocycle condition in explicit form for 1-cocycles.
-/

/-- For a 1-cocycle, the differential vanishes at each 2-simplex. -/
theorem cocycle_at_simplex (F : OModule X) (𝒰 : OpenCover X)
    (c : CechCocycles F 𝒰 1) (σ : Fin 3 → 𝒰.I) :
    (cechDifferential F 𝒰 1 c.val) σ = 0 := by
  -- c is in CechCocycles = ker(d¹), so dc = 0
  have h : cechDifferential F 𝒰 1 c.val = 0 := c.property
  -- Evaluate at σ
  exact congrFun h σ

/-!
### Infrastructure for flasque_H1_zero

The proof of H¹ = 0 for flasque sheaves requires careful handling of
the cocycle condition and the flasque extension property.
-/

/-- The 1-cocycle condition in explicit form.

    For σ = (i₀, i₁, i₂), the cocycle condition says:
    c(i₁,i₂)|_{triple} - c(i₀,i₂)|_{triple} + c(i₀,i₁)|_{triple} = 0

    This is the key constraint that makes the construction work. -/
theorem cocycle_explicit (F : OModule X) (𝒰 : OpenCover X)
    (c : CechCocycles F 𝒰 1) (i₀ i₁ i₂ : 𝒰.I) :
    let σ : Fin 3 → 𝒰.I := ![i₀, i₁, i₂]
    -- The three face contributions sum to zero:
    -- c(i₁,i₂) - c(i₀,i₂) + c(i₀,i₁) = 0 (all restricted to triple)
    (cechDifferential F 𝒰 1 c.val) σ = 0 :=
  cocycle_at_simplex F 𝒰 c _

/-- For flasque sheaves, sections can be extended from any open to any larger open.
    This is the key property used in constructing the primitive. -/
theorem flasque_extend (F : OModule X) [IsFlasque F] (U V : Opens X.carrier) (hUV : U ≤ V)
    (s : F.val.obj (Opposite.op U)) :
    ∃ t : F.val.obj (Opposite.op V), F.val.map (homOfLE hUV).op t = s :=
  IsFlasque.restriction_surjective U V hUV s

/-- The d⁰ differential applied to a 0-cochain b at a 1-simplex σ = (i, j).

    (d⁰b)(i,j) = b(j)|_{U_i∩U_j} - b(i)|_{U_i∩U_j}

    This formula makes explicit what db = c means: for each pair (i,j),
    the difference of restrictions equals c(i,j). -/
theorem d0_explicit (F : OModule X) (𝒰 : OpenCover X)
    (b : CechCochain F 𝒰 0) (i j : 𝒰.I) :
    let σ : Fin 2 → 𝒰.I := ![i, j]
    (cechDifferential F 𝒰 0 b) σ =
      restrictionToFace F 𝒰 σ 0 (b (faceMap 0 σ)) -
      restrictionToFace F 𝒰 σ 1 (b (faceMap 1 σ)) := by
  simp only [cechDifferential]
  -- Sum over j : Fin 2 with alternating signs
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one]
  -- (-1)^1 = -1
  norm_num
  -- Now we have: term0 + (-term1) = term0 - term1
  rw [sub_eq_add_neg]

/-!
### Infrastructure for Transfinite Induction Proof

The proof of H¹ = 0 for flasque sheaves uses:
1. A well-ordering on the index set 𝒰.I
2. Transfinite induction to construct the primitive b
3. Sheaf gluing to combine compatible sections at each step
4. Flasqueness to extend sections to larger opens
5. The cocycle condition for compatibility verification
-/

/-- The cocycle condition at a 2-simplex σ implies the face sections are compatible.
    Specifically: the restriction of c(face₁) equals the restriction of c(face₀)
    on the intersection σ. This is the key fact for proving H⁰ = Γ. -/
theorem cocycle_compat_on_intersection (F : OModule X) (𝒰 : OpenCover X)
    (c : CechCochain F 𝒰 0) (hc : cechDifferential F 𝒰 0 c = 0)
    (σ : Fin 2 → 𝒰.I) :
    F.val.map (homOfLE (intersection_face_le 𝒰 σ 1)).op (c (faceMap 1 σ)) =
    F.val.map (homOfLE (intersection_face_le 𝒰 σ 0)).op (c (faceMap 0 σ)) := by
  have hcoc := congrFun hc σ
  simp only [cechDifferential, Pi.zero_apply] at hcoc
  rw [Fin.sum_univ_two] at hcoc
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul,
    restrictionToFace] at hcoc
  -- hcoc : face0 + (-face1) = 0, need face1 = face0
  have h := hcoc
  rw [← sub_eq_add_neg] at h
  exact (sub_eq_zero.mp h).symm

/-- For any section s ∈ F(V), restriction via any two morphisms from op V to op U
    are equal (thin category). This packages map_eq to work with hypotheses. -/
theorem OModule.map_eq_of_le {X : Scheme} (F : OModule X) {U V : Opens X.carrier}
    (h₁ h₂ : U ≤ V) (s : F.val.obj (Opposite.op V)) :
    F.val.map (homOfLE h₁).op s = F.val.map (homOfLE h₂).op s :=
  OModule.map_eq F _ _ s

/-- The intersection of a 1-simplex (single index) is just the single open set.
    This identifies F(𝒰.intersection σ) with F(𝒰.U (σ 0)) for σ : Fin 1 → 𝒰.I. -/
theorem intersection_eq_single (𝒰 : OpenCover X) (σ : Fin 1 → 𝒰.I) :
    𝒰.intersection σ = 𝒰.U (σ 0) := by
  unfold OpenCover.intersection
  simp only [show (1 : ℕ) ≠ 0 from one_ne_zero, ↓reduceDIte]
  have h : (fun j : Fin 1 => 𝒰.U (σ j)) = fun _ => 𝒰.U (σ 0) := by
    funext j; exact congr_arg (𝒰.U ∘ σ) (Subsingleton.elim j 0)
  rw [h, iInf_const]

/-- Sheaf gluing for O_X-modules: compatible sections over an open cover can be glued.

    This is the gluing axiom for sheaves: given sections s_i ∈ F(V_i) that agree
    on overlaps (s_i|_{V_i ∩ V_j} = s_j|_{V_i ∩ V_j}), there exists a section
    s ∈ F(⋃ V_i) with s|_{V_i} = s_i.

    F is a SheafOfModules, so this follows from F.isSheaf which encodes the
    sheaf condition. In Mathlib, the concrete gluing axiom is
    `Sheaf.existsUnique_gluing'` in `Topology.Sheaves.SheafCondition.UniqueGluing`. -/
theorem OModule.glue_sections {X : Scheme} (F : OModule X)
    {ι : Type*} (V : ι → Opens X.carrier)
    (sf : ∀ i : ι, F.val.obj (Opposite.op (V i)))
    (compat : ∀ i j : ι,
      F.val.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (sf i) =
      F.val.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (sf j)) :
    ∃ s : F.val.obj (Opposite.op (⨆ i, V i)),
      ∀ i : ι, F.val.map (homOfLE (le_iSup V i)).op s = sf i := by
  -- Construct the TopCat.Sheaf of abelian groups from F
  let F_sheaf : TopCat.Sheaf Ab X.carrier := ⟨F.val.presheaf, F.isSheaf⟩
  -- Bridge the compatibility condition to Mathlib's IsCompatible form
  -- Note: infLELeft = homOfLE inf_le_left by LE.le.hom = homOfLE (definitional)
  -- and presheaf_map_apply_coe is rfl, so F.val.presheaf.map and F.val.map agree on elements
  have hcompat : TopCat.Presheaf.IsCompatible F.val.presheaf V sf := by
    intro i j
    exact compat i j
  -- Apply the sheaf gluing theorem (U = V family, result at iSup V)
  -- leSupr V i = homOfLE (le_iSup V i) definitionally
  obtain ⟨s, hs, _⟩ := F_sheaf.existsUnique_gluing V sf hcompat
  exact ⟨s, hs⟩

/-- Presheaf maps compose: f.hom (g.hom x) = (g ≫ f).hom x at the AddCommGrpCat level. -/
theorem OModule.presheaf_comp_apply {X : Scheme} (F : OModule X)
    {A B C : (Opens X.carrier)ᵒᵖ} (f : A ⟶ B) (g : B ⟶ C)
    (s : F.val.obj A) :
    (F.val.presheaf.map g).hom ((F.val.presheaf.map f).hom s) =
    (F.val.presheaf.map (f ≫ g)).hom s := by
  show ((F.val.presheaf.map f ≫ F.val.presheaf.map g)).hom s = _
  rw [← F.val.presheaf.map_comp]

/-- Presheaf map equality: any two morphisms with same source and target give equal maps. -/
theorem OModule.presheaf_map_eq {X : Scheme} (F : OModule X)
    {A B : (Opens X.carrier)ᵒᵖ} (f g : A ⟶ B)
    (s : F.val.obj A) :
    (F.val.presheaf.map f).hom s = (F.val.presheaf.map g).hom s :=
  congrArg (fun m => (F.val.presheaf.map m).hom s) (Subsingleton.elim f g)

/-- Composed presheaf maps can be identified with any single morphism by thin category. -/
theorem OModule.presheaf_comp_eq {X : Scheme} (F : OModule X)
    {A B C : (Opens X.carrier)ᵒᵖ} (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C)
    (s : F.val.obj A) :
    (F.val.presheaf.map g).hom ((F.val.presheaf.map f).hom s) =
    (F.val.presheaf.map h).hom s := by
  rw [OModule.presheaf_comp_apply]; exact OModule.presheaf_map_eq F _ h s

/-- Glue sections and get result over ⊤ when ⨆ V = ⊤. -/
theorem OModule.glue_sections_top {X : Scheme} (F : OModule X)
    {ι : Type*} (V : ι → Opens X.carrier) (hV : ⨆ i, V i = ⊤)
    (sf : ∀ i : ι, F.val.obj (Opposite.op (V i)))
    (compat : ∀ i j : ι,
      F.val.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (sf i) =
      F.val.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (sf j)) :
    ∃ s : F.val.obj (Opposite.op ⊤),
      ∀ i : ι, F.val.map (homOfLE le_top).op s = sf i := by
  obtain ⟨s₀, hs₀⟩ := OModule.glue_sections F V sf compat
  refine ⟨F.val.map (eqToHom (congrArg Opposite.op hV)) s₀, fun i => ?_⟩
  show (F.val.presheaf.map (eqToHom (congrArg Opposite.op hV)) ≫
       F.val.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op).hom s₀ = sf i
  rw [← F.val.presheaf.map_comp,
      show (eqToHom (congrArg Opposite.op hV) ≫ (homOfLE (le_top : V i ≤ ⊤)).op) =
          (homOfLE (le_iSup V i)).op from Subsingleton.elim _ _]
  exact hs₀ i

/-!
### Clean Restriction Maps

`OModule.res` provides restriction maps that return elements in `F.val.obj (op U)` directly,
avoiding the `ModuleCat.restrictScalars` wrapping that makes arithmetic difficult.
-/

/-- Restriction of a section using presheaf-level maps.
    Returns F.val.obj (op U) directly, avoiding ModuleCat.restrictScalars wrapping. -/
noncomputable def OModule.res {X : Scheme} (F : OModule X) {U V : Opens X.carrier} (h : U ≤ V)
    (s : F.val.obj (Opposite.op V)) : F.val.obj (Opposite.op U) :=
  (F.val.presheaf.map (homOfLE h).op).hom s

/-- res agrees with F.val.map on elements. -/
theorem OModule.res_eq_map {X : Scheme} (F : OModule X) {U V : Opens X.carrier} (h : U ≤ V)
    (s : F.val.obj (Opposite.op V)) :
    F.res h s = F.val.map (homOfLE h).op s := rfl

/-- Composition of res. -/
theorem OModule.res_comp {X : Scheme} (F : OModule X) {U V W : Opens X.carrier}
    (h₁ : U ≤ V) (h₂ : V ≤ W) (s : F.val.obj (Opposite.op W)) :
    F.res h₁ (F.res h₂ s) = F.res (le_trans h₁ h₂) s :=
  OModule.presheaf_comp_eq F _ _ _ s

/-- res is independent of the proof of inclusion. -/
theorem OModule.res_irrel {X : Scheme} (F : OModule X) {U V : Opens X.carrier}
    (h₁ h₂ : U ≤ V) (s : F.val.obj (Opposite.op V)) :
    F.res h₁ s = F.res h₂ s :=
  OModule.presheaf_map_eq F _ _ s

/-- res preserves addition. -/
theorem OModule.res_add {X : Scheme} (F : OModule X) {U V : Opens X.carrier} (h : U ≤ V)
    (s t : F.val.obj (Opposite.op V)) :
    F.res h (s + t) = F.res h s + F.res h t :=
  map_add _ s t

/-- res preserves subtraction. -/
theorem OModule.res_sub {X : Scheme} (F : OModule X) {U V : Opens X.carrier} (h : U ≤ V)
    (s t : F.val.obj (Opposite.op V)) :
    F.res h (s - t) = F.res h s - F.res h t :=
  map_sub _ s t

/-!
### Infrastructure for flasque H¹ = 0

The proof constructs a primitive by transfinite induction on a well-ordered index set.
-/

/-- The intersection of a 2-simplex ![i,j] equals U_i ⊓ U_j. -/
theorem intersection_pair (𝒰 : OpenCover X) (i j : 𝒰.I) :
    𝒰.intersection ![i, j] = 𝒰.U i ⊓ 𝒰.U j := by
  unfold OpenCover.intersection
  simp only [show (1 + 1 : ℕ) ≠ 0 from by omega, ↓reduceDIte]
  apply le_antisymm
  · exact le_inf (iInf_le _ 0) (iInf_le _ 1)
  · apply le_iInf; intro k; fin_cases k
    · exact inf_le_left
    · exact inf_le_right

/-- Transport a cocycle value from 𝒰.intersection ![i,j] to F(U_i ⊓ U_j). -/
noncomputable def cocycleAtInf {X : Scheme} (F : OModule X) (𝒰 : OpenCover X)
    (c : CechCocycles F 𝒰 1) (i j : 𝒰.I) :
    F.val.obj (Opposite.op (𝒰.U i ⊓ 𝒰.U j)) :=
  F.val.map (homOfLE (le_of_eq (intersection_pair 𝒰 i j).symm)).op (c.val ![i, j])

/-- The 1-cocycle condition in terms of ⊓ and OModule.res.
    For any i₀, i₁, i₂: c(i₁,i₂) - c(i₀,i₂) + c(i₀,i₁) = 0
    all restricted to the triple intersection U_{i₀} ⊓ U_{i₁} ⊓ U_{i₂}. -/
theorem cocycle_condition_inf {X : Scheme} (F : OModule X) (𝒰 : OpenCover X)
    (c : CechCocycles F 𝒰 1) (i₀ i₁ i₂ : 𝒰.I) :
    let T := 𝒰.U i₀ ⊓ 𝒰.U i₁ ⊓ 𝒰.U i₂
    F.res (show T ≤ 𝒰.U i₁ ⊓ 𝒰.U i₂ from
      le_inf (inf_le_left.trans inf_le_right) inf_le_right) (cocycleAtInf F 𝒰 c i₁ i₂) -
    F.res (show T ≤ 𝒰.U i₀ ⊓ 𝒰.U i₂ from
      le_inf (inf_le_left.trans inf_le_left) inf_le_right) (cocycleAtInf F 𝒰 c i₀ i₂) +
    F.res (show T ≤ 𝒰.U i₀ ⊓ 𝒰.U i₁ from inf_le_left) (cocycleAtInf F 𝒰 c i₀ i₁) = 0 := by
  intro T
  -- Helper: restriction of c.val is independent of path (dependent subst + thin category)
  have res_eq : ∀ (f₁ f₂ : Fin 2 → 𝒰.I) (hf : f₁ = f₂)
      (h₁ : T ≤ 𝒰.intersection f₁) (h₂ : T ≤ 𝒰.intersection f₂),
      (F.val.presheaf.map (homOfLE h₁).op).hom (c.val f₁) =
      (F.val.presheaf.map (homOfLE h₂).op).hom (c.val f₂) := by
    intro f₁ f₂ hf h₁ h₂; subst hf; exact OModule.presheaf_map_eq F _ _ _
  -- Face map evaluations
  have hf0 : faceMap (0 : Fin 3) (![i₀, i₁, i₂] : Fin 3 → 𝒰.I) = ![i₁, i₂] := by
    funext k; fin_cases k <;> simp [faceMap]
  have hf1 : faceMap (1 : Fin 3) (![i₀, i₁, i₂] : Fin 3 → 𝒰.I) = ![i₀, i₂] := by
    funext k; fin_cases k <;> simp [faceMap]
  have hf2 : faceMap (2 : Fin 3) (![i₀, i₁, i₂] : Fin 3 → 𝒰.I) = ![i₀, i₁] := by
    funext k; fin_cases k <;> simp [faceMap]
  -- T ≤ intersection σ
  have hT : T ≤ 𝒰.intersection ![i₀, i₁, i₂] := by
    simp only [T, OpenCover.intersection, show (1 + 1 + 1 : ℕ) ≠ 0 from by omega, ↓reduceDIte]
    exact le_iInf fun j => by fin_cases j
      <;> [exact inf_le_left.trans inf_le_left;
           exact inf_le_left.trans inf_le_right;
           exact inf_le_right]
  -- Helper: res(cocycleAtInf i j) = single presheaf.map application from intersection ![i,j] to T
  have term_eq : ∀ (i j : 𝒰.I) (hle : T ≤ 𝒰.U i ⊓ 𝒰.U j),
      F.res hle (cocycleAtInf F 𝒰 c i j) =
      (F.val.presheaf.map
        (homOfLE (hle.trans (le_of_eq (intersection_pair 𝒰 i j).symm))).op).hom (c.val ![i, j]) := by
    intro i j hle
    simp only [cocycleAtInf, OModule.res]
    exact OModule.presheaf_comp_eq F _ _ _ _
  -- Helper: dependent subst for face map equality
  have face_subst : ∀ (f₁ f₂ : Fin 2 → 𝒰.I) (hf : f₁ = f₂)
      (h₁ : T ≤ 𝒰.intersection f₁) (h₂ : T ≤ 𝒰.intersection f₂),
      (F.val.presheaf.map (homOfLE h₁).op).hom (c.val f₁) =
      (F.val.presheaf.map (homOfLE h₂).op).hom (c.val f₂) := by
    intro f₁ f₂ hf h₁ h₂; subst hf; exact OModule.presheaf_map_eq F _ _ _
  -- Rewrite each goal term to single presheaf.map form
  rw [term_eq i₁ i₂ _, term_eq i₀ i₂ _, term_eq i₀ i₁ _]
  -- Get the cocycle condition restricted to T
  have hcoc := cocycle_at_simplex F 𝒰 c ![i₀, i₁, i₂]
  simp only [cechDifferential, restrictionToFace] at hcoc
  rw [Fin.sum_univ_three] at hcoc
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul,
    show (2 : Fin 3).val = 2 from rfl, show (-1 : ℤ) ^ 2 = 1 from by norm_num, one_smul] at hcoc
  -- Restrict to T
  have h0 := congr_arg (fun x => (F.val.presheaf.map (homOfLE hT).op).hom x) hcoc
  simp only [map_zero, map_add, map_neg] at h0
  -- Each term in h0 has form: (presheaf.map hT).hom (F.val.map (face_le).op (c.val (faceMap k σ)))
  -- We need to compose and match with our single-step form
  -- Compose using presheaf_comp_eq
  have h0' : ∀ (k : Fin 3),
      (F.val.presheaf.map (homOfLE hT).op).hom
        (F.val.map (homOfLE (intersection_face_le 𝒰 ![i₀, i₁, i₂] k)).op
          (c.val (faceMap k ![i₀, i₁, i₂]))) =
      (F.val.presheaf.map (homOfLE (hT.trans (intersection_face_le 𝒰 ![i₀, i₁, i₂] k))).op).hom
        (c.val (faceMap k ![i₀, i₁, i₂])) := by
    intro k
    show (F.val.presheaf.map (homOfLE hT).op).hom
        ((F.val.presheaf.map (homOfLE (intersection_face_le 𝒰 ![i₀, i₁, i₂] k)).op).hom
          (c.val (faceMap k ![i₀, i₁, i₂]))) = _
    exact OModule.presheaf_comp_eq F _ _ _ _
  -- Rewrite h0 using compositions
  rw [h0' 0, h0' 1, h0' 2] at h0
  -- Now match: goal terms use ![i₁,i₂] etc, h0 uses faceMap k σ
  -- Use face_subst to bridge
  rw [sub_eq_add_neg]
  convert h0 using 3
  · exact congr_arg Neg.neg (face_subst _ _ hf1.symm _ _)
  · exact face_subst _ _ hf2.symm _ _

/-- The cocycle condition restricted to any open W ≤ all pairwise intersections.
    This packages `cocycle_condition_inf` for use on arbitrary subsets. -/
private theorem cocycle_on_open {X : Scheme} (F : OModule X) (𝒰 : OpenCover X)
    (c : CechCocycles F 𝒰 1) (i₀ i₁ i₂ : 𝒰.I) {W : Opens X.carrier}
    (h₁₂ : W ≤ 𝒰.U i₁ ⊓ 𝒰.U i₂) (h₀₂ : W ≤ 𝒰.U i₀ ⊓ 𝒰.U i₂)
    (h₀₁ : W ≤ 𝒰.U i₀ ⊓ 𝒰.U i₁) :
    F.res h₁₂ (cocycleAtInf F 𝒰 c i₁ i₂) -
    F.res h₀₂ (cocycleAtInf F 𝒰 c i₀ i₂) +
    F.res h₀₁ (cocycleAtInf F 𝒰 c i₀ i₁) = 0 := by
  have hWT : W ≤ 𝒰.U i₀ ⊓ 𝒰.U i₁ ⊓ 𝒰.U i₂ :=
    le_inf (le_inf (h₀₁.trans inf_le_left) (h₁₂.trans inf_le_left)) (h₁₂.trans inf_le_right)
  -- Factor each term through T via res_comp (proof irrelevance closes the goal)
  have rw₁ : F.res h₁₂ (cocycleAtInf F 𝒰 c i₁ i₂) =
      F.res hWT (F.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        (cocycleAtInf F 𝒰 c i₁ i₂)) := by rw [OModule.res_comp]
  have rw₂ : F.res h₀₂ (cocycleAtInf F 𝒰 c i₀ i₂) =
      F.res hWT (F.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (cocycleAtInf F 𝒰 c i₀ i₂)) := by rw [OModule.res_comp]
  have rw₃ : F.res h₀₁ (cocycleAtInf F 𝒰 c i₀ i₁) =
      F.res hWT (F.res inf_le_left (cocycleAtInf F 𝒰 c i₀ i₁)) := by rw [OModule.res_comp]
  rw [rw₁, rw₂, rw₃, ← OModule.res_sub, ← OModule.res_add]
  -- Inner expression matches cocycle_condition_inf (by proof irrelevance of ≤ proofs)
  exact (congr_arg (F.res hWT) (cocycle_condition_inf F 𝒰 c i₀ i₁ i₂)).trans (map_zero _)

/-- Cocycle antisymmetry: c(i,j) + c(j,i) = 0 when restricted to a common open. -/
private theorem cocycle_antisym {X : Scheme} (F : OModule X) (𝒰 : OpenCover X)
    (c : CechCocycles F 𝒰 1) (i j : 𝒰.I) {W : Opens X.carrier}
    (h_ij : W ≤ 𝒰.U i ⊓ 𝒰.U j) (h_ji : W ≤ 𝒰.U j ⊓ 𝒰.U i) :
    F.res h_ij (cocycleAtInf F 𝒰 c i j) +
    F.res h_ji (cocycleAtInf F 𝒰 c j i) = 0 := by
  have hW_ii : W ≤ 𝒰.U i ⊓ 𝒰.U i := le_inf (h_ij.trans inf_le_left) (h_ij.trans inf_le_left)
  -- From cocycle_on_open i i j: c(i,j) - c(i,j) + c(i,i) = 0
  have hdiag := cocycle_on_open F 𝒰 c i i j h_ij h_ij hW_ii
  -- sub_self gives c(i,i) = 0
  have hii_zero : F.res hW_ii (cocycleAtInf F 𝒰 c i i) = 0 := by
    have hsub : F.res h_ij (cocycleAtInf F 𝒰 c i j) - F.res h_ij (cocycleAtInf F 𝒰 c i j) = 0 :=
      sub_self _
    rwa [hsub, zero_add] at hdiag
  -- From cocycle_on_open i j i: c(j,i) - c(i,i) + c(i,j) = 0
  have hanti := cocycle_on_open F 𝒰 c i j i h_ji hW_ii h_ij
  -- c(j,i) - 0 + c(i,j) = c(j,i) + c(i,j) = 0
  rw [hii_zero, sub_zero] at hanti
  rwa [add_comm]

/-- Flasque sheaves have H¹ = 0.

    **Proof by transfinite induction (Godement/Hartshorne):**

    Well-order 𝒰.I. Construct b(α) ∈ F(U_α) by well-founded recursion.

    At step α, given b(β) for all β < α satisfying the IH:
      ∀ β < α, b(α)|_{U_β∩U_α} - b(β)|_{U_β∩U_α} = c(β,α)

    For each β < α, define s_β := c(β,α) + b(β)|_{U_β∩U_α} ∈ F(U_β ∩ U_α).
    Show s_β are compatible by cocycle condition + IH.
    Glue and extend by flasqueness to get b(α).

    Verification: d⁰b = c follows from the IH. -/
theorem flasque_H1_zero (F : OModule X) [IsFlasque F] (𝒰 : OpenCover X) :
    ∀ c : CechCocycles F 𝒰 1, ∃ b : CechCochain F 𝒰 0,
      cechDifferential F 𝒰 0 b = c.val := by
  intro c
  have hcoc : cechDifferential F 𝒰 1 c.val = 0 := c.property
  classical
  by_cases hne : Nonempty 𝒰.I
  swap
  · exact ⟨fun σ => absurd ⟨σ 0⟩ hne, funext fun σ => absurd ⟨σ 0⟩ hne⟩
  · -- Step 1: Well-order the index set
    letI : LinearOrder 𝒰.I := WellOrderingRel.isWellOrder.linearOrder
    -- Step 2: Build step - given b(β) for β < α with IH, construct b(α)
    -- Uses OModule.res to avoid restrictScalars type issues
    have build : ∀ α : 𝒰.I,
        (prev : ∀ β, β < α → F.val.obj (Opposite.op (𝒰.U β))) →
        (prev_ih : ∀ (β₁ β₂ : 𝒰.I) (h₁ : β₁ < β₂) (h₂ : β₂ < α),
          F.res (inf_le_right : 𝒰.U β₁ ⊓ 𝒰.U β₂ ≤ 𝒰.U β₂) (prev β₂ h₂) -
          F.res (inf_le_left : 𝒰.U β₁ ⊓ 𝒰.U β₂ ≤ 𝒰.U β₁) (prev β₁ (lt_trans h₁ h₂)) =
          cocycleAtInf F 𝒰 c β₁ β₂) →
        ∃ b_α : F.val.obj (Opposite.op (𝒰.U α)),
          ∀ β (hβ : β < α),
            F.res (inf_le_right : 𝒰.U β ⊓ 𝒰.U α ≤ 𝒰.U α) b_α -
            F.res (inf_le_left : 𝒰.U β ⊓ 𝒰.U α ≤ 𝒰.U β) (prev β hβ) =
            cocycleAtInf F 𝒰 c β α := by
      intro α prev prev_ih
      -- For each β < α, define s_β = c(β,α) + b(β)|_{U_β∩U_α}
      let s : (β : 𝒰.I) → β < α → F.val.obj (Opposite.op (𝒰.U β ⊓ 𝒰.U α)) :=
        fun β hβ => cocycleAtInf F 𝒰 c β α + F.res inf_le_left (prev β hβ)
      -- Compatible sections for gluing
      let V : {β : 𝒰.I // β < α} → Opens X.carrier := fun ⟨β, _⟩ => 𝒰.U β ⊓ 𝒰.U α
      let sf : ∀ p : {β // β < α}, F.val.obj (Opposite.op (V p)) :=
        fun ⟨β, hβ⟩ => s β hβ
      -- Compatibility: s_{β₁}|_overlap = s_{β₂}|_overlap
      have compat : ∀ p q : {β // β < α},
          F.val.map (homOfLE (inf_le_left : V p ⊓ V q ≤ V p)).op (sf p) =
          F.val.map (homOfLE (inf_le_right : V p ⊓ V q ≤ V q)).op (sf q) := by
        intro ⟨β₁, hβ₁⟩ ⟨β₂, hβ₂⟩
        show F.res inf_le_left (s β₁ hβ₁) = F.res inf_le_right (s β₂ hβ₂)
        simp only [s]
        rw [OModule.res_add, OModule.res_add, OModule.res_comp, OModule.res_comp]
        -- Goal: res(c(β₁,α)) + res(prev β₁) = res(c(β₂,α)) + res(prev β₂)
        -- (all restricted from their sources to W = V(β₁) ⊓ V(β₂))
        -- ≤ proofs for cocycle and IH restrictions
        have hW21 : (𝒰.U β₁ ⊓ 𝒰.U α) ⊓ (𝒰.U β₂ ⊓ 𝒰.U α) ≤ 𝒰.U β₂ ⊓ 𝒰.U β₁ :=
          le_inf (inf_le_right.trans inf_le_left) (inf_le_left.trans inf_le_left)
        have hW12 : (𝒰.U β₁ ⊓ 𝒰.U α) ⊓ (𝒰.U β₂ ⊓ 𝒰.U α) ≤ 𝒰.U β₁ ⊓ 𝒰.U β₂ :=
          le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
        -- Cocycle condition: res(c(β₁,α)) - res(c(β₂,α)) + res(c(β₂,β₁)) = 0
        have h_coc := cocycle_on_open F 𝒰 c β₂ β₁ α inf_le_left inf_le_right hW21
        -- Handle prev part by case split on ordering of β₁, β₂
        by_cases hlt : β₂ < β₁
        · -- Case β₂ < β₁: IH gives res(prev β₁) - res(prev β₂) = c(β₂,β₁)
          have hih := congr_arg (F.res hW21) (prev_ih β₂ β₁ hlt hβ₁)
          rw [OModule.res_sub, OModule.res_comp, OModule.res_comp] at hih
          -- hih: res(prev β₁) - res(prev β₂) = res(c(β₂,β₁)) on W
          -- Substitute into h_coc: a - c + (b - d) = 0
          rw [← hih] at h_coc
          -- Goal: a + b = c + d follows from a - c + (b - d) = 0
          rw [← sub_eq_zero]; convert h_coc using 1; abel
        · by_cases heq : β₁ = β₂
          · subst heq; rfl
          · -- Case β₁ < β₂
            have hlt' : β₁ < β₂ := lt_of_le_of_ne (not_lt.mp hlt) heq
            have hih := congr_arg (F.res hW12) (prev_ih β₁ β₂ hlt' hβ₂)
            rw [OModule.res_sub, OModule.res_comp, OModule.res_comp] at hih
            -- hih: res(prev β₂) - res(prev β₁) = res(c(β₁,β₂)) on W
            have hanti := cocycle_antisym F 𝒰 c β₂ β₁ hW21 hW12
            -- hanti: res(c(β₂,β₁)) + res(c(β₁,β₂)) = 0
            -- Use antisymmetry to rewrite c(β₂,β₁) as -c(β₁,β₂), then IH
            have he := eq_neg_of_add_eq_zero_left hanti
            rw [he, ← hih] at h_coc
            -- h_coc: a - c + (-(d - b)) = 0, goal: a + b = c + d
            rw [← sub_eq_zero]; convert h_coc using 1; abel
      -- Glue compatible sections
      obtain ⟨s_glued, hs_glued⟩ := OModule.glue_sections F V sf compat
      have hV_le : ⨆ p, V p ≤ 𝒰.U α := iSup_le fun ⟨_, _⟩ => inf_le_right
      -- Extend by flasqueness
      obtain ⟨b_α, hb_α⟩ := IsFlasque.extend_section F (⨆ p, V p) (𝒰.U α) hV_le s_glued
      -- Verify IH: b_α|_{U_β∩U_α} - b(β)|_{U_β∩U_α} = c(β,α)
      refine ⟨b_α, fun β hβ => ?_⟩
      -- Chain: b_α →[hV_le]→ s_glued →[le_iSup]→ sf = s β hβ
      have h_chain : F.res (inf_le_right : 𝒰.U β ⊓ 𝒰.U α ≤ 𝒰.U α) b_α = s β hβ := by
        calc F.res inf_le_right b_α
            = F.res (le_trans (le_iSup V ⟨β, hβ⟩) hV_le) b_α := OModule.res_irrel F _ _ _
          _ = F.res (le_iSup V ⟨β, hβ⟩) (F.res hV_le b_α) := (OModule.res_comp F _ _ _).symm
          _ = F.res (le_iSup V ⟨β, hβ⟩) s_glued := by congr 1
          _ = sf ⟨β, hβ⟩ := hs_glued ⟨β, hβ⟩
      -- s β hβ = cocycleAtInf + res(prev β), so (cocycleAtInf + x) - x = cocycleAtInf
      rw [h_chain]; show cocycleAtInf F 𝒰 c β α + _ - _ = _; abel
    -- Step 3: Assemble via well-founded recursion
    -- Use dite to provide actual proof in true branch; false branch (never reached) returns 0.
    -- After fix_eq, dif_pos prev_ih simplifies to the true branch.
    haveI : IsWellFounded 𝒰.I (· < ·) := ⟨WellOrderingRel.isWellOrder.wf⟩
    let wf : WellFounded ((· < ·) : 𝒰.I → 𝒰.I → Prop) := IsWellFounded.wf
    let b_raw : ∀ α : 𝒰.I, F.val.obj (Opposite.op (𝒰.U α)) :=
      wf.fix fun α rec =>
        if h : (∀ β₁ β₂ (h₁ : β₁ < β₂) (h₂ : β₂ < α),
          F.res (inf_le_right : 𝒰.U β₁ ⊓ 𝒰.U β₂ ≤ 𝒰.U β₂) (rec β₂ h₂) -
          F.res (inf_le_left : 𝒰.U β₁ ⊓ 𝒰.U β₂ ≤ 𝒰.U β₁) (rec β₁ (lt_trans h₁ h₂)) =
          cocycleAtInf F 𝒰 c β₁ β₂) then
          (build α rec h).choose
        else
          0
    -- Prove the IH for b_raw using choose_spec + proof irrelevance
    have b_raw_ih : ∀ (α β : 𝒰.I) (hβ : β < α),
        F.res inf_le_right (b_raw α) - F.res inf_le_left (b_raw β) =
        cocycleAtInf F 𝒰 c β α := by
      intro α; induction α using wf.induction with
      | _ α ih_ind =>
        intro β hβ
        have prev_ih : ∀ β₁ β₂ (h₁ : β₁ < β₂) (h₂ : β₂ < α),
            F.res inf_le_right (b_raw β₂) - F.res inf_le_left (b_raw β₁) =
            cocycleAtInf F 𝒰 c β₁ β₂ :=
          fun β₁ β₂ h₁ h₂ => ih_ind β₂ h₂ β₁ h₁
        -- Unfold b_raw α via WellFounded.fix_eq
        have h_unfold : b_raw α = (build α (fun γ hγ => b_raw γ) prev_ih).choose := by
          show wf.fix _ α = _; rw [WellFounded.fix_eq]; exact dif_pos prev_ih
        rw [h_unfold]
        exact (build α (fun γ hγ => b_raw γ) prev_ih).choose_spec β hβ
    -- Step 4: Construct the 0-cochain and verify d⁰b = c
    -- Helper: restriction along le_refl is identity
    have res_id : ∀ {U : Opens X.carrier} (x : F.val.obj (Opposite.op U)),
        F.res (le_refl U) x = x := by
      intro U x
      show (F.val.presheaf.map (homOfLE (le_refl U)).op).hom x = x
      rw [show (homOfLE (le_refl U)).op = 𝟙 _ from Subsingleton.elim _ _, F.val.presheaf.map_id]
      rfl
    -- Helper: res preserves negation
    have res_neg : ∀ {U V : Opens X.carrier} (h : U ≤ V) (x : F.val.obj (Opposite.op V)),
        F.res h (-x) = -F.res h x := fun h x => map_neg _ x
    -- Helper: cocycleAtInf c i i = 0 (diagonal)
    have cocycle_diag : ∀ i : 𝒰.I, cocycleAtInf F 𝒰 c i i = 0 := by
      intro i
      have h := cocycle_on_open F 𝒰 c i i i (le_refl _) (le_refl _) (le_refl _)
      rw [sub_self, zero_add] at h
      -- h : F.res _ (cocycleAtInf c i i) = 0  (F.res with le_refl-like proof)
      rwa [OModule.res_irrel F _ (le_refl _), res_id] at h
    -- Helper: cocycleAtInf_inv recovers c.val from cocycleAtInf
    have cocycleAtInf_inv : ∀ (i j : 𝒰.I),
        F.res (le_of_eq (intersection_pair 𝒰 i j)) (cocycleAtInf F 𝒰 c i j) =
        c.val ![i, j] := by
      intro i j
      -- cocycleAtInf = F.res (le_of_eq (intersection_pair).symm) (c.val) by res_eq_map (rfl)
      show F.res _ (F.res (le_of_eq (intersection_pair 𝒰 i j).symm) (c.val ![i, j])) = _
      rw [OModule.res_comp, OModule.res_irrel F _ (le_refl _), res_id]
    -- Extend b_raw_ih to all pairs using cocycle antisymmetry
    have b_raw_ih_general : ∀ (i j : 𝒰.I),
        F.res inf_le_right (b_raw j) -
        F.res (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U i) (b_raw i) =
        cocycleAtInf F 𝒰 c i j := by
      intro i j
      -- Trichotomy from LinearOrder (in scope from letI above)
      rcases lt_trichotomy i j with h_lt | h_eq | h_gt
      · -- i < j: direct from b_raw_ih
        exact b_raw_ih j i h_lt
      · -- i = j: both sides are 0
        subst h_eq; rw [cocycle_diag, OModule.res_irrel F inf_le_right inf_le_left, sub_self]
      · -- j < i: negate b_raw_ih, transport via inf_comm, use antisymmetry
        have h_ji := b_raw_ih i j h_gt
        -- h_ji : F.res inf_le_right (b_raw i) - F.res inf_le_left (b_raw j) = cocycleAtInf c j i
        -- in F(U j ⊓ U i)
        -- Negate: b_raw j - b_raw i = -cocycleAtInf c j i
        have h_neg : F.res inf_le_left (b_raw j) -
            F.res (inf_le_right : 𝒰.U j ⊓ 𝒰.U i ≤ 𝒰.U i) (b_raw i) =
            -cocycleAtInf F 𝒰 c j i := by
          rw [← neg_eq_iff_eq_neg, neg_sub]; exact h_ji
        -- Transport to F(U i ⊓ U j) via inf_comm
        have h_tr := congr_arg
          (F.res (le_of_eq (@inf_comm _ _ (𝒰.U i) (𝒰.U j)))) h_neg
        rw [OModule.res_sub, res_neg, OModule.res_comp, OModule.res_comp] at h_tr
        -- Unify restriction proofs
        rw [OModule.res_irrel F _ inf_le_right,
            OModule.res_irrel F _ (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U i)] at h_tr
        -- h_tr: res inf_le_right (b_raw j) - res inf_le_left (b_raw i) =
        --   -F.res (inf_comm) (cocycleAtInf c j i)
        -- Antisymmetry: cocycleAtInf c i j + F.res (inf_comm) (cocycleAtInf c j i) = 0
        have h_anti := cocycle_antisym F 𝒰 c i j
          (le_refl _) (le_of_eq (@inf_comm _ _ (𝒰.U i) (𝒰.U j)))
        rw [OModule.res_irrel F _ (le_refl _), res_id] at h_anti
        -- So cocycleAtInf c i j = -F.res (inf_comm) (cocycleAtInf c j i)
        rw [h_tr]; exact (add_eq_zero_iff_eq_neg.mp h_anti).symm
    -- Define the 0-cochain
    let b : CechCochain F 𝒰 0 := fun σ =>
      F.res (le_of_eq (intersection_eq_single 𝒰 σ)) (b_raw (σ 0))
    refine ⟨b, funext fun τ => ?_⟩
    -- Key fact: τ = ![τ 0, τ 1]
    have htau : τ = ![τ 0, τ 1] := by funext k; fin_cases k <;> simp
    -- Intersection equals pairwise inf
    have hpair : 𝒰.intersection τ = 𝒰.U (τ 0) ⊓ 𝒰.U (τ 1) := by
      rw [htau]; exact intersection_pair 𝒰 (τ 0) (τ 1)
    -- FaceMap facts for n=0
    have fm0 : faceMap (0 : Fin 2) τ (0 : Fin 1) = τ 1 := by
      unfold faceMap; simp
    have fm1 : faceMap (1 : Fin 2) τ (0 : Fin 1) = τ 0 := by
      unfold faceMap; simp
    -- Helper: F.res of b_raw respects equal indices (dependent type transport)
    have b_res_eq : ∀ (i j : 𝒰.I) (hij : i = j)
        (h₁ : 𝒰.intersection τ ≤ 𝒰.U i) (h₂ : 𝒰.intersection τ ≤ 𝒰.U j),
        F.res h₁ (b_raw i) = F.res h₂ (b_raw j) := by
      intro i j hij h₁ h₂; subst hij; exact OModule.res_irrel F _ _ _
    -- Transport b_raw_ih_general to intersection τ
    have key := congr_arg (F.res (le_of_eq hpair)) (b_raw_ih_general (τ 0) (τ 1))
    rw [OModule.res_sub, OModule.res_comp, OModule.res_comp] at key
    -- Each restrictionToFace term reduces to F.res of b_raw
    have term0 : restrictionToFace F 𝒰 τ 0 (b (faceMap 0 τ)) =
        F.res (le_trans (le_of_eq hpair) inf_le_right) (b_raw (τ 1)) := by
      show F.res _ (F.res _ (b_raw _)) = _
      rw [OModule.res_comp]; exact b_res_eq _ _ fm0 _ _
    have term1 : restrictionToFace F 𝒰 τ 1 (b (faceMap 1 τ)) =
        F.res (le_trans (le_of_eq hpair) inf_le_left) (b_raw (τ 0)) := by
      show F.res _ (F.res _ (b_raw _)) = _
      rw [OModule.res_comp]; exact b_res_eq _ _ fm1 _ _
    -- The cocycleAtInf, restricted back, equals c.val τ
    have rhs_eq : F.res (le_of_eq hpair) (cocycleAtInf F 𝒰 c (τ 0) (τ 1)) = c.val τ := by
      -- cocycleAtInf is F.res of c.val by definition (via res_eq_map rfl)
      show F.res _ (F.res (le_of_eq (intersection_pair 𝒰 (τ 0) (τ 1)).symm)
        (c.val ![τ 0, τ 1])) = _
      rw [OModule.res_comp]
      -- Use universal quantification + subst for dependent type transport
      suffices ∀ (a b : Fin 2 → 𝒰.I) (hab : a = b)
          (h : 𝒰.intersection b ≤ 𝒰.intersection a),
          F.res h (c.val a) = c.val b from this _ _ htau.symm _
      intro a b hab h; subst hab; rw [OModule.res_irrel F h (le_refl _), res_id]
    -- Combine everything
    show (∑ j : Fin 2, (-1 : ℤ) ^ j.val •
      restrictionToFace F 𝒰 τ j (b (faceMap j τ))) = c.val τ
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul]
    rw [← sub_eq_add_neg, term0, term1, key, rhs_eq]

/-- Flasque sheaves have Hⁿ⁺¹ = 0 for all n ≥ 0. -/
theorem flasque_acyclic_succ (F : OModule X) [IsFlasque F] (𝒰 : OpenCover X) (n : ℕ) :
    ∀ c : CechCocycles F 𝒰 (n + 1), ∃ b : CechCochain F 𝒰 n,
      cechDifferential F 𝒰 n b = c.val := by
  -- General case follows from the same principle as H¹
  sorry

/-!
## Skyscraper Sheaves are Flasque

A skyscraper sheaf k_p is supported only at the point p, so restriction
maps are either identities (if p is in both opens) or zero maps.
In either case, they are surjective.
-/

/-
Note on skyscraper modules:

A proper definition would use Mathlib's skyscraper presheaf construction
or be defined via pushforward along the closed immersion {p} → X.
The skyscraperModule is defined in Skyscraper.lean.

Skyscraper sheaves are flasque because:

For a skyscraper sheaf k_p:
- k_p(U) = κ(p) if p ∈ U
- k_p(U) = 0 if p ∉ U

The restriction map k_p(V) → k_p(U) for U ⊆ V is:
- Identity κ(p) → κ(p) if p ∈ U (hence p ∈ V)
- The unique map κ(p) → 0 if p ∉ U, p ∈ V
- The zero map 0 → 0 if p ∉ V (hence p ∉ U)

All these maps are surjective.

The theorem skyscraper_isFlasque will be proven in Skyscraper.lean
once skyscraperModule is properly defined.
-/

end RiemannSurfaces.SchemeTheoretic
