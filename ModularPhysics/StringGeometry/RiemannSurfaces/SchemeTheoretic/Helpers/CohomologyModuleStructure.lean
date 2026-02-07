/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Cohomology.CechComplex

/-!
# ℂ-Module Structure on Čech Cohomology

This file develops the ℂ-module structure on Čech cohomology for curves over ℂ.

## Mathematical Background

For a curve C over ℂ:
1. There is a structure morphism ℂ → Γ(C, O_C) (the algebra structure)
2. For proper connected C: Γ(C, O_C) = ℂ (algebraic Liouville theorem)
3. Each O_C(U) is a ℂ-algebra via restriction from global sections
4. Čech cochains inherit ℂ-module structure from the sheaf values
5. Cocycles and coboundaries are ℂ-submodules
6. Cohomology inherits ℂ-module structure as quotient

## Main Definitions

* `CechCochain.module` - ℂ-module structure on Čech cochains
* `CechCohomology.module` - ℂ-module structure on Čech cohomology

## Implementation Notes

For curves over ℂ, the structure morphism gives an algebra structure
ℂ → O_C(U) for each open U. The scalar multiplication on cochains is
defined pointwise using this algebra structure.
-/

open AlgebraicGeometry CategoryTheory

namespace RiemannSurfaces.SchemeTheoretic

variable (C : AlgebraicCurve)

/-!
## Algebra Structure on Sections

The structure morphism of a scheme over ℂ gives an algebra structure
on each ring of sections O_C(U).
-/

/-- For a curve over ℂ, sections have a ℂ-algebra structure.

    This comes from the structure morphism ℂ → O_C which gives
    ℂ → Γ(C, O_C) and then restriction to O_C(U).

    **Construction:**
    1. π : C → Spec ℂ is the structure morphism
    2. π* : Γ(Spec ℂ, ⊤) → Γ(C, ⊤) is the induced global sections map
    3. Γ(Spec ℂ, ⊤) ≅ ℂ via ΓSpecIso
    4. Γ(C, ⊤) → O_C(U) is the restriction map
    5. Compose to get ℂ → O_C(U) -/
noncomputable instance algebraOnSections (U : TopologicalSpace.Opens C.toScheme.carrier) :
    Algebra ℂ (C.toScheme.presheaf.obj (Opposite.op U)) := by
  -- Step 1: Get the ring homomorphism ℂ → Γ(C, ⊤)
  -- This is: ℂ ≅ Γ(Spec ℂ, ⊤) → Γ(C, ⊤) via π*
  let toGlobal : ℂ →+* Γ(C.toScheme, ⊤) :=
    C.structureMorphism.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  -- Step 2: Get the restriction map Γ(C, ⊤) → O_C(U)
  -- The presheaf map is a categorical morphism, extract the ring hom via .hom
  let restrict : Γ(C.toScheme, ⊤) →+* C.toScheme.presheaf.obj (Opposite.op U) :=
    (C.toScheme.presheaf.map (homOfLE le_top).op).hom
  -- Step 3: Compose to get ℂ → O_C(U)
  let toU : ℂ →+* C.toScheme.presheaf.obj (Opposite.op U) := restrict.comp toGlobal
  -- Step 4: Use RingHom.toAlgebra to create the Algebra instance
  exact RingHom.toAlgebra toU

/-- The algebraMap from ℂ to O_C(U) commutes with restriction maps.

    For U ≤ V (as opens), the restriction map res : O_C(V) → O_C(U) satisfies:
      res(algebraMap ℂ O_C(V) a) = algebraMap ℂ O_C(U) a

    This follows from functoriality: algebraMap factors through global sections,
    and res_{V→U} ∘ res_{⊤→V} = res_{⊤→U}. -/
theorem algebraMap_restriction_commute (U V : TopologicalSpace.Opens C.toScheme.carrier)
    (hUV : U ≤ V) (a : ℂ) :
    (C.toScheme.presheaf.map (homOfLE hUV).op).hom (algebraMap ℂ _ a) =
    algebraMap ℂ (C.toScheme.presheaf.obj (Opposite.op U)) a := by
  -- Both sides factor through Γ(C, ⊤), so this follows from presheaf functoriality
  -- res_{U≤V} ∘ res_{V≤⊤} = res_{U≤⊤}
  simp only [algebraOnSections, RingHom.algebraMap_toAlgebra]
  simp only [RingHom.coe_comp, Function.comp_apply]
  -- LHS: res_{U≤V}(res_{V≤⊤}(toGlobal a))
  -- RHS: res_{U≤⊤}(toGlobal a)
  -- These are equal because res_{U≤V} ∘ res_{V≤⊤} = res_{U≤⊤} by presheaf functoriality
  -- Let y = toGlobal(a) ∈ Γ(C, ⊤)
  let y := (C.structureMorphism.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) a
  -- We need: (map hUV).hom ((map le_top_V).hom y) = (map le_top_U).hom y
  -- By functoriality: map f ≫ map g = map (f ≫ g)
  -- So (map le_top_V ≫ map hUV).hom y = map(le_top_V ≫ hUV).hom y
  -- And le_top_V.op ≫ hUV.op = le_top_U.op
  change (C.toScheme.presheaf.map (homOfLE hUV).op).hom
         ((C.toScheme.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom y) =
         (C.toScheme.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom y
  -- The LHS equals (map le_top_V ≫ map hUV).hom y by CommRingCat.comp_apply
  have h1 : (C.toScheme.presheaf.map (homOfLE hUV).op).hom
            ((C.toScheme.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom y) =
            (C.toScheme.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫
             C.toScheme.presheaf.map (homOfLE hUV).op).hom y := by
    simp only [CommRingCat.comp_apply]
  rw [h1]
  -- Now need: (map le_top_V ≫ map hUV).hom y = (map le_top_U).hom y
  -- By functoriality: map le_top_V ≫ map hUV = map (le_top_V.op ≫ hUV.op)
  -- And hUV ≫ le_top_V = le_top_U (both are ⊤ → U in Opens, a thin category)
  congr 2
  rw [← C.toScheme.presheaf.map_comp]
  congr 1

/-!
## Module Structure on Sheaf Values

For an O_C-module F, each F(U) is naturally a ℂ-module via the
algebra structure ℂ → O_C(U).
-/

/-- The value of an O_C-module at U is a ℂ-module. -/
noncomputable instance moduleValueComplex (F : OModule C.toScheme)
    (U : TopologicalSpace.Opens C.toScheme.carrier) :
    Module ℂ (F.val.obj (Opposite.op U)) := by
  -- F(U) is an O_C(U)-module (from ModuleCat structure)
  -- O_C(U) is a ℂ-algebra (from algebraOnSections)
  -- Therefore F(U) is a ℂ-module via restriction of scalars
  --
  -- The type F.val.obj (op U) is in ModuleCat (C.toScheme.presheaf.obj (op U))
  -- which provides the Module instance on the carrier type.
  --
  -- We use Module.compHom to compose the algebra map with the module structure.
  -- This requires careful type management since F.val.obj returns a ModuleCat object.
  haveI : Algebra ℂ (C.toScheme.presheaf.obj (Opposite.op U)) := algebraOnSections C U
  -- The Module instance is provided by ModuleCat
  -- Explicitly specify the target ring for algebraMap
  exact Module.compHom (F.val.obj (Opposite.op U)) (algebraMap ℂ (C.toScheme.presheaf.obj (Opposite.op U)))

/-!
## Module Structure on Cochains

Čech cochains are products of module values, hence inherit ℂ-module structure.
-/

/-- Čech cochains form a ℂ-module.

    This is because cochains are functions σ ↦ F(intersection σ),
    and each F(intersection σ) is a ℂ-module. -/
noncomputable instance CechCochain.module (F : OModule C.toScheme) (𝒰 : OpenCover C.toScheme)
    (n : ℕ) : Module ℂ (CechCochain F 𝒰 n) := by
  -- CechCochain F 𝒰 n is a dependent product type
  -- Each value F.val.obj (op (𝒰.intersection σ)) is a ℂ-module
  -- The product of ℂ-modules is a ℂ-module with pointwise operations
  unfold CechCochain
  haveI : ∀ σ : Fin (n + 1) → 𝒰.I, Module ℂ (F.val.obj (Opposite.op (𝒰.intersection σ))) := by
    intro σ
    exact moduleValueComplex C F (𝒰.intersection σ)
  -- Use Pi.module for the product
  exact Pi.module (Fin (n + 1) → 𝒰.I) (fun σ => F.val.obj (Opposite.op (𝒰.intersection σ))) ℂ

/-- Presheaf restriction applied to an element equals the CommRingCat morphism hom applied.
    This bridges `ringCatSheaf.val.map` and `presheaf.map` for element-level computations. -/
theorem ringCatSheaf_map_eq (U V : TopologicalSpace.Opens C.toScheme.carrier) (hUV : U ≤ V)
    (r : C.toScheme.presheaf.obj (Opposite.op V)) :
    (C.toScheme.ringCatSheaf.val.map (homOfLE hUV).op : _) r =
    (C.toScheme.presheaf.map (homOfLE hUV).op).hom r := rfl

theorem restrictionToFace_smul (F : OModule C.toScheme) (𝒰 : OpenCover C.toScheme)
    {n : ℕ} (σ : Fin (n + 2) → 𝒰.I) (j : Fin (n + 2)) (s : ℂ)
    (m : F.val.obj (Opposite.op (𝒰.intersection (faceMap j σ)))) :
    restrictionToFace F 𝒰 σ j (s • m) = s • restrictionToFace F 𝒰 σ j m := by
  -- Strategy: Convert ℂ-smul to O-smul, apply map_smul, use algebraMap_restriction_commute
  -- Module.compHom is @[reducible] (abbrev), so s • m = (algebraMap s) • m definitionally
  simp only [restrictionToFace]
  -- Step 1: Convert ℂ-smul to O-smul (definitional via Module.compHom)
  let src_ring := C.toScheme.presheaf.obj (Opposite.op (𝒰.intersection (faceMap j σ)))
  let tgt_ring := C.toScheme.presheaf.obj (Opposite.op (𝒰.intersection σ))
  have h_src : (s • m : F.val.obj (Opposite.op (𝒰.intersection (faceMap j σ)))) =
    (algebraMap ℂ ↑src_ring s) • m := rfl
  have h_tgt : ∀ (x : F.val.obj (Opposite.op (𝒰.intersection σ))),
    s • x = (algebraMap ℂ ↑tgt_ring s) • x := fun _ => rfl
  rw [h_src]
  -- Step 2: Apply O-semilinearity (map_smul)
  rw [F.val.map_smul]
  -- Step 3: Convert back and use algebraMap_restriction_commute
  rw [h_tgt]
  congr 1
  -- Goal: ringCatSheaf.val.map h.op (algebraMap s) = algebraMap s
  -- Bridge ringCatSheaf.val.map to presheaf.map, then use algebraMap_restriction_commute
  rw [ringCatSheaf_map_eq C]
  exact algebraMap_restriction_commute C _ _ _ s

/-- The Čech differential is ℂ-linear.

    **Mathematical proof:**
    The differential d : Cⁿ → Cⁿ⁺¹ is defined as:
      (dc)(σ) = Σⱼ (-1)ʲ ρⱼ(c(δʲσ))
    where ρⱼ is restriction and δʲ is face deletion.

    For linearity:
    1. d(a•c + b•c') uses additivity (from cechDifferentialHom) to split
    2. For scalar: d(a•c) = Σⱼ (-1)ʲ ρⱼ((a•c)(δʲσ)) = Σⱼ (-1)ʲ ρⱼ(a • c(δʲσ))
    3. Restriction is ℂ-linear: ρⱼ(a•x) = a•ρⱼ(x) (by restrictionToFace_smul)
    4. Then d(a•c) = a•dc by distributing through the sum -/
theorem cechDifferential_linear (F : OModule C.toScheme) (𝒰 : OpenCover C.toScheme) (n : ℕ) :
    ∀ (c₁ c₂ : CechCochain F 𝒰 n) (a b : ℂ),
      cechDifferential F 𝒰 n (a • c₁ + b • c₂) =
      a • cechDifferential F 𝒰 n c₁ + b • cechDifferential F 𝒰 n c₂ := by
  intro c₁ c₂ a b
  -- Use additivity of the differential (already proven in cechDifferentialHom)
  have hadd : cechDifferential F 𝒰 n (a • c₁ + b • c₂) =
              cechDifferential F 𝒰 n (a • c₁) + cechDifferential F 𝒰 n (b • c₂) := by
    exact (cechDifferentialHom F 𝒰 n).map_add (a • c₁) (b • c₂)
  rw [hadd]
  -- Helper for scalar linearity using restrictionToFace_smul
  have scalar_linear : ∀ (s : ℂ) (c : CechCochain F 𝒰 n),
      cechDifferential F 𝒰 n (s • c) = s • cechDifferential F 𝒰 n c := by
    intro s c
    funext σ
    unfold cechDifferential
    rw [Pi.smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    -- Goal: (-1)^j • restrictionToFace F 𝒰 σ j ((s • c) (faceMap j σ))
    --      = s • ((-1)^j • restrictionToFace F 𝒰 σ j (c (faceMap j σ)))
    -- (s • c)(faceMap j σ) = s • c(faceMap j σ) by Pi.smul_apply
    rw [Pi.smul_apply]
    -- Now use restrictionToFace_smul
    rw [restrictionToFace_smul C]
    -- (-1)^j • (s • ρⱼ(c(δʲσ))) = s • ((-1)^j • ρⱼ(c(δʲσ)))
    rw [smul_comm]
  rw [scalar_linear a c₁, scalar_linear b c₂]

/-!
## Module Structure on Cohomology

Cocycles and coboundaries are ℂ-submodules, so cohomology is a ℂ-module.
-/

/-- Čech coboundaries Bⁿ⁺¹ form a ℂ-submodule of cochains Cⁿ⁺¹.

    Coboundaries are the image of d : Cⁿ → Cⁿ⁺¹, which is a ℂ-linear map
    by `cechDifferential_linear`. -/
noncomputable def CechCoboundariesSucc.submodule (F : OModule C.toScheme) (𝒰 : OpenCover C.toScheme)
    (n : ℕ) : Submodule ℂ (CechCochain F 𝒰 (n + 1)) where
  carrier := {c | ∃ b, cechDifferential F 𝒰 n b = c}
  add_mem' := by
    intro a b ⟨ba, ha⟩ ⟨bb, hb⟩
    use ba + bb
    have := (cechDifferentialHom F 𝒰 n).map_add ba bb
    simp only [cechDifferentialHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    rw [this, ha, hb]
  zero_mem' := by
    use 0
    have := (cechDifferentialHom F 𝒰 n).map_zero
    simp only [cechDifferentialHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    exact this
  smul_mem' := by
    intro c x ⟨b, hb⟩
    -- x = d(b), so c • x = c • d(b) = d(c • b) by linearity
    use c • b
    have hlin := cechDifferential_linear C F 𝒰 n b 0 c 0
    simp only [smul_zero, add_zero, zero_smul] at hlin
    rw [hlin, hb]

/-- Čech cocycles form a ℂ-submodule. -/
noncomputable def CechCocycles.submodule (F : OModule C.toScheme) (𝒰 : OpenCover C.toScheme)
    (n : ℕ) : Submodule ℂ (CechCochain F 𝒰 n) where
  carrier := {c | cechDifferential F 𝒰 n c = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    -- Use that cechDifferentialHom is an AddMonoidHom
    have := (cechDifferentialHom F 𝒰 n).map_add a b
    -- cechDifferentialHom.toFun = cechDifferential by definition
    simp only [cechDifferentialHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    rw [this, ha, hb, add_zero]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    have := (cechDifferentialHom F 𝒰 n).map_zero
    simp only [cechDifferentialHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    exact this
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    -- Need linearity of differential: d(c • x) = c • d(x)
    -- Since d(x) = 0 (by hx), we get d(c • x) = c • 0 = 0
    have hlin := cechDifferential_linear C F 𝒰 n x 0 c 0
    simp only [smul_zero, add_zero, zero_smul] at hlin
    rw [hlin, hx, smul_zero]

/-- Čech cohomology H⁰ has ℂ-module structure. -/
noncomputable instance CechCohomology0.module (F : OModule C.toScheme) (𝒰 : OpenCover C.toScheme) :
    Module ℂ (CechCohomology0 F 𝒰) := by
  -- CechCohomology0 = CechCocycles = kernel of d⁰
  -- CechCocycles.submodule has the same carrier as CechCocycles (the AddSubgroup)
  -- The Module structure can be transferred since the carrier types are definitionally equal
  unfold CechCohomology0 CechCocycles
  -- CechCocycles is (cechDifferentialHom F 𝒰 0).ker which is an AddSubgroup
  -- Its carrier equals the carrier of CechCocycles.submodule
  -- We can use the Module instance from the submodule
  have hcarrier : ((cechDifferentialHom F 𝒰 0).ker : Set (CechCochain F 𝒰 0)) =
                  (CechCocycles.submodule C F 𝒰 0 : Set (CechCochain F 𝒰 0)) := by
    ext c
    simp only [AddMonoidHom.mem_ker, SetLike.mem_coe]
    rfl
  -- The carrier types are the same subtype, so we can transfer the module structure
  exact (CechCocycles.submodule C F 𝒰 0).restrictScalars ℂ |>.module

/-- The comap of coboundaries into cocycles forms a ℂ-submodule.

    This is needed because CechCohomologySucc is defined as
    Cocycles ⧸ (AddSubgroup.comap subtype Coboundaries)
    and we need to show this corresponds to a submodule quotient. -/
noncomputable def CechCoboundariesInCocycles.submodule (F : OModule C.toScheme)
    (𝒰 : OpenCover C.toScheme) (n : ℕ) : Submodule ℂ (CechCocycles.submodule C F 𝒰 (n + 1)) where
  carrier := {z | ∃ b, cechDifferential F 𝒰 n b = z.val}
  add_mem' := by
    intro a b ⟨ba, ha⟩ ⟨bb, hb⟩
    use ba + bb
    have := (cechDifferentialHom F 𝒰 n).map_add ba bb
    simp only [cechDifferentialHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    simp only [Submodule.coe_add]
    rw [this, ha, hb]
  zero_mem' := by
    use 0
    have := (cechDifferentialHom F 𝒰 n).map_zero
    simp only [cechDifferentialHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    simp only [ZeroMemClass.coe_zero]
    exact this
  smul_mem' := by
    intro c x ⟨b, hb⟩
    use c • b
    have hlin := cechDifferential_linear C F 𝒰 n b 0 c 0
    simp only [smul_zero, add_zero, zero_smul] at hlin
    simp only [SetLike.val_smul]
    rw [hlin, hb]

/-! ## Čech cohomology Hⁿ⁺¹ ℂ-module structure

Constructed explicitly using QuotientAddGroup.lift so that the smul
reduction `a • mk z = mk ⟨a • z.val, ...⟩` holds definitionally via
QuotientAddGroup.lift_mk', avoiding expensive type unification between
AddSubgroup and Submodule quotients. -/

section CechCohomologySuccModule

variable (F : OModule C.toScheme) (𝒰 : OpenCover C.toScheme) (n : ℕ)

noncomputable abbrev N_succ :=
  AddSubgroup.comap (CechCocycles F 𝒰 (n + 1)).subtype (CechCoboundariesSucc F 𝒰 n)

/-- ℂ-scalar multiplication preserves cocycles. -/
theorem smul_val_mem_cocycles (a : ℂ) (z : CechCocycles F 𝒰 (n + 1)) :
    a • z.val ∈ CechCocycles F 𝒰 (n + 1) := by
  simp only [CechCocycles, AddMonoidHom.mem_ker]
  -- cechDifferentialHom agrees with cechDifferential on values
  show cechDifferential F 𝒰 (n + 1) (a • z.val) = 0
  have hlin := cechDifferential_linear C F 𝒰 (n + 1) z.val 0 a 0
  simp only [smul_zero, add_zero, zero_smul] at hlin
  rw [hlin]
  have hz : cechDifferential F 𝒰 (n + 1) z.val = 0 :=
    AddMonoidHom.mem_ker.mp z.prop
  rw [hz, smul_zero]

/-- Build the smul'd cocycle element. -/
noncomputable def smulCocycle (a : ℂ) (z : CechCocycles F 𝒰 (n + 1)) :
    CechCocycles F 𝒰 (n + 1) :=
  ⟨a • z.val, smul_val_mem_cocycles C F 𝒰 n a z⟩

/-- smulCocycle sends N_succ to N_succ (needed for well-definedness of quotient smul). -/
theorem smulCocycle_mem_N (a : ℂ) (z : CechCocycles F 𝒰 (n + 1))
    (hz : z ∈ N_succ C F 𝒰 n) : smulCocycle C F 𝒰 n a z ∈ N_succ C F 𝒰 n := by
  simp only [N_succ, AddSubgroup.mem_comap, CechCoboundariesSucc,
    AddMonoidHom.mem_range] at hz ⊢
  obtain ⟨b, hb⟩ := hz
  refine ⟨a • b, ?_⟩
  -- Unfold everything to get goal in terms of cechDifferential
  simp only [smulCocycle, AddSubgroup.coe_subtype, cechDifferentialHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hb ⊢
  have hlin := cechDifferential_linear C F 𝒰 n b 0 a 0
  simp only [smul_zero, add_zero, zero_smul] at hlin
  rw [hlin, hb]

/-- The AddMonoidHom for smul by a on cocycles, landing in the quotient. -/
noncomputable def smulCocycleHom (a : ℂ) :
    CechCocycles F 𝒰 (n + 1) →+ CechCohomologySucc F 𝒰 n where
  toFun z := QuotientAddGroup.mk' (N_succ C F 𝒰 n) (smulCocycle C F 𝒰 n a z)
  map_zero' := by
    show QuotientAddGroup.mk' _ (smulCocycle C F 𝒰 n a 0) = 0
    have : smulCocycle C F 𝒰 n a 0 = 0 :=
      Subtype.ext (show a • (0 : CechCocycles F 𝒰 (n + 1)).val = 0 from smul_zero a)
    rw [this, map_zero]
  map_add' z₁ z₂ := by
    show QuotientAddGroup.mk' _ (smulCocycle C F 𝒰 n a (z₁ + z₂)) =
         QuotientAddGroup.mk' _ (smulCocycle C F 𝒰 n a z₁) +
         QuotientAddGroup.mk' _ (smulCocycle C F 𝒰 n a z₂)
    rw [← map_add (QuotientAddGroup.mk' (N_succ C F 𝒰 n))]
    congr 1; exact Subtype.ext (smul_add a z₁.val z₂.val)

/-- The smul operation on CechCohomologySucc, defined via QuotientAddGroup.lift
    so that `smul_mk' : smulSucc a (mk z) = mk (smulCocycle a z)` holds by lift_mk'. -/
noncomputable def smulSucc (a : ℂ) :
    CechCohomologySucc F 𝒰 n → CechCohomologySucc F 𝒰 n :=
  QuotientAddGroup.lift (N_succ C F 𝒰 n) (smulCocycleHom C F 𝒰 n a)
    (fun z hz => by
      rw [AddMonoidHom.mem_ker]
      show QuotientAddGroup.mk' (N_succ C F 𝒰 n) (smulCocycle C F 𝒰 n a z) = 0
      have hmem := smulCocycle_mem_N C F 𝒰 n a z hz
      exact (QuotientAddGroup.eq_zero_iff (smulCocycle C F 𝒰 n a z)).mpr hmem)

/-- Key reduction lemma: smul on CechCohomologySucc reduces on mk representatives.
    Uses `•` notation which unfolds to `smulSucc` via the Module instance. -/
theorem CechCohomologySucc.smul_mk' (a : ℂ) (z : CechCocycles F 𝒰 (n + 1)) :
    smulSucc C F 𝒰 n a (QuotientAddGroup.mk' _ z) =
    QuotientAddGroup.mk' _ (smulCocycle C F 𝒰 n a z) :=
  QuotientAddGroup.lift_mk' _ _ z

noncomputable instance CechCohomologySucc.module :
    Module ℂ (CechCohomologySucc F 𝒰 n) where
  smul := smulSucc C F 𝒰 n
  one_smul x := by
    induction x using QuotientAddGroup.induction_on with
    | H z =>
      show smulSucc C F 𝒰 n 1 (QuotientAddGroup.mk' _ z) = QuotientAddGroup.mk' _ z
      rw [CechCohomologySucc.smul_mk']
      congr 1; exact Subtype.ext (one_smul ℂ z.val)
  mul_smul a b x := by
    induction x using QuotientAddGroup.induction_on with
    | H z =>
      show smulSucc C F 𝒰 n (a * b) (QuotientAddGroup.mk' _ z) =
           smulSucc C F 𝒰 n a (smulSucc C F 𝒰 n b (QuotientAddGroup.mk' _ z))
      rw [CechCohomologySucc.smul_mk', CechCohomologySucc.smul_mk',
          CechCohomologySucc.smul_mk']
      congr 1; exact Subtype.ext (mul_smul a b z.val)
  smul_zero a := by
    show smulSucc C F 𝒰 n a 0 = 0
    have h0 : (0 : CechCohomologySucc F 𝒰 n) = QuotientAddGroup.mk' _ 0 :=
      (map_zero (QuotientAddGroup.mk' (N_succ C F 𝒰 n))).symm
    rw [h0, CechCohomologySucc.smul_mk']
    have : smulCocycle C F 𝒰 n a 0 = 0 :=
      Subtype.ext (by simp [smulCocycle, smul_zero, ZeroMemClass.coe_zero])
    rw [this, map_zero]
  smul_add a x y := by
    induction x using QuotientAddGroup.induction_on with
    | H zx =>
      induction y using QuotientAddGroup.induction_on with
      | H zy =>
        show smulSucc C F 𝒰 n a (QuotientAddGroup.mk' _ zx + QuotientAddGroup.mk' _ zy) =
             smulSucc C F 𝒰 n a (QuotientAddGroup.mk' _ zx) +
             smulSucc C F 𝒰 n a (QuotientAddGroup.mk' _ zy)
        rw [← map_add (QuotientAddGroup.mk' _), CechCohomologySucc.smul_mk',
            CechCohomologySucc.smul_mk', CechCohomologySucc.smul_mk',
            ← map_add (QuotientAddGroup.mk' _)]
        congr 1; exact Subtype.ext (smul_add a zx.val zy.val)
  add_smul a b x := by
    induction x using QuotientAddGroup.induction_on with
    | H z =>
      show smulSucc C F 𝒰 n (a + b) (QuotientAddGroup.mk' _ z) =
           smulSucc C F 𝒰 n a (QuotientAddGroup.mk' _ z) +
           smulSucc C F 𝒰 n b (QuotientAddGroup.mk' _ z)
      simp only [CechCohomologySucc.smul_mk', ← map_add (QuotientAddGroup.mk' _)]
      congr 1; exact Subtype.ext (add_smul a b z.val)
  zero_smul x := by
    induction x using QuotientAddGroup.induction_on with
    | H z =>
      show smulSucc C F 𝒰 n 0 (QuotientAddGroup.mk' _ z) = 0
      rw [CechCohomologySucc.smul_mk']
      have : smulCocycle C F 𝒰 n 0 z = 0 := Subtype.ext (zero_smul ℂ z.val)
      rw [this, map_zero]

end CechCohomologySuccModule

/-- Čech cohomology in degree 0 has AddCommMonoid structure. -/
noncomputable instance CechCohomologyCurve.addCommMonoid0 (F : OModule C.toScheme) :
    AddCommMonoid (CechCohomologyCurve C F 0) := by
  unfold CechCohomologyCurve CechCohomology CechCohomology0
  infer_instance

/-- Čech cohomology in degree n+1 has AddCommMonoid structure. -/
noncomputable instance CechCohomologyCurve.addCommMonoidSucc (F : OModule C.toScheme) (n : ℕ) :
    AddCommMonoid (CechCohomologyCurve C F (n + 1)) := by
  unfold CechCohomologyCurve CechCohomology CechCohomologySucc
  infer_instance

/-- Čech cohomology in degree 0 has ℂ-module structure. -/
noncomputable instance CechCohomologyCurve.module0 (F : OModule C.toScheme) :
    Module ℂ (CechCohomologyCurve C F 0) := by
  unfold CechCohomologyCurve CechCohomology CechCohomology0
  exact CechCohomology0.module C F (standardAffineCover C)

/-- Čech cohomology in degree n+1 has ℂ-module structure. -/
noncomputable instance CechCohomologyCurve.moduleSucc (F : OModule C.toScheme) (n : ℕ) :
    Module ℂ (CechCohomologyCurve C F (n + 1)) := by
  unfold CechCohomologyCurve CechCohomology CechCohomologySucc
  exact CechCohomologySucc.module C F (standardAffineCover C) n

/-- Sheaf cohomology of a curve has ℂ-module structure.

    This is defined by case analysis since CechCohomologyCurve is defined by cases. -/
noncomputable instance sheafCohomologyModule (i : ℕ) (F : OModule C.toScheme) :
    Module ℂ (SheafCohomology C i F) := by
  cases i with
  | zero => exact CechCohomologyCurve.module0 C F
  | succ n => exact CechCohomologyCurve.moduleSucc C F n

/-!
## Finite Dimensionality

For coherent sheaves on proper curves, cohomology is finite-dimensional.
This is Serre's theorem.
-/

variable (C' : ProperCurve)

/-- Serre's finiteness theorem: For a coherent sheaf F on a proper curve,
    the cohomology Hⁱ(C, F) is finite-dimensional over ℂ.

    **Mathematical content:**
    This is a fundamental theorem in algebraic geometry. The proof uses:
    1. Reduction to the case of line bundles (using coherent resolution)
    2. For line bundles, use vanishing for sufficiently negative degrees
    3. Noetherian property of coherent sheaves

    This is a foundational result that we take as an axiom/sorry
    for the scheme-theoretic development. -/
noncomputable instance sheafCohomology_finiteDimensional (i : ℕ) (F : CoherentSheaf C'.toAlgebraicCurve) :
    FiniteDimensional ℂ (SheafCohomology C'.toAlgebraicCurve i F.toModule) := by
  sorry

/-!
## The h_i Function

With the module structure and finite dimensionality, we can now properly define h_i.
-/

/-- The dimension hⁱ(F) = dim_ℂ Hⁱ(C, F).

    This is the proper definition using Module.finrank, which is well-defined
    because:
    1. SheafCohomology is a ℂ-module (from sheafCohomologyModule)
    2. It's finite-dimensional (from sheafCohomology_finiteDimensional)

    For curves, only h⁰ and h¹ are non-zero (higher cohomology vanishes). -/
noncomputable def h_i_proper (i : ℕ) (F : CoherentSheaf C'.toAlgebraicCurve) : ℕ :=
  -- Use the Module instance which provides AddCommMonoid via type class inference
  haveI : Module ℂ (SheafCohomology C'.toAlgebraicCurve i F.toModule) :=
    sheafCohomologyModule C'.toAlgebraicCurve i F.toModule
  Module.finrank ℂ (SheafCohomology C'.toAlgebraicCurve i F.toModule)

end RiemannSurfaces.SchemeTheoretic
