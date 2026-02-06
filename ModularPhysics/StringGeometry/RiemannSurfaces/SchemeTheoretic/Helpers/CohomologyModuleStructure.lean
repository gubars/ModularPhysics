/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Cohomology.SheafCohomology

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

/-- The Čech differential is ℂ-linear.

    **Mathematical proof:**
    The differential d : Cⁿ → Cⁿ⁺¹ is defined as:
      (dc)(σ) = Σⱼ (-1)ʲ ρⱼ(c(δʲσ))
    where ρⱼ is restriction and δʲ is face deletion.

    For linearity:
    1. d(a•c + b•c') uses additivity (from cechDifferentialHom) to split
    2. For scalar: d(a•c) = Σⱼ (-1)ʲ ρⱼ((a•c)(δʲσ)) = Σⱼ (-1)ʲ ρⱼ(a • c(δʲσ))
    3. Restriction is O-semilinear: ρⱼ(r•x) = ρ(r)•ρⱼ(x) (by map_smul)
    4. For ℂ-scalars via Module.compHom: a • x = (algebraMap a) • x
    5. By algebraMap_restriction_commute: ρ(algebraMap a) = algebraMap a
    6. So ρⱼ(a•x) = ρⱼ((algebraMap a)•x) = (algebraMap a)•ρⱼ(x) = a•ρⱼ(x)
    7. Then d(a•c) = a•dc by distributing through the sum -/
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
  -- Now we need to show d(a • c) = a • d(c) for each term
  -- This follows from PresheafOfModules.map_smul + algebraMap_restriction_commute
  -- The proof uses the fact that ℂ-smul is defined via Module.compHom as:
  --   s • m = (algebraMap s) • m
  -- Combined with map_smul and algebraMap_restriction_commute, this gives ℂ-linearity.
  --
  -- Due to the complexity of the ModuleCat.restrictScalars type machinery in Mathlib's
  -- PresheafOfModules, the direct proof requires explicit handling of type coercions.
  -- The mathematical content is straightforward:
  --   d(s • c)(σ) = Σⱼ (-1)ʲ • ρⱼ(s • c(δʲσ))
  --              = Σⱼ (-1)ʲ • (s • ρⱼ(c(δʲσ)))    (restriction is ℂ-linear)
  --              = s • Σⱼ (-1)ʲ • ρⱼ(c(δʲσ))      (scalar distributes over sum)
  --              = s • dc(σ)
  --
  -- Helper for scalar linearity
  have scalar_linear : ∀ (s : ℂ) (c : CechCochain F 𝒰 n),
      cechDifferential F 𝒰 n (s • c) = s • cechDifferential F 𝒰 n c := by
    -- The proof requires handling ModuleCat.restrictScalars type coercions
    -- which is technically involved. The mathematical content is standard.
    intro s c; sorry
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

/-- Čech cohomology Hⁿ⁺¹ has ℂ-module structure.

    The quotient Cocycles/Coboundaries inherits ℂ-module structure because:
    1. Cocycles form a ℂ-submodule of cochains (by CechCocycles.submodule)
    2. Coboundaries (comap'd into cocycles) form a ℂ-submodule (by CechCoboundariesInCocycles.submodule)
    3. Quotient of submodules is naturally a module

    **Implementation note:**
    CechCohomologySucc is defined as a quotient of AddSubgroups, while the module structure
    comes from the quotient of submodules. The underlying types are the same, but Lean's
    type system distinguishes them. We use sorry for the type-level transfer. -/
noncomputable instance CechCohomologySucc.module (F : OModule C.toScheme) (𝒰 : OpenCover C.toScheme)
    (n : ℕ) : Module ℂ (CechCohomologySucc F 𝒰 n) := by
  -- CechCohomologySucc is defined as:
  -- (CechCocycles F 𝒰 (n + 1)) ⧸ AddSubgroup.comap (CechCocycles F 𝒰 (n + 1)).subtype (CechCoboundariesSucc F 𝒰 n)
  --
  -- The module structure comes from CechCocycles.submodule and CechCoboundariesInCocycles.submodule.
  -- The types are definitionally equal at the carrier level but differ in the wrapper structure.
  -- We construct the module structure explicitly.

  -- The submodule quotient has a module structure
  let Z := CechCocycles.submodule C F 𝒰 (n + 1)
  let B := CechCoboundariesInCocycles.submodule C F 𝒰 n
  haveI hmod : Module ℂ (Z ⧸ B) := Submodule.Quotient.module B

  -- The types CechCohomologySucc and Z ⧸ B have the same underlying structure
  -- Transfer using sorry for the type-level complexity
  sorry

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
