/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Helpers.CohomologyModuleStructure

/-!
# Functoriality of Čech Cohomology

This file proves that Čech cohomology is functorial: a morphism of sheaves
induces maps on cohomology, and isomorphisms of sheaves induce isomorphisms
on cohomology.

## Main Results

* `cochainMap_comm_differential` - The cochain map commutes with the differential
* `cohomology_finrank_eq_of_iso` - Isomorphic sheaves have equal cohomology dimensions
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace RiemannSurfaces.SchemeTheoretic

variable {X : Scheme}

/-!
## Cochain Map
-/

/-- The map on Čech cochains induced by a sheaf morphism f : F → G. -/
noncomputable def cochainMap {F G : OModule X} (f : F ⟶ G) (𝒰 : OpenCover X) (n : ℕ) :
    CechCochain F 𝒰 n → CechCochain G 𝒰 n :=
  fun c σ => f.val.app (Opposite.op (𝒰.intersection σ)) (c σ)

-- Helper: extract the LinearMap from f.val.app at a specific open
private noncomputable def appHom {F G : OModule X} (f : F ⟶ G)
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) :=
  (f.val.app U).hom

/-- The cochain map is additive. -/
theorem cochainMap_add {F G : OModule X} (f : F ⟶ G) (𝒰 : OpenCover X) (n : ℕ)
    (c₁ c₂ : CechCochain F 𝒰 n) :
    cochainMap f 𝒰 n (c₁ + c₂) = cochainMap f 𝒰 n c₁ + cochainMap f 𝒰 n c₂ := by
  funext σ
  -- cochainMap applies f.val.app (a linear map) componentwise
  -- Use LinearMap.map_add
  exact (appHom f (Opposite.op (𝒰.intersection σ))).map_add (c₁ σ) (c₂ σ)

/-- The cochain map preserves zero. -/
theorem cochainMap_zero {F G : OModule X} (f : F ⟶ G) (𝒰 : OpenCover X) (n : ℕ) :
    cochainMap f 𝒰 n 0 = 0 := by
  funext σ
  exact (appHom f (Opposite.op (𝒰.intersection σ))).map_zero

/-- The cochain map preserves integer scalar multiplication. -/
theorem cochainMap_zsmul {F G : OModule X} (f : F ⟶ G) (𝒰 : OpenCover X) (n : ℕ)
    (k : ℤ) (c : CechCochain F 𝒰 n) :
    cochainMap f 𝒰 n (k • c) = k • cochainMap f 𝒰 n c := by
  funext σ
  exact (appHom f (Opposite.op (𝒰.intersection σ))).toAddMonoidHom.map_zsmul (c σ) k

/-- The cochain map as an additive group homomorphism. -/
noncomputable def cochainMapHom {F G : OModule X} (f : F ⟶ G) (𝒰 : OpenCover X) (n : ℕ) :
    CechCochain F 𝒰 n →+ CechCochain G 𝒰 n where
  toFun := cochainMap f 𝒰 n
  map_zero' := cochainMap_zero f 𝒰 n
  map_add' := cochainMap_add f 𝒰 n

/-!
## Commutativity with the Differential
-/

/-- The cochain map commutes with the Čech differential.
    Uses naturality of the sheaf morphism. -/
theorem cochainMap_comm_differential {F G : OModule X} (f : F ⟶ G) (𝒰 : OpenCover X) (n : ℕ)
    (c : CechCochain F 𝒰 n) :
    cochainMap f 𝒰 (n + 1) (cechDifferential F 𝒰 n c) =
    cechDifferential G 𝒰 n (cochainMap f 𝒰 n c) := by
  funext σ
  simp only [cochainMap, cechDifferential]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul]
  congr 1
  simp only [restrictionToFace]
  exact PresheafOfModules.naturality_apply f.val
    (homOfLE (intersection_face_le 𝒰 σ j)).op (c (faceMap j σ))

/-!
## Identity and Composition
-/

/-- The cochain map of the identity morphism is the identity. -/
theorem cochainMap_id (F : OModule X) (𝒰 : OpenCover X) (n : ℕ)
    (c : CechCochain F 𝒰 n) :
    cochainMap (𝟙 F) 𝒰 n c = c := by
  funext σ
  unfold cochainMap
  -- (𝟙 F).val.app U = identity on F.val.obj U
  -- SheafOfModules.id_val : Hom.val (𝟙 F) = 𝟙 F.val
  have hid : SheafOfModules.Hom.val (𝟙 F) = 𝟙 F.val := SheafOfModules.id_val F
  -- The coercion goes through ConcreteCategory.hom which equals .hom for ModuleCat
  -- So we need: ((𝟙 F).val.app U).hom (c σ) = c σ
  -- After rewriting (𝟙 F).val = 𝟙 F.val, then (𝟙 F.val).app U = 𝟙 (F.val.obj U)
  -- Then (𝟙 (F.val.obj U)).hom = LinearMap.id
  show (SheafOfModules.Hom.val (𝟙 F)).app _ (c σ) = c σ
  rw [hid]
  simp [PresheafOfModules.id_app]

/-- The cochain map is functorial: composition of morphisms. -/
theorem cochainMap_comp {F G H : OModule X} (f : F ⟶ G) (g : G ⟶ H)
    (𝒰 : OpenCover X) (n : ℕ) (c : CechCochain F 𝒰 n) :
    cochainMap (f ≫ g) 𝒰 n c = cochainMap g 𝒰 n (cochainMap f 𝒰 n c) := by
  funext σ
  unfold cochainMap
  show (SheafOfModules.Hom.val (f ≫ g)).app _ (c σ) = g.val.app _ (f.val.app _ (c σ))
  rw [SheafOfModules.comp_val]
  simp [PresheafOfModules.comp_app]

/-!
## Cocycle and Coboundary Preservation
-/

/-- The cochain map preserves cocycles. -/
theorem cochainMap_preserves_cocycles {F G : OModule X} (f : F ⟶ G) (𝒰 : OpenCover X) (n : ℕ)
    (c : CechCochain F 𝒰 n) (hc : cechDifferential F 𝒰 n c = 0) :
    cechDifferential G 𝒰 n (cochainMap f 𝒰 n c) = 0 := by
  rw [← cochainMap_comm_differential f 𝒰 n c, hc, cochainMap_zero f 𝒰 (n + 1)]

/-- The cochain map preserves coboundaries. -/
theorem cochainMap_preserves_coboundaries {F G : OModule X} (f : F ⟶ G) (𝒰 : OpenCover X) (n : ℕ)
    (c : CechCochain F 𝒰 (n + 1))
    (hc : ∃ b : CechCochain F 𝒰 n, cechDifferential F 𝒰 n b = c) :
    ∃ b' : CechCochain G 𝒰 n, cechDifferential G 𝒰 n b' = cochainMap f 𝒰 (n + 1) c := by
  obtain ⟨b, rfl⟩ := hc
  exact ⟨cochainMap f 𝒰 n b, (cochainMap_comm_differential f 𝒰 n b).symm⟩

/-!
## Equivalences from Isomorphisms
-/

section IsoEquiv

variable (C : AlgebraicCurve) {F G : OModule C.toScheme} (iso : F ≅ G)
variable (𝒰 : OpenCover C.toScheme)

/-- An isomorphism of sheaves induces an additive equivalence on cochains. -/
noncomputable def cochainAddEquiv (n : ℕ) :
    CechCochain F 𝒰 n ≃+ CechCochain G 𝒰 n where
  toFun := cochainMap iso.hom 𝒰 n
  invFun := cochainMap iso.inv 𝒰 n
  left_inv c := by rw [← cochainMap_comp, Iso.hom_inv_id, cochainMap_id]
  right_inv c := by rw [← cochainMap_comp, Iso.inv_hom_id, cochainMap_id]
  map_add' := cochainMap_add iso.hom 𝒰 n

/-- An isomorphism of sheaves induces an additive equivalence on H⁰ (cocycles in degree 0). -/
noncomputable def cohomology0AddEquiv :
    CechCohomology0 F 𝒰 ≃+ CechCohomology0 G 𝒰 where
  toFun := fun ⟨c, hc⟩ => ⟨cochainMap iso.hom 𝒰 0 c,
    cochainMap_preserves_cocycles iso.hom 𝒰 0 c hc⟩
  invFun := fun ⟨c, hc⟩ => ⟨cochainMap iso.inv 𝒰 0 c,
    cochainMap_preserves_cocycles iso.inv 𝒰 0 c hc⟩
  left_inv := fun ⟨c, hc⟩ => by
    apply Subtype.ext
    show cochainMap iso.inv 𝒰 0 (cochainMap iso.hom 𝒰 0 c) = c
    rw [← cochainMap_comp, Iso.hom_inv_id, cochainMap_id]
  right_inv := fun ⟨c, hc⟩ => by
    apply Subtype.ext
    show cochainMap iso.hom 𝒰 0 (cochainMap iso.inv 𝒰 0 c) = c
    rw [← cochainMap_comp, Iso.inv_hom_id, cochainMap_id]
  map_add' := fun ⟨c₁, _⟩ ⟨c₂, _⟩ => by
    apply Subtype.ext
    exact cochainMap_add iso.hom 𝒰 0 c₁ c₂

/-- Helper: cochainMap of hom maps coboundaries to coboundaries. -/
private theorem cochainMap_hom_coboundary (n : ℕ)
    (c : CechCochain F 𝒰 (n + 1)) (hc : c ∈ CechCoboundariesSucc F 𝒰 n) :
    cochainMap iso.hom 𝒰 (n + 1) c ∈ CechCoboundariesSucc G 𝒰 n := by
  simp only [CechCoboundariesSucc, AddMonoidHom.mem_range, cechDifferentialHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hc ⊢
  obtain ⟨b, hb⟩ := hc
  exact ⟨cochainMap iso.hom 𝒰 n b, by rw [← cochainMap_comm_differential, hb]⟩

/-- Helper: cochainMap of inv maps coboundaries to coboundaries. -/
private theorem cochainMap_inv_coboundary (n : ℕ)
    (c : CechCochain G 𝒰 (n + 1)) (hc : c ∈ CechCoboundariesSucc G 𝒰 n) :
    cochainMap iso.inv 𝒰 (n + 1) c ∈ CechCoboundariesSucc F 𝒰 n := by
  simp only [CechCoboundariesSucc, AddMonoidHom.mem_range, cechDifferentialHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hc ⊢
  obtain ⟨b, hb⟩ := hc
  exact ⟨cochainMap iso.inv 𝒰 n b, by rw [← cochainMap_comm_differential, hb]⟩

/-- An isomorphism of sheaves induces an additive equivalence on Hⁿ⁺¹ (quotient groups). -/
noncomputable def cohomologySuccAddEquiv (n : ℕ) :
    CechCohomologySucc F 𝒰 n ≃+ CechCohomologySucc G 𝒰 n := by
  -- Build additive maps on cocycles
  let φ : CechCocycles F 𝒰 (n + 1) →+ CechCocycles G 𝒰 (n + 1) := {
    toFun := fun ⟨c, hc⟩ => ⟨cochainMap iso.hom 𝒰 (n + 1) c,
      cochainMap_preserves_cocycles iso.hom 𝒰 (n + 1) c hc⟩
    map_zero' := Subtype.ext (cochainMap_zero iso.hom 𝒰 (n + 1))
    map_add' := fun ⟨c₁, _⟩ ⟨c₂, _⟩ => Subtype.ext (cochainMap_add iso.hom 𝒰 (n + 1) c₁ c₂)
  }
  let ψ : CechCocycles G 𝒰 (n + 1) →+ CechCocycles F 𝒰 (n + 1) := {
    toFun := fun ⟨c, hc⟩ => ⟨cochainMap iso.inv 𝒰 (n + 1) c,
      cochainMap_preserves_cocycles iso.inv 𝒰 (n + 1) c hc⟩
    map_zero' := Subtype.ext (cochainMap_zero iso.inv 𝒰 (n + 1))
    map_add' := fun ⟨c₁, _⟩ ⟨c₂, _⟩ => Subtype.ext (cochainMap_add iso.inv 𝒰 (n + 1) c₁ c₂)
  }
  let N_F := AddSubgroup.comap (CechCocycles F 𝒰 (n + 1)).subtype (CechCoboundariesSucc F 𝒰 n)
  let N_G := AddSubgroup.comap (CechCocycles G 𝒰 (n + 1)).subtype (CechCoboundariesSucc G 𝒰 n)
  have hφN : ∀ x : CechCocycles F 𝒰 (n + 1), x ∈ N_F → φ x ∈ N_G := by
    intro ⟨c, hc⟩ hmem
    simp only [N_F, AddSubgroup.mem_comap] at hmem
    simp only [N_G, AddSubgroup.mem_comap]
    exact cochainMap_hom_coboundary C iso 𝒰 n c hmem
  have hψN : ∀ x : CechCocycles G 𝒰 (n + 1), x ∈ N_G → ψ x ∈ N_F := by
    intro ⟨c, hc⟩ hmem
    simp only [N_G, AddSubgroup.mem_comap] at hmem
    simp only [N_F, AddSubgroup.mem_comap]
    exact cochainMap_inv_coboundary C iso 𝒰 n c hmem
  exact {
    toFun := QuotientAddGroup.map N_F N_G φ hφN
    invFun := QuotientAddGroup.map N_G N_F ψ hψN
    left_inv := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H z =>
        -- QuotientAddGroup.map on mk reduces definitionally via lift
        change QuotientAddGroup.mk' N_F (ψ (φ z)) = QuotientAddGroup.mk' N_F z
        congr 1
        apply Subtype.ext
        show cochainMap iso.inv 𝒰 (n + 1) (cochainMap iso.hom 𝒰 (n + 1) z.val) = z.val
        rw [← cochainMap_comp, Iso.hom_inv_id, cochainMap_id]
    right_inv := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H z =>
        change QuotientAddGroup.mk' N_G (φ (ψ z)) = QuotientAddGroup.mk' N_G z
        congr 1
        apply Subtype.ext
        show cochainMap iso.hom 𝒰 (n + 1) (cochainMap iso.inv 𝒰 (n + 1) z.val) = z.val
        rw [← cochainMap_comp, Iso.inv_hom_id, cochainMap_id]
    map_add' := (QuotientAddGroup.map N_F N_G φ hφN).map_add
  }

/-!
## ℂ-Linearity
-/

/-- The cochain map preserves ℂ-scalar multiplication.
    Uses that ℂ-smul on sheaf values is via algebraMap (Module.compHom). -/
theorem cochainMap_smul (f : F ⟶ G) (n : ℕ)
    (a : ℂ) (c : CechCochain F 𝒰 n) :
    cochainMap f 𝒰 n (a • c) = a • cochainMap f 𝒰 n c := by
  funext σ
  -- Collapse the entire chain: cochainMap def + Pi.smul + Module.compHom
  -- LHS: cochainMap f (a•c) σ = f.val.app _ ((a•c) σ) = f.val.app _ (algebraMap(a) • c σ)
  -- RHS: (a • cochainMap f c) σ = algebraMap(a) • f.val.app _ (c σ)
  let R := C.toScheme.presheaf.obj (Opposite.op (𝒰.intersection σ))
  have h_lhs : cochainMap f 𝒰 n (a • c) σ =
    f.val.app (Opposite.op (𝒰.intersection σ)) ((algebraMap ℂ (↑R) a) • c σ) := rfl
  have h_rhs : (a • cochainMap f 𝒰 n c) σ =
    (algebraMap ℂ (↑R) a) • f.val.app (Opposite.op (𝒰.intersection σ)) (c σ) := rfl
  rw [h_lhs, h_rhs]
  -- f.val.app is O_C(U)-linear: f(r • x) = r • f(x)
  exact (appHom f (Opposite.op (𝒰.intersection σ))).map_smul _ _

/-- The H⁰ equivalence is ℂ-linear. -/
theorem cohomology0AddEquiv_smul (a : ℂ) (c : CechCohomology0 F 𝒰) :
    cohomology0AddEquiv C iso 𝒰 (a • c) = a • cohomology0AddEquiv C iso 𝒰 c := by
  apply Subtype.ext
  exact cochainMap_smul C 𝒰 iso.hom 0 a c.val

/-- The H⁰ equivalence as a ℂ-linear equivalence. -/
noncomputable def cohomology0LinearEquiv :
    CechCohomology0 F 𝒰 ≃ₗ[ℂ] CechCohomology0 G 𝒰 :=
  { cohomology0AddEquiv C iso 𝒰 with
    map_smul' := cohomology0AddEquiv_smul C iso 𝒰 }

/-- What `cohomologySuccAddEquiv` does on mk representatives.
    This is needed because `cohomologySuccAddEquiv` is defined via `by exact { ... }`. -/
private theorem cohomologySuccAddEquiv_mk (n : ℕ) (z : CechCocycles F 𝒰 (n + 1)) :
    cohomologySuccAddEquiv C iso 𝒰 n (QuotientAddGroup.mk' _ z) =
    QuotientAddGroup.mk' _
      ⟨cochainMap iso.hom 𝒰 (n + 1) z.val,
       cochainMap_preserves_cocycles iso.hom 𝒰 (n + 1) z.val z.prop⟩ := by
  rfl

/-- The Hⁿ⁺¹ equivalence is ℂ-linear, using the explicit smul_mk' reduction. -/
theorem cohomologySuccAddEquiv_smul (n : ℕ) (a : ℂ) (x : CechCohomologySucc F 𝒰 n) :
    haveI := CechCohomologySucc.module C F 𝒰 n
    haveI := CechCohomologySucc.module C G 𝒰 n
    cohomologySuccAddEquiv C iso 𝒰 n (a • x) = a • cohomologySuccAddEquiv C iso 𝒰 n x := by
  letI := CechCohomologySucc.module C F 𝒰 n
  letI := CechCohomologySucc.module C G 𝒰 n
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    -- Convert • to smulSucc (definitional from Module instance)
    show cohomologySuccAddEquiv C iso 𝒰 n
           (smulSucc C F 𝒰 n a (QuotientAddGroup.mk' _ z)) =
         smulSucc C G 𝒰 n a
           (cohomologySuccAddEquiv C iso 𝒰 n (QuotientAddGroup.mk' _ z))
    -- Reduce smulSucc F on mk z
    rw [CechCohomologySucc.smul_mk' C F 𝒰 n a z]
    -- Reduce equiv on both mk terms
    rw [cohomologySuccAddEquiv_mk C iso 𝒰 n (smulCocycle C F 𝒰 n a z)]
    rw [cohomologySuccAddEquiv_mk C iso 𝒰 n z]
    -- Reduce smulSucc G on mk (φ z)
    rw [CechCohomologySucc.smul_mk' C G 𝒰 n a]
    -- Both sides are now mk of cocycles; show the cocycles are equal
    congr 1
    exact Subtype.ext (cochainMap_smul C 𝒰 iso.hom (n + 1) a z.val)

/-- The Hⁿ⁺¹ equivalence as a ℂ-linear equivalence. -/
noncomputable def cohomologySuccLinearEquiv (n : ℕ) :
    letI := CechCohomologySucc.module C F 𝒰 n
    letI := CechCohomologySucc.module C G 𝒰 n
    CechCohomologySucc F 𝒰 n ≃ₗ[ℂ] CechCohomologySucc G 𝒰 n :=
  letI := CechCohomologySucc.module C F 𝒰 n
  letI := CechCohomologySucc.module C G 𝒰 n
  { cohomologySuccAddEquiv C iso 𝒰 n with
    map_smul' := cohomologySuccAddEquiv_smul C iso 𝒰 n }

end IsoEquiv

/-!
## Finrank Equality
-/

/-- Isomorphic OModules have the same Čech cohomology dimensions. -/
theorem cohomology_finrank_eq_of_iso (C : AlgebraicCurve) {F G : OModule C.toScheme}
    (iso : F ≅ G) (i : ℕ) :
    haveI := sheafCohomologyModule C i F
    haveI := sheafCohomologyModule C i G
    Module.finrank ℂ (SheafCohomology C i F) = Module.finrank ℂ (SheafCohomology C i G) := by
  -- Case split first so CechCohomology pattern-matches to concrete types
  cases i with
  | zero =>
    letI := sheafCohomologyModule C 0 F
    letI := sheafCohomologyModule C 0 G
    -- SheafCohomology C 0 F reduces to CechCohomology0 F 𝒰 through definitions
    change Module.finrank ℂ (CechCohomology0 F (standardAffineCover C)) =
           Module.finrank ℂ (CechCohomology0 G (standardAffineCover C))
    exact LinearEquiv.finrank_eq (cohomology0LinearEquiv C iso (standardAffineCover C))
  | succ n =>
    letI := sheafCohomologyModule C (n + 1) F
    letI := sheafCohomologyModule C (n + 1) G
    change Module.finrank ℂ (CechCohomologySucc F (standardAffineCover C) n) =
           Module.finrank ℂ (CechCohomologySucc G (standardAffineCover C) n)
    exact LinearEquiv.finrank_eq (cohomologySuccLinearEquiv C iso (standardAffineCover C) n)

end RiemannSurfaces.SchemeTheoretic
