/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Chain Complex Infrastructure for L∞ Algebras

This file provides chain complex infrastructure for L∞ theory, building on
Mathlib's `HomologicalComplex` framework.

## Main definitions

* `GradedModule` - A ℤ-graded R-module as a cochain complex
* `DGModule` - A differential graded R-module (using Mathlib's `CochainComplex`)
* `DGMorphism` - Chain maps between DG modules
* `QuasiIso` - Quasi-isomorphisms (from Mathlib)

## Mathematical Background

For L∞ algebras, we work with:
- Graded vector spaces V = ⨁_{n∈ℤ} V_n
- A differential d : V → V of degree 1 (cochain complex convention)
- Cohomology H(V, d)

A quasi-isomorphism f : V → W is a chain map inducing isomorphisms on cohomology.

We use Mathlib's `CochainComplex` for complexes with degree +1 differential.

## References

* Weibel - "An Introduction to Homological Algebra"
* [Mathlib HomologicalComplex](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/HomologicalComplex.html)
-/

universe u v

open CategoryTheory

namespace StringAlgebra.Linfinity.Chain

variable (R : Type u) [CommRing R]

/-! ## Graded R-Modules as Cochain Complexes

We work in the category `ModuleCat R` and use `CochainComplex (ModuleCat R) ℤ`
for ℤ-graded cochain complexes of R-modules.
-/

/-- The category of R-modules -/
abbrev RMod := ModuleCat.{v} R

/-- A cochain complex of R-modules indexed by ℤ -/
abbrev CochainComplexR := CochainComplex (RMod R) ℤ

/-- A graded R-module specified by its components, without differential.
    This is the underlying data for constructing cochain complexes. -/
structure GradedModuleData where
  /-- The component R-module at each degree -/
  component : ℤ → Type v
  /-- Each component is an R-module -/
  [instAddCommGroup : ∀ n, AddCommGroup (component n)]
  [instModule : ∀ n, Module R (component n)]

attribute [instance] GradedModuleData.instAddCommGroup GradedModuleData.instModule

namespace GradedModuleData

variable {R}

/-- Convert a component to a ModuleCat object -/
def toModuleCat (V : GradedModuleData R) (n : ℤ) : RMod R :=
  ModuleCat.of R (V.component n)

/-- A degree d graded linear map between graded modules -/
structure GradedLinearMap (V W : GradedModuleData R) (d : ℤ) where
  /-- The component maps f_n : V_n → W_{n+d} -/
  map : ∀ n : ℤ, V.component n →ₗ[R] W.component (n + d)

end GradedModuleData

/-! ## Differential Graded Modules

A DG-module is a cochain complex with degree +1 differential satisfying d² = 0.
We use Mathlib's CochainComplex which encodes this automatically.
-/

/-- A differential graded R-module.

    This wraps Mathlib's `CochainComplex (ModuleCat R) ℤ` which automatically
    ensures d² = 0 via the `ComplexShape.up` structure. -/
structure DGModule where
  /-- The underlying cochain complex from Mathlib -/
  toComplex : CochainComplexR R

namespace DGModule

variable {R}

/-- Access the n-th component as a ModuleCat object -/
def componentCat (V : DGModule R) (n : ℤ) : RMod R :=
  V.toComplex.X n

/-- The differential d_n : V_n → V_{n+1} extracted from the complex.
    Use `.hom` to convert the categorical morphism to a linear map. -/
def differential (V : DGModule R) (n : ℤ) : (V.toComplex.X n) →ₗ[R] (V.toComplex.X (n + 1)) :=
  (V.toComplex.d n (n + 1)).hom

/-- d² = 0: composition of consecutive differentials is zero -/
theorem d_squared (V : DGModule R) (n : ℤ) :
    (V.differential (n + 1)).comp (V.differential n) = 0 := by
  ext x
  simp only [differential, LinearMap.comp_apply, LinearMap.zero_apply]
  have h : V.toComplex.d n (n + 1) ≫ V.toComplex.d (n + 1) (n + 1 + 1) = 0 :=
    HomologicalComplex.d_comp_d _ _ _ _
  -- Categorical composition f ≫ g means "f then g", so (f ≫ g).hom = g.hom.comp f.hom
  have h' : (V.toComplex.d (n + 1) (n + 1 + 1)).hom.comp (V.toComplex.d n (n + 1)).hom = 0 := by
    rw [← ModuleCat.hom_comp, h]; rfl
  exact congrFun (congrArg DFunLike.coe h') x

/-- The n-th cocycles: Z^n = ker(d_n) -/
def cocycles (V : DGModule R) (n : ℤ) : Submodule R (V.toComplex.X n) :=
  LinearMap.ker (V.differential n)

/-- An element is a cocycle iff d(x) = 0 -/
theorem mem_cocycles_iff (V : DGModule R) (n : ℤ) (x : V.toComplex.X n) :
    x ∈ V.cocycles n ↔ V.differential n x = 0 :=
  LinearMap.mem_ker

/-- The differential d_{n-1} : V_{n-1} → V_n -/
def differentialFrom (V : DGModule R) (n : ℤ) : (V.toComplex.X (n - 1)) →ₗ[R] (V.toComplex.X n) :=
  (V.toComplex.d (n - 1) n).hom

/-- The n-th coboundaries: B^n = im(d_{n-1}) -/
def coboundaries (V : DGModule R) (n : ℤ) : Submodule R (V.toComplex.X n) :=
  LinearMap.range (V.differentialFrom n)

/-- Coboundaries are contained in cocycles (d² = 0) -/
theorem coboundaries_le_cocycles (V : DGModule R) (n : ℤ) :
    V.coboundaries n ≤ V.cocycles n := by
  intro x hx
  rw [mem_cocycles_iff]
  simp only [coboundaries, LinearMap.mem_range] at hx
  obtain ⟨y, hy⟩ := hx
  rw [← hy]
  -- Need: d_n(d_{n-1}(y)) = 0
  simp only [differential, differentialFrom]
  have h : V.toComplex.d (n - 1) n ≫ V.toComplex.d n (n + 1) = 0 :=
    HomologicalComplex.d_comp_d _ _ _ _
  have h' : (V.toComplex.d n (n + 1)).hom.comp (V.toComplex.d (n - 1) n).hom = 0 := by
    rw [← ModuleCat.hom_comp, h]; rfl
  exact congrFun (congrArg DFunLike.coe h') y

/-- The n-th cohomology H^n(V) = Z^n / B^n

    In Mathlib, this is computed by `V.toComplex.homology n` -/
def cohomology (V : DGModule R) (n : ℤ) : Type _ :=
  (V.cocycles n) ⧸ ((V.coboundaries n).comap (V.cocycles n).subtype)

instance cohomologyAddCommGroup (V : DGModule R) (n : ℤ) : AddCommGroup (V.cohomology n) :=
  Submodule.Quotient.addCommGroup _

instance cohomologyModule (V : DGModule R) (n : ℤ) : Module R (V.cohomology n) :=
  Submodule.Quotient.module _

/-- Projection from cocycles to cohomology -/
def toCohomology (V : DGModule R) (n : ℤ) : V.cocycles n →ₗ[R] V.cohomology n :=
  Submodule.mkQ _

end DGModule

/-! ## Morphisms and Quasi-isomorphisms

Chain maps and quasi-isomorphisms between DG modules.
-/

/-- A morphism of DG modules (chain map).
    This wraps Mathlib's morphisms in `HomologicalComplex`. -/
structure DGMorphism (V W : DGModule R) where
  /-- The underlying chain map from Mathlib -/
  toHom : V.toComplex ⟶ W.toComplex

namespace DGMorphism

variable {R}

/-- The component map f_n : V_n → W_n as a linear map -/
def componentMap {V W : DGModule R} (f : DGMorphism R V W) (n : ℤ) :
    (V.toComplex.X n) →ₗ[R] (W.toComplex.X n) :=
  (f.toHom.f n).hom

/-- Chain maps send cocycles to cocycles -/
theorem map_cocycles {V W : DGModule R} (f : DGMorphism R V W) (n : ℤ)
    (x : V.toComplex.X n) (hx : x ∈ V.cocycles n) :
    f.componentMap n x ∈ W.cocycles n := by
  rw [DGModule.mem_cocycles_iff] at hx ⊢
  simp only [componentMap, DGModule.differential]
  have comm := f.toHom.comm n (n + 1)
  -- comm : f.toHom.f n ≫ W.toComplex.d n (n + 1) = V.toComplex.d n (n + 1) ≫ f.toHom.f (n + 1)
  calc (W.toComplex.d n (n + 1)).hom ((f.toHom.f n).hom x)
      = (f.toHom.f n ≫ W.toComplex.d n (n + 1)).hom x := by rfl
    _ = (V.toComplex.d n (n + 1) ≫ f.toHom.f (n + 1)).hom x := by rw [comm]
    _ = (f.toHom.f (n + 1)).hom ((V.toComplex.d n (n + 1)).hom x) := by rfl
    _ = (f.toHom.f (n + 1)).hom 0 := by simp only [DGModule.differential] at hx; rw [hx]
    _ = 0 := LinearMap.map_zero _

/-- Chain maps send coboundaries to coboundaries -/
theorem map_coboundaries {V W : DGModule R} (f : DGMorphism R V W) (n : ℤ)
    (x : V.toComplex.X n) (hx : x ∈ V.coboundaries n) :
    f.componentMap n x ∈ W.coboundaries n := by
  simp only [DGModule.coboundaries, LinearMap.mem_range] at hx ⊢
  obtain ⟨y, hy⟩ := hx
  use (f.toHom.f (n - 1)).hom y
  simp only [componentMap, DGModule.differentialFrom]
  have comm := f.toHom.comm (n - 1) n
  calc (W.toComplex.d (n - 1) n).hom ((f.toHom.f (n - 1)).hom y)
      = (f.toHom.f (n - 1) ≫ W.toComplex.d (n - 1) n).hom y := by rfl
    _ = (V.toComplex.d (n - 1) n ≫ f.toHom.f n).hom y := by rw [comm]
    _ = (f.toHom.f n).hom ((V.toComplex.d (n - 1) n).hom y) := by rfl
    _ = (f.toHom.f n).hom x := by simp only [DGModule.differentialFrom] at hy; rw [hy]

/-- The induced linear map on cocycles -/
def mapCocycles {V W : DGModule R} (f : DGMorphism R V W) (n : ℤ) :
    V.cocycles n →ₗ[R] W.cocycles n where
  toFun x := ⟨f.componentMap n x.val, f.map_cocycles n x.val x.property⟩
  map_add' x y := Subtype.ext ((f.componentMap n).map_add x.val y.val)
  map_smul' r x := Subtype.ext ((f.componentMap n).map_smul r x.val)

/-- The induced linear map on cohomology -/
def mapCohomology {V W : DGModule R} (f : DGMorphism R V W) (n : ℤ) :
    V.cohomology n →ₗ[R] W.cohomology n := by
  refine Submodule.liftQ _ ((W.toCohomology n).comp (f.mapCocycles n)) ?_
  intro x hx
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, DGModule.toCohomology]
  rw [Submodule.mem_comap] at hx
  -- x.val is a coboundary, so f(x.val) is a coboundary
  have hfx := f.map_coboundaries n x.val hx
  -- The image of a coboundary in cohomology is zero
  -- p.mkQ y = 0 ↔ y ∈ p
  have : (f.mapCocycles n x) ∈ (W.coboundaries n).comap (W.cocycles n).subtype := by
    simp only [mapCocycles, Submodule.mem_comap]
    exact hfx
  exact (Submodule.Quotient.mk_eq_zero _).mpr this

/-- The identity morphism -/
def id (V : DGModule R) : DGMorphism R V V where
  toHom := 𝟙 V.toComplex

/-- Composition of morphisms -/
def comp {V W U : DGModule R} (g : DGMorphism R W U) (f : DGMorphism R V W) :
    DGMorphism R V U where
  toHom := f.toHom ≫ g.toHom

/-- A morphism is a quasi-isomorphism if it induces isomorphisms on all cohomology. -/
def isQuasiIso {V W : DGModule R} (f : DGMorphism R V W) : Prop :=
  ∀ n : ℤ, Function.Bijective (f.mapCohomology n)

/-- The mapCocycles of id is the identity -/
theorem id_mapCocycles_eq (V : DGModule R) (n : ℤ) (z : V.cocycles n) :
    (id V).mapCocycles n z = z := by
  apply Subtype.ext
  -- Goal: (id V).componentMap n z.val = z.val
  show (id V).componentMap n z.val = z.val
  simp only [componentMap, id, HomologicalComplex.id_f, ModuleCat.id_apply]

/-- The mapCohomology of id is the identity -/
theorem id_mapCohomology_eq (V : DGModule R) (n : ℤ) (x : V.cohomology n) :
    (id V).mapCohomology n x = x := by
  -- Use the quotient induction principle
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← hz]
  -- mapCohomology sends mk z to mk (mapCocycles z)
  -- For id, mapCocycles z = z, so mapCohomology (mk z) = mk z
  show (id V).mapCohomology n (Submodule.Quotient.mk z) = Submodule.Quotient.mk z
  -- The key is that mapCohomology is defined via liftQ, so it maps mk z to mk (mapCocycles z)
  have key : (id V).mapCohomology n (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((id V).mapCocycles n z) := by
    rfl
  rw [key, id_mapCocycles_eq]

/-- Identity is a quasi-isomorphism -/
theorem id_isQuasiIso (V : DGModule R) : (id V).isQuasiIso := by
  intro n
  constructor
  · -- Injective
    intro x y hxy
    rw [id_mapCohomology_eq, id_mapCohomology_eq] at hxy
    exact hxy
  · -- Surjective
    intro y
    exact ⟨y, id_mapCohomology_eq V n y⟩

/-- mapCohomology respects composition -/
theorem comp_mapCohomology {V W U : DGModule R} (g : DGMorphism R W U) (f : DGMorphism R V W)
    (n : ℤ) (x : V.cohomology n) :
    (g.comp f).mapCohomology n x = g.mapCohomology n (f.mapCohomology n x) := by
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← hz]
  -- Both sides should reduce to Quotient.mk of composed mapCocycles
  rfl

/-- Composition of quasi-isomorphisms is a quasi-isomorphism -/
theorem comp_isQuasiIso {V W U : DGModule R} (g : DGMorphism R W U) (f : DGMorphism R V W)
    (hg : g.isQuasiIso) (hf : f.isQuasiIso) : (g.comp f).isQuasiIso := by
  intro n
  have hgn := hg n
  have hfn := hf n
  -- Composition of bijections is a bijection
  constructor
  · -- Injective
    intro x y hxy
    rw [comp_mapCohomology, comp_mapCohomology] at hxy
    have h1 : f.mapCohomology n x = f.mapCohomology n y := hgn.1 hxy
    exact hfn.1 h1
  · -- Surjective
    intro z
    obtain ⟨w, hw⟩ := hgn.2 z
    obtain ⟨v, hv⟩ := hfn.2 w
    use v
    rw [comp_mapCohomology, hv, hw]

end DGMorphism

/-! ## Construction Helpers

Functions to build DG modules from component data.
-/

/-- Build a DG module from graded components and a differential.

    The differential d_n : V_n → V_{n+1} must satisfy d² = 0. -/
def mkDGModule (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (d : ∀ n, V n →ₗ[R] V (n + 1))
    (d_sq : ∀ n x, d (n + 1) (d n x) = 0) : DGModule R where
  toComplex := {
    X := fun n => ModuleCat.of R (V n)
    d := fun i j => if h : j = i + 1 then
      ModuleCat.ofHom (h ▸ d i)
    else 0
    shape := fun i j h => by
      -- h : ¬(ComplexShape.up ℤ).Rel i j, i.e., i + 1 ≠ j
      simp only [ComplexShape.up_Rel] at h
      exact dif_neg (Ne.symm h)
    d_comp_d' := fun i j k hij hjk => by
      simp only [ComplexShape.up_Rel] at hij hjk
      subst hij hjk
      rw [dif_pos rfl, dif_pos rfl]
      ext x
      exact d_sq i x
  }

end StringAlgebra.Linfinity.Chain
