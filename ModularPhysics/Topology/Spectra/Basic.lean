/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.Topology.Homotopy.Suspension
import ModularPhysics.Topology.Homotopy.WeakEquivalence

/-!
# Sequential Spectra

This file defines sequential spectra, which are the fundamental objects of stable homotopy theory.

## Main Definitions

* `Spectrum` - A sequential spectrum: a sequence of pointed spaces with structure maps
* `SpectrumHom` - Morphisms of spectra (level-wise maps compatible with structure maps)
* `OmegaSpectrum` - An Ω-spectrum where adjoint structure maps are weak equivalences

## Mathematical Background

A sequential spectrum E consists of:
- A sequence of pointed spaces E_n for n ∈ ℕ
- Structure maps σ_n : ΣE_n → E_{n+1}

Equivalently (via the Σ ⊣ Ω adjunction), we can specify:
- Adjoint structure maps ε_n : E_n → ΩE_{n+1}

The homotopy groups of a spectrum are:
- π_k(E) = colim_{n→∞} π_{n+k}(E_n) for k ∈ ℤ

This allows negative homotopy groups, which is a key feature of stable homotopy theory.

## References

* Adams, "Stable Homotopy and Generalised Homology"
* May, "A Concise Course in Algebraic Topology", Chapter 22
-/

universe u

open CategoryTheory PointedTopSpace

namespace Topology

/-! ## Sequential Spectra -/

/-- A sequential spectrum consists of:
    - A sequence of pointed spaces E_n
    - Structure maps (in adjoint form) ε_n : E_n → ΩE_{n+1}

    We use the adjoint form of structure maps for convenience. -/
structure Spectrum where
  /-- The n-th space of the spectrum -/
  space : ℕ → PointedTopSpace
  /-- The adjoint structure map E_n → ΩE_{n+1} -/
  structureMap : ∀ n, space n ⟶ Ω (space (n + 1))

namespace Spectrum

variable (E F G : Spectrum)

/-- The n-th space of a spectrum. -/
def spaceAt (n : ℕ) : PointedTopSpace := E.space n

/-- The structure map from E_n to ΩE_{n+1}. -/
def ε (n : ℕ) : E.spaceAt n ⟶ Ω (E.spaceAt (n + 1)) := E.structureMap n

end Spectrum

/-! ## Morphisms of Spectra -/

/-- A morphism of spectra f : E → F consists of:
    - Level maps f_n : E_n → F_n
    - Compatibility: the diagram commutes -/
structure SpectrumHom (E F : Spectrum) where
  /-- The level-n map -/
  levelMap : ∀ n, E.spaceAt n ⟶ F.spaceAt n
  /-- Compatibility with structure maps -/
  comm : ∀ n, E.ε n ≫ loopSpaceMap (levelMap (n + 1)) = levelMap n ≫ F.ε n

namespace SpectrumHom

variable {E F G : Spectrum}

/-- The identity morphism of spectra. -/
@[simps]
def id (E : Spectrum) : SpectrumHom E E where
  levelMap := fun n => PointedTopSpace.Hom.id (E.spaceAt n)
  comm := fun n => by
    have h1 : PointedTopSpace.Hom.id (E.spaceAt n) ≫ E.ε n = E.ε n := by rfl
    have h2 : loopSpaceMap (PointedTopSpace.Hom.id (E.spaceAt (n + 1))) =
              PointedTopSpace.Hom.id (Ω (E.spaceAt (n + 1))) := loopSpaceMap_id (E.spaceAt (n + 1))
    rw [h2]
    simp only [h1]
    rfl

/-- Composition of spectrum morphisms. -/
@[simps]
def comp (f : SpectrumHom E F) (g : SpectrumHom F G) : SpectrumHom E G where
  levelMap := fun n => f.levelMap n ≫ g.levelMap n
  comm := fun n => by
    -- Need to show: E.ε n ≫ Ω(f_{n+1} ≫ g_{n+1}) = (f_n ≫ g_n) ≫ G.ε n
    rw [loopSpaceMap_comp]
    -- Now: E.ε n ≫ (Ωf_{n+1} ≫ Ωg_{n+1}) = (f_n ≫ g_n) ≫ G.ε n
    rw [← Category.assoc]
    rw [f.comm]
    -- Now: (f_n ≫ F.ε n) ≫ Ωg_{n+1} = (f_n ≫ g_n) ≫ G.ε n
    rw [Category.assoc, Category.assoc]
    congr 1
    exact g.comm n

@[ext]
theorem ext (f g : SpectrumHom E F) (h : ∀ n, f.levelMap n = g.levelMap n) : f = g := by
  cases f; cases g
  simp only [mk.injEq]
  funext n
  exact h n

theorem id_comp (f : SpectrumHom E F) : comp (id E) f = f := by
  apply ext
  intro n
  simp only [comp_levelMap, id_levelMap]
  rfl

theorem comp_id (f : SpectrumHom E F) : comp f (id F) = f := by
  apply ext
  intro n
  simp only [comp_levelMap, id_levelMap]
  rfl

theorem comp_assoc (f : SpectrumHom E F) (g : SpectrumHom F G) (h : SpectrumHom G H) :
    comp (comp f g) h = comp f (comp g h) := by
  apply ext
  intro n
  simp only [comp_levelMap, Category.assoc]

end SpectrumHom

/-! ## Category Instance -/

instance : Category Spectrum where
  Hom := SpectrumHom
  id := SpectrumHom.id
  comp f g := SpectrumHom.comp f g
  id_comp := SpectrumHom.id_comp
  comp_id := SpectrumHom.comp_id
  assoc f g h := SpectrumHom.comp_assoc f g h

namespace Spectrum

/-! ## Basic Examples -/

/-- The trivial spectrum: all spaces are the one-point space. -/
def trivial : Spectrum where
  space := fun _ => PointedTopSpace.point
  structureMap := fun _ => {
    toFun := fun _ => constLoop PointedTopSpace.point
    continuous_toFun := continuous_const
    map_basepoint := rfl
  }

/-- The suspension spectrum of a pointed space X.
    The n-th level is Σ^n X (n-fold reduced suspension).
    Structure maps are the unit of the Σ ⊣ Ω adjunction: η : Σ^n X → Ω(Σ^{n+1} X). -/
def suspensionSpectrum (X : PointedTopSpace) : Spectrum where
  space := fun n => iteratedSuspension n X
  structureMap := fun n => suspensionUnit (iteratedSuspension n X)

/-- Notation for suspension spectrum. -/
scoped notation "Σ^∞" => suspensionSpectrum

/-! ## Ω-Spectra -/

/-- An Ω-spectrum is a spectrum where all adjoint structure maps
    ε_n : E_n → ΩE_{n+1} are weak homotopy equivalences, i.e., they induce
    bijections on all homotopy groups π_k for k ≥ 0.

    This is the standard definition from algebraic topology. -/
def IsOmegaSpectrum (E : Spectrum) : Prop :=
  ∀ n, IsWeakHomotopyEquivalence (E.ε n)

/-- The sphere spectrum S is the suspension spectrum of the two-point space S⁰. -/
def sphereSpectrum : Spectrum := suspensionSpectrum PointedTopSpace.sphere0

/-- Notation for the sphere spectrum. -/
scoped notation "𝕊" => sphereSpectrum

end Spectrum

end Topology
