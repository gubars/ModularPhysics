/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Constructions
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.UnitInterval

/-!
# Pointed Topological Spaces

This file defines the category of pointed topological spaces, which is fundamental
for stable homotopy theory and the definition of spectra.

## Main Definitions

* `PointedTopSpace` - A topological space with a distinguished basepoint
* `PointedTopSpace.Hom` - Continuous basepoint-preserving maps
* `PointedTopCat` - The category of pointed topological spaces

## Implementation Notes

We define pointed topological spaces as a bundled structure containing both the
carrier type with its topology and the basepoint. This differs from Mathlib's
`Pointed` (which is for types without topology) and allows us to work categorically.

The category `PointedTopCat` has:
- Objects: Pointed topological spaces
- Morphisms: Continuous maps f : X → Y with f(x₀) = y₀

## References

* May, "A Concise Course in Algebraic Topology", Chapter 8
-/

universe u v

open CategoryTheory TopologicalSpace unitInterval

/-- A pointed topological space is a topological space with a distinguished basepoint. -/
structure PointedTopSpace : Type (u + 1) where
  /-- The underlying topological space -/
  carrier : Type u
  /-- The topology on the carrier -/
  [topology : TopologicalSpace carrier]
  /-- The distinguished basepoint -/
  basepoint : carrier

namespace PointedTopSpace

attribute [instance] PointedTopSpace.topology

/-- Coercion from PointedTopSpace to Type. -/
instance : CoeSort PointedTopSpace (Type u) := ⟨PointedTopSpace.carrier⟩

/-- The basepoint notation. -/
notation "pt" => PointedTopSpace.basepoint

/-- Construct a pointed space from a topological space and a point. -/
def of (X : Type u) [TopologicalSpace X] (x₀ : X) : PointedTopSpace :=
  ⟨X, x₀⟩

/-- The underlying TopCat of a pointed space. -/
def toTopCat (X : PointedTopSpace) : TopCat := TopCat.of X.carrier

section Morphisms

/-- A morphism of pointed topological spaces is a continuous map preserving basepoints. -/
@[ext]
structure Hom (X Y : PointedTopSpace) where
  /-- The underlying continuous map -/
  toFun : X.carrier → Y.carrier
  /-- Continuity of the map -/
  continuous_toFun : Continuous toFun
  /-- The map preserves basepoints -/
  map_basepoint : toFun X.basepoint = Y.basepoint

namespace Hom

/-- Coercion to function. -/
instance {X Y : PointedTopSpace} : CoeFun (Hom X Y) (fun _ => X.carrier → Y.carrier) :=
  ⟨Hom.toFun⟩

@[simp]
theorem coe_mk {X Y : PointedTopSpace} (f : X.carrier → Y.carrier) (hc : Continuous f)
    (hp : f X.basepoint = Y.basepoint) : (⟨f, hc, hp⟩ : Hom X Y) = f := rfl

theorem continuous {X Y : PointedTopSpace} (f : Hom X Y) : Continuous f := f.continuous_toFun

@[simp]
theorem map_pt {X Y : PointedTopSpace} (f : Hom X Y) : f X.basepoint = Y.basepoint :=
  f.map_basepoint

/-- The identity morphism on a pointed space. -/
@[simps]
def id (X : PointedTopSpace) : Hom X X where
  toFun := _root_.id
  continuous_toFun := continuous_id
  map_basepoint := rfl

/-- Composition of morphisms of pointed spaces. -/
@[simps]
def comp {X Y Z : PointedTopSpace} (g : Hom Y Z) (f : Hom X Y) : Hom X Z where
  toFun := g.toFun ∘ f.toFun
  continuous_toFun := g.continuous.comp f.continuous
  map_basepoint := by rw [Function.comp_apply, f.map_basepoint, g.map_basepoint]

@[simp]
theorem id_comp {X Y : PointedTopSpace} (f : Hom X Y) : comp (id Y) f = f := by
  ext; rfl

@[simp]
theorem comp_id {X Y : PointedTopSpace} (f : Hom X Y) : comp f (id X) = f := by
  ext; rfl

@[simp]
theorem comp_assoc {W X Y Z : PointedTopSpace} (h : Hom Y Z) (g : Hom X Y) (f : Hom W X) :
    comp h (comp g f) = comp (comp h g) f := by
  ext; rfl

end Hom

end Morphisms

section Category

/-- The category of pointed topological spaces. -/
instance : Category PointedTopSpace where
  Hom := Hom
  id := Hom.id
  comp := fun f g => Hom.comp g f
  id_comp := fun f => Hom.comp_id f
  comp_id := fun f => Hom.id_comp f
  assoc := fun f g h => (Hom.comp_assoc h g f).symm

@[simp]
theorem id_toFun (X : PointedTopSpace) : (𝟙 X : Hom X X).toFun = _root_.id := rfl

@[simp]
theorem comp_toFun {X Y Z : PointedTopSpace} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

end Category

section Examples

/-- The one-point space as a pointed space. -/
def point : PointedTopSpace := of Unit ()

/-- The one-point space is terminal in the category of pointed spaces. -/
def toPoint (X : PointedTopSpace) : X ⟶ point where
  toFun := fun _ => ()
  continuous_toFun := continuous_const
  map_basepoint := rfl

/-- The n-sphere as a pointed space. We use the subspace of ℝ^(n+1) of unit vectors,
    with the "north pole" (0,...,0,1) as basepoint.
    For now, we define S⁰ as a two-point discrete space. -/
def sphere0 : PointedTopSpace where
  carrier := Bool
  topology := ⊥  -- discrete topology
  basepoint := true

/-- The unit interval I = [0,1] as a pointed space with basepoint 0. -/
def pointedUnitInterval : PointedTopSpace :=
  of I ⟨0, unitInterval.zero_mem⟩

end Examples

section Forgetful

/-- The forgetful functor from pointed topological spaces to topological spaces. -/
@[simps]
def forget : PointedTopSpace ⥤ TopCat where
  obj X := TopCat.of X.carrier
  map f := ⟨f.toFun, f.continuous⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end Forgetful

end PointedTopSpace
