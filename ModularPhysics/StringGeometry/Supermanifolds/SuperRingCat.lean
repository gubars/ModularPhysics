/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.
-/
import ModularPhysics.StringGeometry.Supermanifolds.Superalgebra
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# The Category of Supercommutative Algebras

This file defines `SuperRingCat`, the category of supercommutative algebras,
following the pattern of `CommRingCat` from Mathlib.

## Main definitions

* `SuperRingCat R` - The category of supercommutative R-algebras
* `SuperRingCat.Hom` - Morphisms are graded algebra homomorphisms
* `IsSuperLocalRing` - A super ring where the even part is local

## Design decisions

We follow Mathlib's bundled category pattern:
- Objects are bundled (carrier + instances)
- Morphisms are bundled ring homomorphisms preserving grading
- Category structure enables use with `SheafedSpace`

The key insight is that the **even part** of a supercommutative algebra is
commutative, which is essential for defining local stalks.

## References

* Mathlib/Algebra/Category/Ring/Basic.lean
* Deligne, P., Morgan, J. "Notes on Supersymmetry"
-/

universe u v

open CategoryTheory

namespace Supermanifolds

/-!
## Graded Algebra Homomorphisms

A morphism of superalgebras must preserve the ℤ/2-grading.
-/

/-- A graded algebra homomorphism between superalgebras.
    Preserves addition, multiplication, unit, and the ℤ/2-grading. -/
structure SuperAlgHom {R : Type*} [CommRing R] (A B : SuperAlgebra R) where
  /-- The underlying function -/
  toFun : A.carrier → B.carrier
  /-- Respects addition -/
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  /-- Respects multiplication -/
  map_mul' : ∀ x y, toFun (x * y) = toFun x * toFun y
  /-- Respects the unit -/
  map_one' : toFun 1 = 1
  /-- Respects zero -/
  map_zero' : toFun 0 = 0
  /-- Preserves the even grading -/
  map_even : ∀ x, x ∈ A.even → toFun x ∈ B.even
  /-- Preserves the odd grading -/
  map_odd : ∀ x, x ∈ A.odd → toFun x ∈ B.odd

namespace SuperAlgHom

variable {R : Type*} [CommRing R] {A B C : SuperAlgebra R}

instance : CoeFun (SuperAlgHom A B) (fun _ => A.carrier → B.carrier) :=
  ⟨SuperAlgHom.toFun⟩

@[simp]
theorem toFun_eq_coe (f : SuperAlgHom A B) : f.toFun = f := rfl

@[ext]
theorem ext {f g : SuperAlgHom A B} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g; simp only [mk.injEq]; ext x; exact h x

/-- Identity homomorphism -/
def id : SuperAlgHom A A where
  toFun := _root_.id
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_one' := rfl
  map_zero' := rfl
  map_even _ hx := hx
  map_odd _ hx := hx

/-- Composition of homomorphisms -/
def comp (g : SuperAlgHom B C) (f : SuperAlgHom A B) : SuperAlgHom A C where
  toFun := g.toFun ∘ f.toFun
  map_add' := fun x y => by simp only [Function.comp_apply]; rw [f.map_add', g.map_add']
  map_mul' := fun x y => by simp only [Function.comp_apply]; rw [f.map_mul', g.map_mul']
  map_one' := by simp only [Function.comp_apply]; rw [f.map_one', g.map_one']
  map_zero' := by simp only [Function.comp_apply]; rw [f.map_zero', g.map_zero']
  map_even := fun x hx => g.map_even _ (f.map_even x hx)
  map_odd := fun x hx => g.map_odd _ (f.map_odd x hx)

@[simp]
theorem id_apply (x : A.carrier) : (id : SuperAlgHom A A) x = x := rfl

@[simp]
theorem comp_apply (g : SuperAlgHom B C) (f : SuperAlgHom A B) (x : A.carrier) :
    (g.comp f) x = g (f x) := rfl

theorem comp_assoc {D : SuperAlgebra R} (h : SuperAlgHom C D) (g : SuperAlgHom B C)
    (f : SuperAlgHom A B) : (h.comp g).comp f = h.comp (g.comp f) := by
  ext; simp

theorem id_comp (f : SuperAlgHom A B) : (id).comp f = f := by ext; simp

theorem comp_id (f : SuperAlgHom A B) : f.comp id = f := by ext; simp

end SuperAlgHom

/-!
## Restriction to Even Parts

A graded homomorphism restricts to a ring homomorphism on the even parts.
-/

/-- The restriction of a SuperAlgHom to the even subrings.

    Since f preserves even elements, this is a well-defined ring homomorphism
    A.evenSubring →+* B.evenSubring.

    This is essential for defining local super homomorphisms, since locality
    is defined in terms of the even (commutative) parts. -/
def SuperAlgHom.restrictEven {R : Type*} [CommRing R] {A B : SuperAlgebra R}
    [SuperCommutative A] [SuperCommutative B]
    [SuperAlgebraWithOne A] [SuperAlgebraWithOne B]
    (f : SuperAlgHom A B) : A.evenSubring →+* B.evenSubring where
  toFun x := ⟨f x, f.map_even x x.property⟩
  map_one' := by
    simp only [Subring.coe_one]
    exact Subtype.ext f.map_one'
  map_mul' x y := by
    simp only [Subring.coe_mul]
    exact Subtype.ext (f.map_mul' x y)
  map_zero' := by
    simp only [Subring.coe_zero]
    exact Subtype.ext f.map_zero'
  map_add' x y := by
    simp only [Subring.coe_add]
    exact Subtype.ext (f.map_add' x y)

/-!
## The Category SuperRingCat

We bundle supercommutative algebras into a category.
-/

/-- The category of supercommutative R-algebras.

    Objects are superalgebras with the supercommutative property.
    Morphisms are graded algebra homomorphisms.

    This follows the bundled category pattern from Mathlib. -/
structure SuperRingCat (R : Type*) [CommRing R] where
  /-- The object constructor -/
  of ::
  /-- The underlying superalgebra -/
  algebra : SuperAlgebra R
  /-- The supercommutative property -/
  [superComm : SuperCommutative algebra]

attribute [instance] SuperRingCat.superComm

namespace SuperRingCat

variable {R : Type*} [CommRing R]

/-- The carrier type of a supercommutative algebra -/
def carrier (A : SuperRingCat R) : Type* := A.algebra.carrier

instance : CoeSort (SuperRingCat R) (Type*) :=
  ⟨fun A => A.carrier⟩

/-- The underlying superalgebra -/
def toSuperAlgebra (A : SuperRingCat R) : SuperAlgebra R := A.algebra

/-- Morphisms in the category of supercommutative algebras -/
@[ext]
structure Hom (A B : SuperRingCat R) where
  /-- The underlying graded homomorphism -/
  hom : SuperAlgHom A.algebra B.algebra

/-- Identity morphism -/
def Hom.id (A : SuperRingCat R) : Hom A A := ⟨SuperAlgHom.id⟩

/-- Composition of morphisms -/
def Hom.comp {A B C : SuperRingCat R} (g : Hom B C) (f : Hom A B) : Hom A C :=
  ⟨g.hom.comp f.hom⟩

/-- Category instance for SuperRingCat -/
instance : Category (SuperRingCat R) where
  Hom := Hom
  id := Hom.id
  comp := fun f g => Hom.comp g f  -- Note: Mathlib uses opposite convention

@[simp]
theorem id_hom (A : SuperRingCat R) : (𝟙 A : Hom A A).hom = SuperAlgHom.id := rfl

@[simp]
theorem comp_hom {A B C : SuperRingCat R} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/-- The forgetful functor to types -/
def forget : SuperRingCat R ⥤ Type* where
  obj A := A.carrier
  map f := f.hom.toFun

end SuperRingCat

/-!
## Local Super Rings

A supercommutative algebra is local if its even part is a local ring.
This is the key property for stalks of locally superringed spaces.
-/

/-- A supercommutative algebra is local if:
    1. The even part forms a local commutative ring
    2. All odd elements are nilpotent (in the maximal ideal)

    This generalizes the notion of a local ring to the super setting.
    The residue field A/m ≅ A₀/m₀ is purely even.

    Note: Requires `SuperAlgebraWithOne A` because `evenSubring` needs 1 ∈ even. -/
class IsSuperLocalRing {R : Type*} [CommRing R] (A : SuperAlgebra R)
    [SuperCommutative A] [SuperAlgebraWithOne A] where
  /-- The even part has a unique maximal ideal -/
  even_hasUniqueMaxIdeal : ∃! (m : Ideal A.evenSubring), m.IsMaximal
  /-- All odd elements are nilpotent -/
  odd_nilpotent : ∀ a : A.carrier, a ∈ A.odd → IsNilpotent a

/-- A local morphism of super local rings: maps maximal ideal to maximal ideal.

    For a homomorphism f : A → B of super local rings to be local, we require
    that the restriction to even parts maps the maximal ideal of A.even into
    the maximal ideal of B.even.

    Since IsSuperLocalRing guarantees a unique maximal ideal in each even part,
    we state this as: for all maximal ideals mA, mB (which are uniquely determined),
    elements of mA are mapped by f.restrictEven into mB.

    Note: This is equivalent to requiring f.restrictEven⁻¹(mB) = mA. -/
class IsSuperLocalHom {R : Type*} [CommRing R] {A B : SuperAlgebra R}
    [SuperCommutative A] [SuperCommutative B]
    [SuperAlgebraWithOne A] [SuperAlgebraWithOne B]
    [IsSuperLocalRing A] [IsSuperLocalRing B]
    (f : SuperAlgHom A B) : Prop where
  /-- The restriction to even parts maps the maximal ideal of A into the maximal ideal of B -/
  map_maxIdeal : ∀ (mA : Ideal A.evenSubring) (mB : Ideal B.evenSubring),
    mA.IsMaximal → mB.IsMaximal →
    ∀ x : A.evenSubring, x ∈ mA → f.restrictEven x ∈ mB

/-!
## Properties of Super Local Rings

Note: The key properties `odd_sq_zero` and `even_comm` are in `SuperCommutative` namespace.
They apply to all supercommutative algebras, not just local ones:
- `SuperCommutative.odd_sq_zero`: odd elements square to zero (char ≠ 2)
- `SuperCommutative.even_comm_even`: even elements commute
-/

end Supermanifolds
