/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.Topology.Homotopy.Pointed

/-!
# Wedge Sum and Smash Product

This file defines the wedge sum and smash product of pointed topological spaces,
which are fundamental constructions in homotopy theory.

## Main Definitions

* `PointedTopSpace.wedgeSum` - The wedge sum X ∨ Y (coproduct in pointed spaces)
* `PointedTopSpace.smashProduct` - The smash product X ∧ Y

## Mathematical Background

For pointed spaces (X, x₀) and (Y, y₀):
- The wedge sum X ∨ Y is the disjoint union X ⊔ Y with x₀ and y₀ identified.
  This is the coproduct in the category of pointed spaces.
- The smash product X ∧ Y is (X × Y) / (X ∨ Y), where we collapse
  X × {y₀} ∪ {x₀} × Y to a point.

## References

* May, "A Concise Course in Algebraic Topology", Chapter 8
* Hatcher, "Algebraic Topology", Chapter 0
-/

universe u v

open CategoryTheory TopologicalSpace

namespace PointedTopSpace

variable (X Y Z : PointedTopSpace.{u})

/-! ## Wedge Sum -/

section WedgeSum

/-- The underlying type of the wedge sum is the disjoint union X ⊔ Y with
    the basepoints identified. We represent this as a quotient of Sum. -/
def wedgeSumRel : (X.carrier ⊕ Y.carrier) → (X.carrier ⊕ Y.carrier) → Prop :=
  fun p q => p = q ∨ (p = Sum.inl X.basepoint ∧ q = Sum.inr Y.basepoint) ∨
                      (p = Sum.inr Y.basepoint ∧ q = Sum.inl X.basepoint)

/-- The wedge sum relation is reflexive. -/
theorem wedgeSumRel_refl : Reflexive (wedgeSumRel X Y) :=
  fun _ => Or.inl rfl

/-- The wedge sum relation is symmetric. -/
theorem wedgeSumRel_symm : Symmetric (wedgeSumRel X Y) := by
  intro p q h
  cases h with
  | inl h => exact Or.inl h.symm
  | inr h =>
    cases h with
    | inl h => exact Or.inr (Or.inr ⟨h.2, h.1⟩)
    | inr h => exact Or.inr (Or.inl ⟨h.2, h.1⟩)

/-- The wedge sum relation is transitive. -/
theorem wedgeSumRel_trans : Transitive (wedgeSumRel X Y) := by
  intro p q r hpq hqr
  cases hpq with
  | inl hpq => rw [hpq]; exact hqr
  | inr hpq =>
    cases hqr with
    | inl hqr => rw [← hqr]; exact Or.inr hpq
    | inr hqr =>
      cases hpq with
      | inl hpq =>
        -- p = inl x₀, q = inr y₀
        cases hqr with
        | inl hqr =>
          -- q = inl x₀, r = inr y₀, but q = inr y₀ ≠ inl x₀
          have h1 : q = Sum.inr Y.basepoint := hpq.2
          have h2 : q = Sum.inl X.basepoint := hqr.1
          rw [h1] at h2
          cases h2
        | inr hqr =>
          -- q = inr y₀, r = inl x₀, so p = inl x₀ = r
          rw [hpq.1, hqr.2]
          exact Or.inl rfl
      | inr hpq =>
        -- p = inr y₀, q = inl x₀
        cases hqr with
        | inl hqr =>
          -- q = inl x₀, r = inr y₀, so p = inr y₀ = r
          rw [hpq.1, hqr.2]
          exact Or.inl rfl
        | inr hqr =>
          -- q = inr y₀, r = inl x₀, but q = inl x₀ ≠ inr y₀
          have h1 : q = Sum.inl X.basepoint := hpq.2
          have h2 : q = Sum.inr Y.basepoint := hqr.1
          rw [h1] at h2
          cases h2

/-- The setoid for the wedge sum. -/
def wedgeSumSetoid : Setoid (X.carrier ⊕ Y.carrier) where
  r := wedgeSumRel X Y
  iseqv := {
    refl := wedgeSumRel_refl X Y
    symm := fun h => wedgeSumRel_symm X Y h
    trans := fun h1 h2 => wedgeSumRel_trans X Y h1 h2
  }

/-- The underlying type of the wedge sum. -/
def WedgeSumType : Type u := Quotient (wedgeSumSetoid X Y)

/-- The wedge sum inherits the quotient topology. -/
instance : TopologicalSpace (WedgeSumType X Y) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

/-- The basepoint of the wedge sum (the common image of x₀ and y₀). -/
def wedgeSumBasepoint : WedgeSumType X Y :=
  Quotient.mk (wedgeSumSetoid X Y) (Sum.inl X.basepoint)

/-- The wedge sum of two pointed spaces. -/
def wedgeSum : PointedTopSpace where
  carrier := WedgeSumType X Y
  topology := inferInstance
  basepoint := wedgeSumBasepoint X Y

/-- Notation for wedge sum. -/
scoped infixl:65 " ∨₊ " => wedgeSum

/-- The left inclusion into the wedge sum. -/
def wedgeInl : X ⟶ X ∨₊ Y where
  toFun := fun x => Quotient.mk (wedgeSumSetoid X Y) (Sum.inl x)
  continuous_toFun := continuous_quotient_mk'.comp continuous_inl
  map_basepoint := rfl

/-- The right inclusion into the wedge sum. -/
def wedgeInr : Y ⟶ X ∨₊ Y where
  toFun := fun y => Quotient.mk (wedgeSumSetoid X Y) (Sum.inr y)
  continuous_toFun := continuous_quotient_mk'.comp continuous_inr
  map_basepoint := by
    simp only [wedgeSum, wedgeSumBasepoint]
    apply Quotient.sound
    -- Need to show: wedgeSumRel (Sum.inr y₀) (Sum.inl x₀)
    right; right
    exact ⟨rfl, rfl⟩

end WedgeSum

/-! ## Smash Product -/

section SmashProduct

/-- A point (x, y) in X × Y is in the "wedge subset" if x = x₀ or y = y₀. -/
def inWedgeSubset (p : X.carrier × Y.carrier) : Prop :=
  p.1 = X.basepoint ∨ p.2 = Y.basepoint

/-- The equivalence relation for the smash product: two points are equivalent
    if they are equal or both lie in the wedge subset. -/
def smashRel : (X.carrier × Y.carrier) → (X.carrier × Y.carrier) → Prop :=
  fun p q => p = q ∨ (inWedgeSubset X Y p ∧ inWedgeSubset X Y q)

/-- The smash relation is reflexive. -/
theorem smashRel_refl : Reflexive (smashRel X Y) :=
  fun _ => Or.inl rfl

/-- The smash relation is symmetric. -/
theorem smashRel_symm : Symmetric (smashRel X Y) := by
  intro p q h
  cases h with
  | inl h => exact Or.inl h.symm
  | inr h => exact Or.inr ⟨h.2, h.1⟩

/-- The smash relation is transitive. -/
theorem smashRel_trans : Transitive (smashRel X Y) := by
  intro p q r hpq hqr
  cases hpq with
  | inl hpq => rw [hpq]; exact hqr
  | inr hpq =>
    cases hqr with
    | inl hqr => rw [← hqr]; exact Or.inr hpq
    | inr hqr => exact Or.inr ⟨hpq.1, hqr.2⟩

/-- The setoid for the smash product. -/
def smashSetoid : Setoid (X.carrier × Y.carrier) where
  r := smashRel X Y
  iseqv := {
    refl := smashRel_refl X Y
    symm := fun h => smashRel_symm X Y h
    trans := fun h1 h2 => smashRel_trans X Y h1 h2
  }

/-- The underlying type of the smash product. -/
def SmashProductType : Type u := Quotient (smashSetoid X Y)

/-- The smash product inherits the quotient topology. -/
instance : TopologicalSpace (SmashProductType X Y) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

/-- The basepoint of the smash product (the equivalence class of (x₀, y₀)). -/
def smashBasepoint : SmashProductType X Y :=
  Quotient.mk (smashSetoid X Y) (X.basepoint, Y.basepoint)

/-- The smash product of two pointed spaces. -/
def smashProduct : PointedTopSpace where
  carrier := SmashProductType X Y
  topology := inferInstance
  basepoint := smashBasepoint X Y

/-- Notation for smash product. -/
scoped infixl:70 " ∧₊ " => smashProduct

/-- The quotient map X × Y → X ∧ Y. -/
def smashQuotientMap : X.carrier × Y.carrier → SmashProductType X Y :=
  Quotient.mk (smashSetoid X Y)

/-- The quotient map is continuous. -/
theorem continuous_smashQuotientMap : Continuous (smashQuotientMap X Y) :=
  continuous_quotient_mk'

end SmashProduct

/-! ## Functoriality of Smash Product -/

section SmashFunctoriality

variable {X Y X' Y' : PointedTopSpace.{u}}

/-- Helper function for smash map before quotienting. -/
def smashMapAux (f : X ⟶ X') (g : Y ⟶ Y') : X.carrier × Y.carrier → SmashProductType X' Y' :=
  fun p => Quotient.mk (smashSetoid X' Y') (f.toFun p.1, g.toFun p.2)

/-- The smash map respects the equivalence relation. -/
theorem smashMapAux_respects (f : X ⟶ X') (g : Y ⟶ Y') :
    ∀ a b, smashSetoid X Y a b → smashMapAux f g a = smashMapAux f g b := by
  intro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  cases h with
  | inl h =>
    have heq : (x₁, y₁) = (x₂, y₂) := h
    rw [heq]
  | inr h =>
    unfold smashMapAux
    apply Quotient.sound
    right
    constructor
    · -- (f x₁, g y₁) in wedge subset
      unfold inWedgeSubset at h ⊢
      simp only at h ⊢
      cases h.1 with
      | inl hx => left; rw [hx, f.map_basepoint]
      | inr hy => right; rw [hy, g.map_basepoint]
    · -- (f x₂, g y₂) in wedge subset
      unfold inWedgeSubset at h ⊢
      simp only at h ⊢
      cases h.2 with
      | inl hx => left; rw [hx, f.map_basepoint]
      | inr hy => right; rw [hy, g.map_basepoint]

/-- The smash product is functorial: given f : X → X' and g : Y → Y',
    we get f ∧ g : X ∧ Y → X' ∧ Y'. -/
def smashMap (f : X ⟶ X') (g : Y ⟶ Y') : (X ∧₊ Y) ⟶ (X' ∧₊ Y') where
  toFun := Quotient.lift (smashMapAux f g) (smashMapAux_respects f g)
  continuous_toFun := by
    have hcont : Continuous (smashMapAux f g) := by
      unfold smashMapAux
      apply continuous_quotient_mk'.comp
      exact (f.continuous.comp continuous_fst).prodMk (g.continuous.comp continuous_snd)
    exact hcont.quotient_lift _
  map_basepoint := by
    show Quotient.lift _ _ (Quotient.mk (smashSetoid X Y) (X.basepoint, Y.basepoint)) =
         Quotient.mk (smashSetoid X' Y') (X'.basepoint, Y'.basepoint)
    simp only [Quotient.lift_mk]
    unfold smashMapAux
    apply Quotient.sound
    right
    constructor
    · left; exact f.map_basepoint
    · left; rfl

end SmashFunctoriality

/-! ## Symmetry of Smash Product -/

section SmashSymmetry

variable (X Y : PointedTopSpace.{u})

/-- Helper function for smash symmetry. -/
def smashSymmAux : X.carrier × Y.carrier → SmashProductType Y X :=
  fun p => Quotient.mk (smashSetoid Y X) (p.2, p.1)

/-- The symmetry map respects the equivalence relation. -/
theorem smashSymmAux_respects :
    ∀ a b, smashSetoid X Y a b → smashSymmAux X Y a = smashSymmAux X Y b := by
  intro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  cases h with
  | inl h =>
    have heq : (x₁, y₁) = (x₂, y₂) := h
    rw [heq]
  | inr h =>
    simp only [smashSymmAux]
    apply Quotient.sound
    right
    constructor
    · cases h.1 with
      | inl hx => right; exact hx
      | inr hy => left; exact hy
    · cases h.2 with
      | inl hx => right; exact hx
      | inr hy => left; exact hy

/-- The smash product is symmetric: X ∧ Y ≅ Y ∧ X. -/
def smashSymm : (X ∧₊ Y) ⟶ (Y ∧₊ X) where
  toFun := Quotient.lift (smashSymmAux X Y) (smashSymmAux_respects X Y)
  continuous_toFun := by
    have hcont : Continuous (smashSymmAux X Y) := by
      unfold smashSymmAux
      apply continuous_quotient_mk'.comp
      exact continuous_snd.prodMk continuous_fst
    exact hcont.quotient_lift _
  map_basepoint := rfl

/-- The symmetry map is an isomorphism. -/
theorem smashSymm_symm : smashSymm X Y ≫ smashSymm Y X = 𝟙 (X ∧₊ Y) := by
  apply Hom.ext
  funext p
  induction p using Quotient.ind
  rename_i xy
  simp only [comp_toFun, Function.comp_apply, id_toFun]
  unfold smashSymm
  simp only [Quotient.lift_mk]
  unfold smashSymmAux
  simp only [Quotient.lift_mk, Prod.mk.eta, id_eq]

end SmashSymmetry

/-! ## Reduced Cone -/

section ReducedCone

/-- The reduced cone CX is the smash product with the unit interval.
    CX = X ∧ I₊ where I₊ is [0,1] pointed at 0. -/
def reducedCone (X : PointedTopSpace) : PointedTopSpace :=
  X ∧₊ pointedUnitInterval

/-- Notation for reduced cone. -/
scoped prefix:max "C₊" => reducedCone

/-- The base inclusion X → CX sending x to (x, 1). -/
def coneBase (X : PointedTopSpace) : X ⟶ C₊ X where
  toFun := fun x => smashQuotientMap X pointedUnitInterval (x, ⟨1, unitInterval.one_mem⟩)
  continuous_toFun := (continuous_smashQuotientMap X pointedUnitInterval).comp
    (continuous_id.prodMk continuous_const)
  map_basepoint := by
    -- (x₀, 1) is in the wedge subset since x₀ = basepoint
    apply Quotient.sound
    right
    constructor
    · left; rfl
    · left; rfl

end ReducedCone

end PointedTopSpace
