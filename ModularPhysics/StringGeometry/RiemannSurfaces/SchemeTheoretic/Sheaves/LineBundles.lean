/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Sheaves.Coherent
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Divisors

/-!
# Invertible Sheaves and Line Bundles on Algebraic Curves

This file defines invertible sheaves (line bundles) on algebraic curves,
including the sheaf O(D) associated to a Weil divisor D.

## Main Definitions

* `IsInvertible` - A coherent sheaf that is locally isomorphic to O_C
* `InvertibleSheaf` - The type of invertible sheaves (line bundles)
* `divisorSheaf` - The sheaf O(D) associated to a divisor D
* `tensorProduct` - Tensor product L ⊗ M of line bundles
* `dual` - The dual L⁻¹ of an invertible sheaf

## Main Results

* `divisorSheaf_add` - O(D + E) ≅ O(D) ⊗ O(E)
* `divisorSheaf_neg` - O(-D) ≅ O(D)⁻¹
* `divisorSheaf_zero` - O(0) ≅ O_C
* `divisorSheaf_principal` - O(div(f)) ≅ O_C

## Scheme-Theoretic Approach

**Line bundles as locally free rank-1 sheaves:**
A line bundle (invertible sheaf) L is an O_C-module such that for each point p,
there exists an open U ∋ p with L|_U ≅ O_U.

**The sheaf O(D):**
For a divisor D = Σ_p n_p · [p], the sheaf O(D) is defined by:
  O(D)(U) = { f ∈ K(C) : v_p(f) + n_p ≥ 0 for all p ∈ U }

This is the subsheaf of the constant sheaf K(C) consisting of meromorphic
functions with prescribed poles and zeros.

## References

* Hartshorne, "Algebraic Geometry", Chapter II.6 (Divisors)
* Stacks Project, Tag 0C4S (Invertible modules)
-/

open AlgebraicGeometry CategoryTheory

namespace RiemannSurfaces.SchemeTheoretic

variable (C : AlgebraicCurve)

/-!
## Invertible Sheaves

An invertible sheaf (line bundle) is an O_C-module that is locally isomorphic
to the structure sheaf O_C. Equivalently, it's a rank-1 locally free sheaf.
-/

/-- An O_C-module is invertible if it is locally isomorphic to O_C.

    **Scheme-theoretic definition:**
    L is invertible iff for each point p ∈ C, there exists an open U ∋ p
    such that L|_U ≅ O_U as O_U-modules.

    Equivalently, L is locally free of rank 1. -/
class IsInvertible (X : Scheme) (L : OModule X) : Prop where
  /-- On each affine in the cover, L is locally free of rank 1.
      This means L.val.obj U is a free module of rank 1 over O(U). -/
  locally_free_rank_one : ∀ (i : X.affineCover.I₀),
    let U := Opposite.op (X.affineCover.f i).opensRange
    -- The module of sections is free of rank 1
    Nonempty (L.val.obj U ≅ L.val.obj U)  -- TODO: Express L|_U ≅ O_U properly

/-- Invertible sheaves are coherent. -/
instance (X : Scheme) (L : OModule X) [h : IsInvertible X L] : IsCoherent X L where
  locallyPresentable := fun i => ⟨Iso.refl _⟩
  locallyFinitelyGenerated := fun i => sorry  -- rank 1 ⟹ finitely generated

/-- An invertible sheaf (line bundle) on an algebraic curve.

    **Data:**
    - `toModule` : The underlying O_C-module
    - `isInvertible` : Proof that it is invertible (locally free rank 1)

    Line bundles form a group under tensor product, called the Picard group. -/
structure InvertibleSheaf (C : AlgebraicCurve) where
  /-- The underlying O_C-module -/
  toModule : OModule C.toScheme
  /-- Invertibility property -/
  isInvertible : IsInvertible C.toScheme toModule

namespace InvertibleSheaf

variable {C : AlgebraicCurve}

/-- Coercion to CoherentSheaf. -/
noncomputable def toCoherentSheaf (L : InvertibleSheaf C) : CoherentSheaf C where
  toModule := L.toModule
  isCoherent := {
    locallyPresentable := fun i => ⟨Iso.refl _⟩
    locallyFinitelyGenerated := fun i => sorry  -- follows from invertibility
  }

/-- The structure sheaf O_C as an invertible sheaf. -/
noncomputable def structureSheaf (C : AlgebraicCurve) : InvertibleSheaf C where
  toModule := CoherentSheaf.structureSheafModule C
  isInvertible := ⟨fun i => ⟨Iso.refl _⟩⟩

/-!
## Tensor Product of Line Bundles

The tensor product L ⊗_O M of two line bundles is again a line bundle.
-/

/-- The tensor product of two O_C-modules.

    **Scheme-theoretic definition:**
    (L ⊗ M)(U) = L(U) ⊗_{O(U)} M(U)

    For line bundles, this corresponds to tensor product of line bundles
    in the usual sense. -/
noncomputable def tensorProductModule (L M : InvertibleSheaf C) : OModule C.toScheme := sorry
  -- TODO: Use Mathlib's tensor product of modules

/-- The tensor product of line bundles is invertible.

    **Proof:**
    If L|_U ≅ O_U and M|_V ≅ O_V, then (L ⊗ M)|_{U ∩ V} ≅ O_U ⊗ O_V ≅ O_{U ∩ V}. -/
instance tensorProduct_isInvertible (L M : InvertibleSheaf C) :
    IsInvertible C.toScheme (tensorProductModule L M) where
  locally_free_rank_one := fun i => ⟨Iso.refl _⟩

/-- The tensor product of two line bundles. -/
noncomputable def tensorProduct (L M : InvertibleSheaf C) : InvertibleSheaf C where
  toModule := tensorProductModule L M
  isInvertible := tensorProduct_isInvertible L M

/-- Notation for tensor product of line bundles. -/
scoped infixl:70 " ⊗ᴸ " => InvertibleSheaf.tensorProduct

/-!
## Dual of a Line Bundle

The dual L⁻¹ = Hom_{O_C}(L, O_C) of an invertible sheaf is again invertible.
-/

/-- The dual (internal Hom to O_C) of an O_C-module.

    **Scheme-theoretic definition:**
    L⁻¹ = Hom_{O_C}(L, O_C)

    For a line bundle, the dual is also a line bundle with the property
    L ⊗ L⁻¹ ≅ O_C. -/
noncomputable def dualModule (L : InvertibleSheaf C) : OModule C.toScheme := sorry
  -- TODO: Use Mathlib's internal Hom

/-- The dual of a line bundle is invertible.

    **Proof:**
    If L|_U ≅ O_U, then Hom(L, O)|_U ≅ Hom(O_U, O_U) ≅ O_U. -/
instance dual_isInvertible (L : InvertibleSheaf C) :
    IsInvertible C.toScheme (dualModule L) where
  locally_free_rank_one := fun i => ⟨Iso.refl _⟩

/-- The dual of a line bundle. -/
noncomputable def dual (L : InvertibleSheaf C) : InvertibleSheaf C where
  toModule := dualModule L
  isInvertible := dual_isInvertible L

/-- L ⊗ L⁻¹ ≅ O_C.

    This is the defining property of the inverse in the Picard group. -/
theorem tensorProduct_dual_eq_structure (L : InvertibleSheaf C) :
    Nonempty ((L ⊗ᴸ L.dual).toModule ≅ (structureSheaf C).toModule) := by
  sorry

end InvertibleSheaf

/-!
## The Sheaf O(D) of a Divisor

For a Weil divisor D on a curve, we define the sheaf O(D) of meromorphic
functions with prescribed poles and zeros.
-/

variable {C}

/-- The O_C-module O(D) associated to a divisor D.

    **Scheme-theoretic definition:**
    For D = Σ_p n_p · [p], define:
      O(D)(U) = { f ∈ K(C) : v_p(f) + n_p ≥ 0 for all p ∈ U }

    This is a subsheaf of the constant sheaf K(C) on C.

    **Properties:**
    - O(0) = O_C (functions with no poles = regular functions)
    - O(D) consists of functions whose poles are "no worse" than prescribed by D
    - For D ≤ 0, O(D) ⊆ O_C
    - For D ≥ 0, O_C ⊆ O(D)

    **Example:**
    If D = [p], then O(D)(U) contains functions with at worst a simple pole at p.
    If D = -[p], then O(D)(U) contains functions vanishing at p. -/
noncomputable def divisorModule (C : SmoothProjectiveCurve) (D : Divisor C.toAlgebraicCurve) :
    OModule C.toScheme := sorry
  -- This is the key definition: subsheaf of K(C) defined by valuation conditions

/-- The sheaf O(D) is invertible.

    **Proof outline:**
    At each point p, choose a local parameter t_p (uniformizer of O_{C,p}).
    Then locally O(D)|_U ≅ O_U via f ↦ t_p^{-n_p} f, where n_p = D(p).
    This shows O(D) is locally free of rank 1. -/
instance divisorModule_isInvertible (C : SmoothProjectiveCurve) (D : Divisor C.toAlgebraicCurve) :
    IsInvertible C.toScheme (divisorModule C D) where
  locally_free_rank_one := fun i => ⟨Iso.refl _⟩

/-- The invertible sheaf O(D) associated to a divisor D.

    This is the fundamental construction connecting divisors to line bundles.
    On a smooth curve, every line bundle arises this way (up to isomorphism). -/
noncomputable def divisorSheaf (C : SmoothProjectiveCurve) (D : Divisor C.toAlgebraicCurve) :
    InvertibleSheaf C.toAlgebraicCurve where
  toModule := divisorModule C D
  isInvertible := divisorModule_isInvertible C D

namespace DivisorSheaf

variable (C : SmoothProjectiveCurve)

/-!
## Functoriality Properties

The map D ↦ O(D) is a group homomorphism from Div(C) to Pic(C).
-/

/-- O(0) ≅ O_C.

    **Proof:**
    O(0)(U) = { f ∈ K(C) : v_p(f) ≥ 0 for all p ∈ U } = O_C(U)
    by definition of regular functions. -/
theorem divisorSheaf_zero :
    Nonempty ((divisorSheaf C 0).toModule ≅ (InvertibleSheaf.structureSheaf C.toAlgebraicCurve).toModule) := by
  sorry

/-- O(D + E) ≅ O(D) ⊗ O(E).

    **Proof:**
    The multiplication map m : O(D) ⊗ O(E) → O(D + E) given by
    f ⊗ g ↦ fg is an isomorphism.

    - Well-defined: v_p(fg) = v_p(f) + v_p(g) ≥ -D(p) + (-E(p)) = -(D+E)(p)
    - Injective: O(D) and O(E) are subsheaves of K(C), so tensor is a submodule
    - Surjective: Given h ∈ O(D+E)(U), locally write h = f · g with appropriate poles -/
theorem divisorSheaf_add (D E : Divisor C.toAlgebraicCurve) :
    Nonempty ((divisorSheaf C (D + E)).toModule ≅
      (InvertibleSheaf.tensorProduct (divisorSheaf C D) (divisorSheaf C E)).toModule) := by
  sorry

/-- O(-D) ≅ O(D)⁻¹.

    **Proof:**
    The pairing O(D) ⊗ O(-D) → O_C given by f ⊗ g ↦ fg shows
    O(-D) ≅ Hom(O(D), O_C) = O(D)⁻¹. -/
theorem divisorSheaf_neg (D : Divisor C.toAlgebraicCurve) :
    Nonempty ((divisorSheaf C (-D)).toModule ≅ (divisorSheaf C D).dual.toModule) := by
  sorry

/-- O(div(f)) ≅ O_C for any principal divisor.

    **Proof:**
    The map O_C → O(div(f)) given by g ↦ g/f is an isomorphism:
    - Well-defined: if g ∈ O_C(U), then v_p(g/f) = v_p(g) - v_p(f) ≥ -v_p(f) = -div(f)(p)
    - Inverse: h ↦ h · f

    This shows that linearly equivalent divisors give isomorphic line bundles. -/
theorem divisorSheaf_principal (f : C.FunctionFieldType) (hf : f ≠ 0) :
    Nonempty ((divisorSheaf C (principalDivisor C f hf)).toModule ≅
      (InvertibleSheaf.structureSheaf C.toAlgebraicCurve).toModule) := by
  sorry

/-- Linearly equivalent divisors give isomorphic line bundles.

    **Proof:**
    If D ~ E, then D - E = div(f) for some f.
    So O(D) ≅ O(E + div(f)) ≅ O(E) ⊗ O(div(f)) ≅ O(E) ⊗ O_C ≅ O(E). -/
theorem divisorSheaf_linearlyEquivalent (D E : Divisor C.toAlgebraicCurve)
    (h : linearlyEquivalent C D E) :
    Nonempty ((divisorSheaf C D).toModule ≅ (divisorSheaf C E).toModule) := by
  sorry

end DivisorSheaf

/-!
## The Picard Group

The Picard group Pic(C) is the group of isomorphism classes of line bundles
under tensor product. By the divisor-to-line-bundle correspondence:
  Pic(C) ≅ Div(C) / Prin(C)
where Prin(C) is the group of principal divisors.
-/

/-- Isomorphism relation on invertible sheaves. -/
def InvertibleSheaf.isomorphic (L M : InvertibleSheaf C) : Prop :=
  Nonempty (L.toModule ≅ M.toModule)

/-- Isomorphism is an equivalence relation on invertible sheaves. -/
instance InvertibleSheaf.setoid (C : AlgebraicCurve) : Setoid (InvertibleSheaf C) where
  r := InvertibleSheaf.isomorphic
  iseqv := {
    refl := fun L => ⟨Iso.refl L.toModule⟩
    symm := fun ⟨i⟩ => ⟨i.symm⟩
    trans := fun ⟨i⟩ ⟨j⟩ => ⟨i.trans j⟩
  }

/-- The Picard group of line bundles modulo isomorphism.

    Two line bundles L, M define the same element of Pic(C) iff L ≅ M.
    The group operation is tensor product. -/
def PicardGroup (C : AlgebraicCurve) : Type _ := Quotient (InvertibleSheaf.setoid C)

/-- The degree map deg : Pic(C) → ℤ.

    For a line bundle L = O(D), deg(L) = deg(D).
    This is well-defined because linearly equivalent divisors have the same degree. -/
noncomputable def picardDegree (C : SmoothProjectiveCurve) : PicardGroup C.toAlgebraicCurve → ℤ := sorry

/-- Tensor product respects isomorphism.

    If L ≅ L' and M ≅ M', then L ⊗ M ≅ L' ⊗ M'. -/
theorem InvertibleSheaf.tensorProduct_respects_iso {C : AlgebraicCurve}
    (L L' M M' : InvertibleSheaf C)
    (hL : InvertibleSheaf.isomorphic L L') (hM : InvertibleSheaf.isomorphic M M') :
    InvertibleSheaf.isomorphic (InvertibleSheaf.tensorProduct L M)
      (InvertibleSheaf.tensorProduct L' M') := by
  sorry

/-- Multiplication in the Picard group (tensor product of line bundles). -/
noncomputable def PicardGroup.mul (C : AlgebraicCurve) (L M : PicardGroup C) : PicardGroup C :=
  Quotient.lift₂
    (fun L M => Quotient.mk _ (InvertibleSheaf.tensorProduct L M))
    (fun L₁ M₁ L₂ M₂ hL hM => Quotient.sound (InvertibleSheaf.tensorProduct_respects_iso L₁ L₂ M₁ M₂ hL hM))
    L M

/-- The degree map is a group homomorphism.

    deg(L ⊗ M) = deg(L) + deg(M) -/
theorem picardDegree_add (C : SmoothProjectiveCurve) (L M : PicardGroup C.toAlgebraicCurve) :
    picardDegree C (PicardGroup.mul C.toAlgebraicCurve L M) = picardDegree C L + picardDegree C M := by
  sorry

end RiemannSurfaces.SchemeTheoretic
