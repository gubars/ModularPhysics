/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.Topology.Homotopy.Pointed
import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Weak Homotopy Equivalences

This file defines the induced map on homotopy groups and the notion of weak homotopy equivalence
for pointed topological spaces.

## Main Definitions

* `PointedTopSpace.inducedGenLoop` - The induced map on generalized loops
* `PointedTopSpace.inducedπ` - The induced map on homotopy groups
* `PointedTopSpace.IsWeakHomotopyEquivalence` - A map inducing bijections on all π_n

## Mathematical Background

For a pointed continuous map f : (X, x₀) → (Y, y₀), we get induced maps:
- On GenLoops: γ ↦ f ∘ γ
- On homotopy groups: [γ] ↦ [f ∘ γ]

A weak homotopy equivalence is a map f such that the induced map on π_n is a bijection
for all n ≥ 0.

## References

* May, "A Concise Course in Algebraic Topology", Chapter 9
* Hatcher, "Algebraic Topology", Section 4.1
-/

universe u

open CategoryTheory TopologicalSpace unitInterval Topology.Homotopy

namespace PointedTopSpace

variable {X Y Z : PointedTopSpace.{0}}

/-! ## Induced Map on Generalized Loops -/

section InducedOnGenLoop

/-- The continuous map associated to a pointed map. -/
def toContinuousMap (f : X ⟶ Y) : C(X.carrier, Y.carrier) :=
  ⟨f.toFun, f.continuous⟩

/-- A pointed map f : X → Y induces a map on generalized loops:
    given γ : I^N → X with boundary sent to x₀, we get f ∘ γ : I^N → Y
    with boundary sent to f(x₀) = y₀. -/
def inducedGenLoop (N : Type*) (f : X ⟶ Y) (γ : GenLoop N X.carrier X.basepoint) :
    GenLoop N Y.carrier Y.basepoint where
  val := (toContinuousMap f).comp γ.val
  property := by
    intro y hy
    simp only [ContinuousMap.comp_apply, toContinuousMap]
    rw [γ.property y hy]
    exact f.map_basepoint

/-- The induced map preserves equality of underlying functions. -/
theorem inducedGenLoop_val (N : Type*) (f : X ⟶ Y) (γ : GenLoop N X.carrier X.basepoint) :
    (inducedGenLoop N f γ).val = (toContinuousMap f).comp γ.val := rfl

/-- Induced map preserves homotopy relative to boundary. -/
theorem inducedGenLoop_homotopic (N : Type*) (f : X ⟶ Y)
    {γ₁ γ₂ : GenLoop N X.carrier X.basepoint}
    (h : GenLoop.Homotopic γ₁ γ₂) :
    GenLoop.Homotopic (inducedGenLoop N f γ₁) (inducedGenLoop N f γ₂) := by
  -- Homotopy H : γ₁ ∼ γ₂ gives f ∘ H : f ∘ γ₁ ∼ f ∘ γ₂
  obtain ⟨H⟩ := h
  refine ⟨?_⟩
  -- H is a homotopy rel boundary, so f ∘ H is also a homotopy rel boundary
  have hcomp : (inducedGenLoop N f γ₁).val = (toContinuousMap f).comp γ₁.val := rfl
  have hcomp' : (inducedGenLoop N f γ₂).val = (toContinuousMap f).comp γ₂.val := rfl
  rw [hcomp, hcomp']
  exact H.compContinuousMap (toContinuousMap f)

/-- The setoid relation is preserved by inducedGenLoop. -/
theorem inducedGenLoop_respects_setoid (N : Type*) (f : X ⟶ Y)
    (γ₁ γ₂ : GenLoop N X.carrier X.basepoint)
    (h : (GenLoop.Homotopic.setoid N X.basepoint).r γ₁ γ₂) :
    (GenLoop.Homotopic.setoid N Y.basepoint).r (inducedGenLoop N f γ₁) (inducedGenLoop N f γ₂) :=
  inducedGenLoop_homotopic N f h

/-- The induced map from identity is homotopic to identity on loops. -/
theorem inducedGenLoop_id_homotopic (N : Type*) (γ : GenLoop N X.carrier X.basepoint) :
    GenLoop.Homotopic (inducedGenLoop N (𝟙 X) γ) γ := by
  -- The identity case: id ∘ γ = γ
  apply GenLoop.Homotopic.refl (f := γ) |>.symm.trans
  apply GenLoop.Homotopic.refl

/-- The induced map from composition agrees with composition of induced maps. -/
theorem inducedGenLoop_comp_homotopic (N : Type*) (f : X ⟶ Y) (g : Y ⟶ Z)
    (γ : GenLoop N X.carrier X.basepoint) :
    GenLoop.Homotopic (inducedGenLoop N (f ≫ g) γ) (inducedGenLoop N g (inducedGenLoop N f γ)) := by
  -- (g ∘ f) ∘ γ = g ∘ (f ∘ γ)
  apply GenLoop.Homotopic.refl

/-! ### Compatibility with Group Operations -/

open GenLoop in
/-- The induced map on GenLoops commutes with transAt (the multiplication operation).
    This is because transAt is defined pointwise and inducedGenLoop is just composition:
    f ∘ (transAt i g₁ g₂) = transAt i (f ∘ g₁) (f ∘ g₂) -/
theorem inducedGenLoop_transAt [Nonempty N] [DecidableEq N] (f : X ⟶ Y) (i : N)
    (g₁ g₂ : GenLoop N X.carrier X.basepoint) :
    inducedGenLoop N f (transAt i g₁ g₂) = transAt i (inducedGenLoop N f g₁) (inducedGenLoop N f g₂) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  -- Unfold both sides manually
  simp only [inducedGenLoop, toContinuousMap, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  -- Unfold transAt and copy to get to the underlying function
  unfold transAt copy
  simp only [ContinuousMap.coe_mk]
  -- Now both sides are if-then-else expressions
  split_ifs <;> rfl

end InducedOnGenLoop

/-! ## Induced Map on Homotopy Groups -/

section InducedOnπ

/-- The induced map on the n-th homotopy group π_n(X) → π_n(Y). -/
def inducedπ (n : ℕ) (f : X ⟶ Y) :
    HomotopyGroup.Pi n X.carrier X.basepoint → HomotopyGroup.Pi n Y.carrier Y.basepoint :=
  Quotient.map' (inducedGenLoop (Fin n) f) (inducedGenLoop_respects_setoid (Fin n) f)

/-- The induced map on π_0 (path components). -/
def inducedπ₀ (f : X ⟶ Y) :
    HomotopyGroup.Pi 0 X.carrier X.basepoint → HomotopyGroup.Pi 0 Y.carrier Y.basepoint :=
  inducedπ 0 f

/-- Functoriality: (g ∘ f)_* = g_* ∘ f_*. -/
theorem inducedπ_comp (n : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z) :
    inducedπ n (f ≫ g) = inducedπ n g ∘ inducedπ n f := by
  funext α
  induction α using Quotient.ind
  simp only [inducedπ, Quotient.map'_mk'', Function.comp_apply]
  apply Quotient.sound
  exact inducedGenLoop_comp_homotopic (Fin n) f g _

/-- The identity map induces the identity on homotopy groups. -/
theorem inducedπ_id (n : ℕ) :
    inducedπ n (𝟙 X) = id := by
  funext α
  induction α using Quotient.ind
  simp only [inducedπ, Quotient.map'_mk'', id_eq]
  apply Quotient.sound
  exact inducedGenLoop_id_homotopic (Fin n) _

/-! ### Group Homomorphism Property -/

/-- The induced map on homotopy groups preserves multiplication.
    This makes f_* : π_n(X) → π_n(Y) a group homomorphism for n ≥ 1. -/
theorem inducedπ_mul (n : ℕ) (f : X ⟶ Y)
    (a b : HomotopyGroup.Pi (n + 1) X.carrier X.basepoint) :
    inducedπ (n + 1) f (a * b) = inducedπ (n + 1) f a * inducedπ (n + 1) f b := by
  -- Use quotient induction first
  induction a using Quotient.ind with
  | _ α =>
    induction b using Quotient.ind with
    | _ β =>
      -- The index for transAt
      let i : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
      -- Cast the quotients to HomotopyGroup.Pi explicitly
      let aX : HomotopyGroup.Pi (n + 1) X.carrier X.basepoint := ⟦α⟧
      let bX : HomotopyGroup.Pi (n + 1) X.carrier X.basepoint := ⟦β⟧
      let aY : HomotopyGroup.Pi (n + 1) Y.carrier Y.basepoint := ⟦inducedGenLoop (Fin (n + 1)) f α⟧
      let bY : HomotopyGroup.Pi (n + 1) Y.carrier Y.basepoint := ⟦inducedGenLoop (Fin (n + 1)) f β⟧
      -- Show the goal uses these
      show inducedπ (n + 1) f (aX * bX) = aY * bY
      -- Use mul_spec for both multiplications
      have hLHS : aX * bX = ⟦GenLoop.transAt i β α⟧ := HomotopyGroup.mul_spec (i := i)
      have hRHS : aY * bY = ⟦GenLoop.transAt i (inducedGenLoop (Fin (n + 1)) f β)
                                                (inducedGenLoop (Fin (n + 1)) f α)⟧ :=
        HomotopyGroup.mul_spec (i := i)
      rw [hLHS, hRHS]
      -- Now goal: inducedπ (n+1) f ⟦transAt i β α⟧ = ⟦transAt i (inducedGenLoop f β) (inducedGenLoop f α)⟧
      simp only [inducedπ, Quotient.map'_mk'']
      apply Quotient.sound
      rw [inducedGenLoop_transAt f i β α]

end InducedOnπ

/-! ## Weak Homotopy Equivalence -/

section WeakHomotopyEquivalence

/-- A pointed continuous map f : X → Y is a weak homotopy equivalence if it induces
    bijections on all homotopy groups π_n for n ≥ 0.

    This is the standard definition from algebraic topology. -/
def IsWeakHomotopyEquivalence (f : X ⟶ Y) : Prop :=
  ∀ n : ℕ, Function.Bijective (inducedπ n f)

/-- Identity is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquiv_id : IsWeakHomotopyEquivalence (𝟙 X) := by
  intro n
  rw [inducedπ_id]
  exact Function.bijective_id

/-- Composition of weak homotopy equivalences is a weak homotopy equivalence. -/
theorem IsWeakHomotopyEquivalence.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsWeakHomotopyEquivalence f) (hg : IsWeakHomotopyEquivalence g) :
    IsWeakHomotopyEquivalence (f ≫ g) := by
  intro n
  rw [inducedπ_comp]
  exact (hg n).comp (hf n)

/-- A homeomorphism of pointed spaces is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquiv_of_iso (f : X ≅ Y) : IsWeakHomotopyEquivalence f.hom := by
  intro n
  have hinv : inducedπ n f.inv ∘ inducedπ n f.hom = id := by
    rw [← inducedπ_comp, Iso.hom_inv_id, inducedπ_id]
  have hcomp : inducedπ n f.hom ∘ inducedπ n f.inv = id := by
    rw [← inducedπ_comp, Iso.inv_hom_id, inducedπ_id]
  exact ⟨Function.LeftInverse.injective (congrFun hinv),
         Function.RightInverse.surjective (congrFun hcomp)⟩

end WeakHomotopyEquivalence

end PointedTopSpace
