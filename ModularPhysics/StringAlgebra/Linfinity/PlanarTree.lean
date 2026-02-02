/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringAlgebra.Linfinity.SymmetricAlgebra

/-!
# Planar Rooted Trees

This file defines planar rooted trees, which are fundamental for the
homotopy transfer theorem for L∞ algebras.

## Main definitions

* `PlanarTree` - Inductive type of planar rooted trees
* `PlanarTree.leaves` - Number of leaves
* `PlanarTree.internalVertices` - Number of internal vertices

## Mathematical Background

The homotopy transfer theorem expresses transferred brackets as sums over trees:

  l_n^H(x₁,...,xₙ) = ∑_{T ∈ Tree(n)} ε(T) · p ∘ T(l, h) ∘ i^⊗n

## References

* Loday, Vallette - "Algebraic Operads", Chapter 5
-/

universe u v

namespace StringAlgebra.Linfinity

/-! ## Planar Rooted Trees -/

/-- Planar rooted trees with binary and ternary nodes. -/
inductive PlanarTree : Type where
  | leaf : PlanarTree
  | node2 : PlanarTree → PlanarTree → PlanarTree
  | node3 : PlanarTree → PlanarTree → PlanarTree → PlanarTree
deriving Inhabited, DecidableEq

namespace PlanarTree

/-- Number of leaves in a tree. -/
def leaves : PlanarTree → ℕ
  | leaf => 1
  | node2 t1 t2 => t1.leaves + t2.leaves
  | node3 t1 t2 t3 => t1.leaves + t2.leaves + t3.leaves

/-- Number of internal vertices in a tree. -/
def internalVertices : PlanarTree → ℕ
  | leaf => 0
  | node2 t1 t2 => 1 + t1.internalVertices + t2.internalVertices
  | node3 t1 t2 t3 => 1 + t1.internalVertices + t2.internalVertices + t3.internalVertices

/-- The arity of the root. -/
def rootArity : PlanarTree → ℕ
  | leaf => 0
  | node2 _ _ => 2
  | node3 _ _ _ => 3

/-- The depth of a tree. -/
def depth : PlanarTree → ℕ
  | leaf => 0
  | node2 t1 t2 => 1 + max t1.depth t2.depth
  | node3 t1 t2 t3 => 1 + max (max t1.depth t2.depth) t3.depth

/-- A binary corolla. -/
def corolla2 : PlanarTree := node2 leaf leaf

/-- A ternary corolla. -/
def corolla3 : PlanarTree := node3 leaf leaf leaf

theorem leaves_pos (t : PlanarTree) : t.leaves ≥ 1 := by
  induction t with
  | leaf => simp [leaves]
  | node2 t1 t2 ih1 _ => simp [leaves]; omega
  | node3 t1 t2 t3 ih1 _ _ => simp [leaves]; omega

theorem corolla2_leaves : corolla2.leaves = 2 := by simp [corolla2, leaves]

theorem corolla3_leaves : corolla3.leaves = 3 := by simp [corolla3, leaves]

/-- A binary tree has only binary nodes. -/
def isBinary : PlanarTree → Bool
  | leaf => true
  | node2 t1 t2 => t1.isBinary && t2.isBinary
  | node3 _ _ _ => false

/-- Collect the arities of all internal vertices. -/
def internalArities : PlanarTree → List ℕ
  | leaf => []
  | node2 t1 t2 => 2 :: (t1.internalArities ++ t2.internalArities)
  | node3 t1 t2 t3 => 3 :: (t1.internalArities ++ t2.internalArities ++ t3.internalArities)

/-- Binary trees with 2 leaves. -/
def binaryTreesL2 : List PlanarTree := [corolla2]

/-- Binary trees with 3 leaves. -/
def binaryTreesL3 : List PlanarTree :=
  [ node2 corolla2 leaf, node2 leaf corolla2 ]

/-- Binary trees with 4 leaves. -/
def binaryTreesL4 : List PlanarTree :=
  [ node2 (node2 corolla2 leaf) leaf
  , node2 (node2 leaf corolla2) leaf
  , node2 corolla2 corolla2
  , node2 leaf (node2 corolla2 leaf)
  , node2 leaf (node2 leaf corolla2) ]

/-! ## Tree Decorations for Transfer -/

/-- A tree decoration assigns brackets and homotopies to tree positions. -/
structure TreeDecoration (R : Type u) [CommRing R] (V H : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)] where
  /-- The binary bracket l₂ -/
  bracket2 : SymPowerElem R V 2 → (Σ (d : ℤ), V d)
  /-- The ternary bracket l₃ -/
  bracket3 : SymPowerElem R V 3 → (Σ (d : ℤ), V d)
  /-- The homotopy h : V → V of degree -1 -/
  homotopy : (d : ℤ) → V d → V (d - 1)
  /-- Projection p : V → H -/
  proj : (d : ℤ) → V d → H d
  /-- Inclusion i : H → V -/
  incl : (d : ℤ) → H d → V d

end PlanarTree

end StringAlgebra.Linfinity
