/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringGeometry.RiemannSurfaces.GAGA.Bridge.LocalRings
import Mathlib.Topology.Sets.Opens
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Scheme Construction from CompactAlgebraicCurve

This file constructs a scheme from a `CompactAlgebraicCurve`. The key insight is that
the function field K(C) together with the discrete valuations at each point determines
a unique smooth projective curve scheme.

## Construction Overview

1. **Points**: The underlying set is `Option C.Point`:
   - `none` = the generic point η (corresponding to the function field)
   - `some p` = the closed point corresponding to p ∈ C.Point

2. **Topology**: Zariski topology where:
   - Open sets: complements of finite sets of closed points, plus ∅
   - Equivalently: {η} is dense, closed sets are finite unions of closed points

3. **Structure Sheaf**: For an open U:
   - O(U) = ⋂_{p ∈ U, p closed} O_p where O_p is the valuation ring at p
   - O({η}) = K(C) (the function field)

4. **Scheme Property**: This is locally isomorphic to Spec of a ring because:
   - The complement of any closed point is affine (Spec of the valuation ring)
   - These affine opens cover the curve

## Main Definitions

* `CurvePoint` - The type of points (Option C.Point)
* `CurveTopology` - The Zariski topology
* `StructureSheaf` - The sheaf of regular functions
* `CurveScheme` - The resulting scheme

## References

* Hartshorne "Algebraic Geometry" II.6 (Divisors and Curves)
* Liu "Algebraic Geometry and Arithmetic Curves" Ch 7
* Stacks Project Tag 0BY1 (Abstract curves from function fields)
-/

namespace RiemannSurfaces.GAGA.Bridge

open CategoryTheory TopologicalSpace Algebraic

variable (C : CompactAlgebraicCurve)

/-!
## The Underlying Set

The points of the curve scheme are:
- Generic point η (= none) corresponding to the function field
- Closed points (= some p) for each p ∈ C.Point
-/

/-- The type of points in the curve scheme.
    `none` is the generic point, `some p` is the closed point at p. -/
abbrev CurvePoint := Option C.Point

/-- The generic point of the curve. -/
def genericPoint : CurvePoint C := none

/-- Convert a point of C to a closed point of the scheme. -/
def closedPoint (p : C.Point) : CurvePoint C := some p

/-- A point is closed iff it's not the generic point. -/
def isClosedPoint (x : CurvePoint C) : Prop := x.isSome

/-- The set of closed points. -/
def closedPoints : Set (CurvePoint C) := {x | isClosedPoint C x}

/-!
## The Zariski Topology

For a curve, the Zariski topology is the cofinite topology on closed points,
plus the generic point is in every nonempty open set.

Closed sets are:
- The empty set
- Finite sets of closed points
- The whole space (which includes the generic point)

Open sets are:
- The empty set
- Complements of finite sets of closed points (these contain the generic point)
- The whole space
-/

/-- A set is Zariski-closed if it's either:
    - Empty
    - A finite set of closed points (not containing the generic point)
    - The whole space -/
def isZariskiClosed (S : Set (CurvePoint C)) : Prop :=
  S = ∅ ∨ (S.Finite ∧ genericPoint C ∉ S) ∨ S = Set.univ

/-- The collection of Zariski-closed sets. -/
def zariskiClosedSets : Set (Set (CurvePoint C)) :=
  {S | isZariskiClosed C S}

/-- Empty set is closed. -/
theorem empty_isZariskiClosed : isZariskiClosed C ∅ := Or.inl rfl

/-- The whole space is closed. -/
theorem univ_isZariskiClosed : isZariskiClosed C Set.univ := Or.inr (Or.inr rfl)

/-- Finite intersection of closed sets is closed. -/
theorem inter_isZariskiClosed {S T : Set (CurvePoint C)}
    (hS : isZariskiClosed C S) (hT : isZariskiClosed C T) :
    isZariskiClosed C (S ∩ T) := by
  rcases hS with rfl | ⟨hSfin, hSgen⟩ | rfl
  · simp [empty_isZariskiClosed]
  · rcases hT with rfl | ⟨hTfin, hTgen⟩ | rfl
    · simp [empty_isZariskiClosed]
    · right; left
      exact ⟨hSfin.inter_of_left T, fun h => hSgen h.1⟩
    · simp [isZariskiClosed, hSfin, hSgen]
  · simp [hT]

/-- Binary union of Zariski-closed sets is closed. -/
theorem union_isZariskiClosed {S T : Set (CurvePoint C)}
    (hS : isZariskiClosed C S) (hT : isZariskiClosed C T) :
    isZariskiClosed C (S ∪ T) := by
  rcases hS with rfl | ⟨hSfin, hSgen⟩ | rfl
  · simp [hT]
  · rcases hT with rfl | ⟨hTfin, hTgen⟩ | rfl
    · simp [isZariskiClosed, hSfin, hSgen]
    · -- Both are finite sets not containing generic point
      right; left
      exact ⟨hSfin.union hTfin, fun h => h.elim hSgen hTgen⟩
    · right; right; simp
  · right; right; simp

/-- A set is Zariski-open if it's either empty or contains the generic point
    with a cofinite complement. -/
def isZariskiOpen (U : Set (CurvePoint C)) : Prop :=
  U = ∅ ∨ (genericPoint C ∈ U ∧ Uᶜ.Finite)

/-- The Zariski topology on the curve.

    Open sets are:
    - The empty set
    - Cofinite sets containing the generic point

    This is the Zariski topology on a smooth projective curve,
    where closed points are closed and the generic point is dense. -/
def zariskiTopology : TopologicalSpace (CurvePoint C) where
  IsOpen U := isZariskiOpen C U
  isOpen_univ := by
    right
    constructor
    · trivial
    · simp
  isOpen_inter := fun s t hs ht => by
    rcases hs with rfl | ⟨hs_gen, hs_fin⟩
    · simp [isZariskiOpen]
    · rcases ht with rfl | ⟨ht_gen, ht_fin⟩
      · simp [isZariskiOpen]
      · right
        constructor
        · exact ⟨hs_gen, ht_gen⟩
        · simp only [Set.compl_inter]
          exact hs_fin.union ht_fin
  isOpen_sUnion := fun S hS => by
    by_cases h_empty : ⋃₀ S = ∅
    · exact Or.inl h_empty
    · right
      -- The union is nonempty, so some U ∈ S is nonempty
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h_empty
      obtain ⟨U, hU_mem, hx_U⟩ := Set.mem_sUnion.mp hx
      have hU_open := hS U hU_mem
      rcases hU_open with rfl | ⟨hU_gen, hU_fin⟩
      · simp at hx_U
      · constructor
        · -- Generic point is in the union
          exact Set.mem_sUnion.mpr ⟨U, hU_mem, hU_gen⟩
        · -- Complement of union is subset of complement of U, which is finite
          have h_sub : (⋃₀ S)ᶜ ⊆ Uᶜ := Set.compl_subset_compl.mpr (Set.subset_sUnion_of_mem hU_mem)
          exact hU_fin.subset h_sub

/-!
## The Structure Sheaf

The structure sheaf O assigns to each open set U the ring of functions
that are regular at all closed points in U.

For a curve:
- O(U) = ⋂_{p ∈ U, p closed} O_p
- O({η}) = K(C) (the function field)
- Stalks: O_{x,η} = K(C), O_{x,p} = O_p (the DVR at p)
-/

/-- The ring of functions regular on an open set U.
    This is the intersection of valuation rings at all closed points in U. -/
noncomputable def regularFunctions (U : Set (CurvePoint C)) : Subring C.FunctionField where
  carrier := {f | ∀ p : C.Point, closedPoint C p ∈ U → f ∈ ValuationSubringAt C p}
  mul_mem' := fun {a b} ha hb p hp => by
    have ha' := ha p hp
    have hb' := hb p hp
    simp only [mem_valuationSubringAt] at *
    by_cases hab : a * b = 0
    · simp only [hab, C.toAlgebraicCurve.valuation_zero]; exact le_refl 0
    · have ha_ne : a ≠ 0 := fun h => by simp [h] at hab
      have hb_ne : b ≠ 0 := fun h => by simp [h] at hab
      rw [C.toAlgebraicCurve.valuation_mul p a b ha_ne hb_ne]
      omega
  one_mem' := fun p _ => by
    simp only [mem_valuationSubringAt, C.toAlgebraicCurve.valuation_one]; exact le_refl 0
  add_mem' := fun {a b} ha hb p hp => by
    have ha' := ha p hp
    have hb' := hb p hp
    simp only [mem_valuationSubringAt] at *
    by_cases hab : a + b = 0
    · simp only [hab, C.toAlgebraicCurve.valuation_zero]; exact le_refl 0
    · have h := C.toAlgebraicCurve.valuation_add_min p a b hab
      omega
  zero_mem' := fun p _ => by
    simp only [mem_valuationSubringAt, C.toAlgebraicCurve.valuation_zero]; exact le_refl 0
  neg_mem' := fun {a} ha p hp => by
    have ha' := ha p hp
    simp only [mem_valuationSubringAt] at *
    by_cases ha_ne : a = 0
    · simp only [ha_ne, neg_zero, C.toAlgebraicCurve.valuation_zero]; exact le_refl 0
    · -- Prove valuation of -a equals valuation of a
      have hneg1_ne : (-1 : C.FunctionField) ≠ 0 := neg_ne_zero.mpr one_ne_zero
      have h1 : C.toAlgebraicCurve.valuation p (-1) + C.toAlgebraicCurve.valuation p (-1) =
                C.toAlgebraicCurve.valuation p 1 := by
        rw [← C.toAlgebraicCurve.valuation_mul p (-1) (-1) hneg1_ne hneg1_ne]
        ring_nf
      rw [C.toAlgebraicCurve.valuation_one] at h1
      have hneg1_val : C.toAlgebraicCurve.valuation p (-1) = 0 := by omega
      have : -a = -1 * a := by ring
      rw [this, C.toAlgebraicCurve.valuation_mul p (-1) a hneg1_ne ha_ne, hneg1_val]
      simp only [zero_add]
      exact ha'

/-- For U ⊆ V, there's a restriction map O(V) → O(U). -/
noncomputable def restrictionMap {U V : Set (CurvePoint C)} (hUV : U ⊆ V) :
    regularFunctions C V →+* regularFunctions C U where
  toFun f := ⟨f.val, fun p hp => f.property p (hUV hp)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The stalk at a point x is:
    - K(C) if x is the generic point
    - O_p (the valuation ring) if x = closedPoint p -/
noncomputable def stalkType (x : CurvePoint C) : Type _ :=
  match x with
  | none => C.FunctionField
  | some p => ValuationSubringAt C p

/-- The stalk at the generic point is the function field. -/
noncomputable def stalkAtGeneric : stalkType C (genericPoint C) = C.FunctionField := rfl

/-- The stalk at a closed point is the valuation ring. -/
noncomputable def stalkAtClosed (p : C.Point) :
    stalkType C (closedPoint C p) = ValuationSubringAt C p := rfl

/-!
## Key Properties

The construction gives a scheme because:
1. Stalks are local rings (generic point: field, closed points: DVRs)
2. There exist affine open covers
-/

/-- The function field is a field, hence a local ring. -/
noncomputable instance functionFieldIsLocalRing : IsLocalRing C.FunctionField :=
  inferInstance

/-- The stalk at the generic point is the function field, which is a local ring (as a field).
    Note: We can't directly make an instance on `stalkType C (genericPoint C)` because
    Lean doesn't automatically reduce the match. Use `functionFieldIsLocalRing` directly. -/
theorem stalkAtGeneric_isLocalRing :
    IsLocalRing C.FunctionField := functionFieldIsLocalRing C

/-!
## Summary

This file establishes the foundational infrastructure for constructing a scheme
from a CompactAlgebraicCurve:

1. **CurvePoint** - The underlying set with generic and closed points
2. **zariskiTopology** - The Zariski topology on CurvePoint
3. **regularFunctions** - The presheaf of regular functions
4. **stalkType** - Stalks at each point (K(C) at generic, O_p at closed)

The remaining work to complete the scheme construction:
- Verify the presheaf is actually a sheaf (locality and gluing)
- Prove stalks are local rings (done for generic, need DVR instance for closed)
- Construct affine open covers
- Package everything into Mathlib's Scheme structure

This provides the foundation for the bridge CompactAlgebraicCurve → SmoothProjectiveCurve.
-/

end RiemannSurfaces.GAGA.Bridge
