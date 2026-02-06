/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringGeometry.RiemannSurfaces.GAGA.Bridge.SchemeProperties
import ModularPhysics.StringGeometry.RiemannSurfaces.GAGA.Bridge.EulerCharBridge

/-!
# Bridge Theorems: Connecting CompactAlgebraicCurve to Scheme Theory

This file provides theorems that connect the GAGA-style `CompactAlgebraicCurve`
infrastructure to scheme-theoretic results.

## Main Results

* `genericPoint_specializes_to_closedPoint` - Generic point specializes to every closed point
* `regular_iff_in_all_valuationSubrings` - Characterization of regular functions
* `properness_criterion` - Properness via regular functions being constant

## What's Missing for exact_at_V₃

The `exact_at_V₃` theorem (ker f₃ = range f₂) requires **sheaf cohomology**:

1. The short exact sequence of sheaves: 0 → O(D-p) → O(D) → k_p → 0
2. The long exact sequence in cohomology:
   0 → H⁰(O(D-p)) → H⁰(O(D)) → H⁰(k_p) → H¹(O(D-p)) → H¹(O(D)) → 0
3. Serre duality: H¹(O(D)) ≅ H⁰(K-D)*

The Bridge files provide local ring and topological infrastructure, but
sheaf cohomology is a separate piece of infrastructure.

## References

* Hartshorne "Algebraic Geometry" II.6, III.4 (Curves, Cohomology)
* Liu "Algebraic Geometry and Arithmetic Curves" Ch 5, 7
-/

namespace RiemannSurfaces.GAGA.Bridge

open Algebraic TopologicalSpace

variable (C : CompactAlgebraicCurve)

/-!
## Generic Point Properties

The generic point has special properties in the Zariski topology.
-/

/-- The generic point specializes to every closed point.
    In scheme-theoretic terms: η ∈ cl({p}) for every closed point p.
    Equivalently: every open neighborhood of p contains η. -/
theorem genericPoint_specializes_to_closedPoint (p : C.Point) :
    ∀ U : Set (CurvePoint C), (zariskiTopology C).IsOpen U →
      closedPoint C p ∈ U → genericPoint C ∈ U := by
  intro U hU hp
  have hne : U.Nonempty := ⟨closedPoint C p, hp⟩
  exact genericPoint_mem_of_nonempty_open C hU hne

/-!
## Properness Characterization

The `regularIsConstant` property characterizes properness.
-/

/-- A function is regular at all points iff it's in all valuation rings. -/
theorem regular_iff_in_all_valuationSubrings (f : C.FunctionField) :
    (∀ p : C.Point, 0 ≤ C.toAlgebraicCurve.valuation p f) ↔
    (∀ p : C.Point, f ∈ ValuationSubringAt C p) := by
  constructor
  · intro h p; exact h p
  · intro h p; exact (mem_valuationSubringAt C p f).mp (h p)

/-- The properness criterion: regular functions are constant.
    This is equivalent to the valuative criterion of properness. -/
theorem properness_criterion (f : C.FunctionField)
    (hf : ∀ p : C.Point, f ∈ ValuationSubringAt C p) :
    ∃ c : ℂ, f = @algebraMap ℂ C.FunctionField _ _ C.algebraInst.algebraInst c :=
  regular_everywhere_isConstant C f hf

/-!
## What the Bridge Provides vs What's Needed

### Bridge Infrastructure (complete):
- `zariskiTopology` : Zariski topology on CurvePoint C
- `regularFunctions` : Structure presheaf O(U) = ∩ O_p
- `ValuationSubringAt` : Local ring O_p at each point
- `valuationSubringAt_isDomain` : O_p is an integral domain
- `isUnit_of_not_mem_maximalIdeal` : Units characterized by valuation
- `curveSpace_irreducible` : The curve is irreducible
- `regular_everywhere_isConstant` : Properness (Liouville)
- `alternating_sum_exact_five` : Euler char theorem for exact sequences
- `a_plus_b_eq_one` : For dim V₃ = 1, we have a + b = 1

### Missing for exact_at_V₃:
The proof of `ker f₃ = range f₂` requires:
1. **Sheaf cohomology H^i(X, F)** for coherent sheaves
2. **Long exact sequence** from 0 → F' → F → F'' → 0
3. **Serre duality** H¹(C, O(D)) ≅ H⁰(C, O(K-D))*

This is substantial infrastructure beyond what the Bridge provides.
The Bridge gives local/topological data; sheaf cohomology is global.
-/

end RiemannSurfaces.GAGA.Bridge
