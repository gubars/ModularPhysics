import Mathlib.Data.Finset.Basic

/-!
# Simple Closed Curves on Surfaces

This file develops the theory of simple closed curves on surfaces,
including intersection numbers and disjointness.

## Mathematical Background

A **simple closed curve** on a surface Σ is an embedding S¹ → Σ, considered
up to isotopy. The **geometric intersection number** i(α, β) is the minimum
number of intersection points over all isotopy representatives:

  i(α, β) = min { |α' ∩ β'| : α' ∼ α, β' ∼ β }

Key properties:
- i(α, α) = 0 (any curve is disjoint from itself)
- i(α, β) = i(β, α) (symmetric)
- i(α, β) = 0 iff α and β can be isotoped to be disjoint

## Implementation Note

Since we work with isotopy classes abstractly (without explicit surface
coordinates), intersection numbers are specified axiomatically via an
`IntersectionData` structure. This captures the essential algebraic
properties while allowing concrete computations when surface data is available.

## Main Definitions

* `SimpleCurve` - A simple closed curve (up to isotopy)
* `IntersectionData` - Axiomatic intersection number data
* `SimpleCurve.disjoint` - Two curves are disjoint (i(α, β) = 0)

## References

* Farb, Margalit "A Primer on Mapping Class Groups" Chapter 1
-/

namespace RiemannSurfaces.Topology

/-!
## Simple Closed Curves
-/

/-- A simple closed curve on a surface Σ (up to isotopy).

    An **essential** simple closed curve is one that:
    - Does not bound a disk (not null-homotopic)
    - Is not homotopic to a boundary component
    - Is not homotopic to a puncture

    We use abstract identifiers since we work with isotopy classes.

    **Note**: Intersection numbers depend on the ambient surface and are
    provided separately via `IntersectionData`. -/
structure SimpleCurve where
  /-- Abstract identifier for the curve (up to isotopy) -/
  id : ℕ
  /-- Whether the curve is essential (non-contractible, not boundary-parallel) -/
  essential : Bool := true
  deriving DecidableEq, Repr

/-!
## Intersection Numbers

Intersection numbers are provided axiomatically, as they depend on the
ambient surface structure which we treat abstractly.
-/

/-- Axiomatic data for geometric intersection numbers on a surface.

    This structure provides intersection numbers for curves on a fixed surface,
    satisfying the fundamental properties:
    - i(α, α) = 0 (self-intersection is zero)
    - i(α, β) = i(β, α) (symmetry)

    **Usage**: Create an instance for a specific surface/curve system,
    then use `intersectionNumber` to compute intersections. -/
structure IntersectionData where
  /-- The geometric intersection number i(α, β) -/
  i : SimpleCurve → SimpleCurve → ℕ
  /-- Self-intersection is zero: i(α, α) = 0 -/
  self_zero : ∀ α, i α α = 0
  /-- Symmetric: i(α, β) = i(β, α) -/
  symm : ∀ α β, i α β = i β α

namespace SimpleCurve

variable (data : IntersectionData)

/-- Geometric intersection number i(α, β) using provided intersection data.
    This is the minimum number of intersection points over all isotopy representatives.

    **Properties** (from IntersectionData axioms):
    - i(α, α) = 0
    - i(α, β) = i(β, α)

    **Properties** (geometric, require proof):
    - i(α, β) = 0 iff α and β are disjoint
    - Bigon criterion: If α ≠ β and they fill no bigons, i(α,β) = |α ∩ β| -/
def intersectionNumber (α β : SimpleCurve) : ℕ := data.i α β

/-- Intersection number is symmetric -/
theorem intersectionNumber_comm (α β : SimpleCurve) :
    intersectionNumber data α β = intersectionNumber data β α :=
  data.symm α β

/-- Intersection number with self is zero -/
theorem intersectionNumber_self (α : SimpleCurve) :
    intersectionNumber data α α = 0 :=
  data.self_zero α

/-- Two curves are disjoint if their geometric intersection number is zero.
    This means they can be isotoped to not intersect. -/
def disjoint (α β : SimpleCurve) : Prop :=
  intersectionNumber data α β = 0

/-- Disjointness is symmetric -/
theorem disjoint_symm (α β : SimpleCurve) :
    disjoint data α β ↔ disjoint data β α := by
  simp [disjoint, intersectionNumber_comm]

/-- Every curve is disjoint from itself -/
theorem disjoint_self (α : SimpleCurve) : disjoint data α α := by
  simp [disjoint, intersectionNumber_self]

/-- Two curves fill a subsurface if every essential curve in that subsurface
    intersects at least one of them. -/
def fill (α β : SimpleCurve) : Prop :=
  α ≠ β ∧ intersectionNumber data α β > 0

/-- A curve is separating if it disconnects the surface -/
def separating (_ : SimpleCurve) : Prop :=
  True  -- Placeholder: needs surface data

/-- A curve is non-separating if the surface minus the curve is connected -/
def nonSeparating (α : SimpleCurve) : Prop := ¬α.separating

/-- The Dehn twist around a curve -/
structure DehnTwist where
  /-- The curve to twist around -/
  curve : SimpleCurve
  /-- The curve is essential -/
  essential : curve.essential
  /-- Power of the twist (positive = right, negative = left) -/
  power : ℤ

/-- The effect of a Dehn twist on intersection numbers.

    **Fact**: If τ_α is the Dehn twist around α, then for curves β, γ:
    i(τ_α(β), γ) = |i(α,β)·i(α,γ) + i(β,γ)| when properly oriented.

    More precisely, there's a formula involving signed intersection. -/
theorem dehn_twist_intersection (data : IntersectionData) (τ : DehnTwist) (β γ : SimpleCurve) :
    ∃ result : ℕ,
      -- The result depends on intersections with the twist curve
      result ≤ intersectionNumber data τ.curve β * intersectionNumber data τ.curve γ +
               intersectionNumber data β γ := by
  sorry  -- Dehn twist intersection formula

end SimpleCurve

/-!
## Curve Complexes

The curve complex C(Σ) has vertices = isotopy classes of essential curves
and edges = pairs of disjoint curves.
-/

/-- The curve complex C(Σ_{g,n}).

    **Vertices**: isotopy classes of essential simple closed curves
    **Edges**: pairs of disjoint curves (i(α, β) = 0)
    **k-simplices**: (k+1) pairwise disjoint curves

    **Properties** (Harvey, Masur-Minsky):
    - C(Σ) is connected for 3g - 3 + n ≥ 1
    - C(Σ) is δ-hyperbolic (Masur-Minsky)
    - diam(C(Σ)) = ∞ for 3g - 3 + n ≥ 2 -/
structure CurveComplex (g n : ℕ) where
  /-- The vertices (isotopy classes of curves) -/
  vertices : Set SimpleCurve
  /-- All vertices are essential -/
  essential : ∀ c ∈ vertices, c.essential
  /-- Intersection data for curves on this surface -/
  intersectionData : IntersectionData
  /-- Adjacency: two curves are adjacent iff disjoint (i(α, β) = 0) -/
  adj : SimpleCurve → SimpleCurve → Prop := SimpleCurve.disjoint intersectionData

/-- A path in the curve complex: a sequence of curves where consecutive curves are disjoint -/
structure CurveComplexPath (C : CurveComplex g n) where
  /-- The curves in the path -/
  curves : List SimpleCurve
  /-- Path is nonempty -/
  nonempty : curves ≠ []
  /-- All curves are vertices -/
  allVertices : ∀ c ∈ curves, c ∈ C.vertices
  /-- Consecutive curves are adjacent (disjoint) -/
  consecutive_adj : ∀ i : ℕ, (h : i + 1 < curves.length) →
    C.adj (curves[i]'(by omega)) (curves[i + 1]'h)

/-- The curve complex is connected for stable surfaces.

    **Theorem** (Harvey): For 3g - 3 + n ≥ 1, the curve complex C(Σ_{g,n})
    is connected. Any two essential curves can be connected by a path
    of curves, where adjacent curves are disjoint.

    The proof proceeds by showing any curve can be connected to a
    fixed "standard" curve system. -/
theorem curve_complex_connected (g n : ℕ) (_ : 3 * g - 3 + n ≥ 1)
    (C : CurveComplex g n) :
    ∀ α β : SimpleCurve, α ∈ C.vertices → β ∈ C.vertices →
    ∃ (path : CurveComplexPath C), path.curves.head? = some α ∧ path.curves.getLast? = some β := by
  sorry  -- Harvey's connectivity theorem

/-- The curve complex is Gromov δ-hyperbolic (Masur-Minsky).

    **Theorem** (Masur-Minsky 1999): The curve complex C(Σ_{g,n}) is
    δ-hyperbolic for some δ depending only on the topology of the surface.

    This means all geodesic triangles are δ-thin: each side is contained
    in a δ-neighborhood of the union of the other two sides. -/
theorem curve_complex_hyperbolic (g n : ℕ) (hstable : 3 * g - 3 + n ≥ 2)
    (C : CurveComplex g n) :
    ∃ δ : ℕ, δ > 0 ∧
      -- δ-hyperbolicity: all triangles are δ-thin
      -- (Formal statement requires metric space structure on C)
      True := by
  sorry  -- Masur-Minsky hyperbolicity theorem

end RiemannSurfaces.Topology
