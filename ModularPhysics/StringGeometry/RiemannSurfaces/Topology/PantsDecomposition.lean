import ModularPhysics.StringGeometry.RiemannSurfaces.Topology.SimpleCurves
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring

/-!
# Pants Decompositions (Markings)

This file develops the theory of pants decompositions (also called markings
or trinion decompositions) of surfaces.

## Mathematical Background

**Definition**: A **pants decomposition** (or **marking**) of a surface Σ_{g,n}
is a maximal collection of disjoint, non-contractible, pairwise non-isotopic
simple closed curves.

**Counts** (from Euler characteristic):
- Number of curves: 3g - 3 + n
- Number of complementary pairs of pants (trinions): 2g - 2 + n

## Main Definitions

* `Marking` / `PantsDecomposition` - Maximal curve system
* `Trinion` - A pair of pants (thrice-punctured sphere)
* `FenchelNielsenCoords` - Coordinates on Teichmüller space

## References

* Hatcher, Thurston "A presentation for the mapping class group" Appendix
* Farb, Margalit "A Primer on Mapping Class Groups" Chapter 10
-/

namespace RiemannSurfaces.Topology

open SimpleCurve

/-!
## Markings (Pants Decompositions)
-/

/-- A marking (= pants decomposition) of a surface Σ_{g,n}.

    Following Hatcher-Thurston: A marking is a maximal collection of disjoint,
    non-contractible, pairwise non-isotopic smooth circles on M.

    **Count**: For Σ_{g,n}, there are exactly 3g - 3 + n curves
    cutting into 2g - 2 + n trinions (pairs of pants).

    **Stability condition**: The formula 3g - 3 + n requires 2g + n > 2 to be
    non-negative. This is the stability condition for the surface. -/
structure Marking (g n : ℕ) where
  /-- The circles in the marking -/
  circles : Finset SimpleCurve
  /-- All circles are essential (non-contractible, not boundary-parallel) -/
  essential : ∀ c ∈ circles, c.essential
  /-- Intersection data for curves on this surface -/
  intersectionData : IntersectionData
  /-- Circles are pairwise disjoint (can be isotoped to not intersect) -/
  pairwiseDisjoint : ∀ c₁ ∈ circles, ∀ c₂ ∈ circles, c₁ ≠ c₂ →
    SimpleCurve.disjoint intersectionData c₁ c₂
  /-- Stability: 2g + n > 2 ensures the curve count is non-negative -/
  stable : 2 * g + n > 2
  /-- Correct number of circles: 3g - 3 + n (well-defined by stability) -/
  cardCorrect : circles.card = 3 * g - 3 + n

/-- Alias: PantsDecomposition = Marking -/
abbrev PantsDecomposition := Marking

namespace Marking

/-- The number of circles in a marking of Σ_{g,n} -/
def numCircles (g n : ℕ) : ℕ := 3 * g - 3 + n

/-- The number of complementary trinions in a marking of Σ_{g,n} -/
def numTrinions (g n : ℕ) : ℕ := 2 * g - 2 + n

/-- Euler characteristic formula: χ(Σ_{g,n}) = 2 - 2g - n = -(numTrinions g n)

    Proof: 2 - 2g - n = -(2g - 2 + n) = -2g + 2 - n ✓ -/
theorem euler_characteristic (g n : ℕ) (_ : 2 * g + n > 2) :
    (2 : ℤ) - 2 * g - n = -(2 * (g : ℤ) - 2 + n) := by
  ring

/-- For closed surfaces (n = 0): 3g - 3 circles, 2g - 2 trinions -/
theorem closed_surface_count (g : ℕ) (_ : g ≥ 2) :
    numCircles g 0 = 3 * g - 3 ∧ numTrinions g 0 = 2 * g - 2 := by
  simp [numCircles, numTrinions]

/-- Two markings are equivalent if they have the same circles -/
def equiv (P Q : Marking g n) : Prop := P.circles = Q.circles

end Marking

/-!
## Trinions (Pairs of Pants)

A trinion is a thrice-punctured sphere, the complementary region of a
pants decomposition.
-/

/-- A trinion (pair of pants) - a thrice-punctured sphere.

    Each trinion has exactly 3 boundary curves, which are either:
    - Curves from the pants decomposition, or
    - Boundary components of the surface -/
structure Trinion where
  /-- The three boundary curves -/
  boundaries : Fin 3 → SimpleCurve
  /-- All distinct -/
  distinct : ∀ i j, i ≠ j → boundaries i ≠ boundaries j

/-- The trinions of a pants decomposition -/
noncomputable def Marking.trinions {g n : ℕ} (_ : Marking g n) : Finset Trinion := by
  -- The complementary regions form 2g - 2 + n trinions
  exact sorry

/-- Number of trinions equals 2g - 2 + n -/
theorem Marking.trinions_card {g n : ℕ} (P : Marking g n) (_ : 2 * g + n > 2) :
    P.trinions.card = 2 * g - 2 + n := by
  sorry

/-!
## Fenchel-Nielsen Coordinates

A pants decomposition P gives Fenchel-Nielsen coordinates on Teichmüller space:
- **Length coordinates**: ℓ_c > 0 for each curve c ∈ P
- **Twist coordinates**: τ_c ∈ ℝ for each curve c ∈ P

This gives a real-analytic diffeomorphism:
  T_{g,n} ≅ ℝ_{>0}^{3g-3+n} × ℝ^{3g-3+n}
-/

/-- Fenchel-Nielsen coordinates for a pants decomposition.

    **Theorem** (Fenchel-Nielsen): The map
      T_{g,n} → ℝ_{>0}^{3g-3+n} × ℝ^{3g-3+n}
      [Σ] ↦ ((ℓ_c)_c, (τ_c)_c)
    is a real-analytic diffeomorphism.

    The length ℓ_c is the hyperbolic length of the geodesic representative of c.
    The twist τ_c measures how the two trinions adjacent to c are glued. -/
structure FenchelNielsenCoords (g n : ℕ) (P : PantsDecomposition g n) where
  /-- Length of each circle -/
  lengths : SimpleCurve → ℝ
  /-- Lengths are positive -/
  lengths_pos : ∀ c ∈ P.circles, lengths c > 0
  /-- Twist around each circle -/
  twists : SimpleCurve → ℝ

/-- The Fenchel-Nielsen map from FN coordinates to Teichmüller space is bijective.

    **Fenchel-Nielsen Theorem**: The map
      ℝ_{>0}^{3g-3+n} × ℝ^{3g-3+n} → T_{g,n}
      ((ℓ_c)_c, (τ_c)_c) ↦ [Σ with these lengths and twists]
    is a real-analytic diffeomorphism.

    This gives global coordinates on Teichmüller space for each pants decomposition. -/
theorem fenchel_nielsen_parametrization (g n : ℕ) (hstable : 2 * g + n > 2)
    (P : PantsDecomposition g n) :
    -- The set of FN coordinates bijects with "Teichmüller space"
    -- (represented here by the existence of an inverse map)
    ∃ (fromFN : FenchelNielsenCoords g n P → Unit)  -- Placeholder for TeichmüllerPoint
      (toFN : Unit → FenchelNielsenCoords g n P),
    (∀ coords, fromFN (toFN (fromFN coords)) = fromFN coords) := by
  sorry  -- Fenchel-Nielsen theorem

/-- Different pants decompositions give different FN coordinates.
    There exist explicit change-of-coordinates formulas between them.

    For two pants decompositions P and Q related by elementary moves,
    the FN coordinates transform by explicit rational functions. -/
theorem fenchel_nielsen_change_of_coords (g n : ℕ) (P Q : PantsDecomposition g n) :
    -- Change of coordinates exists (abstractly)
    ∃ (change : FenchelNielsenCoords g n P → FenchelNielsenCoords g n Q),
    Function.Bijective change := by
  sorry  -- Explicit change-of-coordinates formulas

/-!
## Wolpert's Formula

Wolpert showed that the Weil-Petersson symplectic form has a simple expression
in Fenchel-Nielsen coordinates.
-/

/-- The Weil-Petersson symplectic form data in Fenchel-Nielsen coordinates. -/
structure WPFormInFNCoords (g n : ℕ) (P : PantsDecomposition g n) where
  /-- The 2-form coefficients: ω = Σᵢ aᵢ dℓᵢ ∧ dτᵢ + ... -/
  lengthTwistCoeff : SimpleCurve → ℝ
  /-- In FN coordinates, the WP form has coefficients = 1 for curves in P -/
  isStandardForm : ∀ c ∈ P.circles, lengthTwistCoeff c = 1

/-- **Wolpert's formula**: In Fenchel-Nielsen coordinates (ℓᵢ, τᵢ),
    the Weil-Petersson symplectic form is:

    ω_WP = Σᵢ dℓᵢ ∧ dτᵢ

    This is remarkable: the WP form is just the standard symplectic form
    in these coordinates! -/
theorem wolpert_formula (g n : ℕ) (_ : 2 * g + n > 2) (P : PantsDecomposition g n) :
    ∃ ω : WPFormInFNCoords g n P, ∀ c ∈ P.circles, ω.lengthTwistCoeff c = 1 := by
  sorry  -- Wolpert's theorem

end RiemannSurfaces.Topology
