import ModularPhysics.StringGeometry.RiemannSurfaces.GAGA.Moduli.DualGraph

/-!
# Boundary Stratification of M̄_g

This file describes the boundary stratification of the Deligne-Mumford
compactification M̄_g.

## Mathematical Background

The boundary ∂M̄_g = M̄_g \ M_g consists of stable curves with at least one node.
It has a natural stratification by dual graphs (combinatorial types):

  ∂M̄_g = ⋃_Γ Δ_Γ

where Δ_Γ parametrizes stable curves with dual graph Γ.

### Irreducible Components

The boundary ∂M̄_g has ⌊g/2⌋ + 1 irreducible components (divisors):
- **Δ_0**: Non-separating node (one component of genus g-1 with self-loop)
- **Δ_i** (1 ≤ i ≤ ⌊g/2⌋): Separating node (components of genus i and g-i)

## Main Definitions

* `BoundaryDivisorType` - Types of irreducible boundary divisors

## References

* Deligne, Mumford "The irreducibility of the space of curves of given genus"
* Arbarello, Cornalba, Griffiths "Geometry of Algebraic Curves II"
-/

namespace RiemannSurfaces.Algebraic

open DualGraph

/-- The irreducible boundary divisors in M̄_g.

    For g ≥ 2, the boundary has ⌊g/2⌋ + 1 irreducible components:
    - Δ_0: non-separating node (one component of genus g-1 with self-loop)
    - Δ_i (1 ≤ i ≤ ⌊g/2⌋): separating node (two components of genera i and g-i) -/
inductive BoundaryDivisorType (g : ℕ)
  /-- Δ_0: non-separating node -/
  | nonseparating : BoundaryDivisorType g
  /-- Δ_i: separating node creating components of genus i and g-i -/
  | separating (i : ℕ) (hi : 1 ≤ i ∧ i ≤ g / 2) : BoundaryDivisorType g

/-- Δ_0 graph has one node (a self-loop) -/
theorem delta0_has_one_node (g : ℕ) (hg : g ≥ 1) :
    (oneNodeNonsepGraph g hg).numEdges = 1 := by
  simp only [DualGraph.numEdges, DualGraph.numSimpleEdges, DualGraph.totalSelfLoops,
             oneNodeNonsepGraph, Finset.univ_unique, Finset.sum_singleton,
             SimpleGraph.bot_degree, Nat.zero_div, zero_add]

/-- Δ_0 is stable for g ≥ 2 -/
theorem delta0_stable (g : ℕ) (hg : g ≥ 2) : (oneNodeNonsepGraph g (by omega)).isStable := by
  intro v
  simp only [DualGraph.vertexStable, oneNodeNonsepGraph, SimpleGraph.bot_degree]
  omega

/-- Δ_i graph has one node (connecting two components) -/
theorem deltaI_has_one_node (g i : ℕ) (hi : 1 ≤ i ∧ i ≤ g / 2) :
    (oneNodeSepGraph g i hi).numEdges = 1 := by
  simp only [DualGraph.numEdges, DualGraph.numSimpleEdges, DualGraph.totalSelfLoops,
             oneNodeSepGraph]
  -- boolCompleteGraph has sum of degrees = 2, so numSimpleEdges = 2/2 = 1
  -- selfLoops are all 0
  simp only [boolCompleteGraph_degree_sum, Finset.sum_const_zero, add_zero]

/-- For g = 2: two boundary divisor types -/
theorem boundary_divisors_g2 : 2 / 2 + 1 = 2 := rfl

/-- For g = 3: two boundary divisor types -/
theorem boundary_divisors_g3 : 3 / 2 + 1 = 2 := rfl

/-- For g = 4: three boundary divisor types -/
theorem boundary_divisors_g4 : 4 / 2 + 1 = 3 := rfl

end RiemannSurfaces.Algebraic
