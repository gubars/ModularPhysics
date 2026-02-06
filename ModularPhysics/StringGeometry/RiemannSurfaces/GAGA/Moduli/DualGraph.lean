import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Dual Graphs of Nodal Curves

This file defines the dual graph (also called the combinatorial type) of a nodal curve.

## Mathematical Background

For a nodal curve C, the dual graph Γ(C) encodes:
- **Vertices**: Irreducible components of C
- **Edges**: Nodes (ordinary double points) of C
- **Genus labels**: Geometric genus of each component
- **Self-loops**: Nodes where a component meets itself

The dual graph determines the topology of the nodal curve:
- Arithmetic genus: g_a(C) = Σ_v g(v) + b₁(Γ)
- Connected: C is connected iff Γ is connected

## Main Definitions

* `DualGraph` - The dual graph of a nodal curve
* `DualGraph.vertexStable` - Stability condition at a vertex
* `DualGraph.isStable` - A stable dual graph
* `DualGraph.totalGenus` - Arithmetic genus from dual graph

## References

* Harris, Morrison "Moduli of Curves" Chapter 3
* Deligne, Mumford "The irreducibility of the space of curves of given genus"
-/

namespace RiemannSurfaces.Algebraic

/-- A node (ordinary double point) on a curve.

    Locally, a node looks like the origin in the curve xy = 0 in ℂ².
    It is the mildest kind of singularity on a curve.

    We represent a node as a pair of distinct points on the normalization
    that map to the same point on the nodal curve. -/
structure Node (NormalizationPoints : Type*) where
  /-- The two preimage points on the normalization -/
  branch1 : NormalizationPoints
  branch2 : NormalizationPoints
  /-- The branches are distinct -/
  distinct : branch1 ≠ branch2

/-- The dual graph of a nodal curve.

    The dual graph Γ(C) encodes the combinatorial structure:
    - Vertices = irreducible components of C
    - Edges = nodes of C (each edge connects two vertices)
    - Genus labels = geometric genus of each component

    This is a proper combinatorial definition using Mathlib's SimpleGraph. -/
structure DualGraph where
  /-- The vertex type (irreducible components) -/
  V : Type*
  /-- Decidable equality on vertices -/
  [decEq : DecidableEq V]
  /-- The vertex type is finite -/
  [fin : Fintype V]
  /-- The adjacency relation (from SimpleGraph) -/
  adj : SimpleGraph V
  /-- Fintype on neighbor sets (for degree) -/
  [neighborFintype : ∀ v, Fintype (adj.neighborSet v)]
  /-- Genus labeling: each vertex v has genus g(v) ≥ 0 -/
  genusLabel : V → ℕ
  /-- Number of self-loops at each vertex (nodes connecting a component to itself) -/
  selfLoops : V → ℕ

attribute [instance] DualGraph.decEq DualGraph.fin DualGraph.neighborFintype

namespace DualGraph

variable (Γ : DualGraph)

/-- Number of vertices in a dual graph -/
def numVertices : ℕ := Fintype.card Γ.V

/-- Number of edges in the simple graph part (not counting self-loops).
    We count this as sum of degrees / 2 (handshaking lemma). -/
def numSimpleEdges : ℕ :=
  (Finset.univ.sum (fun v => Γ.adj.degree v)) / 2

/-- Total number of self-loops -/
def totalSelfLoops : ℕ :=
  Finset.univ.sum Γ.selfLoops

/-- Total number of edges (including self-loops) -/
def numEdges : ℕ :=
  Γ.numSimpleEdges + Γ.totalSelfLoops

/-- Sum of genus labels at all vertices -/
def sumGenera : ℕ :=
  Finset.univ.sum Γ.genusLabel

/-- The first Betti number of the graph.

    For a connected graph: b₁ = |E| - |V| + 1
    This counts independent cycles. -/
def firstBetti : ℤ :=
  Γ.numEdges - Γ.numVertices + 1

/-- Total genus: Σ_v g(v) + b₁(Γ)

    For a connected nodal curve with dual graph Γ, this equals the arithmetic genus. -/
def totalGenus : ℤ :=
  Γ.sumGenera + Γ.firstBetti

/-- The stability condition for a vertex in a dual graph.

    A component of genus g with n special points (= valence + 2×self-loops)
    is stable if 2g - 2 + n > 0.

    This ensures finite automorphism groups on each component. -/
def vertexStable (v : Γ.V) : Prop :=
  let valence := Γ.adj.degree v
  let specialPoints := valence + 2 * Γ.selfLoops v
  2 * Γ.genusLabel v + specialPoints > 2

/-- A stable graph is one where every vertex is stable.

    A nodal curve is stable iff its dual graph is stable. -/
def isStable : Prop :=
  ∀ v : Γ.V, Γ.vertexStable v

/-- The valence (degree) of a vertex in the dual graph -/
def valence (v : Γ.V) : ℕ := Γ.adj.degree v

/-- Number of special points at a vertex: valence + 2 * self-loops -/
def specialPoints (v : Γ.V) : ℕ :=
  Γ.valence v + 2 * Γ.selfLoops v

/-- Alternative formulation of stability: 2g - 2 + n > 0 where n is special points -/
theorem vertexStable_iff (v : Γ.V) :
    Γ.vertexStable v ↔ 2 * Γ.genusLabel v + Γ.specialPoints v > 2 := by
  simp only [vertexStable, specialPoints, valence]

end DualGraph

/-!
## Special Dual Graphs
-/

/-- The complete graph on Bool (two vertices with one edge) -/
def boolCompleteGraph : SimpleGraph Bool where
  Adj := fun a b => a ≠ b
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h rfl

instance : ∀ v, Fintype (boolCompleteGraph.neighborSet v) := fun v => by
  have : boolCompleteGraph.neighborSet v = {!v} := by
    ext x
    simp only [SimpleGraph.mem_neighborSet, boolCompleteGraph, Set.mem_singleton_iff]
    cases v <;> cases x <;> simp
  rw [this]
  exact Set.fintypeSingleton _

/-- The degree of each vertex in boolCompleteGraph is 1 -/
theorem boolCompleteGraph_degree (v : Bool) : boolCompleteGraph.degree v = 1 := by
  simp only [SimpleGraph.degree]
  have h : boolCompleteGraph.neighborFinset v = {!v} := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, boolCompleteGraph, Finset.mem_singleton]
    cases v <;> cases x <;> simp
  simp [h]

/-- The sum of degrees in boolCompleteGraph is 2 -/
theorem boolCompleteGraph_degree_sum :
    (Finset.univ : Finset Bool).sum (fun v => boolCompleteGraph.degree v) = 2 := by
  have h : (Finset.univ : Finset Bool) = {true, false} := by decide
  rw [h]
  simp only [boolCompleteGraph_degree]
  decide

/-- A smooth curve corresponds to a dual graph with one vertex and no edges -/
def smoothCurveGraph (g : ℕ) : DualGraph where
  V := Unit
  adj := ⊥  -- empty graph
  genusLabel := fun _ => g
  selfLoops := fun _ => 0

/-- A smooth curve of genus g ≥ 2 is stable -/
theorem smooth_curve_stable (g : ℕ) (hg : g ≥ 2) : (smoothCurveGraph g).isStable := by
  intro v
  simp only [DualGraph.vertexStable, smoothCurveGraph, SimpleGraph.bot_degree]
  omega

/-- The dual graph for a one-node curve with non-separating node:
    one vertex of genus g-1 with a self-loop -/
def oneNodeNonsepGraph (g : ℕ) (_ : g ≥ 1) : DualGraph where
  V := Unit
  adj := ⊥
  genusLabel := fun _ => g - 1
  selfLoops := fun _ => 1

/-- The dual graph for a one-node curve with separating node:
    two vertices of genus i and g-i connected by an edge -/
def oneNodeSepGraph (g i : ℕ) (_ : 1 ≤ i ∧ i ≤ g / 2) : DualGraph where
  V := Bool
  adj := boolCompleteGraph
  genusLabel := fun b => if b then i else g - i
  selfLoops := fun _ => 0

/-- For a connected nodal curve with dual graph Γ:
    g_a = Σ_v g(v) + b₁(Γ)

    This matches `DualGraph.totalGenus`. -/
theorem arithmetic_genus_formula (Γ : DualGraph) :
    Γ.totalGenus = Γ.sumGenera + Γ.firstBetti := rfl

end RiemannSurfaces.Algebraic
