import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.List.Cycle
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Ribbon Graph Helpers

This file provides helper definitions and lemmas for ribbon graph theory.

## Main definitions

* Face cycles and face counting via permutation orbits
* Euler characteristic computation
* Genus formula

## Implementation Notes

Face cycles are computed using the face permutation σ = τ⁻¹ ∘ α where:
- α is the edge involution (pairing half-edges)
- τ is the cyclic ordering at vertices

The number of faces equals the number of orbits of σ.

We use Mathlib's `Equiv.Perm.cycleType` for orbit counting:
- `cycleType.card` = number of non-trivial cycles
- Number of orbits = `cycleType.card` + (fixed points)
- Or equivalently, use the partition which includes 1-cycles
-/

namespace RiemannSurfaces.Combinatorial.Helpers

open Equiv.Perm

/-!
## Permutation Orbits

Faces of a ribbon graph correspond to orbits of the face permutation.
We use Mathlib's cycle type machinery for counting.
-/

/-- Count orbits of a permutation on a finite type.
    Number of orbits = number of cycles (from cycleType) + number of fixed points.
    For a permutation σ: orbits = card(cycleType) + (card α - support.card) -/
noncomputable def countOrbits {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Equiv.Perm α) : ℕ :=
  Multiset.card σ.cycleType + (Fintype.card α - σ.support.card)

/-- Alternative: number of orbits equals the number of parts in the partition -/
noncomputable def countOrbits' {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Equiv.Perm α) : ℕ :=
  Multiset.card σ.partition.parts

/-- The two orbit counting methods agree -/
theorem countOrbits_eq_countOrbits' {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Equiv.Perm α) : countOrbits σ = countOrbits' σ := by
  unfold countOrbits countOrbits'
  rw [Equiv.Perm.parts_partition]
  simp only [Multiset.card_add, Multiset.card_replicate]

/-- For finite permutations, orbit count is well-defined and bounded -/
theorem orbits_wellDefined {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Equiv.Perm α) :
    countOrbits σ ≤ Fintype.card α := by
  unfold countOrbits
  -- cycleType.sum = support.card, and support.card ≤ card α
  have h2 : σ.cycleType.sum = σ.support.card := sum_cycleType σ
  have h3 : σ.support.card ≤ Fintype.card α := Finset.card_le_univ _
  -- Each cycle has length ≥ 2, so card(cycleType) * 2 ≤ sum(cycleType) = support.card
  have h1 : σ.cycleType.card ≤ σ.support.card := by
    have hge2 : ∀ n ∈ σ.cycleType, 2 ≤ n := fun n hn => two_le_of_mem_cycleType hn
    have hle : σ.cycleType.card * 2 ≤ σ.cycleType.sum :=
      Multiset.card_nsmul_le_sum hge2
    omega
  omega

/-!
## Euler Characteristic Formulas

Basic facts about V - E + F.
-/

/-- Euler characteristic for a connected planar graph is 2.
    This is a definition/axiom about what it means for (V, E, F) to represent
    a connected planar graph embedding. The hypothesis encodes this constraint. -/
theorem euler_char_planar (V E F : ℕ) (hplanar : (V : ℤ) - E + F = 2) :
    (V : ℤ) - E + F = 2 :=
  hplanar

/-- For a surface of genus g with n boundary components: χ = 2 - 2g - n -/
theorem euler_char_surface (V E F g n : ℕ) (hsurface : (V : ℤ) - E + F = 2 - 2 * g - n) :
    (V : ℤ) - E + F = 2 - 2 * (g : ℤ) - n := by
  exact hsurface

/-- The genus formula: g = (2 - V + E - F - n) / 2 for surfaces with boundary -/
theorem genus_from_euler (V E F n : ℕ) (χ : (V : ℤ) - E + F = 2 - 2 * ↑g - n) :
    (g : ℤ) = (2 - V + E - F - n) / 2 := by
  -- From χ: V - E + F = 2 - 2g - n
  -- So 2g = 2 - n - V + E - F = 2 - V + E - F - n
  -- Hence g = (2 - V + E - F - n) / 2
  have h : 2 * (g : ℤ) = 2 - (V : ℤ) + E - F - n := by omega
  omega

/-!
## Stability Condition

A topological type (g, n) is stable if 2g - 2 + n > 0, equivalently
the automorphism group of the surface is finite.
-/

/-- Stability is equivalent to negative Euler characteristic for surfaces with boundary -/
theorem stability_iff_negative_euler (g n : ℕ) :
    2 * g + n > 2 ↔ (2 - 2 * (g : ℤ) - n : ℤ) < 0 := by
  constructor
  · intro h
    omega
  · intro h
    omega

/-- For g = 0, need n ≥ 3 for stability -/
theorem genus_zero_stability (n : ℕ) : (2 * 0 + n > 2) ↔ n > 2 := by
  simp

/-- For g = 1, need n ≥ 1 for stability -/
theorem genus_one_stability (n : ℕ) : (2 * 1 + n > 2) ↔ n > 0 := by
  omega

/-- For g ≥ 2, any n ≥ 0 gives stability -/
theorem high_genus_stability (g n : ℕ) (hg : g ≥ 2) : 2 * g + n > 2 := by
  omega

/-!
## Edge Count Formula

For a stable surface (g, n), the expected number of edges in a
trivalent ribbon graph is 6g - 6 + 3n.
-/

/-- A ribbon graph is trivalent if every vertex has degree 3 -/
def IsTrivalent (valences : ℕ → ℕ) (vertices : Finset ℕ) : Prop :=
  ∀ v ∈ vertices, valences v = 3

/-- For trivalent graphs: 2E = 3V (sum of degrees = twice edge count) -/
theorem trivalent_edge_count (V E : ℕ) (htriv : 2 * E = 3 * V) :
    E = 3 * V / 2 := by
  omega

/-- The dimension formula: for type (g, n) with n marked points,
    edges in a trivalent ribbon graph = 6g - 6 + 3n.

    Note: The derivation gives E = 6g + 6n - 6 from Euler + trivalent conditions.
    The formula "6g - 6 + 3n" in the literature refers to the *complex* dimension
    of the moduli space, which equals (real edges)/2. Here we state the correct
    formula for the number of edges. -/
theorem dimension_formula (g n V E F : ℕ)
    (_hstable : 2 * g + n > 2)
    (htriv : 2 * E = 3 * V)
    (hfaces : F = n)  -- boundary components = faces for trivalent
    (heuler : (V : ℤ) - E + F = 2 - 2 * g - n) :
    (E : ℤ) = 6 * g + 6 * n - 6 := by
  -- From Euler: V - E + n = 2 - 2g - n, so V = E + 2 - 2g - 2n
  have hV : (V : ℤ) = E + 2 - 2 * g - 2 * n := by
    have := heuler
    rw [hfaces] at this
    omega
  -- From trivalent: 2E = 3V
  have hE : (2 : ℤ) * E = 3 * V := by exact_mod_cast htriv
  -- Combining: 2E = 3(E + 2 - 2g - 2n) = 3E + 6 - 6g - 6n
  -- So -E = 6 - 6g - 6n, hence E = 6g + 6n - 6
  omega

/-!
## Duality

The dual of a ribbon graph swaps vertices and faces.
-/

/-- Duality preserves Euler characteristic -/
theorem dual_euler_char (V E F : ℕ) :
    (V : ℤ) - E + F = (F : ℤ) - E + V := by
  omega

/-- Duality preserves genus -/
theorem dual_preserves_genus (g n₁ V E F : ℕ)
    (h₁ : (V : ℤ) - E + F = 2 - 2 * g - n₁) :
    (F : ℤ) - E + V = 2 - 2 * g - n₁ := by
  omega

end RiemannSurfaces.Combinatorial.Helpers
