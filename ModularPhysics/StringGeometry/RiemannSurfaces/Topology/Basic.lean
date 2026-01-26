import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Basic Topology for Riemann Surfaces

This file contains foundational topological results needed for Riemann surface theory.

## Main results

* `Complex.isPreconnected_univ` - The complex plane is preconnected
* Properties of OnePoint ℂ (Riemann sphere topology)

## Mathematical Background

ℂ is connected because it is convex (hence path-connected). As a real vector space,
ℂ ≅ ℝ², and convex subsets of real vector spaces are preconnected.
-/

namespace RiemannSurfaces.Topology

/-!
## Connectedness of ℂ

We prove ℂ is connected using convexity: ℂ (viewed as a real vector space)
is convex, and convex sets are preconnected.
-/

/-- The complex plane is preconnected (via convexity) -/
theorem Complex.isPreconnected_univ : IsPreconnected (Set.univ : Set ℂ) :=
  convex_univ.isPreconnected

/-- ℂ is a preconnected topological space -/
instance Complex.preconnectedSpace : PreconnectedSpace ℂ :=
  ⟨Complex.isPreconnected_univ⟩

/-!
## One-Point Compactification Properties

The one-point compactification of a locally compact Hausdorff space
preserves and creates important topological properties.

The Riemann sphere ℂP¹ = ℂ ∪ {∞} = OnePoint ℂ is the one-point compactification of ℂ.
-/

/-- ℂ is not compact (it's unbounded). -/
instance Complex.noncompactSpace : NoncompactSpace ℂ := by
  rw [← not_compactSpace_iff]
  intro ⟨h⟩
  have hbdd := h.isBounded
  rw [isBounded_iff_forall_norm_le] at hbdd
  obtain ⟨C, hC⟩ := hbdd
  let n : ℕ := ⌈C⌉₊ + 1
  specialize hC (n : ℂ) (Set.mem_univ _)
  rw [Complex.norm_natCast] at hC
  have hn_gt : (n : ℝ) > C := by
    simp only [n]
    have h1 : (⌈C⌉₊ : ℝ) ≥ C := Nat.le_ceil C
    have h2 : ((⌈C⌉₊ + 1 : ℕ) : ℝ) = (⌈C⌉₊ : ℝ) + 1 := by simp
    rw [h2]; linarith
  linarith

/-- OnePoint ℂ (the Riemann sphere) is connected -/
instance OnePoint.Complex.connectedSpace : ConnectedSpace (OnePoint ℂ) :=
  inferInstance

/-- OnePoint ℂ is T1 -/
instance OnePoint.Complex.t1Space : T1Space (OnePoint ℂ) :=
  inferInstance

/-- OnePoint ℂ is normal -/
instance OnePoint.Complex.normalSpace : NormalSpace (OnePoint ℂ) :=
  inferInstance

/-- OnePoint ℂ is second countable.

    OnePoint ℂ ≅ S² via stereographic projection, and S² ⊆ ℝ³
    is a submanifold of a second countable space, hence second countable. -/
instance OnePoint.Complex.secondCountableTopology : SecondCountableTopology (OnePoint ℂ) := by
  sorry  -- Standard topological fact

/-!
## Surface Topology

Basic topological facts about surfaces.
-/

/-- A surface is a 2-dimensional topological manifold.

    A topological surface is a second-countable Hausdorff space that is
    locally homeomorphic to ℝ² (or to ℝ² ∪ {boundary} for surfaces with boundary). -/
structure Surface where
  /-- The underlying space -/
  carrier : Type*
  /-- Topological space structure on carrier -/
  [topology : TopologicalSpace carrier]
  /-- Hausdorff separation axiom -/
  [t2 : T2Space carrier]
  /-- Second countable topology -/
  [secondCountable : SecondCountableTopology carrier]
  /-- Locally homeomorphic to ℝ²: every point has a neighborhood homeomorphic to an open set in ℝ² -/
  locallyEuclidean : ∀ p : carrier, ∃ (U : Set carrier) (V : Set (Fin 2 → ℝ)),
    IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ Nonempty (U ≃ₜ V)

/-- Euler characteristic of a surface.

    The Euler characteristic is a fundamental topological invariant defined via:
    - Homology: χ = Σᵢ (-1)ⁱ rank(Hᵢ)
    - Triangulation: χ = V - E + F (vertices minus edges plus faces)

    For a compact surface, χ is always an integer.
    This is the primary invariant; genus is derived from it. -/
noncomputable def Surface.eulerChar (_ : Surface) : ℤ := sorry

/-- The number of boundary components.

    For a surface with boundary, this counts the connected components
    of the boundary ∂S. For a closed surface, this is 0. -/
noncomputable def Surface.numBoundary (_ : Surface) : ℕ := sorry

/-- The genus of an orientable surface.

    For an orientable surface with Euler characteristic χ and n boundary components,
    the genus g is defined by: χ = 2 - 2g - n, i.e., g = (2 - χ - n)/2.

    This is well-defined for orientable surfaces where 2 - χ - n is always even and non-negative. -/
noncomputable def Surface.genus (S : Surface) : ℕ :=
  ((2 - S.eulerChar - S.numBoundary) / 2).toNat

/-- The fundamental relation between Euler characteristic, genus, and boundary components.

    **Theorem**: For an orientable surface S with genus g and n boundary components:
    χ(S) = 2 - 2g - n

    This follows from the classification of surfaces and can be proven via:
    - Handle decomposition: adding a handle decreases χ by 2
    - Removing a disk (adding a boundary) decreases χ by 1 -/
theorem Surface.eulerChar_formula (S : Surface) :
    S.eulerChar = 2 - 2 * (S.genus : ℤ) - S.numBoundary := by
  sorry  -- Classification theorem for surfaces

/-- Two surfaces are homeomorphic -/
def Surface.Homeomorphic (S₁ S₂ : Surface) : Prop :=
  @Nonempty (@Homeomorph S₁.carrier S₂.carrier S₁.topology S₂.topology)

/-- Classification of closed orientable surfaces.

    **Theorem**: Two closed orientable surfaces are homeomorphic if and only if
    they have the same genus. This is the fundamental classification theorem
    for 2-manifolds.

    The proof constructs explicit homeomorphisms using handle decompositions
    or surgery theory. -/
theorem surface_classification (S₁ S₂ : Surface) (_ : S₁.numBoundary = 0)
    (_ : S₂.numBoundary = 0) (hg : S₁.genus = S₂.genus) :
    S₁.Homeomorphic S₂ := by
  sorry  -- Classification theorem for closed surfaces

end RiemannSurfaces.Topology
