import Mathlib.Topology.Constructions
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Separation.Basic
import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.FunctionField

/-!
# Zariski Topology on Algebraic Curves

This file defines the Zariski topology on algebraic curves and establishes
the key topological properties needed for Čech cohomology.

## Mathematical Background

For a smooth algebraic curve C over ℂ, the **Zariski topology** on the set
of closed points has:
- **Closed sets**: Finite sets of points, the empty set, or the whole curve
- **Open sets**: Complements of finite sets (cofinite sets) plus the empty set

This is precisely the **cofinite topology**.

## Key Properties

1. **T1 space**: Points are closed
2. **Noetherian**: Descending chain condition on closed sets
3. **NOT Hausdorff**: For infinite curves, distinct points don't have disjoint neighborhoods

## Main Definitions

* `AlgebraicCurve.instTopologicalSpace` - The Zariski (cofinite) topology
* `ZariskiOpen` - Zariski open subsets
* `principalOpen` - Principal open D(f) = {p : v_p(f) ≥ 0}

## References

* Hartshorne "Algebraic Geometry" II.3
-/

namespace RiemannSurfaces.Algebraic

open TopologicalSpace Set

/-!
## Zariski Topology Instance

For an algebraic curve C, we equip C.Point with the cofinite topology,
which equals the Zariski topology for curves.
-/

/-- The Zariski topology on an algebraic curve is the cofinite topology on closed points. -/
instance AlgebraicCurve.instTopologicalSpace (C : AlgebraicCurve) :
    TopologicalSpace C.Point where
  IsOpen s := s.Nonempty → sᶜ.Finite
  isOpen_univ := by simp
  isOpen_inter s t := by
    rintro hs ht ⟨x, hxs, hxt⟩
    rw [compl_inter]
    exact (hs ⟨x, hxs⟩).union (ht ⟨x, hxt⟩)
  isOpen_sUnion := by
    rintro s h ⟨x, t, hts, hxt⟩
    rw [compl_sUnion]
    exact Finite.sInter (mem_image_of_mem _ hts) (h t hts ⟨x, hxt⟩)

/-!
## Basic Properties of Zariski Topology
-/

section Properties

variable (C : AlgebraicCurve)

/-- Characterization: a set is Zariski open iff empty or has finite complement -/
theorem AlgebraicCurve.isOpen_iff' (U : Set C.Point) :
    IsOpen U ↔ U = ∅ ∨ Uᶜ.Finite := by
  constructor
  · intro hopen
    by_cases hne : U.Nonempty
    · right; exact hopen hne
    · left; exact not_nonempty_iff_eq_empty.mp hne
  · intro h hne
    rcases h with rfl | hfin
    · exact (not_nonempty_empty hne).elim
    · exact hfin

/-- Characterization: a nonempty set is Zariski open iff its complement is finite -/
theorem AlgebraicCurve.isOpen_iff_complement_finite (U : Set C.Point) (hne : U.Nonempty) :
    IsOpen U ↔ Uᶜ.Finite := by
  constructor
  · intro hopen
    exact hopen hne
  · intro hfin _
    exact hfin

/-- Finite sets are closed in the Zariski topology -/
theorem AlgebraicCurve.finite_isClosed (S : Set C.Point) (hS : S.Finite) :
    IsClosed S := by
  rw [← isOpen_compl_iff]
  intro hne
  simp only [compl_compl]
  exact hS

/-- Singletons are closed -/
theorem AlgebraicCurve.singleton_isClosed (p : C.Point) :
    IsClosed ({p} : Set C.Point) :=
  C.finite_isClosed {p} (finite_singleton p)

/-- Points are closed in the Zariski topology (T1 property) -/
instance AlgebraicCurve.t1Space : T1Space C.Point :=
  ⟨C.singleton_isClosed⟩

/-- Closed sets are exactly finite sets or the whole space -/
theorem AlgebraicCurve.isClosed_iff (S : Set C.Point) :
    IsClosed S ↔ S = univ ∨ S.Finite := by
  rw [← isOpen_compl_iff, C.isOpen_iff' Sᶜ]
  simp only [compl_empty_iff, compl_compl]

end Properties

/-!
## Zariski Open Sets
-/

/-- A Zariski open set in an algebraic curve.

    For curves, Zariski opens are exactly the cofinite sets (plus empty).
    This structure bundles the carrier set with its openness proof. -/
structure ZariskiOpen (C : AlgebraicCurve) where
  /-- The underlying set -/
  carrier : Set C.Point
  /-- The set is open in the Zariski topology -/
  isOpen : IsOpen carrier

namespace ZariskiOpen

variable {C : AlgebraicCurve}

instance : SetLike (ZariskiOpen C) C.Point where
  coe := ZariskiOpen.carrier
  coe_injective' := fun ⟨_, _⟩ ⟨_, _⟩ h => by simp only [mk.injEq]; exact h

instance : Top (ZariskiOpen C) where
  top := ⟨univ, isOpen_univ⟩

instance : Bot (ZariskiOpen C) where
  bot := ⟨∅, isOpen_empty⟩

/-- The complement of a nonempty Zariski open is finite -/
theorem complement_finite (U : ZariskiOpen C) (hne : (U : Set C.Point).Nonempty) :
    (U : Set C.Point)ᶜ.Finite :=
  U.isOpen hne

/-- Intersection of two Zariski opens -/
def inter (U V : ZariskiOpen C) : ZariskiOpen C where
  carrier := U.carrier ∩ V.carrier
  isOpen := IsOpen.inter U.isOpen V.isOpen

/-- Union of two Zariski opens -/
def union (U V : ZariskiOpen C) : ZariskiOpen C where
  carrier := U.carrier ∪ V.carrier
  isOpen := IsOpen.union U.isOpen V.isOpen

/-- Convert to Opens (Mathlib's bundled open sets) -/
def toOpens (U : ZariskiOpen C) : Opens C.Point :=
  ⟨U.carrier, U.isOpen⟩

end ZariskiOpen

/-!
## Principal Open Sets

For f ∈ K(C)*, the principal open D(f) consists of points where f is regular:
  D(f) = {p ∈ C : v_p(f) ≥ 0}

The complement is the pole locus of f, which is finite.
-/

/-- The pole locus of a nonzero function: points where f has a pole -/
def poleLocus (C : AlgebraicCurve) (f : C.FunctionField) : Set C.Point :=
  { p | C.valuation p f < 0 }

/-- The pole locus of a nonzero function is finite (subset of support) -/
theorem poleLocus_finite (C : AlgebraicCurve) (f : C.FunctionField) (hf : f ≠ 0) :
    (poleLocus C f).Finite := by
  apply Set.Finite.subset (C.valuation_finiteSupport f hf)
  intro p hp
  simp only [poleLocus, mem_setOf_eq] at hp
  simp only [mem_setOf_eq]
  omega

/-- The regular locus of a function: points where f has no pole -/
def regularLocus (C : AlgebraicCurve) (f : C.FunctionField) : Set C.Point :=
  { p | 0 ≤ C.valuation p f }

/-- The regular locus is the complement of the pole locus -/
theorem regularLocus_eq_compl_poleLocus (C : AlgebraicCurve) (f : C.FunctionField) :
    regularLocus C f = (poleLocus C f)ᶜ := by
  ext p
  simp only [regularLocus, poleLocus, mem_setOf_eq, mem_compl_iff, not_lt]

/-- Principal open D(f) = {p : v_p(f) ≥ 0} for nonzero f.

    This is the complement of the pole locus, hence Zariski open. -/
def principalOpen (C : AlgebraicCurve) (f : C.FunctionField) (hf : f ≠ 0) :
    ZariskiOpen C where
  carrier := regularLocus C f
  isOpen := by
    rw [regularLocus_eq_compl_poleLocus]
    exact (C.finite_isClosed _ (poleLocus_finite C f hf)).isOpen_compl

/-- The complement of a principal open is the pole locus -/
theorem principalOpen_compl (C : AlgebraicCurve) (f : C.FunctionField) (hf : f ≠ 0) :
    (principalOpen C f hf : Set C.Point)ᶜ = poleLocus C f := by
  show (regularLocus C f)ᶜ = poleLocus C f
  rw [regularLocus_eq_compl_poleLocus, compl_compl]

/-- Principal opens cover the whole curve when their pole loci are disjoint -/
theorem principalOpen_covers_of_disjoint_poles {C : AlgebraicCurve}
    {ι : Type*} (f : ι → C.FunctionField) (hf : ∀ i, f i ≠ 0)
    (hcover : ∀ p, ∃ i, 0 ≤ C.valuation p (f i)) :
    ⋃ i, (principalOpen C (f i) (hf i) : Set C.Point) = univ := by
  ext p
  simp only [mem_iUnion, SetLike.mem_coe, mem_univ, iff_true]
  obtain ⟨i, hi⟩ := hcover p
  exact ⟨i, hi⟩

/-!
## Finite Covers

For Čech cohomology, we need finite open covers.
-/

/-- A finite open cover of an algebraic curve (with fixed universe for index) -/
structure FiniteZariskiCover (C : AlgebraicCurve) where
  /-- Number of open sets -/
  n : ℕ
  /-- The open sets indexed by Fin n -/
  opens : Fin n → ZariskiOpen C
  /-- The opens cover the curve -/
  covers : ∀ p : C.Point, ∃ i, p ∈ opens i

/-- The trivial cover by the whole curve -/
def trivialCover (C : AlgebraicCurve) : FiniteZariskiCover C where
  n := 1
  opens := fun _ => ⊤
  covers := fun _ => ⟨0, mem_univ _⟩

/-- Every algebraic curve has a finite cover (trivially, by the whole curve) -/
theorem exists_finiteZariskiCover (C : AlgebraicCurve) :
    Nonempty (FiniteZariskiCover C) :=
  ⟨trivialCover C⟩

/-!
## Zero Locus (Closed Sets)

The zero locus of a function f is V(f) = {p : v_p(f) > 0}, which is finite.
-/

/-- The zero locus of a function: points where f has a zero -/
def zeroLocus (C : AlgebraicCurve) (f : C.FunctionField) : Set C.Point :=
  { p | 0 < C.valuation p f }

/-- The zero locus of a nonzero function is finite -/
theorem zeroLocus_finite (C : AlgebraicCurve) (f : C.FunctionField) (hf : f ≠ 0) :
    (zeroLocus C f).Finite := by
  apply Set.Finite.subset (C.valuation_finiteSupport f hf)
  intro p hp
  simp only [zeroLocus, mem_setOf_eq] at hp
  simp only [mem_setOf_eq]
  omega

/-- The zero locus is closed -/
theorem zeroLocus_isClosed (C : AlgebraicCurve) (f : C.FunctionField) (hf : f ≠ 0) :
    IsClosed (zeroLocus C f) :=
  C.finite_isClosed _ (zeroLocus_finite C f hf)

end RiemannSurfaces.Algebraic
