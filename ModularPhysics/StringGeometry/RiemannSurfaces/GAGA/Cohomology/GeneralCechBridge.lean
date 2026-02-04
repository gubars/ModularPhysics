import ModularPhysics.Topology.Sheaves.CechCohomology
import ModularPhysics.StringGeometry.RiemannSurfaces.GAGA.Cohomology.MathlibBridge
import Mathlib.Topology.Sets.Opens

/-!
# Bridge to General Čech Cohomology Infrastructure

This file bridges the general Čech cohomology infrastructure in
`ModularPhysics.Topology.Sheaves.CechCohomology` with the Riemann surface
sheaf definitions.

## Main Constructions

* `coherentSheafToAbPresheaf` - Converts `CoherentSheaf RS O` to `AbPresheaf`
* `coverToOpenCover` - Converts Riemann surface covers to general open covers
* Transfer theorems showing that the Riemann surface Čech definitions
  match the general infrastructure

## Mathematical Background

The general Čech cohomology framework works with:
- `AbPresheaf X` - presheaves of abelian groups on any topological space X
- `OpenCover X` - indexed open covers
- `CechCochain F U n` - n-cochains for arbitrary n
- `cechDiff` - the general Čech differential with alternating signs

The key theorem `cechDiff_comp_zero` proves d² = 0 in full generality.

This bridge allows us to use the general infrastructure for Riemann surfaces
while maintaining compatibility with the existing coherent sheaf definitions.

## References

* General infrastructure: `ModularPhysics/Topology/Sheaves/CechCohomology.lean`
* Riemann surface sheaves: `ModularPhysics/StringGeometry/RiemannSurfaces/Algebraic/Cohomology/`
-/

namespace RiemannSurfaces.Algebraic.Cohomology.GeneralCechBridge

open RiemannSurfaces TopologicalSpace

-- Bring MathlibBridge definitions into scope
open RiemannSurfaces.Algebraic.Cohomology.MathlibBridge

/-!
## Topological Space Instance

The general Čech cohomology infrastructure requires `TopologicalSpace X`.
For a Riemann surface RS, we use `RS.topology` on `RS.carrier`.
-/

/-- Provide TopologicalSpace instance for Riemann surface carrier -/
instance RiemannSurface.instTopologicalSpace (RS : RiemannSurface) : TopologicalSpace RS.carrier :=
  RS.topology

/-!
## Converting Opens

The general infrastructure uses `Opens X` (from Mathlib), while Riemann surface
code uses `OpenSet RS`. We establish the correspondence.
-/

/-- Convert our OpenSet to Mathlib's Opens -/
def OpenSet.toOpens {RS : RiemannSurface} (U : OpenSet RS) : Opens RS.carrier :=
  ⟨U.carrier, U.isOpen⟩

/-- Convert Mathlib's Opens to our OpenSet -/
def OpenSet.fromOpens {RS : RiemannSurface} (U : Opens RS.carrier) : OpenSet RS :=
  ⟨U.carrier, U.isOpen⟩

/-- Roundtrip fromOpens ∘ toOpens = id -/
theorem OpenSet.fromOpens_toOpens {RS : RiemannSurface} (U : OpenSet RS) :
    OpenSet.fromOpens (OpenSet.toOpens U) = U := by
  simp only [OpenSet.fromOpens, OpenSet.toOpens]

/-- Roundtrip toOpens ∘ fromOpens = id -/
theorem OpenSet.toOpens_fromOpens {RS : RiemannSurface} (U : Opens RS.carrier) :
    OpenSet.toOpens (OpenSet.fromOpens U) = U := by
  simp only [OpenSet.fromOpens, OpenSet.toOpens]

/-!
## Converting Coherent Sheaves to AbPresheaf

A coherent sheaf on a Riemann surface can be viewed as an AbPresheaf
(presheaf of abelian groups) by forgetting the module structure.
-/

/-- Convert a CoherentSheaf to an AbPresheaf on the underlying topological space.

    This forgets the O-module structure and retains only the abelian group structure.
    The key properties (restrict_id, restrict_comp, restrict_add) are inherited. -/
noncomputable def coherentSheafToAbPresheaf {RS : RiemannSurface} {O : StructureSheaf RS}
    (F : CoherentSheaf RS O) : CechCohomology.AbPresheaf RS.carrier where
  sections := fun U => F.sections (OpenSet.fromOpens U)
  addCommGroup := fun U => F.addCommGroup (OpenSet.fromOpens U)
  restrict := fun {U V} h s => F.restrict (fun x hx => h hx) s
  restrict_id := fun U s => F.restrict_id (OpenSet.fromOpens U) s
  restrict_comp := fun {U V W} h₁ h₂ s => by
    simp only [F.restrict_comp]
  restrict_add := fun {U V} h s t => F.restrict_add _ s t

/-- Derive AddCommGroup from CommRing for structure sheaf sections -/
noncomputable instance StructureSheaf.addCommGroupOfCommRing {RS : RiemannSurface}
    (O : StructureSheaf RS) (U : OpenSet RS) : AddCommGroup (O.sections U) :=
  @Ring.toAddCommGroup _ (@CommRing.toRing _ (O.algebraStructure U))

/-- The structure sheaf as an AbPresheaf -/
noncomputable def structureSheafToAbPresheaf {RS : RiemannSurface}
    (O : StructureSheaf RS) : CechCohomology.AbPresheaf RS.carrier where
  sections := fun U => O.sections (OpenSet.fromOpens U)
  addCommGroup := fun U => StructureSheaf.addCommGroupOfCommRing O (OpenSet.fromOpens U)
  restrict := fun {U V} h s => O.restrict (fun x hx => h hx) s
  restrict_id := fun U s => O.restrict_id (OpenSet.fromOpens U) s
  restrict_comp := fun {U V W} h₁ h₂ s => by
    simp only [O.restrict_comp]
  restrict_add := fun {U V} h s t => O.restrict_add _ s t

/-!
## Converting Covers

The MathlibBridge uses `Cover RS U` (cover of a specific open set U).
The general infrastructure uses `OpenCover X` (cover of the whole space X).

For a compact Riemann surface, we typically use a cover of the whole space.
-/

/-- Convert a Cover of the whole space to a general OpenCover -/
def coverToOpenCover {RS : RiemannSurface} (cov : Cover RS OpenSet.univ) :
    CechCohomology.OpenCover RS.carrier where
  ι := cov.ι
  cover := fun i => OpenSet.toOpens (cov.opens i)
  covers := fun x => by
    have h := cov.covers (Set.mem_univ x)
    simp only [OpenSet.union, Set.mem_iUnion] at h
    obtain ⟨i, hi⟩ := h
    exact ⟨i, hi⟩

/-!
## Correspondence of Čech Cochains

The specialized Čech definitions in MathlibBridge (Cech0, Cech1) correspond
to the general definitions for n = 0, 1. The correspondence is via the
fact that:
- For n = 0: `(coverToOpenCover cov).inter (fun _ => i) = coverToOpenCover cov).cover i`
- For n = 1: `(coverToOpenCover cov).inter ![i,j] = (cover i) ⊓ (cover j)`

The opens are isomorphic via `OpenSet.toOpens`/`OpenSet.fromOpens`, though
the correspondence is not definitional equality.
-/

/-- For n = 0, the intersection with constant function equals the single open -/
theorem inter_const_eq_cover {RS : RiemannSurface} (cov : Cover RS OpenSet.univ) (i : cov.ι) :
    (coverToOpenCover cov).inter (fun _ : Fin 1 => i) = (coverToOpenCover cov).cover i := by
  unfold CechCohomology.OpenCover.inter coverToOpenCover
  -- The inf over Fin 1 is just the single element
  exact Finset.inf_singleton

/-- For n = 1, the intersection with a 2-element function equals the binary inf -/
theorem inter_pair_eq_inf {RS : RiemannSurface} (cov : Cover RS OpenSet.univ) (i j : cov.ι) :
    (coverToOpenCover cov).inter (![i, j] : Fin 2 → cov.ι) =
    (coverToOpenCover cov).cover i ⊓ (coverToOpenCover cov).cover j := by
  unfold CechCohomology.OpenCover.inter coverToOpenCover
  -- The inf over Fin 2 is the inf of the two elements
  have h : Finset.univ (α := Fin 2) = {0, 1} := Finset.univ_fin2
  rw [h]
  simp only [Finset.inf_insert, Finset.inf_singleton, Matrix.cons_val_zero, Matrix.cons_val_one]

/-!
## Key Result: d² = 0 Transfers

The general `cechDiff_comp_zero` theorem gives d² = 0 for all n.
This immediately gives us d¹ ∘ d⁰ = 0 for Riemann surface Čech cohomology.
-/

/-- The general d² = 0 theorem specialized to our setting.

    This shows that for any coherent sheaf on a Riemann surface,
    the Čech differential satisfies d² = 0. This is the key result
    that makes Čech cohomology well-defined. -/
theorem cechDiff_comp_zero_coherent {RS : RiemannSurface} {O : StructureSheaf RS}
    (F : CoherentSheaf RS O) (cov : Cover RS OpenSet.univ)
    (n : ℕ) (σ : CechCohomology.CechCochain (coherentSheafToAbPresheaf F) (coverToOpenCover cov) n) :
    CechCohomology.cechDiff (coherentSheafToAbPresheaf F) (coverToOpenCover cov) (n + 1)
      (CechCohomology.cechDiff (coherentSheafToAbPresheaf F) (coverToOpenCover cov) n σ) = 0 :=
  CechCohomology.cechDiff_comp_zero (coherentSheafToAbPresheaf F) (coverToOpenCover cov) n σ

/-!
## Čech Cohomology Groups

Using the general infrastructure, we get well-defined Čech cohomology groups
for any coherent sheaf on a Riemann surface.
-/

/-- H^n(U, F) using the general Čech infrastructure -/
def CechCohomologyGroup {RS : RiemannSurface} {O : StructureSheaf RS}
    (F : CoherentSheaf RS O) (cov : Cover RS OpenSet.univ) (n : ℕ) : Type _ :=
  CechCohomology.CechH (coherentSheafToAbPresheaf F) (coverToOpenCover cov) n

/-- H⁰(U, F) is the group of 0-cocycles -/
theorem cechH0_eq {RS : RiemannSurface} {O : StructureSheaf RS}
    (F : CoherentSheaf RS O) (cov : Cover RS OpenSet.univ) :
    CechCohomologyGroup F cov 0 = CechCohomology.CechH0 (coherentSheafToAbPresheaf F) (coverToOpenCover cov) := rfl

/-- H^{n+1}(U, F) is the quotient Z^{n+1}/B^{n+1} -/
theorem cechHSucc_eq {RS : RiemannSurface} {O : StructureSheaf RS}
    (F : CoherentSheaf RS O) (cov : Cover RS OpenSet.univ) (n : ℕ) :
    CechCohomologyGroup F cov (n + 1) =
      CechCohomology.CechHSucc (coherentSheafToAbPresheaf F) (coverToOpenCover cov) n := rfl

end RiemannSurfaces.Algebraic.Cohomology.GeneralCechBridge
