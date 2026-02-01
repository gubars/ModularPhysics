# Topology Module - Development Roadmap

## Goal
Develop infrastructure for stable homotopy theory and spectra, with the long-term aim of
formalizing Topological Modular Forms (TMF).

## Current Status

### What Mathlib Provides
- **Homotopy groups** `π_n X x` via `GenLoop` (Mathlib.Topology.Homotopy.HomotopyGroup)
- **Paths and homotopies** (Mathlib.Topology.Homotopy.Basic, Path)
- **Loop space** `Ω` as `Path x x` (not as a pointed space)
- **Model categories** (Mathlib.AlgebraicTopology.ModelCategory)
- **Simplicial sets** and Dold-Kan (Mathlib.AlgebraicTopology)
- **Triangulated categories** (Mathlib.CategoryTheory.Triangulated)
- **Pointed types** (Mathlib.CategoryTheory.Category.Pointed) - but NOT pointed topological spaces

### What We Need to Build
- Pointed topological spaces as a category
- Smash product X ∧ Y
- Wedge sum X ∨ Y
- Reduced suspension Σ and loop space Ω as functors on pointed spaces
- Σ ⊣ Ω adjunction
- Sequential spectra
- Homotopy groups of spectra
- Stable homotopy category

---

## Phase 1: Pointed Homotopy Theory

### 1.1 Pointed Spaces (`Homotopy/Pointed.lean`) ✓
- [x] Define `PointedTopSpace` structure (TopologicalSpace + basepoint)
- [x] Category instance for pointed spaces with continuous basepoint-preserving maps
- [x] Forgetful functor to TopCat
- [x] Examples: point, sphere0, pointedUnitInterval

### 1.2 Basic Constructions (`Homotopy/Constructions.lean`) ✓
- [x] Wedge sum X ∨ Y (coproduct in pointed spaces)
- [x] Smash product X ∧ Y (X × Y / X ∨ Y)
- [x] Prove: smash is symmetric (smashSymm_symm)
- [x] Reduced cone CX = X ∧ I₊
- [ ] Reduced suspension ΣX = S¹ ∧ X (alternative formulation)

### 1.3 Loop Space and Suspension (`Homotopy/Suspension.lean`) ✓
- [x] Loop space functor Ω: PointedSpace → PointedSpace
- [x] Reduced suspension Σ₊: PointedSpace → PointedSpace (as quotient)
- [x] Iterated loop space Ω^n and suspension Σ^n
- [x] Loop space map functoriality (Ωf for f : X → Y)
- [x] Continuity of loopSpaceMap
- [x] Σ ⊣ Ω adjunction unit η : X → Ω(ΣX)

### 1.4 Fiber and Cofiber Sequences (`Homotopy/Sequences.lean`) ◐
- [x] Mapping cone / cofiber Cf (via EqvGen.setoid)
- [x] Mapping fiber / homotopy fiber Ff (as subspace of X × PathsToBase)
- [x] Cofiber inclusion X → Cf and cone map CA → Cf
- [x] Puppe sequence of spaces: A, X, Cf, ΣA, ΣX, ΣCf, ...
- [x] Connecting map Cf → ΣA in cofiber sequence (via coneToSuspension)
- [x] Fiber sequence map: ΩY → Ff (fiberInclusionFromLoop)
- [x] Induced maps on homotopy groups (fiberProjectionInduced, cofiberInclusionInduced, etc.)
- [x] fiber_sequence_exact_at_Ff: composition ΩY → Ff → X is trivial
- [x] cofiber_sequence_composition_induced: functoriality of cofiber sequence
- [ ] fiber_sequence_ker_eq_im: exactness at Ff (1 sorry - requires lifting)

---

## Phase 2: Sequential Spectra

### 1.5 Weak Homotopy Equivalence (`Homotopy/WeakEquivalence.lean`) ✓
- [x] Induced map on generalized loops: γ ↦ f ∘ γ
- [x] Induced map on homotopy groups: inducedπ n f
- [x] Functoriality: (g ∘ f)_* = g_* ∘ f_*
- [x] IsWeakHomotopyEquivalence: bijections on all π_n

### 1.6 Loop Space Isomorphism (`Homotopy/LoopSpaceIso.lean`) ◐
- [x] Connection between PointedTopSpace.loopSpace and Mathlib's LoopSpace
- [x] Curry homeomorphism via GenLoop.loopHomeo
- [x] Type signature for π_n(ΩX) ≅ π_{n+1}(X)
- [ ] Full proof of loopSpaceHomotopyGroupEquiv (3 sorrys)
- [x] spectrumTransitionMap: composed transition for spectrum homotopy groups

---

## Phase 2: Sequential Spectra

### 2.1 Definition (`Spectra/Basic.lean`) ✓
- [x] Sequential spectrum: sequence {Xₙ} with adjoint structure maps εₙ: Xₙ → ΩX_{n+1}
- [x] Category instance for Spectrum with SpectrumHom
- [x] Ω-spectrum predicate using proper weak homotopy equivalence
- [x] Examples: trivial spectrum, suspension spectrum

### 2.2 Homotopy Groups (`Spectra/HomotopyGroups.lean`) ✓
- [x] levelHomotopyGroup, loopLevelHomotopyGroup accessors
- [x] structureMapInduced: π_n(E_k) → π_n(ΩE_{k+1})
- [x] transitionMap: full transition π_n(E_k) → π_{n+1}(E_{k+1})
- [x] Colimit index system: startIndex, levelIndex, colimitTerm
- [x] StableHomotopyGroupRep: representation type for colimit elements
- [x] StableHomotopyGroup: proper quotient by equivalence relation
- [x] Transitivity of equivalence relation (imageAtLevel_compose proved)
- [ ] Long exact sequence for spectrum maps

### 2.3 Basic Examples (`Spectra/Examples.lean`) ◐
- [x] Properties of suspension spectra (level theorems)
- [x] suspensionMap: Σ functoriality on pointed maps
- [x] iteratedSuspensionMap: Σ^n functoriality
- [x] suspensionSpectrumMap: functoriality Σ^∞X → Σ^∞Y (1 sorry: naturality)
- [x] Properties of sphere spectrum (level theorems)
- [x] shiftSpectrum: shift operation E[1]_n = E_{n+1}
- [x] mkSpectrum: construct spectrum from spaces + structure maps
- [x] trivial_isOmegaSpectrum ✓ (proved: homotopy groups of Unit are subsingletons)
- [x] EilenbergMacLaneSpectrum structure (proper structure, not axiom)
- [ ] eilenbergMacLane_unique (1 sorry: uniqueness theorem)

---

## Phase 3: Stable Homotopy Category

### 3.1 Triangulated Structure (`Spectra/Triangulated.lean`)
- [ ] Stable homotopy category Ho(Sp)
- [ ] Shift functor [1] = Σ
- [ ] Distinguished triangles from cofiber sequences
- [ ] Verify triangulated category axioms

### 3.2 Smash Product (`Spectra/SmashProduct.lean`)
- [ ] Smash product of spectra X ∧ Y (requires care!)
- [ ] Symmetric monoidal structure
- [ ] Ring spectra (monoids in spectra)

---

## Phase 4: Cohomology Theories (Future)

### 4.1 Brown Representability
- [ ] Statement: cohomology theories ↔ spectra
- [ ] E^n(X) = [Σ^∞X, Σ^n E] for spectrum E

### 4.2 Examples
- [ ] Singular cohomology via HZ
- [ ] K-theory spectrum (later)

---

## Phase 5: Toward TMF (Long-term)

### 5.1 Prerequisites
- [ ] Formal group laws
- [ ] Complex cobordism MU
- [ ] Landweber exact functor theorem

### 5.2 Elliptic Cohomology
- [ ] Elliptic curves → formal groups
- [ ] Elliptic spectra

### 5.3 TMF
- [ ] Moduli stack of elliptic curves
- [ ] TMF as global sections of sheaf of E_∞ ring spectra

---

---

## Remaining Sorrys (6 total)

All sorrys are for substantive mathematical theorems requiring careful proof work.
No placeholders, axioms, or empty definitions remain.

### LoopSpaceIso.lean (3 sorrys)
1. `uncurry_homotopic_of_path_homotopic` - Preservation of homotopy under uncurrying
   - Uses: GenLoop.loopHomeo preserves homotopy
2. `loopSpaceHomotopyGroupEquiv` - The main π_n(ΩX) ≅ π_{n+1}(X) equivalence
   - Requires: Connecting Path-based loop space to GenLoop, using loopHomeo + Quotient.congr
3. `loopSpaceHomotopyGroupEquiv_mul` - Group homomorphism property
   - Follows from: Loop concatenation compatibility

### HomotopyGroups.lean (0 sorrys) ✓
- `StableHomotopyGroupRep.Equiv.trans` - PROVED via imageAtLevel_compose
- `imageAtLevel_compose` - PROVED by strong induction on (M - n)

### Examples.lean (2 sorrys)
4. `suspensionSpectrumMap.comm` - Naturality of suspension unit
   - Requires: η natural transformation property
5. `eilenbergMacLane_unique` - Uniqueness of EM spectra
   - Requires: Uniqueness of K(R,n) spaces up to weak equivalence

### Sequences.lean (1 sorry)
6. `fiber_sequence_ker_eq_im` - Exactness of fiber sequence
   - Requires: Lifting property for null-homotopic maps through fiber

---

## Design Principles

1. **Sound definitions**: No placeholders, no axioms, no arbitrary choices
2. **Build on Mathlib**: Use existing TopCat, homotopy infrastructure
3. **Category-theoretic**: Define as categories/functors where possible
4. **Prove as we go**: Don't accumulate sorrys

## Key References

- May, "A Concise Course in Algebraic Topology"
- Adams, "Stable Homotopy and Generalised Homology"
- Lurie, "Higher Algebra" (for ∞-categorical perspective)
- Hopkins, "Spectra and stable homotopy theory" (lecture notes)

## Dependencies

```
Homotopy/Pointed.lean
    ↓
Homotopy/Constructions.lean (wedge, smash)
    ↓
Homotopy/Suspension.lean (Σ, Ω, adjunction)
    ↓                          ↓
Homotopy/Sequences.lean    Homotopy/WeakEquivalence.lean
(cofiber, fiber)           (induced maps, weak equiv)
    ↓                          ↓
    │                    Homotopy/LoopSpaceIso.lean
    │                    (π_n(ΩX) ≅ π_{n+1}(X))
    │                          ↓
    └──────────┬───────────────┘
               ↓
        Spectra/Basic.lean
               ↓
        Spectra/HomotopyGroups.lean
               ↓
        Spectra/Examples.lean
```
