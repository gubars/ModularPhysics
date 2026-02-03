# Topology Module - Development Roadmap

## Goal
Develop infrastructure for stable homotopy theory and spectra, with the long-term aim of
formalizing Topological Modular Forms (TMF).

---

## Near-Term Development Focus

### Priority 1: Long Exact Sequence for Spectrum Maps
**File:** `Spectra/HomotopyGroups.lean`

The key missing piece for computing stable homotopy groups is the long exact sequence
associated with a map of spectra f : E → F. This involves:

1. **Cofiber spectrum Cf** - Given f : E → F, define the cofiber spectrum levelwise
   - (Cf)_n = cofiber(f_n : E_n → F_n)
   - Structure maps from the levelwise cofiber sequence

2. **Induced maps on stable homotopy groups**
   - f_* : π_k(E) → π_k(F)
   - i_* : π_k(F) → π_k(Cf)  (cofiber inclusion)
   - ∂ : π_k(Cf) → π_{k-1}(E)  (connecting map)

3. **Exactness** - Prove the sequence is exact:
   ```
   ... → π_k(E) → π_k(F) → π_k(Cf) → π_{k-1}(E) → ...
   ```

**Dependencies:** Uses existing infrastructure from Sequences.lean (fiber_sequence_ker_eq_im)
and the stable homotopy group quotient construction.

### Priority 2: Cofiber Spectrum Definition ◐
**File:** `Spectra/Cofiber.lean`

Define the cofiber of a spectrum map and verify it forms a spectrum:
- [x] `cofiberSpaceAt`: (Cf)_n = mappingCone(f_n)
- [x] `cofiberStructureMap`: structure map Cf_n → Ω(Cf_{n+1})
- [x] `cofiberSpectrum`: the cofiber spectrum Cf for f : E ⟶ F
- [x] `cofiberInclusionSpectrum`: inclusion F → Cf (comm proof pending)
- [ ] `cofiberInclusionSpectrum.comm`: compatibility with structure maps
- [ ] `connectingMapSpectrum`: connecting map Cf → E[1]
- [ ] Long exact sequence for stable homotopy groups

### Priority 3: Induced Maps on Stable π_k ✓ COMPLETED
**File:** `Spectra/HomotopyGroups.lean`

For a spectrum map f : E ⟶ F, define:
- [x] `stableπInduced f : StableHomotopyGroup E k → StableHomotopyGroup F k`
- [x] Well-defined on the quotient (via `colimitTermInduced_preserves_equiv`)
- [x] Functoriality: `stableπInduced_id`, `stableπInduced_comp`

### Priority 4: Group Structure on Stable π_k ◐
**File:** `Spectra/HomotopyGroups.lean`

The stable homotopy groups should be abelian groups (not just sets):
- [x] `inducedπ_mul`: induced maps preserve multiplication (WeakEquivalence.lean)
- [x] `inducedGenLoop_transAt`: induced maps commute with transAt
- [x] `structureMapInduced_mul`: structure map induced preserves multiplication
- [x] `transitionMap_mul`: full transition map preserves multiplication
- [x] `groupStartIndex`: minimum level for group structure
- [x] `levelIndex_ge_one_at_groupStart`: at groupStartIndex, level index ≥ 1
- [ ] Define addition on StableHomotopyGroup using the group structure on π_{n+k}(E_n)
- [ ] Prove well-defined on quotient
- [ ] Prove abelian group axioms
- [ ] Prove induced maps are group homomorphisms

---

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

### 1.4 Fiber and Cofiber Sequences (`Homotopy/Sequences.lean`) ✓
- [x] Mapping cone / cofiber Cf (via EqvGen.setoid)
- [x] Mapping fiber / homotopy fiber Ff (as subspace of X × PathsToBase)
- [x] Cofiber inclusion X → Cf and cone map CA → Cf
- [x] Puppe sequence of spaces: A, X, Cf, ΣA, ΣX, ΣCf, ...
- [x] Connecting map Cf → ΣA in cofiber sequence (via coneToSuspension)
- [x] Fiber sequence map: ΩY → Ff (fiberInclusionFromLoop)
- [x] Induced maps on homotopy groups (fiberProjectionInduced, cofiberInclusionInduced, etc.)
- [x] fiber_sequence_exact_at_Ff: composition ΩY → Ff → X is trivial
- [x] cofiber_sequence_composition_induced: functoriality of cofiber sequence
- [x] fiber_sequence_ker_eq_im: exactness at Ff ✓ (HomotopyRel lift construction)

---

## Phase 2: Sequential Spectra

### 1.5 Weak Homotopy Equivalence (`Homotopy/WeakEquivalence.lean`) ✓
- [x] Induced map on generalized loops: γ ↦ f ∘ γ
- [x] Induced map on homotopy groups: inducedπ n f
- [x] Functoriality: (g ∘ f)_* = g_* ∘ f_*
- [x] IsWeakHomotopyEquivalence: bijections on all π_n

### 1.6 Loop Space Isomorphism (`Homotopy/LoopSpaceIso.lean`) ✓
- [x] Connection between PointedTopSpace.loopSpace and Mathlib's LoopSpace
- [x] Curry homeomorphism via GenLoop.loopHomeo
- [x] Type signature for π_n(ΩX) ≅ π_{n+1}(X)
- [x] genLoopCurryEquiv: Equivalence GenLoop (Fin n) (Path x x) ≃ GenLoop (Fin (n+1)) X
- [x] genLoopCurryEquiv_homotopic: Forward homotopy preservation
- [x] genLoopCurryEquiv_homotopic_inv: Backward homotopy preservation
- [x] loopSpaceHomotopyGroupEquiv: π_n(ΩX) ≃ π_{n+1}(X) as sets
- [x] loopSpaceHomotopyGroupEquiv_mul: Group homomorphism property ✓
- [x] spectrumTransitionMap: composed transition for spectrum homotopy groups

---

## Phase 2: Sequential Spectra

### 2.1 Definition (`Spectra/Basic.lean`) ✓
- [x] Sequential spectrum: sequence {Xₙ} with adjoint structure maps εₙ: Xₙ → ΩX_{n+1}
- [x] Category instance for Spectrum with SpectrumHom
- [x] Ω-spectrum predicate using proper weak homotopy equivalence
- [x] Examples: trivial spectrum, suspension spectrum

### 2.2 Homotopy Groups (`Spectra/HomotopyGroups.lean`) ◐
- [x] levelHomotopyGroup, loopLevelHomotopyGroup accessors
- [x] structureMapInduced: π_n(E_k) → π_n(ΩE_{k+1})
- [x] transitionMap: full transition π_n(E_k) → π_{n+1}(E_{k+1})
- [x] Colimit index system: startIndex, levelIndex, colimitTerm
- [x] StableHomotopyGroupRep: representation type for colimit elements
- [x] StableHomotopyGroup: proper quotient by equivalence relation
- [x] Transitivity of equivalence relation (imageAtLevel_compose proved)
- [x] **Induced maps on stable π_k** for spectrum maps f : E → F ✓
  - [x] levelInducedMap, colimitTermInduced
  - [x] transitionMap_natural: commutativity with transitionMap
  - [x] colimitTermInduced_colimitTransition: commutativity with colimitTransition
  - [x] colimitTermInduced_imageAtLevel: commutativity with imageAtLevel
  - [x] colimitTermInduced_preserves_equiv: preserves equivalence relation
  - [x] stableπInduced: f_* : π_k(E) → π_k(F)
  - [x] stableπInduced_id, stableπInduced_comp: functoriality
- [ ] **Group structure** on StableHomotopyGroup (abelian group)
- [ ] Long exact sequence for spectrum maps (see Phase 3.0)

### 2.3 Basic Examples (`Spectra/Examples.lean`) ✓
- [x] Properties of suspension spectra (level theorems)
- [x] suspensionMap: Σ functoriality on pointed maps (moved to Suspension.lean)
- [x] suspensionUnit_natural: naturality of η (in Suspension.lean)
- [x] iteratedSuspensionMap: Σ^n functoriality
- [x] suspensionSpectrumMap: functoriality Σ^∞X → Σ^∞Y ✓
- [x] Properties of sphere spectrum (level theorems)
- [x] shiftSpectrum: shift operation E[1]_n = E_{n+1}
- [x] mkSpectrum: construct spectrum from spaces + structure maps
- [x] trivial_isOmegaSpectrum ✓ (proved: homotopy groups of Unit are subsingletons)

### 2.4 Eilenberg-MacLane (`Spectra/EilenbergMacLane.lean`) ◐
- [x] EilenbergMacLaneSpectrum structure (proper structure, not axiom)
- [ ] eilenbergMacLane_unique (1 sorry: requires K(R,n) infrastructure not in Mathlib)

---

## Phase 3: Stable Homotopy Category

### 3.0 Cofiber Spectra (`Spectra/Cofiber.lean`) ◐
- [x] Cofiber spectrum Cf for spectrum map f : E → F
- [x] Structure maps for cofiber spectrum (with full proof of `cofiberStructureMapAux_respects`)
- [x] Cofiber inclusion F → Cf
- [ ] `cofiberInclusionSpectrum.comm`: compatibility proof
- [ ] Connecting map Cf → E[1]
- [ ] Long exact sequence for stable homotopy groups
- [ ] Distinguished triangles structure

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

All sorrys are for substantive mathematical theorems requiring deep infrastructure.
No placeholders, axioms, or empty definitions remain.

### Cofiber.lean (5 sorrys) - IN PROGRESS
- `cofiberInclusionSpectrum.comm` - Compatibility of cofiber inclusion with structure maps
- `connectingMapSpectrum` - Connecting map Cf → E[1]
- `exact_at_F` - Exactness at F in the long exact sequence
- `longExactSequence_composition_trivial` - Composition f_* followed by i_* is trivial
- `cofiberTriangle.h` - Third map in the distinguished triangle

### LoopSpaceIso.lean (0 sorrys) ✓
- `uncurry_homotopic_of_path_homotopic` - PROVED ✓ (uses Mathlib's homotopicFrom)
- `loopSpaceHomotopyGroupEquiv` - PROVED ✓ (reduces to genLoopCurryEquiv infrastructure)
- `genLoopCurryEquiv` - PROVED ✓ (explicit curry/uncurry via Fin.init/Fin.snoc)
- `genLoopCurryEquiv_homotopic` - PROVED ✓ (constructs homotopy explicitly)
- `genLoopCurryEquiv_homotopic_inv` - PROVED ✓ (uses HomotopyRel.eq_fst)
- `uncurryGenLoopMap_transAt` - PROVED ✓ (key compatibility lemma for group homomorphism)
- `loopSpaceHomotopyGroupEquiv_mul` - PROVED ✓ (uses uncurryGenLoopMap_transAt + mul_spec)

### HomotopyGroups.lean (0 sorrys) ✓
- `StableHomotopyGroupRep.Equiv.trans` - PROVED via imageAtLevel_compose
- `imageAtLevel_compose` - PROVED by strong induction on (M - n)

### Examples.lean (0 sorrys) ✓
- `suspensionSpectrumMap.comm` - PROVED ✓ (uses suspensionUnit_natural)

### Sequences.lean (0 sorrys) ✓
- `fiber_sequence_ker_eq_im` - PROVED ✓ (constructs lift via HomotopyRel extraction)
   - Infrastructure: homotopyToPathsToBase, fiberLift, fiberLiftGenLoop

### EilenbergMacLane.lean (1 sorry) - BLOCKED
- `eilenbergMacLane_unique` - Uniqueness of EM spectra
   - Requires: Uniqueness of K(R,n) spaces up to weak equivalence
   - Note: K(R,n) spaces are not defined in Mathlib; this is deep infrastructure
   - **Status:** Not a near-term priority. Would require building CW complex theory from scratch.

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
               ↓
        Spectra/Cofiber.lean (cofiber spectra, long exact seq)
```
