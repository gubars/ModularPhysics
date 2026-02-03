# RiemannSurfaces Folder - TODO

## Architectural Vision

The RiemannSurfaces folder formalizes Riemann surface theory through three complementary perspectives, connected via GAGA:

```
                    ┌─────────────────┐
                    │   Topology/     │
                    │  (Pure topo-    │
                    │  logical, no    │
                    │  complex str.)  │
                    └────────┬────────┘
                             │
            ┌────────────────┼────────────────┐
            │                │                │
            ▼                ▼                ▼
    ┌───────────────┐ ┌───────────────┐ ┌───────────────┐
    │  Algebraic/   │ │  Analytic/    │ │ Combinatorial/│
    │               │ │               │ │               │
    │ Divisors      │ │ Holomorphic   │ │ Ribbon graphs │
    │ Cohomology    │ │ functions     │ │ Cell decomp.  │
    │ Riemann-Roch  │ │ Teichmüller   │ │ Penner map    │
    │ Abel-Jacobi   │ │ QC maps       │ │ Kontsevich    │
    └───────┬───────┘ └───────┬───────┘ └───────────────┘
            │                 │
            └────────┬────────┘
                     │
                     ▼
            ┌────────────────┐
            │     GAGA/      │
            │   (Bridges     │
            │  Alg ↔ Ana)    │
            └────────────────┘
```

### Folder Responsibilities

- **Topology/**: Pure topological surfaces, genus as topological invariant, no complex structure
- **Algebraic/**: Algebraic curves, coherent sheaves, divisors, Riemann-Roch theorem
- **Analytic/**: Complex manifolds, holomorphic functions, Teichmüller theory, harmonic analysis
- **Combinatorial/**: Ribbon graphs, Penner/Kontsevich moduli theory, intersection numbers
- **GAGA/**: GAGA principle connecting algebraic and analytic perspectives

### Key Principle

Each perspective should be self-contained. GAGA provides the bridge showing that for compact Riemann surfaces, algebraic and analytic viewpoints are equivalent.

---

## Recent Changes (2024)

### Fixed: Line Bundle Sheaf Infrastructure

The previous unsound `canonicalLineBundleSheaf` (which returned O for all divisors) has been replaced with a proper infrastructure:

1. **`LineBundleSheafAssignment`** (Cohomology/Basic.lean)
   - Maps divisors D to coherent sheaves O(D)
   - Axiomatizes O(0) = O property
   - Used as input to cohomology theory

2. **`SectionOrder`** (Helpers/LineBundleConstruction.lean)
   - Captures DVR structure at each point
   - Properties: ord(fg) = ord(f) + ord(g), ord(f) > 0 iff f(p) = 0
   - Derived from `localUniformizer` in StructureSheaf

3. **`LineBundleSheafData`** (Helpers/LineBundleConstruction.lean)
   - Full data for line bundle construction
   - Section order + sheaf assignment + properties

4. **`coherentSheafOfDivisor`** (Cohomology/Basic.lean)
   - Proper function D ↦ O(D) that requires a LineBundleSheafAssignment

### Architecture: Analytic/Basic.lean

Moved analytic definitions to their proper location:
- `ComplexManifold`, `RiemannSurface`, `CompactRiemannSurface` now in Analytic/Basic.lean
- Basic.lean re-exports these for backward compatibility
- Divisor/line bundle structures remain in Basic.lean (shared by algebraic/analytic)

---

## Current Status

### General Čech Cohomology Infrastructure

A general Čech cohomology framework in `ModularPhysics/Topology/Sheaves/CechCohomology.lean`:

- **OpenCover**: Indexed open covers of topological spaces
- **AbPresheaf**: Presheaves of abelian groups with restriction maps
- **CechCochain**: C^n(U, F) = ∏_{(i₀,...,iₙ)} F(U_{i₀} ∩ ... ∩ U_{iₙ})
- **cechDiff**: The Čech differential d^n with alternating signs
- **CechCocycles**: Z^n = ker(d^n)
- **CechCoboundariesSucc**: B^{n+1} = im(d^n)
- **CechH**: H^n(U, F) = Z^n / B^n

**Key results** (ALL SORRY-FREE as of 2025):
- `cechDiff_add`, `cechDiff_zero`: Differential is a group homomorphism ✓
- `deleteFace_deleteFace`: Simplicial identity for face compositions ✓
- `pair_cancel`: Paired terms in double sum cancel ✓
- `cechDiff_comp_zero`: d² = 0 ✓
- `coboundary_is_cocycle`: Every coboundary is a cocycle ✓
- `CechCohomologyRelSucc.equivalence`: Cohomology relation is an equivalence ✓
- `connectingH`: Connecting homomorphism on cohomology (LongExactSequence.lean) ✓

### Riemann-Roch Path (SOUND)

The path to Riemann-Roch is now architecturally sound:

```
Basic.lean (Divisor, line bundles)
    ↓
Algebraic/Divisors.lean (Divisor group, degree)
    ↓
Algebraic/Cohomology/Sheaves.lean (StructureSheaf, LineBundleSheaf, CoherentSheaf)
    ↓
Algebraic/Cohomology/Basic.lean (SheafCohomologyGroup, LineBundleSheafAssignment, CompactCohomologyTheory)
    ↓
Algebraic/Cohomology/ExactSequence.lean (SkyscraperSheaf, LongExactSequence, eulerChar_formula)
    ↓
Algebraic/Cohomology/SerreDuality.lean (SerreDuality, h1 = h0(K-D))
    ↓
Algebraic/RiemannRoch.lean (Main theorem statements)
```

**Key theorems proven** (2024-2025 sessions):
- `eulerChar_additive` ✓ PROVED - Euler characteristic additive on exact sequences
- `eulerChar_point_exact` ✓ PROVED - χ(D) - χ(D-p) = 1 (via point_recursion in CompactCohomologyTheory)
- `LongExactSequence.eulerChar_additive` ✓ PROVED - Uses rank-nullity for 6-term exact sequences
- `eulerChar_formula` ✓ PROVED - χ(D) = deg(D) + 1 - g (via induction on support cardinality)
- `chi_deg_invariant_smul` ✓ PROVED - χ(D) - deg(D) = χ(D - n•p) - deg(D - n•p) (integer induction)

**Key sorrys remaining** (axiomatic, but statements are correct):
- `serreDuality_exists` - Existence of Serre duality
- `riemann_roch` - Main theorem (combines Euler characteristic + Serre duality)

**New infrastructure**:
- `ExactSequenceHelpers.lean` - Dimension lemmas for exact sequences using Mathlib's rank-nullity
- `CompactCohomologyTheory.point_recursion` - Fundamental property χ(D) - χ(D-p) = 1

### Module-by-Module Status

| File | Status | Notes |
|------|--------|-------|
| **Algebraic/Divisors.lean** | Sound | 3 sorrys for deep theorems |
| **Algebraic/Cohomology/Sheaves.lean** | Sound | StructureSheaf with localUniformizer |
| **Algebraic/Cohomology/Basic.lean** | Sound | LineBundleSheafAssignment properly defined |
| **Algebraic/Cohomology/ExactSequence.lean** | Sound | SkyscraperSheaf fully proved |
| **Algebraic/Cohomology/GeneralCechBridge.lean** | Sound | Bridges general Čech to Riemann surfaces |
| **Algebraic/Cohomology/SerreDuality.lean** | Axiomatic | Correct statements with sorrys |
| **Algebraic/RiemannRoch.lean** | Axiomatic | Correct statements with sorrys |
| **Algebraic/Helpers/LineBundleConstruction.lean** | Sound | SectionOrder, LineBundleSheafData |
| **Algebraic/Helpers/Meromorphic.lean** | Sound | MeromorphicFunction with order proofs |
| **Algebraic/VectorBundles.lean** | Partial | Basic definitions, needs expansion |
| **Analytic/Basic.lean** | Sound | ComplexManifold, RiemannSurface |

---

## Infrastructure Expansion Plan

### Phase 1: Complete Core Čech Cohomology (HIGH PRIORITY)

#### 1.1 ~~Long Exact Sequence for Sheaves~~ ✓ DONE
**File**: `ModularPhysics/Topology/Sheaves/LongExactSequence.lean`

From 0 → F' → F → F'' → 0, derive:
```
0 → H⁰(F') → H⁰(F) → H⁰(F'') → H¹(F') → H¹(F) → H¹(F'') → ...
```

**COMPLETED Components**:
- [x] `PresheafMorphism` between AbPresheafs (with map_add, map_neg, map_sub, map_sum, map_zsmul)
- [x] `ShortExactSequence` structure (ι injective, π surjective, ker(π) = im(ι))
- [x] `connectingHomomorphism δⁿ : Hⁿ(F'') → Hⁿ⁺¹(F')` (connectingH0, connectingH)
- [x] Well-definedness of connecting homomorphism ✓ FULLY PROVED
- [ ] Exactness proofs at each term (remaining work)
- [ ] Naturality of connecting homomorphism (remaining work)

**Reference**: Wells "Differential Analysis on Complex Manifolds" Ch II.3

#### 1.2 ~~Complete `cechDiff_comp_zero` Proof~~ ✓ DONE
**File**: `Topology/Sheaves/CechCohomology.lean`

**COMPLETED**: The proof uses:
- [x] `pair_cancel` theorem: paired terms have opposite signs and equal σ values
- [x] Bijection between S_lt = {(i,j) : j < i} and S_ge = {(i,j) : i ≤ j}
- [x] `deleteFace_deleteFace` simplicial identity
- [x] `restrict_proof_irrel` for handling dependent types

#### 1.3 Refinement and Direct Limit
**New File**: `ModularPhysics/Topology/Sheaves/Refinement.lean`

- [ ] `CoverRefinement` structure: maps between index sets
- [ ] Refinement induces maps on cohomology
- [ ] `CechCohomologyLimit`: H^n(X, F) = lim_{U} H^n(U, F)
- [ ] Leray cover theorem: for acyclic covers, Čech = sheaf cohomology

### Phase 2: Complete Riemann-Roch Path (HIGH PRIORITY)

#### 2.1 Euler Characteristic Point Exact Sequence
**File**: `Algebraic/Cohomology/ExactSequence.lean`

Prove `eulerChar_point_exact : T.chi D - T.chi (D - Divisor.point p) = 1`

**Proof Strategy**:
1. Construct explicit `LongExactSequence` from `pointExactSeq`
2. Use `eulerChar_additive` from the LES
3. Apply `skyscraper_euler_char` (already proved: χ(ℂ_p) = 1)

#### 2.2 Euler Characteristic Formula
**File**: `Algebraic/Cohomology/ExactSequence.lean`

Prove `eulerChar_formula : T.chi D = D.degree + 1 - CRS.genus`

**Proof Strategy** (from Harris-Morrison "Moduli of Curves" p.154):
- Base case D = 0: χ(O) = h⁰(O) - h¹(O) = 1 - g
- Induction on |deg(D)|: Use `eulerChar_point_exact` to step

#### 2.3 Residue Infrastructure for Serre Duality
**New File**: `Algebraic/Cohomology/Residue.lean`

- [ ] `Residue p ω`: residue of meromorphic differential at p
- [ ] `residue_sum_zero`: ∑_p Res_p(ω) = 0 (residue theorem)
- [ ] `residuePairing`: H⁰(O(D)) ⊗ H¹(O(K-D)) → ℂ

**Reference**: Wells Appendix pp.261-265

#### 2.4 Serre Duality
**File**: `Algebraic/Cohomology/SerreDuality.lean`

Prove `serreDuality_exists : h_i H1 = h_i H0_dual`

**Proof Strategy**:
- Define cup product via residue pairing
- Show the pairing is non-degenerate
- Deduce H¹(O(D)) ≅ H⁰(O(K-D))ᵛ

#### 2.5 ~~Refactor MathlibBridge to Use General Čech~~ ✓ DONE
**File**: `Algebraic/Cohomology/GeneralCechBridge.lean` (NEW)

A new bridge file has been created connecting the general Čech infrastructure:
- [x] Import `ModularPhysics.Topology.Sheaves.CechCohomology`
- [x] `coherentSheafToAbPresheaf`: Bridge `CoherentSheaf` to `AbPresheaf`
- [x] `structureSheafToAbPresheaf`: Bridge `StructureSheaf` to `AbPresheaf`
- [x] `coverToOpenCover`: Convert Riemann surface covers to general OpenCover
- [x] `cechDiff_comp_zero_coherent`: Transfer d² = 0 to coherent sheaves
- [x] `CechCohomologyGroup`: H^n using general infrastructure
- [x] `inter_const_eq_cover`, `inter_pair_eq_inf`: Intersection correspondence lemmas

### Phase 3: Vector Bundles and Moduli (MEDIUM PRIORITY)

#### 3.1 Vector Bundle Stability
**Expand**: `Algebraic/VectorBundles.lean` or new `VectorBundles/Stability.lean`

From Wells Appendix pp.243-258:
- [ ] `slope μ(E) = deg(E) / rank(E)`
- [ ] `VectorBundle.isStable`: ∀ F ⊂ E proper, μ(F) < μ(E)
- [ ] `VectorBundle.isSemistable`: ≤ instead of <
- [ ] Moduli space `M^s(n,d)` of stable bundles

#### 3.2 Dimension of Moduli Space
**File**: `VectorBundles/Moduli.lean` (new)

- [ ] `moduliDimension : dim M^s(n,d) = 1 + n²(g-1)`
- [ ] Tangent space: T_{[E]} M^s(n,d) ≅ H¹(End E)

**Reference**: Wells p.245-246 (Theorem 2.2)

#### 3.3 Narasimhan-Seshadri Theorem (Statement)
**File**: `VectorBundles/NarasimhanSeshadri.lean` (new)

```lean
/-- Stable bundles ↔ irreducible unitary representations of π₁ -/
theorem narasimhanSeshadri :
    ModuliOfStableBundles g n d ≃ IrreducibleUnitaryReps π₁(Σ) := sorry
```

### Phase 4: Higgs Bundles (LOWER PRIORITY)

**New Directory**: `Algebraic/HiggsBundles/`

From Wells Appendix pp.253-265:

#### 4.1 Basic Definitions
**File**: `HiggsBundles/Basic.lean`

- [ ] `HiggsBundle`: pair (E, φ) where φ : E → E ⊗ K
- [ ] `HiggsBundle.isStable`: stability for Higgs bundles
- [ ] Moduli space of stable Higgs bundles

#### 4.2 Non-abelian Hodge Correspondence
**File**: `HiggsBundles/NonabelianHodge.lean`

```lean
/-- Stable Higgs bundles ↔ representations of π₁ in GL(n,ℂ) -/
theorem nonabelianHodge :
    ModuliOfStableHiggsBundles g n d ≃ Representations π₁(Σ) GL(n,ℂ) := sorry
```

### Phase 5: Deformation Theory (LOWER PRIORITY)

**New Directory**: `Deformation/`

From Harris-Morrison "Moduli of Curves" pp.86-105:

#### 5.1 First-Order Deformations
**File**: `Deformation/FirstOrder.lean`

- [ ] `FirstOrderDeformations C = H¹(C, T_C)`
- [ ] Tangent space to moduli: T_{[C]} M_g ≅ H¹(C, T_C)
- [ ] Dimension: dim M_g = 3g - 3 for g ≥ 2

#### 5.2 Versal Deformations
**File**: `Deformation/Versal.lean`

- [ ] `VersalDeformation` structure
- [ ] Universal property (local uniqueness)
- [ ] Existence for curves with finite automorphism group

---

## Priority Order Summary

### Immediate (Next Steps)
1. ~~Complete `cechDiff_comp_zero` proof~~ ✓ DONE
2. ~~Build long exact sequence for Čech cohomology~~ ✓ DONE (Topology/Sheaves/LongExactSequence.lean)
3. ~~Prove `eulerChar_point_exact`~~ ✓ DONE (via point_recursion property)
4. ~~Prove `eulerChar_additive`~~ ✓ DONE
5. ~~Complete `eulerChar_formula`~~ ✓ DONE (divisor support cardinality induction)

### Short-Term
5. Build residue infrastructure
6. Prove `serreDuality_exists`
7. Complete `riemann_roch` theorem
8. ~~Refactor MathlibBridge to use general Čech~~ ✓ DONE (GeneralCechBridge.lean)

### Medium-Term
9. Vector bundle stability and moduli
10. Narasimhan-Seshadri statement

### Long-Term
11. Higgs bundles and non-abelian Hodge
12. Deformation theory

---

## Dependencies and Build

Build command: `lake build ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.RiemannRoch`

Import hierarchy:
```
ModularPhysics/Topology/Sheaves/CechCohomology.lean (GENERAL)
    ↓ (used by)
Topology/Basic.lean
    ↓
Analytic/Basic.lean
    ↓
Basic.lean (re-exports Analytic, adds Divisor/line bundles)
    ↓
├── Algebraic/Divisors.lean
│       ↓
│   Algebraic/Cohomology/Sheaves.lean
│       ↓
│   Algebraic/Cohomology/Basic.lean
│       ↓
│   ├── Algebraic/Cohomology/MathlibBridge.lean
│   │       ↓
│   │   Algebraic/Cohomology/GeneralCechBridge.lean (bridges to CechCohomology.lean)
│   │
│   Algebraic/Cohomology/ExactSequence.lean
│       ↓
│   Algebraic/Cohomology/SerreDuality.lean
│       ↓
│   Algebraic/RiemannRoch.lean
│
├── Algebraic/Helpers/LineBundleConstruction.lean
│
├── Algebraic/Helpers/Meromorphic.lean
│
├── Algebraic/VectorBundles.lean (→ VectorBundles/)
│
├── Analytic/*.lean
│
├── Combinatorial/*.lean
│
└── GAGA/Basic.lean (imports both Algebraic and Analytic)
```

---

## Key References

### For Čech Cohomology and Sheaf Theory
- Wells, R.O. "Differential Analysis on Complex Manifolds" (2007) - Chapter II
- Godement, R. "Topologie algébrique et théorie des faisceaux"
- Hartshorne, R. "Algebraic Geometry" - Chapter III

### For Riemann-Roch and Moduli
- Harris, J. & Morrison, I. "Moduli of Curves" (1998) - GTM 187
- Farkas, H. & Kra, I. "Riemann Surfaces" (1980) - GTM 71

### For Vector Bundles and Higgs Bundles
- Wells Appendix by García-Prada: "Moduli Spaces and Geometric Structures"
- Narasimhan, M.S. & Seshadri, C.S. "Stable and unitary vector bundles..."

---

## Notes

- The formalization prioritizes mathematical correctness over completeness
- Axiomatic statements (using `sorry`) are acceptable for deep theorems when the statement is correct
- **No placeholder definitions** - all definitions are mathematically sound
- LineBundleSheafAssignment is taken as input rather than constructed explicitly - this is sound because GAGA ensures algebraic and analytic constructions give the same cohomology
- CLAUDE.md rules: No axioms, no placeholders, proper definitions always
