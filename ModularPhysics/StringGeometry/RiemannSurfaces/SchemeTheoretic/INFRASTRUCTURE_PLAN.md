# Comprehensive Infrastructure Development Plan

## Overview

This plan addresses the remaining sorrys in the SchemeTheoretic Riemann-Roch proof.
All infrastructure must be developed from scratch since it's not available in Mathlib.

## Priority Order

### TIER 1: Critical Path (Blocks Main Theorem)

#### 1.1 `h_i` Definition (SheafCohomology.lean:109)

**Mathematical Content:** dim_ℂ H^i(C, F) via Module.finrank

**Required Infrastructure:**
1. **ℂ-Module structure on CechCohomology**
   - File: `Helpers/CohomologyModuleStructure.lean` (~200 LOC)
   - Cech cochains are modules over global sections Γ(C, O_C)
   - For curves over ℂ, Γ(C, O_C) = ℂ (Liouville)
   - Scalar multiplication: c • [class of σ] = [class of c • σ]
   - Show this is well-defined on quotients

2. **Finite dimensionality (Serre's Theorem)**
   - File: `Helpers/FiniteDimensionality.lean` (~300 LOC)
   - For coherent F on proper C: H^i(C, F) is finite-dim ℂ-vector space
   - Proof outline:
     - Coherent = locally finitely presented
     - Proper = universally closed + separated + finite type
     - Noetherian induction on support
   - May need additional Mathlib infrastructure for proper schemes

3. **Connection to finrank**
   ```lean
   noncomputable def h_i (C : ProperCurve) (i : ℕ) (F : CoherentSheaf C.toAlgebraicCurve) : ℕ :=
     @Module.finrank ℂ (SheafCohomology C.toAlgebraicCurve i F.toModule) _ (cohomologyModule C i F)
   ```

#### 1.2 `skyscraperModule` (Skyscraper.lean:91)

**Mathematical Content:** O_C-module structure on skyscraper presheaf

**Required Infrastructure:**
1. **Skyscraper Presheaf of Modules**
   - File: `Helpers/SkyscraperModule.lean` (~400 LOC)
   - Define presheaf: U ↦ κ(p) if p ∈ U, else 0
   - Use `PUnit` for the zero object
   - O_C(U)-module structure via `evalAtPoint` (already have this)

2. **Sheaf Condition**
   - Skyscraper presheaves are automatically sheaves
   - Gluing is trivial (supported at single point)

3. **Package as SheafOfModules**
   ```lean
   noncomputable def skyscraperModule (p : C.PointType) : OModule C.toScheme where
     val := {
       presheaf := skyscraperPresheafOfModules p
       isSheaf := skyscraper_isSheaf p
     }
   ```

#### 1.3 `h0_skyscraper = 1` (Skyscraper.lean:173)

**Mathematical Content:** H⁰(C, k_p) = Γ(C, k_p) = κ(p) ≅ ℂ

**Required Infrastructure:**
1. **Global sections of skyscraper**
   - Γ(C, k_p) = k_p(C) = κ(p) (since p ∈ C always)
   - Already have: `residueFieldLinearEquiv : κ(p) ≃ₗ[ℂ] ℂ`
   - Already have: `residueField_finrank_one : finrank ℂ κ(p) = 1`

2. **H⁰ = global sections**
   - Cech H⁰ = 0-cocycles = sections agreeing on overlaps = global sections
   - Need isomorphism: CechCohomology0 F 𝒰 ≃ Γ(C, F)

3. **Combine:**
   ```lean
   theorem h0_skyscraper (C : ProperCurve) (p : C.toAlgebraicCurve.PointType) :
       h_i C 0 (skyscraperSheaf C.toAlgebraicCurve p) = 1 := by
     -- H⁰ ≅ Γ(C, k_p) ≅ κ(p) ≅ ℂ
     -- finrank ℂ ℂ = 1
     have h1 := h0_eq_globalSections_iso C (skyscraperModule C.toAlgebraicCurve p)
     have h2 := skyscraper_globalSections_eq_residueField C p
     have h3 := residueField_finrank_one C.toAlgebraicCurve p
     -- Combine via LinearEquiv.finrank_eq
   ```

#### 1.4 `h1_skyscraper = 0` (Skyscraper.lean:187)

**Mathematical Content:** Flasque sheaves are acyclic

**Required Infrastructure:**
1. **Flasque framework** (already started in FlasqueSheaves.lean)
   - File: `Helpers/FlasqueSheaves.lean` (~200 LOC)
   - IsFlasque class: restriction maps are surjective
   - Skyscrapers are flasque (3 cases, already proven in SkyscraperInfrastructure)

2. **Flasque ⟹ H¹ = 0**
   - File: Continue in `Helpers/FlasqueSheaves.lean`
   - Proof: Given 1-cocycle c_{ij}, construct primitive b_i
   - Use flasqueness to extend sections inductively
   - Key lemma: every cocycle is a coboundary

3. **Apply to skyscraper:**
   ```lean
   theorem h1_skyscraper (C : ProperCurve) (p : C.toAlgebraicCurve.PointType) :
       h_i C 1 (skyscraperSheaf C.toAlgebraicCurve p) = 0 := by
     haveI : IsFlasque (skyscraperModule C.toAlgebraicCurve p) := skyscraperModule_isFlasque C.toAlgebraicCurve p
     exact flasque_h1_zero C (skyscraperSheaf C.toAlgebraicCurve p)
   ```

### TIER 2: Supporting Infrastructure

#### 2.1 `pair_cancel.hval_eq` Technical Sorry (CechComplex.lean:353)

**Mathematical Content:** Transport along equal faces in categorical modules

**Required Infrastructure:**
1. **Cast lemmas for OModule**
   - File: `Helpers/OModuleCast.lean` (~150 LOC)
   - Lemma: if face1 = face2, then F.val.map (restrictions) gives equal results
   - Need to handle the dependent type: `F.val.obj (op (intersection face))`
   - Use `eq_rec_on` or explicit cast manipulation

2. **Alternative approach:** Refactor CechComplex to avoid dependent types
   - Use a single intersection type with proof that Opens are equal
   - More invasive but cleaner

#### 2.2 `cohomology_long_exact_sequence` (SheafCohomology.lean:181)

**Mathematical Content:** SES of sheaves induces LES in cohomology

**Required Infrastructure:**
1. **Snake Lemma for Cech complexes**
   - File: `Helpers/SnakeLemma.lean` (~400 LOC)
   - SES 0 → F' → F → F'' → 0 induces SES of Cech complexes
   - Snake lemma gives connecting homomorphism δ: H^i(F'') → H^{i+1}(F')

2. **Exactness verification**
   - File: `Helpers/LongExactSequence.lean` (~300 LOC)
   - Verify exactness at each term
   - For curves: sequence terminates at H¹

3. **Dimension formula:**
   ```lean
   theorem cohomology_long_exact_sequence (C : ProperCurve) (ses : ShortExactSeq C.toAlgebraicCurve) :
       (h_i C 0 ses.F' : ℤ) - (h_i C 0 ses.F) + (h_i C 0 ses.F'')
       - (h_i C 1 ses.F') + (h_i C 1 ses.F) - (h_i C 1 ses.F'') = 0 := by
     -- Alternating sum of dimensions in exact sequence = 0
   ```

#### 2.3 `h0_structure_sheaf_eq_one` (SheafCohomology.lean:266)

**Mathematical Content:** Liouville theorem - Γ(C, O_C) = ℂ for proper C

**Required Infrastructure:**
1. **Algebraic Liouville theorem**
   - File: `Helpers/AlgebraicLiouville.lean` (~200 LOC)
   - For X proper connected over k: Γ(X, O_X) = k
   - Proof: structure morphism factors through closed point by properness
   - Global sections form finite k-algebra that is a domain ⟹ = k

2. **Application to dimension:**
   ```lean
   theorem h0_structure_sheaf_eq_one (C : SmoothProjectiveCurve) :
       h_i C.toProperCurve 0 (CoherentSheaf.structureSheaf C.toAlgebraicCurve) = 1 := by
     -- Γ(C, O_C) = ℂ by algebraic Liouville
     -- finrank ℂ ℂ = 1
   ```

### TIER 3: Morphism Definitions

#### 3.1 `inclusionMorphism` (PointExactMorphisms.lean:135)

**Mathematical Content:** Natural inclusion O(D-p) → O(D)

**Required Infrastructure:**
1. **Multiplication by uniformizer**
   - File: `Helpers/UniformizerMultiplication.lean` (~200 LOC)
   - Let π be uniformizer at p (already have `exists_localParameter`)
   - Define multiplication map: f ↦ π · f
   - This is the inclusion O(D-p) ↪ O(D) on sections

2. **Module homomorphism structure:**
   ```lean
   noncomputable def inclusionMorphism (D : Divisor C.toAlgebraicCurve) (p : C.PointType) :
       (divisorSheaf C (D - Divisor.point p)).toModule ⟶ (divisorSheaf C D).toModule := {
     val := uniformizerMultiplicationPresheaf C D p
     property := uniformizerMultiplication_isModuleHom C D p
   }
   ```

#### 3.2 `evaluationMorphism` (PointExactMorphisms.lean:167)

**Mathematical Content:** Restriction to residue field at p

**Required Infrastructure:**
1. **Evaluation map on divisor sheaf**
   - File: `Helpers/DivisorEvaluation.lean` (~200 LOC)
   - For f ∈ O(D)(U) with p ∈ U: evaluate at p to get κ(p)
   - Use `evalAtPoint` from SkyscraperInfrastructure

2. **Surjectivity (for exactness):**
   ```lean
   noncomputable def evaluationMorphism (D : Divisor C.toAlgebraicCurve) (p : C.PointType) :
       (divisorSheaf C D).toModule ⟶ skyscraperModule C.toAlgebraicCurve p := {
     val := divisorEvaluationPresheaf C D p
     property := divisorEvaluation_isModuleHom C D p
   }
   ```

#### 3.3 `divisorModule` (LineBundles.lean:208)

**Mathematical Content:** O(D) as O_C-module

**Required Infrastructure:**
1. **Subsheaf of function field**
   - File: `Helpers/DivisorSheafConstruction.lean` (~300 LOC)
   - O(D)(U) = { f ∈ K(C) : ∀ p ∈ U, v_p(f) ≥ -D(p) }
   - Use `valuationAt` from LocalRings.lean

2. **O_C-module structure:**
   - Multiplication by sections of O_C preserves the valuation condition
   - Gluing follows from sheaf property of K(C)

## Implementation Schedule

### Phase 1: Critical Path (Est. 3-4 days)
1. Day 1: SkyscraperModule construction
2. Day 2: h_i definition with ℂ-module structure
3. Day 3: h0_skyscraper = 1 and flasque H¹ = 0
4. Day 4: h1_skyscraper = 0 and testing

### Phase 2: Supporting Infrastructure (Est. 2-3 days)
1. Day 5: OModule cast lemmas (fix pair_cancel)
2. Day 6: Long exact sequence setup
3. Day 7: Algebraic Liouville theorem

### Phase 3: Morphisms (Est. 2 days)
1. Day 8: inclusionMorphism and evaluationMorphism
2. Day 9: divisorModule and exactness verification

### Phase 4: Integration and Testing (Est. 1 day)
1. Day 10: Verify all sorrys resolved, test main theorem

## File Structure

```
SchemeTheoretic/
├── Helpers/
│   ├── SkyscraperInfrastructure.lean    (existing)
│   ├── SkyscraperModule.lean            (NEW - 400 LOC)
│   ├── CohomologyModuleStructure.lean   (NEW - 200 LOC)
│   ├── FiniteDimensionality.lean        (NEW - 300 LOC)
│   ├── FlasqueSheaves.lean              (existing, extend)
│   ├── OModuleCast.lean                 (NEW - 150 LOC)
│   ├── SnakeLemma.lean                  (NEW - 400 LOC)
│   ├── LongExactSequence.lean           (NEW - 300 LOC)
│   ├── AlgebraicLiouville.lean          (NEW - 200 LOC)
│   ├── UniformizerMultiplication.lean   (NEW - 200 LOC)
│   ├── DivisorEvaluation.lean           (NEW - 200 LOC)
│   └── DivisorSheafConstruction.lean    (NEW - 300 LOC)
└── ...
```

**Total new code:** ~2,650 LOC across 11 new files

## Dependencies

All new files depend only on:
- Mathlib (AlgebraicGeometry, CategoryTheory, Algebra.Module)
- Existing SchemeTheoretic files (Basic, LocalRings, Divisors, CechComplex)

No imports from Algebraic/ or GAGA/ folders (maintains independence).
