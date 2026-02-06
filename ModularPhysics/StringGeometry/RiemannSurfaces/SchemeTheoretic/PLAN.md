# SchemeTheoretic Development Plan

## Goal

Build a self-contained, purely scheme-theoretic foundation for algebraic curves over ℂ that:
1. Uses only Mathlib's `Scheme` infrastructure (no axiom smuggling)
2. Develops necessary sheaf-theoretic infrastructure (purely algebraic)
3. Defines arithmetic genus via sheaf cohomology
4. Proves Riemann-Roch theorem from first principles
5. **NO analytic geometry** - all constructions are algebraic

---

## Current State

### Hierarchy (Basic.lean) ✅
```
AlgebraicCurve        -- integral, separated, finite type over ℂ
  ↓
ProperCurve           -- + proper
  ↓
SmoothProjectiveCurve -- + smooth of relative dim 1, + genus field
```

### Proven Infrastructure
| File | What's Proven |
|------|---------------|
| Basic.lean | Integrality, function field is a field, ℂ-algebra structure |
| Helpers/NoetherianStalks.lean | Stalks are Noetherian |
| Helpers/StalkDVR.lean | Stalks are DVRs (for smooth curves) |
| Helpers/ValuationExtension.lean | DVR valuation extends to fraction field |
| Helpers/ConstantValuation.lean | Constants have valuation 0 |
| LocalRings.lean | `valuationAt`, multiplicativity, ultrametric |

### Remaining Sorrys (3)
1. `globalSections_eq_constants` (Basic.lean) - Liouville from properness
2. `valuationAt_finiteSupport` (LocalRings.lean) - finite zeros/poles
3. `cotangent_finrank_eq_one` (SmoothCotangent.lean) - dim(m/m²) = 1

---

## Mathlib Infrastructure Available

### Sheaves and Modules
- `Scheme.Modules` - Category of O_X-modules (abelian)
- `SheafOfModules` - Sheaves of modules over a ringed space
- Pushforward/pullback functors with adjunction

### Derived Functors
- `Functor.rightDerived` - Right derived functors via injective resolutions
- `HasInjectiveResolutions` - When injective resolutions exist
- `HomotopyCategory` - For computing derived functors

### Kähler Differentials
- `KaehlerDifferential R S` (notation `Ω[S⁄R]`) - Module of differentials
- `KaehlerDifferential.D` - Universal derivation
- Exact sequences for Kähler differentials

**What Mathlib does NOT have:**
- Sheaf cohomology H^i(X, F) for schemes
- Coherent sheaves as a formalized concept
- Dualizing sheaves / Grothendieck duality
- Serre duality for curves

---

## Proposed File Structure

```
SchemeTheoretic/
├── Basic.lean                    ✅ Hierarchy
├── LocalRings.lean               ✅ Valuations from DVR structure
│
├── Sheaves/                      🆕 Sheaf-theoretic infrastructure
│   ├── Coherent.lean             🔧 Coherent O_C-modules
│   ├── LineBundles.lean          🆕 Invertible sheaves
│   ├── Skyscraper.lean           🆕 Skyscraper sheaf k(p)
│   └── ExactSequences.lean       🆕 SES, point sequence
│
├── Cohomology/                   🆕 Sheaf cohomology (derived functors)
│   ├── SheafCohomology.lean      🆕 H^i via derived functors
│   ├── CurveVanishing.lean       🆕 H^i = 0 for i ≥ 2
│   ├── LongExactSequence.lean    🆕 LES from SES
│   └── Finiteness.lean           🆕 H^i finite-dimensional
│
├── Divisors.lean                 🆕 Weil divisors, principal divisors
├── CanonicalSheaf.lean           🆕 ω_C via Kähler differentials
├── Duality.lean                  🆕 Serre duality (algebraic)
├── ArithmeticGenus.lean          🆕 g_a := h¹(O_C)
├── RiemannRoch.lean              🆕 χ(D) = deg(D) + 1 - g_a
│
└── Helpers/
    ├── NoetherianStalks.lean     ✅
    ├── StalkDVR.lean             ✅
    ├── SmoothCotangent.lean      ⚠️ (1 sorry)
    ├── ValuationExtension.lean   ✅
    ├── ConstantValuation.lean    ✅
    └── ConstantsEmbedding.lean   ✅
```

---

## Part 1: Sheaves Infrastructure

### 1.1 Sheaves/Coherent.lean 🔧

**Purpose:** Define coherent O_C-modules using Mathlib's Scheme.Modules

**Key Definitions:**
```lean
-- The category of O_C-modules
abbrev OModule (X : Scheme) := X.Modules

-- Coherent sheaf (finitely generated quasi-coherent)
structure CoherentSheaf (C : AlgebraicCurve) where
  toModule : OModule C.toScheme
  isCoherent : IsCoherent C.toScheme toModule
```

### 1.2 Sheaves/Skyscraper.lean

**Purpose:** Skyscraper sheaves at closed points

**Definition:**
```lean
/-- The skyscraper sheaf at point p with fiber ℂ.
    k_p(U) = ℂ if p ∈ U, else 0. -/
def skyscraperSheaf (C : AlgebraicCurve) (p : C.PointType) : CoherentSheaf C
```

**Properties:**
- Stalk at p is ℂ (from `residueFieldIsComplex`)
- Stalk away from p is 0
- χ(k_p) = 1 (key for Riemann-Roch induction)

### 1.3 Sheaves/LineBundles.lean

**Purpose:** Invertible sheaves and their connection to divisors

**Definition:**
```lean
/-- An invertible sheaf: locally free O_C-module of rank 1. -/
structure InvertibleSheaf (C : AlgebraicCurve) extends CoherentSheaf C where
  locallyFree : ...
  rankOne : ...

/-- The line bundle O(D) associated to a Weil divisor. -/
def lineBundleOfDivisor (C : ProperCurve) (D : Divisor C) : InvertibleSheaf C
```

### 1.4 Sheaves/ExactSequences.lean

**Purpose:** Short exact sequences, especially the fundamental point sequence

**Key Exact Sequence:**
```lean
/-- 0 → O(D-p) → O(D) → k_p → 0
    This is the key sequence for Riemann-Roch induction. -/
def pointExactSeq (C : ProperCurve) (D : Divisor C) (p : C.PointType) :
    ShortExactSeq C
```

---

## Part 2: Cohomology Infrastructure

### 2.1 Cohomology/SheafCohomology.lean

**Purpose:** Define H^i(C, F) via derived functors

**Approach:** Use Mathlib's `Functor.rightDerived` with global sections functor

```lean
/-- Sheaf cohomology H^i(C, F) := R^i Γ(C, F)
    where Γ is the global sections functor. -/
noncomputable def sheafCohomology (C : AlgebraicCurve) (F : CoherentSheaf C) (i : ℕ) :
    Type _ := (Γ_functor.rightDerived i).obj F

/-- Dimension h^i(C, F) := dim_ℂ H^i(C, F). -/
noncomputable def h (C : ProperCurve) (F : CoherentSheaf C) (i : ℕ) : ℕ
```

### 2.2 Cohomology/CurveVanishing.lean

**Purpose:** Prove H^i(C, F) = 0 for i ≥ 2 on curves

**Theorem:**
```lean
/-- Grothendieck vanishing: For a curve C and coherent F, H^i(C, F) = 0 for i ≥ 2.
    This follows from dim(C) = 1. -/
theorem cohomology_vanishing (C : AlgebraicCurve) (F : CoherentSheaf C) (i : ℕ) (hi : i ≥ 2) :
    sheafCohomology C F i = 0
```

### 2.3 Cohomology/LongExactSequence.lean

**Purpose:** Long exact sequence from short exact sequence of sheaves

**Theorem:**
```lean
/-- The LES in cohomology:
    0 → H⁰(F') → H⁰(F) → H⁰(F'') → H¹(F') → H¹(F) → H¹(F'') → 0 -/
theorem les_from_ses (C : AlgebraicCurve) (ses : ShortExactSeq C) : ...
```

**Corollary:**
```lean
/-- Euler characteristic is additive: χ(F) = χ(F') + χ(F''). -/
theorem euler_char_additive (ses : ShortExactSeq C) :
    eulerChar ses.F = eulerChar ses.F' + eulerChar ses.F''
```

### 2.4 Cohomology/Finiteness.lean

**Purpose:** Prove H^i is finite-dimensional for proper curves

**Theorem:**
```lean
/-- For proper C and coherent F, H^i(C, F) is finite-dimensional over ℂ. -/
theorem cohomology_finite_dimensional (C : ProperCurve) (F : CoherentSheaf C) (i : ℕ) :
    FiniteDimensional ℂ (sheafCohomology C F i)
```

---

## Part 3: Canonical Sheaf and Duality

### 3.1 CanonicalSheaf.lean

**Purpose:** Define the dualizing sheaf ω_C via Kähler differentials

```lean
/-- The canonical sheaf ω_C = Ω¹_{C/ℂ} (sheaf of Kähler differentials).
    For a smooth curve, this is an invertible sheaf of degree 2g-2. -/
noncomputable def canonicalSheaf (C : SmoothProjectiveCurve) : InvertibleSheaf C

/-- Degree of the canonical sheaf. -/
theorem canonicalSheaf_degree (C : SmoothProjectiveCurve) :
    degree (canonicalSheaf C) = 2 * C.genus - 2
```

### 3.2 Duality.lean

**Purpose:** Prove Serre duality algebraically

**Theorem:**
```lean
/-- Serre duality for curves: H¹(C, L)^∨ ≅ H⁰(C, ω_C ⊗ L^∨).

    This is proven via:
    1. Algebraic residue theory (trace maps)
    2. Grothendieck duality (algebraic, not analytic)
    3. Or: direct construction using repartitions -/
theorem serre_duality (C : SmoothProjectiveCurve) (L : InvertibleSheaf C) :
    (sheafCohomology C L 1)^∨ ≅ sheafCohomology C (ω_C ⊗ L^∨) 0
```

---

## Part 4: Divisors

### 4.1 Divisors.lean

```lean
/-- A Weil divisor: formal ℤ-linear combination of points. -/
structure Divisor (C : AlgebraicCurve) where
  coeff : C.PointType → ℤ
  finiteSupport : Set.Finite {p | coeff p ≠ 0}

/-- The principal divisor of f ∈ K(C)*. -/
def principalDivisor (C : AlgebraicCurve) (f : C.FunctionFieldType) (hf : f ≠ 0) : Divisor C

/-- Degree of a divisor. -/
def Divisor.degree (D : Divisor C) : ℤ := ∑ p, D.coeff p

/-- Argument Principle: deg(div(f)) = 0 for proper curves. -/
theorem principalDivisor_degree_zero (C : ProperCurve) (f : C.FunctionFieldType) (hf : f ≠ 0) :
    (principalDivisor C f hf).degree = 0
```

---

## Part 5: Riemann-Roch

### 5.1 ArithmeticGenus.lean

```lean
/-- Euler characteristic χ(F) = h⁰(F) - h¹(F). -/
noncomputable def eulerChar (C : ProperCurve) (F : CoherentSheaf C) : ℤ :=
  h C F 0 - h C F 1

/-- Arithmetic genus g_a = h¹(O_C). -/
noncomputable def arithmeticGenus (C : ProperCurve) : ℕ := h C (structureSheaf C) 1

/-- χ(O_C) = 1 - g_a. -/
theorem euler_char_structure_sheaf (C : ProperCurve) :
    eulerChar C (structureSheaf C) = 1 - arithmeticGenus C
```

### 5.2 RiemannRoch.lean

**Main Theorem:**
```lean
/-- Riemann-Roch Theorem: χ(D) = deg(D) + 1 - g_a.

    **Proof strategy:**
    By induction on the support of D using the point exact sequence.

    Base case: D = 0
      χ(O) = 1 - g_a ✓

    Inductive step: From 0 → O(D-p) → O(D) → k_p → 0
      χ(D) = χ(D-p) + χ(k_p) = χ(D-p) + 1
      deg(D) = deg(D-p) + 1
      By induction: χ(D-p) = deg(D-p) + 1 - g_a
      Therefore: χ(D) = deg(D) + 1 - g_a ✓ -/
theorem riemann_roch (C : ProperCurve) (D : Divisor C) :
    eulerChar C (lineBundleOfDivisor C D) = D.degree + 1 - arithmeticGenus C
```

---

## Implementation Order

### Phase 0: Fix Current Files
- [ ] Resolve remaining sorrys in Basic.lean, LocalRings.lean

### Phase 1: Sheaves Infrastructure
1. [🔧] `Sheaves/Coherent.lean` - Fix and complete
2. [ ] `Sheaves/Skyscraper.lean` - Skyscraper sheaves
3. [ ] `Sheaves/LineBundles.lean` - Invertible sheaves
4. [ ] `Sheaves/ExactSequences.lean` - Point exact sequence

### Phase 2: Cohomology
1. [ ] `Cohomology/SheafCohomology.lean` - Derived functor approach
2. [ ] `Cohomology/CurveVanishing.lean` - H^i = 0 for i ≥ 2
3. [ ] `Cohomology/LongExactSequence.lean` - LES
4. [ ] `Cohomology/Finiteness.lean` - Finite-dimensionality

### Phase 3: Canonical Sheaf
1. [ ] `CanonicalSheaf.lean` - Kähler differentials
2. [ ] `Duality.lean` - Serre duality (algebraic)

### Phase 4: Divisors
1. [ ] `Divisors.lean` - Weil divisors

### Phase 5: Riemann-Roch
1. [ ] `ArithmeticGenus.lean` - g_a = h¹(O)
2. [ ] `RiemannRoch.lean` - Main theorem

---

## Key Principle: Purely Algebraic

**All constructions must be scheme-theoretic:**
- Sheaf cohomology via derived functors (not Čech with convergence arguments)
- Dualizing sheaf via Kähler differentials (not holomorphic forms)
- Serre duality via trace maps / Grothendieck duality (not residues with Stokes)
- Riemann-Roch via exact sequences and induction (no analytic methods)

**References:**
- Stacks Project (algebraic approach)
- Hartshorne Chapter III (cohomology via derived functors)
- Mathlib's `Functor.rightDerived`

---

## Success Criteria

SchemeTheoretic is complete when:
1. ✅ No imports from Algebraic/, Analytic/, GAGA/, Combinatorial/, Topology/
2. ✅ No axiom smuggling
3. ⬜ Coherent sheaves defined (scheme-theoretically)
4. ⬜ Sheaf cohomology H^i defined (derived functors)
5. ⬜ Canonical sheaf ω_C defined (Kähler differentials)
6. ⬜ Serre duality proven (algebraically)
7. ⬜ `arithmeticGenus` defined via h¹(O)
8. ⬜ `riemann_roch` theorem proven
9. ⬜ All sorrys resolved
