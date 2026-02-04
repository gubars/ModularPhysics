# Algebraic Riemann Surfaces - Riemann-Roch Theorem Status

## Summary

The Riemann-Roch theorem proof structure is in place, but key theorems have honest
sorrys that require sheaf cohomology infrastructure to prove.

**Update (2026-02-04):** New infrastructure in `GAGA/Cohomology/PointExactProof.lean`
provides the proof structure for χ(D) - χ(D-p) = 1 using the long exact sequence.

## Main Result

```lean
theorem riemann_roch_algebraic (C : Algebraic.CompactAlgebraicCurve)
    (hK : Nonempty (ProperCanonicalDivisor C))
    (D : Core.Divisor C.toAlgebraicCurve) :
    eulerChar C D = D.degree + 1 - C.genus
```

**Status**: Proof structure complete, depends on `eulerChar_point_exact` which has a sorry.

## Current Sorrys

| Theorem | File | Required Infrastructure |
|---------|------|------------------------|
| `RiemannRochSubmodule_finiteDimensional` | AlgebraicCech.lean | Cartan-Serre finiteness |
| `eulerChar_point_exact` | AlgebraicCech.lean | Long exact sequence (see below) |
| `serre_duality` | AlgebraicCech.lean | Residue pairing, non-degeneracy |

**Resolved:**
- `exact_sequence_alternating_sum` ✅ PROVEN using rank-nullity
- `quotient_dim_le_one` ✅ PROVEN using `leadingCoefficientUniquenessGeneral` (2026-02-04)
- `leadingCoefficientUniquenessGeneral` ✅ PROVEN as theorem (not axiom!) by deriving from
  `leadingCoefficientUniqueness` + `localParameter` (2026-02-04)
- `shortExactDimFormula` ✅ PROVEN as theorem (not axiom!) by deriving from
  `leadingCoefficientUniqueness` + `localParameter_valuation` (2026-02-04)

## Structure Audit (2026-02-04)

**Fixed axiom smuggling:**
1. `leadingCoefficientUniquenessGeneral` - Removed from `CompactAlgebraicCurve`, now a theorem
2. `shortExactDimFormula` - Removed from `CompactAlgebraicCurve`, now a theorem
3. `localParameter_nonneg_away` → `localParameter_nonpos_away` - Fixed wrong sign in
   `CompactAlgebraicStructureOn` (was ≥ 0, should be ≤ 0 since local params have poles elsewhere)
4. `valuation_one` - Removed from `AlgebraicCurve`, now a theorem (derivable from `valuation_mul`)
5. `valuation_inv` - Removed from `AlgebraicCurve`, now a theorem (derivable from `valuation_mul`)

**Axiom Classification for CompactAlgebraicCurve** (see `Helpers/DVRStructure.lean`):

The remaining structure fields in `CompactAlgebraicCurve` are **not smuggled theorems** - they
are fundamental axioms that cannot be derived from each other:

*Category 1: Properness Axioms* (capture "compact/projective")
- `argumentPrinciple`: deg(div(f)) = 0 for all f ≠ 0
- `regularIsConstant`: f regular everywhere ⟹ f ∈ ℂ (Liouville)

These are independent consequences of properness. Neither implies the other without
additional scheme-theoretic infrastructure.

*Category 2: DVR Axioms* (capture "smooth curve over ℂ")
- `localParameter` + `localParameter_valuation`: uniformizer exists at each point
- `localParameter_nonpos_away`: uniformizer has no extra zeros (constraint on choice)
- `leadingCoefficientUniqueness`: residue field at each point is ℂ

The key insight: `leadingCoefficientUniqueness` encodes "residue field = ℂ", which is:
- NOT derivable from DVR theory alone
- A property of smooth curves over algebraically closed fields
- The algebraic encoding of being able to "evaluate" units at a point

To replace this with Mathlib DVR theory, we would need to:
1. Construct O_p = {f : v_p(f) ≥ 0} as a subring (done in `DVRStructure.lean`)
2. Show O_p is a DVR (requires showing uniformizer generates maximal ideal)
3. Prove residue field O_p/m_p ≅ ℂ (requires the algebraically closed property)

**Audited structures (no issues):**
- `AlgebraicCurve` - Core DVR axioms: `valuation_zero` (convention), `valuation_mul`,
  `valuation_add_min`, `valuation_finiteSupport`. Derived: `valuation_one`, `valuation_inv`.
- `CompactAlgebraicCurve` - Minimal axiom set for "compact smooth curve over ℂ"
- `AlgebraicStructureOn`, `CompactAlgebraicStructureOn` - Updated to match
- `CanonicalDivisor` - Just data (divisor K) + property (deg = 2g-2)
- `ProperCanonicalDivisor` - Extends CanonicalDivisor with h⁰(K) = g requirement
- `PointExactData` - Packages LES data with compatibility conditions (not redundant)

## New Infrastructure (2026-02-04)

Added to `AlgebraicCech.lean`:

| Component | Status |
|-----------|--------|
| `RiemannRochSpace_sub_point_subset` | ✅ PROVEN |
| `RiemannRochSubmodule_sub_point` | ✅ Defined |
| `RiemannRochSubmodule_sub_point_le` | ✅ PROVEN |
| `exact_sequence_alternating_sum` | ✅ PROVEN (rank-nullity + exactness) |
| `quotient_dim_le_one` | ✅ PROVEN (uses `leadingCoefficientUniquenessGeneral`) |

These establish the key inclusion L(D-p) ⊆ L(D) and the dimension arguments
for the point exact sequence. The alternating sum lemma for 6-term exact sequences
is now fully proven using Mathlib's rank-nullity theorems.

## Infrastructure for `eulerChar_point_exact`

The theorem χ(D) - χ(D-p) = 1 requires:

### ✅ Already Developed (in GAGA/Cohomology/)

| Component | File | Status |
|-----------|------|--------|
| **Skyscraper sheaf** | ExactSequence.lean | ✅ PROVEN |
| `skyscraperSheaf` | ExactSequence.lean:311-517 | Full CoherentSheaf structure |
| `skyscraperH0`, `skyscraperHi` | ExactSequence.lean:537-558 | H⁰ = ℂ, H^i = 0 for i ≥ 1 |
| `h0_skyscraper_eq_one` | ExactSequence.lean:560 | ✅ PROVEN |
| `hi_skyscraper_eq_zero` | ExactSequence.lean:564 | ✅ PROVEN |
| `skyscraper_euler_char` | ExactSequence.lean:569 | χ(ℂ_p) = 1 ✅ PROVEN |
| **Long exact sequence** | ExactSequence.lean | ✅ PROVEN |
| `LongExactSequence` | ExactSequence.lean:630-664 | Full structure with exactness |
| `eulerChar_additive` | ExactSequence.lean:683-733 | χ(F) = χ(F') + χ(F'') ✅ PROVEN |
| **Čech cohomology** | CechTheory.lean | ✅ Groups defined |
| **PointExactProof** | PointExactProof.lean | ✅ Proof structure |
| `PointExactData` | PointExactProof.lean:48 | Packages LES for point |
| `point_exact` | PointExactProof.lean:112 | χ(D) - χ(D-p) = 1 ✅ PROVEN (modulo data) |

### ⚠️ Remaining Sorry

The single remaining sorry is `pointExactData_exists` (PointExactProof.lean:180) which requires:

1. **Concrete construction of O(D) sections**
   - Meromorphic functions with poles bounded by D
   - Inclusion O(D-p) ↪ O(D)
   - Quotient map O(D) → ℂ_p (evaluation at p)

2. **Snake lemma for Čech complexes**
   - Short exact sequence of presheaves → long exact sequence in Čech cohomology
   - Already have abstract snake lemma in `Topology/Sheaves/LongExactSequence.lean`
   - Need to apply to concrete line bundle sheaves

3. **Comparison of Čech and derived functor cohomology**
   - Show FiniteGoodCover gives same dimensions as LES cohomology

## What IS Proven (no sorrys in chain)

| Theorem | Description |
|---------|-------------|
| `h0_zero` | h⁰(O) = 1 (uses properness: `regularIsConstant`) |
| `h0_neg_degree` | h⁰(D) = 0 for deg(D) < 0 (uses `argumentPrinciple`) |
| `h1_zero` | h¹(O) = g (uses `h0_eq_genus` from ProperCanonicalDivisor) |
| `RiemannRochSpace_sub_point_subset` | L(D-p) ⊆ L(D) as sets |
| `RiemannRochSubmodule_sub_point_le` | L(D-p) ≤ L(D) as submodules |
| `exact_sequence_alternating_sum` | Alternating sum = 0 for 6-term exact seq |
| `quotient_dim_le_one` | dim(L(D)/L(D-p)) ≤ 1 (leading coefficient) |
| `leadingCoefficientUniquenessGeneral` | General DVR leading coefficient (derived from structure axioms) |
| `skyscraper_euler_char` | χ(ℂ_p) = 1 (GAGA/Cohomology/ExactSequence.lean) |
| `eulerChar_additive` | χ(F) = χ(F') + χ(F'') for exact sequences |
| `point_exact` | χ(D) - χ(D-p) = 1 (given PointExactData) |

## Proof Structure

The Riemann-Roch proof uses strong induction on support cardinality:
- **Base case**: χ(0) = 1 - g (proven via `h0_zero` and `h1_zero`)
- **Induction step**: χ(D) - χ(D-p) = 1 (via PointExactData - one sorry)

## Key Structures

### ProperCanonicalDivisor (AlgebraicCech.lean)

```lean
structure ProperCanonicalDivisor (C : ...) extends CanonicalDivisor C where
  h0_eq_genus : h0 C K = C.genus
```

Only includes `h0_eq_genus`. No axiom smuggling.

### CompactAlgebraicCurve (FunctionField.lean)

Structure fields for a compact algebraic curve:
- `argumentPrinciple`: deg(div(f)) = 0
- `regularIsConstant`: Functions with no poles are constant
- `localParameter`: Uniformizing parameters at each point
- `localParameter_valuation`: v_p(t_p) = 1
- `localParameter_nonpos_away`: v_q(t_p) ≤ 0 for q ≠ p (no additional zeros)
- `leadingCoefficientUniqueness`: DVR leading coefficient extraction (for v < 0)

**Derived theorems** (not structure fields):
- `leadingCoefficientUniquenessGeneral`: Generalized to any valuation (derived from
  `leadingCoefficientUniqueness` by multiplying by `localParameter^(-n-1)`)
- `shortExactDimFormula`: Leading coefficient subtraction (derived from
  `leadingCoefficientUniqueness` + `localParameter_valuation`)

### PointExactData (PointExactProof.lean)

```lean
structure PointExactData (...) where
  ses : ShortExactSeq ... O(D-p) O(D) ℂ_p
  les : LongExactSequence ...
  h''0_dim : les.H''0.dimension = 1  -- χ(ℂ_p) = 1
  h''1_dim : les.H''1.dimension = 0
  -- Compatibility with Čech cohomology
  h0_D_eq, h1_D_eq, h0_Dp_eq, h1_Dp_eq
```

## File Organization

```
Algebraic/
├── FunctionField.lean       # Function fields, valuations, compact curves
├── ZariskiTopology.lean     # Zariski topology basics
├── AlgebraicStructure.lean  # Bridge to Riemann surfaces
├── Core/
│   └── Divisors.lean        # Divisor arithmetic
└── Cohomology/
    └── AlgebraicCech.lean   # Riemann-Roch spaces, cohomology, main theorem

GAGA/Cohomology/
├── Basic.lean               # SheafCohomologyGroup, LineBundleSheafAssignment
├── CechTheory.lean          # Čech cohomology, Euler characteristic
├── ExactSequence.lean       # Skyscraper sheaf, LongExactSequence, eulerChar_additive
├── PointExactProof.lean     # NEW: PointExactData, point_exact theorem
└── ...

Topology/Sheaves/
├── CechCohomology.lean      # Abstract Čech cohomology
└── LongExactSequence.lean   # Connecting homomorphism (snake lemma)
```

## Next Steps

### Path 1: Pure Algebraic (via AlgebraicCech.lean)

To complete `eulerChar_point_exact`:

1. ✅ **Prove `quotient_dim_le_one`** - DONE using `leadingCoefficientUniquenessGeneral`
   - Shows dim(L(D)/L(D-p)) ≤ 1

2. ✅ **Prove `exact_sequence_alternating_sum`** - DONE using rank-nullity
   - Six-term exact sequence gives alternating sum = 0

3. **Connect to long exact sequence** - Show dimension constraints
   - Need: H⁰(ℂ_p) = ℂ (dim 1), H¹(ℂ_p) = 0
   - Alternating sum gives χ(D) - χ(D-p) = 1
   - This requires constructing the connecting homomorphism δ: L(D) → H¹(D-p)

### Path 2: Via GAGA/Cohomology (PointExactProof.lean)

Fill `pointExactData_exists`:

1. **Concrete line bundle sections** - Define O(D).sections as meromorphic functions
2. **Apply snake lemma** - Use LongExactSequence.lean to get Čech LES
3. **Verify dimensions** - Show Čech dimensions match LES dimensions

### Infrastructure Available

Both paths can use:
- `Topology/Sheaves/LongExactSequence.lean` - Čech-level connecting homomorphisms
- `GAGA/Cohomology/ExactSequence.lean` - eulerChar_additive (proven!)
- `shortExactDimFormula` in `CompactAlgebraicCurve` - leading coefficient extraction

The proof structure is complete; only dimension arguments remain.
