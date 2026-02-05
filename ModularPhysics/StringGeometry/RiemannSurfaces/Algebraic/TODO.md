# Algebraic Riemann Surfaces - Riemann-Roch Theorem Status

## Summary

The Riemann-Roch theorem proof structure uses induction on divisor support.

**Update (2026-02-05):** The proof approach has been corrected. The key step `χ(D) - χ(D-p) = 1`
follows from the **abstract exactness of the LES** in sheaf cohomology, NOT from case analysis
on quotient dimensions.

## Main Result

```lean
theorem riemann_roch_algebraic (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C)
    (D : Core.Divisor C.toAlgebraicCurve) :
    eulerChar C K D = D.degree + 1 - C.genus
```

## Proof Strategy (Corrected)

### The Standard Proof

1. **Base case**: χ(0) = h⁰(0) - h¹(0) = 1 - g (by definition of genus)

2. **Induction step**: From the short exact sequence of sheaves
   `0 → O(D-p) → O(D) → ℂ_p → 0`

   The long exact sequence in cohomology gives:
   `0 → H⁰(D-p) → H⁰(D) → ℂ → H¹(D-p) → H¹(D) → 0`

   By **exactness** (a standard fact from homological algebra):
   - Alternating sum of dimensions = 0
   - `h⁰(D-p) - h⁰(D) + 1 - h¹(D-p) + h¹(D) = 0`
   - Rearranging: `χ(D) - χ(D-p) = 1`

3. **Conclusion**: By induction, χ(D) = deg(D) + 1 - g

### Key Insight

The formula `a + b = 1` (where a = dim L(D)/L(D-p), b = dim L(K-D+p)/L(K-D)) is a
**CONSEQUENCE** of LES exactness, not something requiring case analysis.

The LES exactness is automatic from the definition of sheaf cohomology as a delta functor.

## Current Sorrys

| Theorem | File | Required Infrastructure |
|---------|------|------------------------|
| `LES_dimension_constraint` | PointExactSequence.lean | LES exactness from sheaf cohomology |
| `canonical_divisor_degree_algebraic` | AlgebraicCech.lean:174 | Riemann-Hurwitz |
| `h0_canonical_eq_genus` | AlgebraicCech.lean:802 | Hodge theory or definitional |

### Note on `LES_dimension_constraint`

This is the **key interface point** between the algebraic theory and sheaf cohomology.
The formula follows **directly** from the alternating sum applied to the exact sequence:

  0 → L(D-p) → L(D) → ℂ → H¹(D-p) → H¹(D) → 0

By `alternating_sum_exact_five`: h⁰(D-p) - h⁰(D) + 1 - h¹(D-p) + h¹(D) = 0

Using Serre duality and rearranging gives the formula. **No case analysis needed.**

The remaining content is proving the LES is exact (standard theorem from sheaf cohomology:
SES of sheaves → LES in cohomology, plus skyscraper acyclicity H¹(ℂ_p) = 0).

### Note on `h0_canonical_eq_genus`

This may be approached by:
1. **Definitional**: Define genus g := h¹(O) = h⁰(K) (by Serre duality)
2. **From Riemann-Roch**: Apply RR to K: χ(K) = deg(K) + 1 - g = 2g - 2 + 1 - g = g - 1
   Combined with χ(K) = h⁰(K) - h⁰(0) = h⁰(K) - 1, we get h⁰(K) = g

## What IS Proven (no sorrys)

| Theorem | Description |
|---------|-------------|
| `h0_zero` | h⁰(O) = 1 (uses properness: `regularIsConstant`) |
| `h0_neg_degree` | h⁰(D) = 0 for deg(D) < 0 (uses `argumentPrinciple`) |
| `RiemannRochSubmodule_finiteDimensional` | L(D) is finite-dimensional |
| `RiemannRochSpace_sub_point_subset` | L(D-p) ⊆ L(D) as sets |
| `quotient_dim_le_one` | dim(L(D)/L(D-p)) ≤ 1 |
| `quotient_a_le_one`, `quotient_b_le_one` | a, b ∈ {0, 1} for the point exact formula |
| `alternating_sum_exact_five` | Alternating sum = 0 for 5-term exact sequences |
| `eulerChar_additive` | χ(F) = χ(F') + χ(F'') for exact sequences |
| `skyscraper_euler_char` | χ(ℂ_p) = 1 |

## CompactAlgebraicCurve Axioms

The structure fields in `CompactAlgebraicCurve` are fundamental axioms:

**Properness Axioms:**
- `argumentPrinciple`: deg(div(f)) = 0 for all f ≠ 0
- `regularIsConstant`: f regular everywhere ⟹ f ∈ ℂ

**DVR Axioms:**
- `localParameter` + `localParameter_valuation`: uniformizer at each point
- `localParameter_nonpos_away`: uniformizer has no extra zeros
- `leadingCoefficientUniqueness`: residue field = ℂ

## File Organization

```
Algebraic/
├── FunctionField.lean       # Function fields, valuations, compact curves
├── Core/
│   └── Divisors.lean        # Divisor arithmetic
├── Helpers/
│   ├── DVRStructure.lean    # DVR infrastructure
│   ├── ResidueTheory.lean   # ⚠️ DEPRECATED - not needed for RR
│   └── PointExactInfrastructure.lean  # ⚠️ DEPRECATED - case analysis approach
└── Cohomology/
    ├── AlgebraicCech.lean      # Riemann-Roch spaces, h0, h1
    ├── AlternatingSum.lean     # ✓ Alternating sum formula for exact sequences
    ├── PointExactSequence.lean # Key LES dimension constraint (with sorry)
    └── RiemannRoch.lean        # Main Riemann-Roch theorem

GAGA/Cohomology/
├── ExactSequence.lean       # LongExactSequence, eulerChar_additive
├── ExactSequenceHelpers.lean # 6-term alternating sum formula
└── ...
```

**Note**: `ResidueTheory.lean` and `PointExactInfrastructure.lean` contain deprecated
code for the case analysis approach. The useful DVR helper lemmas are preserved, but
the main case-analysis theorems are disabled via `#exit`.
