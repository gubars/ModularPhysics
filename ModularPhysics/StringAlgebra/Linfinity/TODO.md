# L∞ Algebra Formalization - Status and Plan

## Overview

This folder contains a formalization of L∞ algebras (strongly homotopy Lie algebras) using the coalgebraic approach: an L∞ structure on V is a degree 1 square-zero coderivation D on the reduced symmetric coalgebra S⁺(V[1]).

## Current Status

All 12 files compile successfully. The core infrastructure is in place with proper definitions.

### Files and Status

| File | Status | Description |
|------|--------|-------------|
| Basic.lean | ✅ Complete | Foundational graded structures, Koszul signs |
| SymmetricCoalgebra.lean | ✅ Complete | Symmetric coalgebra S(V) with shuffle coproduct |
| GradedInfrastructure.lean | ✅ Complete | Graded vector spaces, linear maps using Mathlib |
| ChainComplex.lean | ✅ Complete | Chain complexes using Mathlib's HomologicalComplex |
| Coderivations.lean | ✅ Complete | Coderivations on S⁺(V), square-zero condition |
| **SymmetricTensor.lean** | ✅ **NEW** | Symmetric tensors with actual elements, permutation action, Koszul signs |
| **SymmetricAlgebra.lean** | ✅ **NEW** | Full symmetric algebra S(V) and reduced S⁺(V) with actual elements |
| **PlanarTree.lean** | ✅ **NEW** | Planar rooted trees for homotopy transfer theorem |
| LInfinityAlgebra.lean | ⚠️ 2 sorrys | Main L∞ definition, Lie algebra embedding |
| Morphisms.lean | ✅ Complete | L∞ morphisms (coalgebra morphisms compatible with D) |
| MaurerCartan.lean | ✅ Complete | Maurer-Cartan elements, gauge equivalence |
| DGLA.lean | ⚠️ 4 sorrys | Differential graded Lie algebras |
| Transfer.lean | ⚠️ 3 sorrys | Homotopy transfer theorem |
| BVAlgebra.lean | ⚠️ 2 sorrys | BV algebras, cyclic L∞, Gerstenhaber bracket, Hochschild complex |
| Formality.lean | ⚠️ 8 sorrys | Kontsevich formality theorem |

### New Element-Based Infrastructure

The new `SymmetricTensor.lean` and `SymmetricAlgebra.lean` files provide:
- **Actual computable elements**: `SymTensor` with `degrees : Fin n → ℤ` and `elements : (i : Fin n) → V (degrees i)`
- **Koszul sign computation**: Real sign calculations, not axiomatized
- **Permutation action**: `SymTensor.permute` with proper sign tracking
- **Quotient structure**: `SymPowerElem` as `Quotient (SymTensor.setoid R V n)`
- **Product**: `SymPowerElem.product` implementing Sym^m × Sym^n → Sym^{m+n}
- **Projection to V**: `SymPowerElem.toV` for word-length-1 elements
- **Bracket extraction**: `CoderivationElem` with `l1`, `l2`, and `nthBracket` methods
- **L∞ structure with elements**: `LInftyElem` for computable L∞ algebras

### BV Formalism Extensions

The `BVAlgebra.lean` file now includes:
- **BVAlgebra structure**: Proper graded commutative algebra with BV Laplacian Δ
- **Gerstenhaber bracket**: `BVAlgebra.gerstenhaberBracket` computing `[a,b] = Δ(ab) - Δ(a)b - (-1)^|a| aΔ(b)`
- **Classical master equation**: `satisfiesCME` for `{S, S} = 0`
- **Quantum master equation**: `satisfiesQME` for `2ΔS + [S,S] = 0` (degree 0 elements)
- **QME_implies_CME_obstruction**: Proved that QME implies Δ([S,S]) = 0
- **Cyclic L∞ structure**: `CyclicLInfty` with graded pairing and cyclicity
- **Hochschild complex**: Full axiomatization with differential, cup product, and Gerstenhaber bracket
- **Trivial BV algebra**: Example with Subsingleton degrees

### Remaining Sorrys

#### LInfinityAlgebra.lean (2 sorrys)
- `transferredStructure` (line 208): Transferred L∞ structure via homotopy transfer
- `transferMorphism` (line 220): The transfer quasi-isomorphism

These require implementing the **tree sum formulas** for homotopy transfer:
```
l_n^H(x₁,...,xₙ) = ∑_T ε(T) p ∘ (products of l_k and h) ∘ i^⊗n
```

#### Transfer.lean (3 sorrys)
- Line 155: Tree formula coefficients
- Line 163: Transfer morphism construction
- Line 207: Quasi-isomorphism property

#### BVAlgebra.lean (2 sorrys)
- `gerstenhaberBracket_symm` (line 207): Graded symmetry [a,b] = (-1)^{mn} [b,a]
  - Requires extensive cast manipulation using graded commutativity
  - Infrastructure developed: `koszulSign_succ_left`, `koszulSign_succ_right` in Basic.lean
- `CME_implies_differential` (line 264): [S, [S, -]] = 0 from CME
  - Requires Jacobi identity for Gerstenhaber bracket (not yet proved)

#### DGLA.lean (4 sorrys)
- Lines 202, 248: DGLA-specific constructions for HKR theorem

#### Formality.lean (8 sorrys)
Kontsevich formality theorem constructions:
- Configuration space integrals
- Graph weights
- Formality L∞ morphism
- Deformation quantization star product

## Infrastructure Needs

### To Complete Transfer Theorem
1. **Tree combinatorics**: Planar rooted trees, tree automorphisms
2. **Tree sum formulas**: Implement the explicit formulas for transferred brackets
3. **Sign computations**: Koszul signs for tree operations

### To Complete Formality Theorem
1. **Configuration spaces**: Conf_n(ℂ) and compactifications
2. **Graph theory**: Kontsevich graphs, graph weights
3. **Polyvector fields**: T_poly as a DGLA
4. **Differential operators**: D_poly as a DGLA
5. **Integration**: Formal integrals over configuration spaces

## Design Decisions

### Coalgebraic Approach
We use the coalgebraic definition of L∞ algebras rather than explicit bracket identities because:
- Single condition D² = 0 encodes all generalized Jacobi identities
- Morphisms are simply coalgebra maps compatible with D
- Cleaner for homotopy transfer

### Placeholder Strategy
Some components use `Unit` placeholders or map to zero elements:
- `LieAlg.toLInfty`: Maps to zero (D² = 0 trivially)
- This is intentional for compilation while proper implementations are developed

### Integration with Mathlib
- Uses `DirectSum` for graded vector spaces
- Uses `HomologicalComplex` for chain complexes
- Uses `LieRing`/`LieAlgebra` for Lie algebra embedding

## Next Steps (Priority Order)

1. **Tree Infrastructure** (High Priority)
   - Define planar rooted trees as an inductive type
   - Implement tree iteration/recursion
   - Define tree automorphism groups

2. **Homotopy Transfer** (High Priority)
   - Implement tree sum formulas
   - Prove transferred structure satisfies L∞ axioms
   - Construct transfer quasi-isomorphism

3. **DGLA Completions** (Medium Priority)
   - Complete HKR theorem statement
   - Formalize polyvector fields and differential operators

4. **Formality Theorem** (Lower Priority - Major Project)
   - Configuration space infrastructure
   - Graph weights and integrals
   - This is a substantial project on its own

## References

- Lada, Stasheff - "Introduction to sh Lie algebras for physicists"
- Loday, Vallette - "Algebraic Operads"
- Kontsevich - "Deformation quantization of Poisson manifolds"
- Dolgushev - "A proof of Tsygan's formality conjecture"
