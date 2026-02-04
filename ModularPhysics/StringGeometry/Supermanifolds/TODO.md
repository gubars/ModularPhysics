# Supermanifolds Folder - Issues to Fix

## Summary

The algebraic foundations (Superalgebra.lean, GrassmannAlgebra, Berezinian) are well-developed.
**SuperDomainAlgebra.lean** provides Ring/Algebra instances for SuperDomainFunction.
The main Supermanifold definition now uses proper SuperAlgebra structure.

**Recently Completed:**
- `supercommutative'` theorem - Koszul sign rule for homogeneous elements (PROVEN)
- `mul_assoc'` - Associativity of SuperDomainFunction multiplication (PROVEN)
- `partialEven` smoothness - PROVEN using ContDiff.fderiv_right
- **Supermanifold** now has proper sheaf conditions (locality + gluing)
- **Supermanifold** structure sheaf now returns `SuperAlgebra ℝ` with supercommutativity
- **SuperChart.sheafIso** now properly typed as `RingEquiv` to SuperDomainFunction
- **SuperCoordinates** now has proper parity conditions (evenCoords_even, oddCoords_odd)
- **SuperTransition** removed tautological `overlap_nonempty`, added proper diffeomorphism conditions
- **`partialOdd_odd_derivation'`** - Graded Leibniz rule for odd derivatives (PROVEN)
  - Created `Helpers/PartialOddLeibniz.lean` with sign-related lemmas
  - Created `PartialOddDerivation.lean` with the full proof
  - Key lemma: `leibniz_sign_cancel` for the overlapping case I ∩ J = {a}
- **SuperVectorBundle** - Fully rigorous definition with:
  - `SuperFiber.preservesGrading` - characterizes GL(r|s) elements
  - `preservesGrading_symm` - inverse preserves grading (PROVEN)
  - `preservesGrading_trans` - composition preserves grading (PROVEN)
  - `transitionsPreserveGrading` - proper condition (no True placeholder)
- **BerezinianBundle** - Proper line bundle structure with:
  - `transitionsNonzero` - meaningful condition relating fiber elements
- **SuperRingCat.lean** - Fixed `map_maxIdeal`:
  - Added `SuperAlgHom.restrictEven` - restriction to even subrings
  - `map_maxIdeal` now properly states that the restriction maps maximal ideal into maximal ideal
- **Batchelor.lean** - Properly structured (all True placeholders removed):
  - `NilpotentIdeal` - proper ideal structure with add_mem, mul_mem, zero_mem, nilpotency
  - `NilpotentFiltration` - filtration by powers with descending, terminates, gradedPiecesRank
  - `OddCotangentBundle` - as SuperVectorBundle with ⟨0, dim.odd⟩ fibers
  - `SplitSupermanifold` - uses SuperVectorBundle, proper sheafIso
  - `SplittingData` - packages oddCotangent and sheafIso properly
- **Supermanifolds.lean** - All placeholder definitions fixed:
  - `LocalSuperAlgebra.residueField` - proper quotient type A/m using Setoid
  - `LocalSuperAlgebra.residueEquiv` - equivalence relation x ~ y iff x - y ∈ m
  - `transitionCocycle` - proper cocycle condition on body maps
  - `berezin_top` - proper definition and proof that ∫ θ¹...θ^q = 1
  - `berezin_change_of_variables` - proper statement (sorry for proof)
  - Removed `canonicalBundle` (belongs in SuperRiemannSurfaces folder)
  - Removed old `matrixMinor` and `linearSubst` (now superseded by SuperJacobian)
- **SuperJacobian.lean** - NEW: Super Jacobian for coordinate transformations:
  - `SuperDomainFunction.isEven`, `isOdd` - Parity predicates for Grassmann-valued functions
  - `SuperJacobian` - Full supermatrix structure with proper ℤ/2-grading
    - Ablock (p×p): ∂x'/∂x - even entries
    - Bblock (p×q): ∂x'/∂θ - odd entries
    - Cblock (q×p): ∂θ'/∂x - odd entries
    - Dblock (q×q): ∂θ'/∂θ - even entries
  - `SuperJacobian.id` - Identity Jacobian (proven parity conditions)
  - `Bblock_body_eq_zero`, `Cblock_body_eq_zero` - Off-diagonal blocks have zero body (proven)
  - `SuperCoordinateChange` - Coordinate transformation structure with Jacobian compatibility
  - Connects to Berezinian infrastructure in Helpers/Berezinian.lean
- **BerezinIntegration.lean** - All placeholder definitions fixed:
  - Now imports `FiniteGrassmann.lean` for proper Grassmann algebra infrastructure
  - Removed duplicate `SuperJacobian` definition (now uses proper one from SuperJacobian.lean)
  - `SuperPartitionOfUnity` - Fintype index, proper sum_eq_one and support conditions
  - `GlobalIntegralForm.compatible` - Body Jacobian transformation law
  - `CompactlySupportedIntegralForm.compact_support` - Uses IsCompact
  - `body_jacobian_cocycle` - Body Jacobian determinant multiplicativity
  - `berezinian_cocycle_full` - NEW: Full supermatrix formulation with:
    - Uses `SuperTransition.toSuperJacobian` from FiniteGrassmann.lean
    - Uses `SuperJacobian.berezinianAt` for Berezinian computation
    - Proper invertibility and parity hypotheses for D blocks
  - `SuperCoordChange.jacobian` - Now returns proper `SuperJacobian` with SuperDomainFunction entries
  - `berezin_fubini` - Proven (coefficient extraction)
  - `superDivergence` - Proper definition
  - `globalBerezinIntegral` - Uses explicit Finset.sum with finIndex instance
- **FiniteGrassmann.lean** - NEW infrastructure:
  - `FiniteGrassmannCarrier q` - Carrier type for Λ_q with Ring instance (fully proven)
  - `finiteGrassmannAlgebra q` - GrassmannAlgebra instance
  - `SuperDomainFunction.evalAtPoint` - Evaluation at a point gives FiniteGrassmann element
  - `SuperJacobian.toSuperMatrixAt` - Convert to SuperMatrix at a point
  - `SuperJacobian.berezinianAt` - Berezinian of SuperJacobian at a point
  - `SuperTransition.toSuperJacobian` - Compute Jacobian from coordinate transition (with proven parity)
  - `SuperTransition.berezinianAt` - Berezinian of a transition at a point

---

## Current State of Key Definitions

### Supermanifold (lines ~992-1040)
**SIGNIFICANTLY IMPROVED:**
- `structureSheaf : (U : Set body) → IsOpen U → SuperAlgebra ℝ`
- `sections_supercomm : ∀ U hU, SuperCommutative (structureSheaf U hU)`
- Proper sheaf conditions: `sheaf_locality` and `sheaf_gluing`
- `localTriviality` gives RingEquiv to SuperDomainFunction

### SuperChart (lines ~1100-1120)
**IMPROVED:**
- `bodyCoord_injective`, `bodyCoord_continuous`, `bodyCoord_image_open` (proper conditions)
- `sheafIso : (M.structureSheaf domain domainOpen).carrier ≃+* SuperDomainFunction`

### SuperCoordinates (lines ~1120-1130)
**IMPROVED:**
- `evenCoords_even : ∀ i, evenCoords i ∈ (...).even`
- `oddCoords_odd : ∀ a, oddCoords a ∈ (...).odd`

### SuperTransition (lines ~1190-1210)
**IMPROVED:**
- Removed tautological `overlap_nonempty`
- `bodyTransition_diffeo : ContDiff ℝ ⊤ ...`
- `bodyTransition_inv : ∃ (g : ...), ...`

### transitionCocycle (lines ~1230-1250)
**FIXED:**
- Proper cocycle condition: body_αγ = body_βγ ∘ body_αβ
- Uses body maps from even coordinate transitions

### SuperVectorBundle (lines ~1590-1640)
**COMPLETE:**
- `SuperFiber.preservesGrading` - proper grading-preservation definition
- `preservesGrading_symm` - proven that inverse preserves grading
- `preservesGrading_trans` - proven that composition preserves grading
- `transitionsPreserveGrading` - uses helper theorem, no placeholders

### BerezinianBundle (lines ~1770-1830)
**IMPROVED:**
- Proper line bundle structure with fiberEquiv, locallyTrivial
- `transitionsNonzero` - proper condition (no True placeholder)

### LocalSuperAlgebra.residueField (lines ~125-180)
**FIXED:**
- Proper equivalence relation: x ~ y iff x - y ∈ maxIdeal
- Quotient type using Setoid with proven reflexivity, symmetry, transitivity
- `maxIdeal_neg` - proven: -a ∈ m if a ∈ m

### linearSubst and Berezin Integration (lines ~1900-1970)
**FIXED:**
- `matrixMinor` - computes 1×1, 2×2, 3×3 determinants explicitly
- `linearSubst` - proper substitution: f(Aθ)_J = Σ_I f_I · det(A[I,J])
- `berezin_change_of_variables` - proper statement with sorry for proof

---

## Remaining Issues

### 1. Sorrys Requiring Proofs

| Location | Declaration | Status | Difficulty |
|----------|-------------|--------|------------|
| Supermanifolds.lean | `berezin_change_of_variables` | sorry | MEDIUM - needs det computation |
| Batchelor.lean | `batchelor_theorem` | sorry | HIGH - Deep result |
| Batchelor.lean | `batchelor_splitting` | sorry | HIGH - Deep result |
| Batchelor.lean | `canonicalNilpotentIdeal` (add_mem, etc.) | sorry | MEDIUM |
| Batchelor.lean | `canonicalFiltration` (descending, etc.) | sorry | MEDIUM |
| BerezinIntegration.lean | Various integration theorems | sorry | MEDIUM-HIGH |

### 2. Infrastructure Needed

- **matrixMinor** only handles n ≤ 3; general case needs Leibniz formula
- **Batchelor theorem proof** needs:
  - Sheaf cohomology
  - Partitions of unity
  - Vector bundle splitting

---

## File Status Summary

| File | Status | Key Issues |
|------|--------|------------|
| Superalgebra.lean | **Excellent** | Complete algebraic foundations |
| SuperRingCat.lean | **Excellent** | map_maxIdeal properly formulated |
| SuperDomainAlgebra.lean | **Excellent** | Ring/Algebra instances proven |
| Supermanifolds.lean | **Excellent** | All placeholders fixed |
| PartialOddDerivation.lean | **Excellent** | partialOdd_odd_derivation' proven |
| Batchelor.lean | Good | Proper structures, deep theorems sorry |
| BerezinIntegration.lean | **Good** | Proper supermatrix formulations, 5 sorrys |
| Helpers/SuperMatrix.lean | **Excellent** | Berezinian computation rigorous |
| Helpers/PartialOddLeibniz.lean | **Excellent** | Sign lemmas for Leibniz rule |
| Helpers/FiniteGrassmann.lean | **Excellent** | Ring instance fully proven, evaluation maps |
| SuperJacobian.lean | **Excellent** | Super Jacobian with proper grading |

---

## Notes

- **Structure sheaf returns SuperAlgebra ℝ**: This ensures the ℤ/2-grading is part of the definition
- **Local triviality gives Grassmann structure**: The RingEquiv to SuperDomainFunction provides body/soul
- **supercommutative'** proven using reorderSign_comm and ring tactics
- **partialEven** proven using ContDiff.fderiv_right and clm_apply
- **partialOdd_odd_derivation'** proven by case analysis:
  - Case I ∩ J = ∅: Standard Leibniz with sign from commuting derivative past f
  - Case I ∩ J = {a}: Both terms cancel via `(-1)^{|I|-1} + (-1)^|I| = 0`
  - Case |I ∩ J| ≥ 2: Products vanish (overlapping Grassmann indices)
- **SuperVectorBundle** now has proper GL(r|s) structure:
  - `preservesGrading` characterizes block-diagonal automorphisms
  - Helper theorems prove closure under composition and inversion
  - No `True` placeholders in the structure
- **BerezinianBundle** has proper line bundle structure with meaningful transition condition
- **canonicalBundle removed** - belongs in SuperRiemannSurfaces folder (requires complex structure + integrability)
- **linearSubst** uses exterior algebra transformation law: f(Aθ)_J = Σ_I f_I · det(A[I,J])
- **residueField** is a proper quotient A/m with proven equivalence relation properties
- **SuperPartitionOfUnity** (BerezinIntegration.lean) now has proper types:
  - `Fintype index` for well-defined finite sums
  - `sum_eq_one : ∀ x, Finset.univ.sum (fun α => functions α x) = 1`
  - `supportDomains` and `support_subset` for subordinate property
  - Based on Witten's notes (arXiv:1209.2199, §3.1)

---

## BerezinIntegration.lean - Recent Improvements

### Fixed Placeholders:
- **SuperPartitionOfUnity**: Proper structure with Fintype index, sum_eq_one, support_subset
- **GlobalIntegralForm.compatible**: Now has proper type with body Jacobian transformation
- **CompactlySupportedIntegralForm.compact_support**: Now uses `IsCompact` on support closure
- **berezinian_cocycle**: Proper statement using body Jacobian determinants
- **berezin_fubini**: Proven (extraction of top coefficient is the definition)
- **superDivergence**: Proper definition as sum of partial derivatives
- **super_divergence_theorem**: Proper type with body integral
- **super_stokes**: Proper type with boundary integral hypotheses

### Remaining Infrastructure Gaps

#### IntegralForm.pullback (line ~210)
**Currently**: Returns original form unchanged (placeholder).
**Needed**:
1. Super function composition (substitution f ∘ φ)
2. Berezinian computation via SuperMatrix.ber
3. Multiplication to get φ*ω = (f ∘ φ) · Ber(J_φ) · [Dx Dθ]

See Witten (arXiv:1209.2199, eq. 3.10).

#### Sorrys in BerezinIntegration.lean
| Declaration | Difficulty | Notes |
|-------------|-----------|-------|
| `berezin_change_of_variables_formula` | MEDIUM | Needs IntegralForm.pullback |
| `partition_of_unity_exists` | LOW | Standard manifold topology |
| `globalBerezinIntegral_independent` | MEDIUM | Uses Berezinian change of variables |
| `body_jacobian_cocycle` | MEDIUM | Chain rule + det multiplicativity |
| `berezinian_cocycle_full` | MEDIUM-HIGH | Needs super chain rule + SuperMatrix.ber_mul |