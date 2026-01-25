# RiemannSurfaces Folder - Issues to Fix

## Summary

The RiemannSurfaces folder contains extensive formalization of Riemann surface theory across three perspectives:
- **Analytic**: Teichmuller theory, quasiconformal maps, Green's functions
- **Algebraic**: Divisors, Riemann-Roch, theta functions, Abel-Jacobi
- **Combinatorial**: Ribbon graphs, cell decompositions

Main gaps are in:
1. Proper holomorphic atlas definitions (needs Mathlib complex manifold infrastructure)
2. Integration theory for period computations
3. Cohomology computations for Riemann-Roch
4. Sheaf-theoretic definitions for schemes/stacks

---

## Basic.lean (~7 True placeholders, ~6 sorry)

### RiemannSurface (line 80)
- `atlas : True` - Placeholder for HolomorphicAtlas
- **Suggestion**: Use Mathlib's `ChartedSpace C carrier` with holomorphic transition functions

### HolomorphicLineBundle (line 163)
- `holomorphicStructure : True` - Needs proper bundle formalism

### CanonicalBundle (line 168)
- `isCanonical : True` - Should verify sections are holomorphic 1-forms

### SpinStructure (line 197)
- `isSquareRoot : True` - Should be `spinBundle tensor spinBundle = K`

### Divisor (line 224)
- `finiteSupport : True` - Use `Set.Finite { p | coeff p != 0 }`

### IsPrincipal (line 235)
- `hasMeromorphicFn : True` - Should reference actual meromorphic function

### Notable sorry statements
- `HolomorphicLineBundle.degree` (line 175) - Requires Chern class theory
- `canonical_degree` (line 182) - Riemann-Hurwitz theorem
- `SpinStructure.parity` (line 212) - Requires h^0 computation
- `Divisor.degree` (line 230) - Finite sum over support
- `principal_divisor_degree_zero` (line 243) - Argument principle
- `riemann_roch` (line 284) - Full theorem (see Algebraic/RiemannRoch.lean)

---

## Moduli.lean (~40+ True placeholders, ~15 sorry)

### Scheme/Stack Infrastructure (lines 82-200)
- `Scheme.locallyAffine : True` - Needs proper scheme definition
- `CurveFamily` properties all True - proper, flat, smoothFibers, fiberGenus
- `DMStack` properties - etaleAtlas, finiteAutomorphisms, unramifiedDiagonal
- `ModuliStack.representsModuli : True` - Should be functor representability

### Deformation Theory (lines 210-340)
- `TangentSheaf.dualToCanonical : True` - Should use proper bundle duality
- `TangentSpaceToModuli.serreDualityIso : True` - Needs Serre duality
- `moduli_dim_deformation` (line 350) - sorry

### Coarse Moduli Space (lines 385-475)
- `ModuliSpace.quasiProjective : True` - Needs algebraic geometry
- Many automorphism and locus placeholders

### Teichmuller Space (lines 520-680)
- `TeichmullerSpace.contractible : True` - **HIGH PRIORITY**
- `TeichmullerSpace.simplyConnected : True`
- `teichmuller_contractible` (line 660) - sorry, Earle-Eells theorem

### Bers Embedding (lines 700-730)
- `BersEmbedding` properties - holomorphic, injective, bounded, domainOfHolomorphy
- `bers_embedding_exists` (line 726) - sorry

### Mapping Class Group (lines 738-780)
- `dehn_lickorish` (line 761) - sorry
- `moduli_as_quotient` (line 777) - sorry

### Deligne-Mumford Compactification (lines 788-822)
- `StableCurve` properties all True
- `DeligneMumfordCompactification.boundaryNCD : True`

### Period Map (lines 830-880)
- `SiegelUpperHalfSpace.posDefIm : True` - Should be `Matrix.PosDef (Ω.map Complex.im)`
- `torelli` (line 870) - sorry

---

## Analytic/GreenFunction.lean (~9 True placeholders, ~4 sorry)

### GreenFunction (lines 62-70)
- `logSingularity : True` - Should be `ContinuousAt (G + log |z - w|) w`
- `boundaryCondition : True` - Should be `∀ z ∈ frontier U, G z = 0`

### CompactGreenFunction (lines 144-155)
- `logSingularity : True` - Logarithmic singularity on diagonal
- `normalized : True` - Should be `∫_Σ G(·, w) dA = 0`
- `harmonicOffDiag : True` - Δ_z G = 0 for z ≠ w

### AdmissibleMetric (lines 168-175)
- `metric : True` - Metric tensor in local coordinates
- `smooth : True` - Smooth and positive
- `normalized : True` - Total area equals 1

### Notable sorry statements
- `poissonIntegral` (line 129) - Needs circle integration
- `poissonIntegral_harmonic` (line 133) - Harmonic extension theorem
- `compact_green_exists` (line 158) - Existence of Green's function
- `arakelov_green_exists_unique` (line 192) - Existence and uniqueness

---

## Analytic/Harmonic.lean (~3 True placeholders, ~14 sorry)

### IsHarmonicConjugate (line 152)
- Cauchy-Riemann condition as `True` placeholder

### HarmonicOnSurface (line 197)
- Placeholder for chart-based definition

### Harmonic1Form (line 212)
- `closed : True` - Needs differential forms infrastructure

### Notable sorry statements - **HIGH PRIORITY for harmonic analysis**
- `harmonic_iff_laplacian_zero` (line 89) - Characterization
- `harmonic_mean_value` (line 112) - Mean value property
- `mean_value_implies_harmonic` (line 119) - Converse
- `harmonic_maximum_principle` (line 132) - Maximum principle
- `harmonic_minimum_principle` (line 139) - Minimum principle
- `harmonic_conjugate_exists_locally` (line 157) - Local existence
- `harmonic_conjugate_simply_connected` (line 163) - Global existence
- `holomorphic_real_part_harmonic` (line 173) - Real part harmonic
- `holomorphic_imag_part_harmonic` (line 179) - Imaginary part harmonic
- `log_norm_harmonic` (line 186) - log|f| harmonic
- `harmonic_1forms_dimension` (line 229) - Hodge theory
- `poisson_dirichlet_existence` (line 249) - Dirichlet problem

---

## Analytic/Moduli.lean (~35+ True placeholders, ~15 sorry)

### QuasiconformalMap (lines 84-95) - **HIGH PRIORITY**
- `homeomorph : True` - Should be `IsHomeomorph f U V`
- `dilatation_bound : True` - `|∂f/∂z̄| ≤ k|∂f/∂z|`
- `sobolev : True` - `f ∈ W^{1,2}_{loc}`

### BeltramiDifferential (lines 176-185)
- `measurable : True` - `Measurable μ`
- `transformationLaw : True` - (-1,1)-form transformation

### HarmonicBeltramiDifferential (lines 200-207)
- `holomorphic : True` - φ is holomorphic
- `harmonicCondition : True` - μ = φ̄/ρ

### TeichmullerSpaceAnalytic (lines 264-276)
- `complexStructure : True` - Complex manifold charts
- `contractible : True` - Earle-Eells theorem
- `simplyConnected : True` - Follows from contractible
- `stein : True` - Bers embedding

### TeichmullerMetricAnalytic (lines 350-363)
- `metric : True` - Metric space axioms
- `finsler : True` - Non-Riemannian unit ball
- `complete : True` - Complete metric space
- `uniquelyGeodesic : True` - Unique geodesics
- `nonPositiveCurvature : True` - CAT(0) property

### WeilPeterssonMetricAnalytic (lines 451-464)
- `kahler : True` - Kähler form
- `negativeHolomorphicCurvature : True` - Ahlfors-Royden
- `negativeRicci : True`
- `incomplete : True` - Finite distance to boundary

### Notable sorry statements
- `dilatation_lt_one` (line 114) - k < 1 for K > 1
- `quasiconformal_comp` (line 127) - Composition bound
- `measurable_riemann_mapping` (line 225) - **KEY THEOREM**
- `teichmuller_distance_formula` (line 377)
- `royden_theorem` (line 410) - Kobayashi = Teichmuller
- `wp_volume_finite` (line 507) - Wolpert
- `bers_embedding_exists` (line 570)
- `torelli_analytic` (line 608)

---

## Algebraic/Divisors.lean (~5 True placeholders, ~3 sorry)

### MeromorphicFunction (lines 322-336)
- `meromorphic : True` - Needs proper holomorphic/meromorphic definition

### orderAt (lines 377-378)
- Currently returns 0 as placeholder
- **Suggestion**: Define via local power series expansion

### Notable sorry statements
- `principal_degree_zero` (line 417) - Argument principle
- `degree_well_defined_quotient` (line 523) - Degree on quotient
- `ell_lower_bound` (line 597) - Riemann-Roch lower bound

---

## Algebraic/RiemannRoch.lean (~13 True placeholders, ~7 sorry)

### LineBundleRR (line 92)
- `bundleData : True` - Actual bundle structure needed

### CanonicalDivisor (line 143)
- `isCanonical : True` - Verify divisor of 1-form

### H0Space/H1Space (lines 180-207)
- `elements_bounded : True` - Proper function space
- `dolbeault : True` - Dolbeault description

### SerreDuality (lines 234-244)
- `dualityIso : True` - **HIGH PRIORITY**: H^1(D) = H^0(K-D)*

### QuadDiffSpace (lines 409-413)
- `h1_vanishes : True` - h^0(K^{-1}) = 0

### Notable sorry statements - **CRITICAL for applications**
- `canonical_divisor_degree` (line 154) - deg(K) = 2g - 2
- `riemann_roch` (line 311) - **THE MAIN THEOREM**
- `h0_trivial` (line 346) - Maximum principle
- `genus_equals_h0_canonical` (line 362) - g = h^0(K)
- `h0_negative_degree` (line 377) - No sections for deg < 0
- `no_global_vector_fields` (line 430) - h^0(T) = 0
- `quadratic_differentials_dimension` (line 451) - h^0(K^2) = 3g-3

---

## Algebraic/ThetaFunctions.lean (~6 True placeholders, ~8 sorry)

### SiegelHg (line 73)
- `posDefIm : True` - Should be `Matrix.PosDef (Ω.map Complex.im)`

### Notable sorry statements
- `theta_holomorphic` (line 93) - Uniform convergence
- `theta_holomorphic_in_omega` (line 100) - Holomorphic dependence
- `thetaWithChar_relation` (line 157) - Relation to Riemann theta
- `theta_parity` (line 167) - Parity under negation
- `halfIntegerCharacteristics` (line 196) - Combinatorics of (Z/2)^{2g}
- `num_half_int_characteristics` (line 200) - Count = 2^{2g}
- `riemannConstant` (line 269) - Requires Weierstrass points
- `fay_trisecant` (line 289) - Deep theta identity

---

## Algebraic/AbelJacobi.lean (~20+ True placeholders, ~5 sorry)

### Holomorphic1Form (lines 58-63)
- `holomorphic : True` - Proper holomorphic condition

### HolomorphicBasis (lines 65-72)
- `linearIndep : True`, `spans : True` - Vector space basis

### SymplecticBasis (lines 95-106)
- All intersection pairings as `True` placeholders

### PeriodMatrix (lines 124-133)
- `posDefIm : True` - Positive definite imaginary part
- `normalized : True` - a-period normalization

### abelJacobiMap (lines 195-199)
- Currently uses `Classical.arbitrary` - needs integration

### Notable sorry statements
- `abel_theorem'` (line 228) - **Abel's theorem**
- `pic0_isomorphic_jacobian` (line 237) - Pic^0 = J
- `jacobi_inversion` (line 273) - **Jacobi inversion theorem**

---

## Combinatorial/RibbonGraph.lean (~10 True placeholders, ~4 sorry)

### RibbonGraph operations
- `numFaces` (lines 147-152) - Currently a placeholder formula
- `numBoundaryComponents` (line 163) - Assumes closed surface
- `contractEdge`, `deleteEdge`, `dual` - All return original graph

### ThickenedSurface (lines 206-214)
- `orientable : True`, `hasBoundary : True` - Topological properties

### Automorphism (lines 288-299)
- `preserves_cyclic : True` - Cyclic order preservation

### Notable sorry statements
- `euler_formula` (line 179) - χ = 2 - 2g - n
- `closed_surface_genus` (line 239) - Genus formula
- `cell_dimension` (line 382) - Dimension = 6g - 6 + 3n

---

## Combinatorial/Moduli.lean (~15 True placeholders, ~1 sorry)

### TeichmullerCell'/DecoratedTeichmullerSpace' (lines 78-94)
- All properties as `True` placeholders

### WeilPeterssonForm (lines 107-114)
- `form : True`, `closed : True`, `kahler : True`

### wpVolume (line 128)
- Returns 1 as placeholder - should compute via Mirzakhani recursion

### intersectionNumber (line 154)
- Returns 0 as placeholder - should use Kontsevich formula

### ModuliForm (lines 200-206)
- Abstract form with True placeholders

### integrateModuli (line 213)
- Returns 0 as placeholder

### Notable sorry statements
- `intersection_dimension_constraint` (line 160) - Σdᵢ = 3g - 3 + n

---

## Priority Order for Fixes

### Critical (Core Theorems)
1. **Riemann-Roch theorem** (`Algebraic/RiemannRoch.lean`) - Foundation for dimension computations
2. **Abel's theorem** (`Algebraic/AbelJacobi.lean`) - Principal divisor characterization
3. **Jacobi inversion** (`Algebraic/AbelJacobi.lean`) - Surjectivity of Abel-Jacobi

### High Priority (Analytic Foundations)
4. **QuasiconformalMap** proper definition - homeomorphism, Sobolev, dilatation
5. **Measurable Riemann Mapping theorem** - Existence of QC maps
6. **Harmonic function theory** - Mean value, maximum principle
7. **TeichmullerSpace.contractible** - Earle-Eells theorem

### Medium Priority (Infrastructure)
8. **RiemannSurface.atlas** - Use Mathlib complex manifold when available
9. **Serre duality** implementation
10. **Period matrix** computations via integration
11. **Green's function** existence theorems

### Lower Priority (Advanced Topics)
12. **Theta function** identities (Fay trisecant)
13. **Kontsevich intersection numbers**
14. **Weil-Petersson volumes** (Mirzakhani recursion)
15. **Ribbon graph** operations (contraction, deletion, duality)

---

## Notes

- The **Divisors.lean** file has proper `AddCommGroup` structure and working degree computations
- The **RibbonGraph.lean** file has good combinatorial foundations
- Main work needed is connecting to Mathlib's:
  - Complex manifold infrastructure (when available)
  - Integration theory for period computations
  - Sheaf cohomology for Riemann-Roch
- Many placeholders use `Classical.arbitrary` or constant functions - these need proper implementations
- The `True` placeholders in structures should be replaced with proper Prop conditions
