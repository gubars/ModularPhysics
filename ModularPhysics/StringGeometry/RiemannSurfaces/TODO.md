# RiemannSurfaces Folder - TODO

## Summary

The RiemannSurfaces folder contains extensive formalization of Riemann surface theory across four perspectives:
- **Analytic**: Teichmuller theory, quasiconformal maps, Green's functions
- **Algebraic**: Divisors, Riemann-Roch, theta functions, Abel-Jacobi
- **Combinatorial**: Ribbon graphs, cell decompositions, Penner/Kontsevich map
- **Topology**: Surface topology, simple curves, pants decompositions, Hatcher-Thurston

Main gaps are in:
1. Proper holomorphic atlas definitions (needs Mathlib complex manifold infrastructure)
2. Integration theory for period computations
3. Cohomology computations for Riemann-Roch
4. Sheaf-theoretic definitions for schemes/stacks

---

## Priority Order for Fixes

### Critical (Core Theorems)
1. **Riemann-Roch theorem** (`Algebraic/RiemannRoch.lean`) - Foundation for dimension computations
2. **Abel's theorem** (`Algebraic/AbelJacobi.lean`) - Principal divisor characterization
3. **Jacobi inversion** (`Algebraic/AbelJacobi.lean`) - Surjectivity of Abel-Jacobi

### High Priority (Analytic Foundations)
4. **Measurable Riemann Mapping theorem** - Existence of QC maps
5. **Harmonic function theory** - Mean value, maximum principle
6. **TeichmullerSpace.contractible** - Earle-Eells theorem

### Medium Priority (Infrastructure)
7. **RiemannSurface.atlas** - Use Mathlib complex manifold when available
8. **Serre duality** implementation
9. **Period matrix** computations via integration
10. **Green's function** existence theorems

### Lower Priority (Advanced Topics)
11. **Theta function** identities (Fay trisecant)
12. **Kontsevich intersection numbers**
13. **Weil-Petersson volumes** (Mirzakhani recursion)
14. **Ribbon graph** operations (contraction, deletion, duality)

---

## Moduli.lean

### Scheme/Stack Infrastructure
- `Scheme.locallyAffine` - Needs proper scheme definition
- `CurveFamily` properties - proper, flat, smoothFibers, fiberGenus
- `DMStack` properties - etaleAtlas, finiteAutomorphisms, unramifiedDiagonal
- `ModuliStack.representsModuli` - Should be functor representability

### Deformation Theory
- `TangentSheaf.dualToCanonical` - Should use proper bundle duality
- `TangentSpaceToModuli.serreDualityIso` - Needs Serre duality
- `moduli_dim_deformation` - sorry

### Coarse Moduli Space
- `ModuliSpace.quasiProjective` - Needs algebraic geometry

### Teichmuller Space
- `TeichmullerSpace.contractible` - Earle-Eells theorem
- `TeichmullerSpace.simplyConnected`
- `teichmuller_contractible` - sorry

### Bers Embedding
- `BersEmbedding` properties - holomorphic, injective, bounded, domainOfHolomorphy
- `bers_embedding_exists` - sorry

### Mapping Class Group
- `dehn_lickorish` - sorry
- `moduli_as_quotient` - sorry

### Deligne-Mumford Compactification
- `StableCurve` properties
- `DeligneMumfordCompactification.boundaryNCD`

### Period Map
- `SiegelUpperHalfSpace.posDefIm` - Should be `Matrix.PosDef (Ω.map Complex.im)`
- `torelli` - sorry

---

## Basic.lean

### Remaining sorry statements
- `HolomorphicLineBundle.degree` - Requires Chern class theory
- `canonical_degree` - Riemann-Hurwitz theorem
- `SpinStructure.parity` - Requires h^0 computation
- `Divisor.degree` - Finite sum over support
- `principal_divisor_degree_zero` - Argument principle
- `riemann_roch` - Full theorem (see Algebraic/RiemannRoch.lean)

---

## Analytic/GreenFunction.lean

### True placeholders to fix
- `GreenFunction.logSingularity` - Should be `ContinuousAt (G + log |z - w|) w`
- `GreenFunction.boundaryCondition` - Should be `∀ z ∈ frontier U, G z = 0`
- `CompactGreenFunction.logSingularity` - Logarithmic singularity on diagonal
- `CompactGreenFunction.normalized` - Should be `∫_Σ G(·, w) dA = 0`
- `CompactGreenFunction.harmonicOffDiag` - Δ_z G = 0 for z ≠ w
- `AdmissibleMetric` properties - metric, smooth, normalized

### sorry statements
- `poissonIntegral` - Needs circle integration
- `poissonIntegral_harmonic` - Harmonic extension theorem
- `compact_green_exists` - Existence of Green's function
- `arakelov_green_exists_unique` - Existence and uniqueness

---

## Analytic/Harmonic.lean

### True placeholders to fix
- `IsHarmonicConjugate` - Cauchy-Riemann condition
- `HarmonicOnSurface` - Chart-based definition
- `Harmonic1Form.closed` - Needs differential forms infrastructure

### sorry statements (HIGH PRIORITY for harmonic analysis)
- `harmonic_iff_laplacian_zero` - Characterization
- `harmonic_mean_value` - Mean value property
- `mean_value_implies_harmonic` - Converse
- `harmonic_maximum_principle` - Maximum principle
- `harmonic_minimum_principle` - Minimum principle
- `harmonic_conjugate_exists_locally` - Local existence
- `harmonic_conjugate_simply_connected` - Global existence
- `holomorphic_real_part_harmonic` - Real part harmonic
- `holomorphic_imag_part_harmonic` - Imaginary part harmonic
- `log_norm_harmonic` - log|f| harmonic
- `harmonic_1forms_dimension` - Hodge theory
- `poisson_dirichlet_existence` - Dirichlet problem

---

## Analytic/Moduli.lean

### True placeholders to fix
- `BeltramiDifferential.measurable` - `Measurable μ`
- `BeltramiDifferential.transformationLaw` - (-1,1)-form transformation
- `HarmonicBeltramiDifferential.holomorphic` - φ is holomorphic
- `HarmonicBeltramiDifferential.harmonicCondition` - μ = φ̄/ρ
- `TeichmullerSpaceAnalytic` properties - complexStructure, contractible, simplyConnected, stein
- `TeichmullerMetricAnalytic` properties - metric, finsler, complete, uniquelyGeodesic, nonPositiveCurvature
- `WeilPeterssonMetricAnalytic` properties - kahler, negativeHolomorphicCurvature, negativeRicci, incomplete

### sorry statements
- `dilatation_lt_one` - k < 1 for K > 1
- `quasiconformal_comp` - Composition bound
- `measurable_riemann_mapping` - **KEY THEOREM**
- `teichmuller_distance_formula`
- `royden_theorem` - Kobayashi = Teichmuller
- `wp_volume_finite` - Wolpert
- `bers_embedding_exists`
- `torelli_analytic`

---

## Algebraic/Divisors.lean

### sorry statements
- `principal_degree_zero` - Argument principle (deep theorem)
- `degree_well_defined_quotient` - Degree on quotient
- `ell_lower_bound` - Riemann-Roch lower bound

---

## Algebraic/RiemannRoch.lean

### sorry statements (CRITICAL for applications)
- `canonical_divisor_degree` - deg(K) = 2g - 2
- `riemann_roch` - **THE MAIN THEOREM**
- `h0_trivial` - Maximum principle
- `genus_equals_h0_canonical` - g = h^0(K)
- `h0_negative_degree` - No sections for deg < 0
- `no_global_vector_fields` - h^0(T) = 0
- `quadratic_differentials_dimension` - h^0(K^2) = 3g-3
- `hyperbolic_nondegenerate` (in Arf.lean) - Hyperbolic form is non-degenerate

---

## Algebraic/ThetaFunctions.lean

### True placeholders to fix
- `SiegelHg.posDefIm` - Should be `Matrix.PosDef (Ω.map Complex.im)`

### sorry statements
- `theta_holomorphic` - Uniform convergence
- `theta_holomorphic_in_omega` - Holomorphic dependence
- `thetaWithChar_relation` - Relation to Riemann theta
- `theta_parity` - Parity under negation
- `halfIntegerCharacteristics` - Combinatorics of (Z/2)^{2g}
- `num_half_int_characteristics` - Count = 2^{2g}
- `riemannConstant` - Requires Weierstrass points
- `fay_trisecant` - Deep theta identity

---

## Algebraic/AbelJacobi.lean

### True placeholders to fix
- `Holomorphic1Form.holomorphic` - Proper holomorphic condition
- `HolomorphicBasis` - linearIndep, spans
- `SymplecticBasis` - All intersection pairings
- `PeriodMatrix.posDefIm` - Positive definite imaginary part
- `PeriodMatrix.normalized` - a-period normalization
- `abelJacobiMap` - Currently uses `Classical.arbitrary`, needs integration

### sorry statements
- `abel_theorem'` - **Abel's theorem**
- `pic0_isomorphic_jacobian` - Pic^0 = J
- `jacobi_inversion` - **Jacobi inversion theorem**

---

## Combinatorial/RibbonGraph.lean

### True placeholders to fix
- `contractEdge`, `deleteEdge`, `dual` - All return original graph (need proper implementations)
- `ThickenedSurface` properties - orientable, hasBoundary
- `Automorphism.preserves_cyclic` - Cyclic order preservation

### sorry statements
- `euler_formula` - χ = 2 - 2g - n
- `closed_surface_genus` - Genus formula
- `cell_dimension` - Dimension = 6g - 6 + 3n

---

## Combinatorial/Moduli.lean

### True placeholders to fix
- `TeichmullerCell'/DecoratedTeichmullerSpace'` properties
- `WeilPeterssonForm` - form, closed, kahler
- `wpVolume` - Returns 1 (should use Mirzakhani recursion)
- `intersectionNumber` - Returns 0 (should use Kontsevich formula)

### sorry statements
- `kontsevich_theorem_2_2` - Main bijection theorem
- `strebel_existence_uniqueness` - Existence of Strebel differentials
- `intersection_dimension_constraint` - Σdᵢ = 3g - 3 + n

---

## Topology/ Folder

### Topology/Basic.lean
- `Surface.genus` - sorry (requires triangulation or homology)
- `Surface.numBoundary` - sorry
- `OnePoint.Complex.secondCountableTopology` - sorry

### Topology/SimpleCurves.lean
- `dehn_twist_intersection` - sorry (intersection formula)
- `curve_complex_connected` - sorry (Harvey's theorem)
- `curve_complex_hyperbolic` - sorry (Masur-Minsky)

### Topology/PantsDecomposition.lean
- `Marking.trinions` - sorry
- `trinions_card` - sorry
- `fenchel_nielsen_parametrization` - sorry
- `fenchel_nielsen_change_of_coords` - sorry
- `wolpert_formula` - sorry

### Topology/HatcherThurston.lean
- `applyMove` - Multiple sorry statements for move well-definedness
- `hatcher_thurston` - sorry (main connectivity theorem)
- `pants_graph_infinite` - sorry
- `pantsDistance` - sorry
- `pants_graph_infinite_diameter` - sorry
- `pants_distance_eq_min_length` - sorry

---

## Notes

- Main work needed is connecting to Mathlib's:
  - Complex manifold infrastructure (when available)
  - Integration theory for period computations
  - Sheaf cohomology for Riemann-Roch
- Many placeholders use `Classical.arbitrary` or constant functions - these need proper implementations
