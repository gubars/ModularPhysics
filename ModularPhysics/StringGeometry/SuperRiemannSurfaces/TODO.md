# SuperRiemannSurfaces Folder - Issues to Fix

## Summary

The SuperRiemannSurfaces folder contains the formalization of super Riemann surfaces (SRS) - the worldsheet geometry for superstring theory. It covers:
- Basic definitions (superconformal structure, coordinates, spin structures)
- Superconformal maps and OSp(1|2)
- Supermoduli space and Donagi-Witten theorem
- Integration over supermoduli (picture-changing formalism)

Main gaps are in:
1. Holomorphic function theory over Grassmann algebras
2. Derivative computations for Grassmann-valued functions
3. The Donagi-Witten non-projectedness theorem
4. Integration infrastructure for supermoduli

---

## Basic.lean (~12 True placeholders, ~3 sorry)

### SuperDomain11 (lines 96-123)
- `partialZ` (line 105) - `sorry` for holomorphic derivative of coefficients
- `D_theta_squared` (line 121) - `sorry` for key relation D_θ² = ∂/∂z
- **Suggestion**: Define partial derivatives properly using GrassmannAlgebra structure

### SuperconformalDistribution (lines 189-196)
- `maximalNonIntegrability : Prop` - Should have proper definition/proof
- **Note**: The constraint [D, D] = TM/D is the defining equation of SRS

### SuperconformalCoordinates (line 295)
- `generates_D : True` - Should verify D_θ = ∂/∂θ + θ∂/∂z generates the distribution

### SuperconformalTransition (lines 309-323)
- `theta_transition : True` - Should verify θ' = ψ(z) + θη(z)
- `superconformal_constraint : True` - Should verify η² = f' + ψψ'
- **Note**: Requires proper derivatives on Λ.evenCarrier

### DistributionRestriction (lines 362-370)
- `squareIsTangent : True` - Should be `D|_{Σ_red} ⊗ D|_{Σ_red} ≅ T`
- `dualIsSpinBundle : True` - Should be `(D|_{Σ_red})* ≅ K^{1/2}`

### SplitSuperRiemannSurface (lines 385-392)
- `isSplit : True` - Should verify structure sheaf is O_Σ ⊕ S*

### SuperRiemannSurface.isSplit (line 412)
- `sorry` - Requires checking if extension class in H¹(Sym²E) vanishes

### SuperVirasoroRelations (lines 447-453)
- `LL_comm : True` - Should be [L_m, L_n] = (m-n)L_{m+n} + central term
- `LG_comm : True` - Should be [L_m, G_r] = (m/2 - r)G_{m+r}
- `GG_anticomm : True` - Should be {G_r, G_s} = 2L_{r+s} + central term
- **HIGH PRIORITY**: Super Virasoro algebra relations

### SuperMeasure (line 486)
- `measure : True` - Should define Berezinian measure properly

### integrate (line 497)
- Returns 0 as placeholder - needs Berezin integration infrastructure

---

## SuperModuli.lean (~55+ True placeholders, ~15 sorry)

### SuperModuliSpace (lines 89-100) - **HIGH PRIORITY**
- Structure is well-defined but dimension computations need proofs

### Dimension Computations (lines 108-148)
- `evenTangentDim` (line 110) - `sorry` for dim H¹(Σ, T_Σ)
- `oddTangentDim` (line 120) - `sorry` for dim H¹(Σ, K^{1/2})
- `supermoduli_even_dim` (line 130) - `sorry` for 3g - 3
- `supermoduli_odd_dim` (line 147) - `sorry` for 2g - 2
- **Requires**: Cohomology computations from RiemannRoch.lean

### SuperModuliProjection (lines 151-162)
- `submersion : True` - Should verify projection is a submersion
- `fiberStructure : True` - Fibers related to spin structures

### SpinModuliSpace (lines 172-178)
- `spinStructure : True` - Should specify choice of spin structure

### OddTangentBundle (lines 190-196)
- `odd_tangent_bundle_rank` (line 206) - `sorry` for rank = 2g - 2
- **Requires**: Riemann-Roch for K^{3/2}

### ProjectedSupermanifold (lines 222-234)
- `bundleStructure : True` - Needs proper vector bundle formalism
- `structureSheafIsExterior : True` - O_M ≅ ∧•E*

### ProjectednessObstruction (lines 259-266)
- `projected_iff_zero : True` - Should be proper iff statement

### Donagi-Witten Theorem (lines 282-296) - **CRITICAL**
- `supermoduli_not_projected` (line 286) - `sorry` for non-projectedness (g ≥ 5)
- `h1_sym2E_nonzero` (line 591) - Placeholder for H¹(M_g, Sym²E) ≠ 0
- `low_genus_projected` (line 601) - Placeholder for g ≤ 4 case

### HodgeBundle (lines 307-314)
- `hodge_bundle_rank` (line 323) - `sorry` for rank = g
- **Requires**: Riemann-Roch for K

### Sym2OddBundle (lines 397-403)
- `sym2_odd_bundle_rank` (line 409) - `sorry` for rank formula

### ObstructionCohomology (lines 413-419)
- `finiteDim : True`, `dimensionFormula : True` - Need cohomology theory

### GRR Computations (lines 560-580)
- `eulerCharSym2E` (line 578) - `sorry` for GRR computation
- `h1_Sym2E` (line 680) - `sorry` for dimension
- `h1_growth` (line 686) - `sorry` for monotonicity
- `h1_dimension_formula` (line 696) - Placeholder

### String Theory Structures (lines 706-893)
- `NaiveAmplitudeApproach` - Illustrates failure of naive approach
- `IntrinsicSupermoduliIntegration` - All True placeholders
- `PictureChangingFormalism` - All True placeholders
- `SuperChartFromPCO` - Local trivialization via PCO
- `GluedIntegrationCycle` - Wang-Yin construction
- `VerticalIntegration` - Sen-Witten prescription

---

## SuperconformalMaps.lean (~35+ True placeholders, ~20 sorry)

### GrassmannValuedHolomorphic (lines 107-130) - **HIGH PRIORITY**
- Inductive definition for holomorphic functions over Grassmann algebras
- `Nonempty` instance (line 117) - `sorry` axiom for existence
- `zero_toFun` (line 239) - axiom for partial function behavior
- `id_derivative_toFunEven` (line 302) - axiom for derivative of identity
- `zero_derivative_toFun` (line 307) - axiom for derivative of zero

### GrassmannHolomorphic (lines 170-183)
- `taylor_expansion : True` - Should verify Taylor formula with nilpotent soul

### GrassmannHolomorphic.derivative (lines 188-194)
- `toFun` - `sorry` for derivative via Taylor expansion
- `bodyRestriction_eq` - `sorry` for agreement with body restriction

### GrassmannHolomorphicEven/Odd derivatives (lines 252-266)
- `GrassmannHolomorphicEven.derivative` (line 257) - `sorry` for even preservation
- `GrassmannHolomorphicOdd.derivative` (line 265) - `sorry` for odd preservation

### GrassmannHolomorphicEven.comp (lines 310-316)
- `bodyRestriction` - `sorry` for composition of holomorphic functions
- `bodyRestriction_eq` - `sorry` for agreement

### LocalHoloSuperDiff (lines 349-392)
- Well-structured for super-diffeomorphisms
- Identity properly defined with invertibility proofs

### LocalSuperconformalMap (lines 434-473)
- `r_eq_gh` constraint - properly stated
- `superconformal_constraint` - properly stated as η² = f' + ψψ'
- Identity properly defined with constraint verification

### LocalSuperconformalMap.compHoloSuperDiff (lines 491-524)
- `h_invertible` (line 520) - `sorry` for product invertibility
- `f_deriv_invertible` (line 524) - `sorry` for chain rule
- Various `sorry` in bodyRestriction constructions

### LocalSuperconformalMap.comp (lines 545-556)
- `superconformal_constraint` (line 555) - `sorry` for composition preserves constraint
- **Requires**: Chain rule for Grassmann-holomorphic functions

### InfinitesimalSuperconformal (lines 589-598)
- `constraint : True` - Should be v' = 2χ'χ

### SuperWittGeneratorL/G (lines 600-611)
- `is_Ln : True`, `is_Gr : True` - Should verify generator form

### SuperWittRelations (lines 614-620)
- `LL_comm : True` - [L_m, L_n] = (m-n)L_{m+n}
- `LG_comm : True` - [L_m, G_r] = (m/2 - r)G_{m+r}
- `GG_anticomm : True` - {G_r, G_s} = 2L_{r+s}

### OSp12 (lines 639-701)
- Well-structured with proper SL(2) constraint
- `mul` (line 680) - odd parameter composition is placeholder (lines 697-698)
- **Note**: Full super-group multiplication law needed

### SuperconformalMap (lines 710-718)
- `localForm : True` - Should verify coordinate expression
- `preserves_D : True` - Should verify φ_* D₁ = D₂

### SuperconformalAutomorphism (lines 721-726)
- `is_iso : True` - Should verify inverse composition is identity

### SuperAutomorphismGroup (lines 729-736)
- `are_automorphisms : True` - Should verify elements are automorphisms

---

## Priority Order for Fixes

### Critical (Core Theorems)
1. **Donagi-Witten theorem** - Non-projectedness for g ≥ 5 (the main result)
2. **Supermoduli dimensions** - 3g-3 | 2g-2 via cohomology
3. **D_theta_squared** - D_θ² = ∂/∂z (key superconformal relation)

### High Priority (Foundational)
4. **GrassmannValuedHolomorphic** - Proper derivative theory
5. **LocalSuperconformalMap.comp** - Composition preserves superconformality
6. **Super Virasoro relations** - Bracket computations

### Medium Priority (Structure)
7. **SuperconformalTransition.superconformal_constraint** - η² = f' + ψψ'
8. **OSp12.mul** - Full super-group multiplication
9. **OddTangentBundle/Sym2OddBundle ranks** - Via Riemann-Roch

### Lower Priority (Applications)
10. **PictureChangingFormalism** - Wang-Yin construction
11. **VerticalIntegration** - Sen-Witten prescription
12. **Berezin integration** over supermoduli

---

## Notes

### Well-Developed Parts
- **SuperRiemannSurface structure** - Clean bundled definition with body, genus, spin structure
- **LocalHoloSuperDiff** - Proper grading constraints and invertibility conditions
- **LocalSuperconformalMap** - Correct structural constraint r = g·h and integrability
- **OSp12** - Proper SL(2) determinant condition and basic group structure
- **Spin structure correspondence** - Well-documented relationship to superconformal

### Key Dependencies
- **RiemannRoch.lean** - For cohomology dimension computations
- **Supermanifolds.lean** - For NilpotentFiltration and obstruction theory
- **BerezinIntegration.lean** - For supermoduli integration
- **GrassmannAlgebra** - For Λ.even, Λ.odd, and grading infrastructure

### Mathematical Notes
- The folder properly captures the non-trivial relationship between SRS and spin structures
- Donagi-Witten non-projectedness is correctly stated but proof requires deep cohomology
- Picture-changing formalism follows Wang-Yin's geometric interpretation
- The superconformal constraint η² = f' + ψψ' is correctly formulated

### Implementation Challenges
1. **Derivatives on Λ.evenCarrier** - Need Taylor expansion with nilpotent soul
2. **Coinductive holomorphic functions** - GrassmannValuedHolomorphic uses partial
3. **Chain rule for composition** - Requires careful grading and soul expansion
4. **Cohomology on M_g** - Needs GRR and intersection theory from Moduli.lean
