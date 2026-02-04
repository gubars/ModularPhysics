# Supermanifold Theory - Design Notes

## Key Distinction: Fermionic Coordinates vs Grassmann Algebra Coefficients

### The Local Model ℝ^{p|q}

For a super domain ℝ^{p|q}, there are **q fermionic coordinates** θ₁,...,θq.
The structure sheaf assigns to each open U ⊆ ℝ^p:

```
O(U) = C^∞(U, ℝ) ⊗_ℝ ∧(ℝ^q)
```

Sections have the form:
```
f(x,θ) = Σ_I f_I(x) θ^I
```
where:
- I ranges over subsets of {1,...,q}
- f_I : U → ℝ are smooth **ℝ-valued** coefficient functions
- θ^I = θ^{i₁} ∧ ... ∧ θ^{i_k} for I = {i₁ < ... < i_k}

**In the local model, coefficients are in ℝ**, not in a Grassmann algebra.

### Transition Maps and Grassmann Algebra Coefficients

When gluing local models to form a supermanifold, transition maps
```
φ_αβ : U_α ∩ U_β → ℝ^{p|q}
```
have the form:
```
x'_i = f^i_0(x) + θ^j f^i_j(x) + θ^j θ^k f^i_{jk}(x) + ...
θ'_s = ψ^s_j(x) θ^j + ψ^s_{jk}(x) θ^j θ^k + ...
```

For a **single supermanifold** (not a family):
- The coefficients f^i_I, ψ^s_I are still ℝ-valued

For **families of supermanifolds** (e.g., parameterized by odd moduli η₁,...,η_s):
- The coefficients can be **Grassmann algebra-valued** (involving η's)
- This is essential for super Riemann surfaces and supermoduli spaces

### Super Riemann Surfaces

As noted in Witten's "Notes On Supermanifolds And Integration" (arXiv:1209.2199):

> "Though M depends on η₁...ηs, it does not have a reduced space that depends on
> those parameters. The reason is that since the gluing functions ψ^i_αβ can depend
> on the η's, we will in general get gluing laws such as θ_α = θ_β + η and we cannot
> consistently set the θ's to zero unless we also set the η's to zero."

This is why:
- Supermoduli space of super Riemann surfaces involves Grassmann-valued transition maps
- There is no elementary map from supermoduli space to ordinary moduli space
- The Grassmann algebra for coefficients is **separate** from the fermionic coordinates

### Summary

| Context | Fermionic coords | Coefficient algebra |
|---------|-----------------|---------------------|
| Local model ℝ^{p|q} | θ₁,...,θq | ℝ |
| Single supermanifold | θ₁,...,θq | ℝ |
| Family of supermanifolds | θ₁,...,θq | Grassmann algebra (involving η's) |
| Supermoduli space | θ₁,...,θq (on fibers) | Full Grassmann algebra |

## File Structure

### Core Algebraic Files
- `Superalgebra.lean`: Basic ℤ/2-graded algebra structure, parity, GrassmannAlgebra
- `SuperRingCat.lean`: Bundled category of supercommutative algebras
- `SuperDomainAlgebra.lean`: Ring/Algebra instances for SuperDomainFunction
- `SuperJacobian.lean`: Super Jacobian matrices for coordinate transformations

### Sheaf and Geometry Files
- `Sheaves/SuperSheafBasic.lean`: Structure sheaf of super domains, SuperSection
- `Supermanifolds.lean`: Main supermanifold definitions, charts, transitions, Berezin integration axioms

### Integration Theory
- `BerezinIntegration.lean`: Berezin integral, partition of unity, global integration
  - Imports chain rule infrastructure from Helpers/SuperChainRule.lean

### Helper Infrastructure
- `Helpers/SuperMatrix.lean`: Super matrices with ℤ/2-grading, multiplication
- `Helpers/Berezinian.lean`: Berezinian (superdeterminant) computation
- `Helpers/BerezinianMul.lean`: Berezinian multiplicativity theorem (2900+ lines)
- `Helpers/FiniteGrassmann.lean`: Finite Grassmann algebra Λ_q with Ring instance
- `Helpers/SuperChainRule.lean`: Chain rule infrastructure for Berezinian cocycle
- `Helpers/PartialOddLeibniz.lean`: Sign lemmas for graded Leibniz rule
- `PartialOddDerivation.lean`: Odd derivations satisfy graded Leibniz rule

## Completed Work

### Algebraic Foundations
- [x] SuperAlgebra with parity, even/odd subspaces
- [x] SuperCommutative class with supercommutation property
- [x] SuperDomainFunction with coefficients indexed by Finset (Fin q)
- [x] reorderSign and inversions counting for Grassmann multiplication
- [x] **supercommutative' theorem** - Koszul sign rule for homogeneous elements
- [x] **mul_assoc'** - Associativity of super multiplication
- [x] Ring and Algebra instances for SuperDomainFunction
- [x] FiniteGrassmannCarrier with Field instance (for q generators)
- [x] **finiteGrassmannAlgebra_superCommutative** - SuperCommutative instance

### Super Matrices and Berezinian
- [x] SuperMatrix with block structure (A, B; C, D) and proper ℤ/2-grading
- [x] Berezinian computation using Schur complement: Ber(M) = det(A - BD⁻¹C) / det(D)
- [x] **SuperMatrix.ber_mul** - Berezinian multiplicativity (2900+ line proof)
- [x] **SuperMatrix.ber_congr** - Congruence lemma for proof transport

### Super Jacobian and Coordinate Transformations
- [x] SuperJacobian structure with proper block parities
- [x] SuperJacobian.toSuperMatrixAt - Evaluation at a point
- [x] SuperJacobian.berezinianAt - Berezinian at a point
- [x] SuperTransition.toSuperJacobian - Jacobian from coordinate transition

### Chain Rule and Cocycle Conditions
- [x] **body_jacobian_cocycle** - Body Jacobians satisfy J_αγ = J_βγ · J_αβ
- [x] **berezinian_cocycle_from_chain_rule** - Full Berezinian cocycle theorem
- [x] ChainRuleHypotheses - Structure packaging chain rule equations
- [x] FullSuperCocycle - Composition condition using SuperDomainFunction.compose

### Derivatives and Partial Derivatives
- [x] partialEven derivative is smooth (ContDiff.fderiv_right)
- [x] **partialOdd_odd_derivation'** - Graded Leibniz rule for odd derivatives
- [x] partialEven_compBody_chain_rule - Chain rule for body composition

### Integration Theory
- [x] Berezin integral as top θ-coefficient extraction
- [x] berezin_fubini - Integration commutes with body integration
- [x] GlobalIntegralForm structure with cocycle condition
- [x] SuperPartitionOfUnity with proper sum_eq_one, support conditions

## In Progress / Remaining

### Integration Theorems (documented proofs, technical sorrys)
- [ ] partition_of_unity_exists - Needs connection to Mathlib infrastructure
- [ ] globalBerezinIntegral_independent - Proof outline documented
- [ ] berezin_change_of_variables_formula - Needs IntegralForm.pullback

### Chain Rule Infrastructure
- [ ] SuperDomainFunction.compose - Full coefficient computation (simplified placeholder)
- [ ] full_cocycle_implies_chain_rule - Derive chain rule from composition (sorrys)

### Future Work
- [ ] Connect to Mathlib's ExteriorAlgebra for ∧(ℝ^q) structure
- [ ] Super Stokes theorem
- [ ] Batchelor theorem (classification of supermanifolds)

## References

1. Witten, E. "Notes On Supermanifolds And Integration" (arXiv:1209.2199)
2. Deligne, P., Morgan, J. "Notes on Supersymmetry" (in Quantum Fields and Strings)
3. Manin, "Gauge Field Theory and Complex Geometry"
4. Varadarajan, "Supersymmetry for Mathematicians"
