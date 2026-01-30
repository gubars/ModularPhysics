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
- `SuperDomainAlgebra.lean`: Ring/Algebra instances for SuperDomainFunction (NEW)

### Sheaf and Geometry Files
- `Sheaves/SuperSheafBasic.lean`: Structure sheaf of super domains, SuperSection
- `Supermanifolds.lean`: Main supermanifold definitions, charts, transitions

### Integration and Helpers
- `BerezinIntegration.lean`: Berezin integral and integration theory
- `Helpers/SuperMatrix.lean`: Super matrices and Berezinian computation
- `Helpers/OddDerivations.lean`: Odd derivations for super Riemann surfaces

## Completed Work

- [x] SuperAlgebra with parity, even/odd subspaces
- [x] SuperCommutative class with supercommutation property
- [x] SuperDomainFunction with coefficients indexed by Finset (Fin q)
- [x] reorderSign and inversions counting for Grassmann multiplication
- [x] **supercommutative' theorem** - Koszul sign rule for homogeneous elements
- [x] **mul_assoc'** - Associativity of super multiplication
- [x] Ring and Algebra instances for SuperDomainFunction
- [x] SuperMatrix with block structure (A, B; C, D)
- [x] Berezinian computation using Schur complement

## TODO

- [ ] Define SuperMap with Grassmann-valued coefficients for transition maps
- [ ] Connect to Mathlib's ExteriorAlgebra for ∧(ℝ^q) structure
- [ ] Implement proper sheaf gluing conditions using Mathlib's TopCat.Sheaf
- [ ] Prove stalks are local superrings
- [ ] Define supermanifold as locally super-ringed space
- [ ] Prove partialEven derivative is smooth
- [ ] Prove partialOdd satisfies graded Leibniz rule
- [ ] Fill in SuperChart and SuperTransition placeholders

## References

1. Witten, E. "Notes On Supermanifolds And Integration" (arXiv:1209.2199)
2. Deligne, P., Morgan, J. "Notes on Supersymmetry" (in Quantum Fields and Strings)
3. Manin, "Gauge Field Theory and Complex Geometry"
4. Varadarajan, "Supersymmetry for Mathematicians"
