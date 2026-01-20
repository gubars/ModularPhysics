import ModularPhysics.StringGeometry.Supermanifolds.Helpers.GradedRings
import ModularPhysics.StringGeometry.Supermanifolds.Helpers.Berezinian
import ModularPhysics.StringGeometry.Supermanifolds.Helpers.OddDerivations
import ModularPhysics.StringGeometry.Supermanifolds.Helpers.SchurComplement

/-!
# Supermanifold Helper Lemmas

This module collects foundational lemmas for supermanifold theory:

## Files

* `GradedRings` - Lemmas for ℤ/2-graded structures and Koszul signs
* `Berezinian` - Superdeterminant (Berezinian) properties
* `OddDerivations` - Odd derivations and the key identity D_θ² = ∂/∂z
* `SchurComplement` - Schur complement identities for block matrices

## Key results for eliminating sorrys

These helpers are designed to fill gaps in the main Superalgebra.lean file:

1. **Type class diamond in odd_anticomm**: Use `neg_one_zsmul_eq_neg` from GradedRings
   to convert (-1 : ℤ) • x to -x in any ring.

2. **odd_sq_zero**: Use `eq_neg_self_implies_zero` with the anticommutativity result.

3. **supertrace_supercommutator**: Follows from cyclicity of trace on blocks.

4. **Berezinian multiplicativity**: The key property for integration.

5. **D_θ² = ∂/∂z**: Fundamental for super Riemann surfaces.

## Usage

Import this module to get all helper lemmas:
```lean
import ModularPhysics.StringGeometry.Supermanifolds.Helpers.Helpers
```
-/
