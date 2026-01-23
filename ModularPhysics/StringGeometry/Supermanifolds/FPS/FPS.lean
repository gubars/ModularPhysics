/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license.
-/
import ModularPhysics.StringGeometry.Supermanifolds.FPS.Basic
import ModularPhysics.StringGeometry.Supermanifolds.FPS.Convergence
import ModularPhysics.StringGeometry.Supermanifolds.FPS.Composition
import ModularPhysics.StringGeometry.Supermanifolds.FPS.LogExp

/-!
# Formal Power Series Theory

This module provides infrastructure for formal power series over commutative rings,
following the treatment in the Waterloo C&O 430 notes (Section 7).

## Contents

* `FPS.Basic` - Ring structure and invertibility (Proposition 7.5)
* `FPS.Convergence` - Convergence of FPS sequences (Definition 7.10)
* `FPS.Composition` - Composition conditions (Propositions 7.15, 7.16)
* `FPS.LogExp` - Logarithmic and exponential series, and the key identity
                 exp(log(1-x)) = 1-x (Exercise 12d)

## Mathematical Background

The ring R[[x]] of formal power series has elements f(x) = Σₙ aₙxⁿ.
Key results include:

1. **Invertibility** (Prop 7.5): f(x) is invertible iff a₀ is invertible
2. **Convergence** (Def 7.10): Sequences converge when coefficients are eventually constant
3. **Composition** (Prop 7.15): f(g(x)) is well-defined when I(g) > 0
4. **Compositional Inverse** (Prop 7.16): Exists iff I(f) = 1
5. **Exp-Log Identity** (Ex 12d): exp(log(1-x)) = 1-x

## Application to Nilpotent Elements

For nilpotent x with x^{N+1} = 0, the infinite series truncate:
- log(1-x) = -x - x²/2 - ⋯ - x^N/N (finite sum)
- exp(L) = 1 + L + L²/2! + ⋯ (truncates when L is nilpotent)

The identity exp(log(1-x)) = 1-x becomes a polynomial identity
that can be verified algebraically.

## References

* Waterloo C&O 430 notes, Section 7: Formal Power Series
* Waterloo C&O 430 notes, Section 8: The Lagrange Implicit Function Theorem
-/
