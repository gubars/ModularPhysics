/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.vNA.Spectral.CayleyTransform
import ModularPhysics.RigorousQFT.vNA.Spectral.FunctionalCalculusFromCFC

/-!
# Spectral Theory Module (vNA/Spectral/)

This module re-exports the spectral theory infrastructure.
Note: This is separate from `vNA/Unbounded/Spectral.lean` which contains
the main `SpectralMeasure` structure and theorems. This folder contains
supporting infrastructure for the Cayley transform approach.

1. **CayleyTransform** - The bijection between unbounded self-adjoint operators and
   unitary operators. Key definitions:
   - `CayleyTransform` - U = (T-i)(T+i)⁻¹
   - `cayleyMap` - The map λ ↦ (λ-i)/(λ+i) from ℝ to S¹

2. **FunctionalCalculusFromCFC** - Connection to Mathlib's continuous functional
   calculus infrastructure. Key definitions:
   - `UnboundedCFC` - f(T) via Cayley transform
   - `spectralProjection` - P(E) for Borel sets E

## Mathematical Background

The spectral theorem for unbounded self-adjoint operators states that every
self-adjoint operator T has a unique spectral decomposition T = ∫ λ dP(λ)
where P is a projection-valued measure.

Our approach uses:
1. The Cayley transform to reduce to bounded (unitary) operators
2. Mathlib's CFC infrastructure for bounded normal operators
3. Pullback via the inverse Cayley map

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I", Chapter VIII
* Mathlib's Analysis.CStarAlgebra.ContinuousFunctionalCalculus
-/
