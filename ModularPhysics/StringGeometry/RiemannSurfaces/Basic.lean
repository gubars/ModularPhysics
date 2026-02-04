import ModularPhysics.StringGeometry.RiemannSurfaces.Analytic.Basic

/-!
# Riemann Surfaces - Common Entry Point

This file serves as the main entry point for Riemann surface theory, re-exporting
definitions from the specialized subfolders.

## Architecture

The formalization is organized into three perspectives:

- **Analytic/** - Complex manifolds, holomorphic functions, analytic meromorphic functions
- **Algebraic/** - Function fields, divisors, sheaf cohomology, Riemann-Roch
- **Combinatorial/** - Ribbon graphs, Penner/Kontsevich moduli theory

These are connected via **GAGA/** which shows that for compact Riemann surfaces,
the algebraic and analytic viewpoints are equivalent.

## What's in this file

This file re-exports the core definitions (RiemannSurface, CompactRiemannSurface)
from Analytic/Basic.lean.

## Specialized Content

For specific topics, import the appropriate submodule:

- **Divisors**: `Algebraic/Divisors.lean` (algebraic) or `Analytic/Divisors.lean` (analytic)
- **Line bundles**: `Algebraic/Cohomology/` or `Analytic/LineBundles.lean`
- **Riemann-Roch**: `Algebraic/RiemannRoch.lean` or `Analytic/RiemannRoch.lean`
- **Spin structures**: `Algebraic/Helpers/SpinStructures.lean`
- **Function fields**: `Algebraic/FunctionField.lean`

## References

* Farkas, Kra "Riemann Surfaces"
* Griffiths, Harris "Principles of Algebraic Geometry", Chapter 2
* Donaldson "Riemann Surfaces"
-/

namespace RiemannSurfaces

-- Re-export core definitions from Analytic
-- This allows downstream code to continue using RiemannSurfaces.RiemannSurface
export Analytic (ComplexManifold RiemannSurface CompactRiemannSurface
  complexManifold_complex ComplexPlane RiemannSphere genus0Surface genus0Surface_genus
  chartedSpace_onePoint complexManifold_onePoint)

end RiemannSurfaces
