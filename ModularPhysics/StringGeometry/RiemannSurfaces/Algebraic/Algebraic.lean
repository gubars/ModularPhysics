import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.Divisors
import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.Moduli
import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.Cohomology.Sheaves
import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.Cohomology.Basic
import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.Cohomology.ExactSequence
import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.Cohomology.SerreDuality
import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.RiemannRoch
import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.FunctionField

/-!
# Algebraic Theory of Riemann Surfaces

This module collects the algebraic geometry aspects of Riemann surface theory:

- Divisors and line bundles
- Function fields and algebraic meromorphic functions
- Sheaf cohomology and Riemann-Roch theorem
- Moduli stacks and the Deligne-Mumford compactification

For theta functions and Abel-Jacobi map, see `Analytic/` folder
(these use analytic constructions like integration and series).

These tools are essential for:
1. The Riemann-Roch theorem
2. Understanding M_g as an algebraic variety/stack
-/
