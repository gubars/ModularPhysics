import ModularPhysics.StringGeometry.RiemannSurfaces.GAGA.Moduli.DualGraph
import ModularPhysics.StringGeometry.RiemannSurfaces.GAGA.Moduli.Boundary

/-!
# Algebraic Moduli Theory - Re-exports

This file re-exports the algebraic moduli theory developed in the Moduli/ subfolder.

## Structure

* **DualGraph.lean** - Proper combinatorial definition of dual graphs of nodal curves
  - `DualGraph` structure with vertices, edges, genus labels, self-loops
  - Stability conditions derived from graph structure
  - First Betti number and total genus

* **Boundary.lean** - Boundary divisor types for M̄_g
  - `BoundaryDivisorType` enumeration (Δ_0, Δ_i)
  - Theorems about one-node graphs

## What This Does NOT Include

Dimension formulas like "dim M_g = 3g - 3" are NOT defined here because:
- They should be PROVEN from deformation theory
- Deformation theory requires: tangent space = H¹(T_C), Serre duality, Riemann-Roch
- These are substantial pieces of infrastructure

## References

* Deligne, Mumford "The irreducibility of the space of curves of given genus"
* Harris, Morrison "Moduli of Curves"
-/

namespace RiemannSurfaces.Algebraic

-- All definitions are imported from submodules

end RiemannSurfaces.Algebraic
