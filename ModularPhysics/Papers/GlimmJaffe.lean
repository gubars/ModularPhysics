/-
  Glimm-Jaffe Construction of φ⁴₂ Theory

  This module imports all components of the Glimm-Jaffe construction
  of 2D φ⁴ scalar field theory, following their book "Quantum Physics:
  A Functional Integral Point of View" (1987).

  The construction proves that 2D φ⁴ theory satisfies the Osterwalder-Schrader
  axioms, thereby establishing it as a well-defined quantum field theory.

  ## Structure

  The construction proceeds in stages:

  1. **Basic** - Foundational definitions (Euclidean space, parameters, etc.)

  2. **LatticeTheory** - Lattice approximation (Chapter 9.5-9.6)
     - Lattice Laplacian and covariance operators
     - Lattice action and measure
     - Stability of the action

  3. **CorrelationInequalities** - GKS bounds (Chapter 4, 10.2)
     - Griffiths inequalities
     - FKG inequality
     - Uniform bound |Sₙ| ≤ Cⁿ

  4. **ReflectionPositivity** - OS3 axiom (Chapter 10.4)
     - Reflection positivity for Gaussian measures
     - Reflection positivity for P(φ) measures
     - Multiple reflection bounds

  5. **InfiniteVolumeLimit** - Existence (Chapter 11)
     - Monotone convergence
     - Uniform upper bounds
     - Properties of the limit (OS0, OS2, OS3)

  6. **Regularity** - OS1 and main theorem (Chapter 12)
     - Integration by parts
     - Regularity bounds
     - Main theorem: φ⁴₂ satisfies OS axioms

  ## References

  - Glimm-Jaffe (1987) "Quantum Physics: A Functional Integral Point of View"
  - Osterwalder-Schrader (1973) "Axioms for Euclidean Green's Functions"
  - Osterwalder-Schrader (1975) "Axioms for Euclidean Green's Functions II"
-/

import ModularPhysics.Papers.GlimmJaffe.Basic
import ModularPhysics.Papers.GlimmJaffe.LatticeTheory
import ModularPhysics.Papers.GlimmJaffe.CorrelationInequalities
import ModularPhysics.Papers.GlimmJaffe.ReflectionPositivity
import ModularPhysics.Papers.GlimmJaffe.InfiniteVolumeLimit
import ModularPhysics.Papers.GlimmJaffe.Regularity
-- Detailed proof modules
import ModularPhysics.Papers.GlimmJaffe.Griffiths.Basic
import ModularPhysics.Papers.GlimmJaffe.ReflectionPositivity.GaussianRP
import ModularPhysics.Papers.GlimmJaffe.ClusterExpansion.Basic
import ModularPhysics.Papers.GlimmJaffe.Hypercontractivity.Basic
