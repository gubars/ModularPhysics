import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic

namespace ModularPhysics.Core.Quantum

set_option autoImplicit false

/-- A quantum state space (abstract Hilbert space) -/
class QuantumStateSpace (H : Type _) extends
  NormedAddCommGroup H,
  InnerProductSpace ℂ H,
  CompleteSpace H

/-- 2-dimensional complex Hilbert space (qubit) -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- n-dimensional complex Hilbert space -/
abbrev FiniteDimQuantum (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- Qubit is a quantum state space -/
noncomputable instance : QuantumStateSpace Qubit := {}

/-- Finite dimensional systems are quantum state spaces -/
noncomputable instance (n : ℕ) : QuantumStateSpace (FiniteDimQuantum n) := {}

/-- Pure state (normalized vector) -/
structure PureState (H : Type _) [QuantumStateSpace H] where
  vec : H
  normalized : ‖vec‖ = 1

/-- Inner product (probability amplitude) -/
noncomputable def innerProduct {H : Type _} [QuantumStateSpace H] (ψ φ : H) : ℂ :=
  @inner ℂ H _ ψ φ

/-- Superposition principle -/
noncomputable def superposition {H : Type _} [QuantumStateSpace H]
    (α β : ℂ) (ψ φ : H) : H :=
  α • ψ + β • φ

/-- Computational basis states -/
axiom ket0 : Qubit
axiom ket1 : Qubit
axiom ket0_normalized : ‖ket0‖ = 1
axiom ket1_normalized : ‖ket1‖ = 1

/-- Any qubit can be written as superposition of basis states -/
axiom qubit_decomposition : ∀ (ψ : Qubit),
  ∃ (α β : ℂ), ψ = superposition α β ket0 ket1

end ModularPhysics.Core.Quantum
