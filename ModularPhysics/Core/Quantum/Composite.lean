import ModularPhysics.Core.Quantum.Basic

namespace ModularPhysics.Core.Quantum

/-- Tensor product of two quantum systems -/
axiom TensorProduct (H₁ H₂ : Type _) [QuantumStateSpace H₁] [QuantumStateSpace H₂] : Type _

/-- Tensor product is a quantum state space -/
noncomputable instance {H₁ H₂ : Type _}
    [QuantumStateSpace H₁] [QuantumStateSpace H₂] :
    QuantumStateSpace (TensorProduct H₁ H₂) := by sorry

/-- Tensor product operation -/
axiom tensorProduct {H₁ H₂ : Type _} [QuantumStateSpace H₁] [QuantumStateSpace H₂] :
  H₁ → H₂ → TensorProduct H₁ H₂

notation:100 ψ " ⊗ " φ => tensorProduct ψ φ

/-- Bell state (maximally entangled state) -/
axiom bellState : TensorProduct Qubit Qubit

/-- Bell state has unit norm -/
axiom bellState_norm : ‖bellState‖ = 1

end ModularPhysics.Core.Quantum
