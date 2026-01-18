import ModularPhysics.Core.Quantum
import ModularPhysics.Core.QuantumInformation.Correlations

namespace ModularPhysics.Core.QuantumInformation

open Quantum QuantumInformation

/-- A state is separable (not entangled) -/
axiom Separable {H1 H2 : Type _} [QuantumStateSpace H1] [QuantumStateSpace H2] :
  DensityOperator (TensorProduct H1 H2) → Prop

/-- Product states are separable -/
axiom product_separable {H1 H2 : Type _} [QuantumStateSpace H1] [QuantumStateSpace H2] :
  ∃ (rho : DensityOperator (TensorProduct H1 H2)), Separable rho

/-- Separable states can have nonzero discord -/
axiom separable_discord_nonzero :
  ∃ (rho : DensityOperator (TensorProduct Qubit Qubit)),
    Separable rho ∧ quantumDiscord rho > 0

/-- Entanglement of formation -/
axiom entanglementOfFormation {H1 H2 : Type _}
  [QuantumStateSpace H1] [QuantumStateSpace H2] :
  DensityOperator (TensorProduct H1 H2) → ℝ

/-- Separable states have zero EoF -/
axiom separable_zero_entanglement {H1 H2 : Type _}
  [QuantumStateSpace H1] [QuantumStateSpace H2]
  (rho : DensityOperator (TensorProduct H1 H2))
  (h : Separable rho) :
  entanglementOfFormation rho = 0

/-- Entanglement of distillation -/
axiom entanglementOfDistillation {H1 H2 : Type _}
  [QuantumStateSpace H1] [QuantumStateSpace H2] :
  DensityOperator (TensorProduct H1 H2) → ℝ

/-- Distillable entanglement is less than EoF.

    This is a THEOREM (provable from entanglement theory), not an axiom itself. -/
theorem distillation_less_than_formation {H1 H2 : Type _}
  [QuantumStateSpace H1] [QuantumStateSpace H2]
  (rho : DensityOperator (TensorProduct H1 H2)) :
  entanglementOfDistillation rho ≤ entanglementOfFormation rho := by
  sorry

/-- Bound entangled states exist (undistillable but entangled) -/
axiom bound_entanglement_exists :
  ∃ (rho : DensityOperator (TensorProduct Qubit Qubit)),
    entanglementOfFormation rho > 0 ∧ entanglementOfDistillation rho = 0

/-- Squashed entanglement -/
axiom squashedEntanglement {H1 H2 : Type _}
  [QuantumStateSpace H1] [QuantumStateSpace H2] :
  DensityOperator (TensorProduct H1 H2) → ℝ

/-- Logarithmic negativity -/
axiom logarithmicNegativity {H1 H2 : Type _}
  [QuantumStateSpace H1] [QuantumStateSpace H2] :
  DensityOperator (TensorProduct H1 H2) → ℝ

/-- LOCC operations -/
axiom LOCC {H1 H2 : Type _} [QuantumStateSpace H1] [QuantumStateSpace H2] : Type _

/-- Apply LOCC operation -/
axiom applyLOCC {H1 H2 : Type _} [QuantumStateSpace H1] [QuantumStateSpace H2] :
  @LOCC H1 H2 _ _ → DensityOperator (TensorProduct H1 H2) → DensityOperator (TensorProduct H1 H2)

/-- LOCC cannot increase entanglement (monotonicity).

    This is a THEOREM (provable from LOCC theory), not an axiom itself. -/
theorem locc_monotone {H1 H2 : Type _} [QuantumStateSpace H1] [QuantumStateSpace H2]
  (rho : DensityOperator (TensorProduct H1 H2))
  (locc_op : @LOCC H1 H2 _ _) :
  entanglementOfFormation (@applyLOCC H1 H2 _ _ locc_op rho) ≤ entanglementOfFormation rho := by
  sorry

/-- LOCC cannot create entanglement from separable states.

    This is a THEOREM (provable from LOCC theory), not an axiom itself. -/
theorem locc_preserves_separability {H1 H2 : Type _} [QuantumStateSpace H1] [QuantumStateSpace H2]
  (rho : DensityOperator (TensorProduct H1 H2))
  (h : Separable rho)
  (locc_op : @LOCC H1 H2 _ _) :
  Separable (@applyLOCC H1 H2 _ _ locc_op rho) := by
  sorry

end ModularPhysics.Core.QuantumInformation
