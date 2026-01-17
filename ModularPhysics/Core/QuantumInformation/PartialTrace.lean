import ModularPhysics.Core.Quantum

namespace ModularPhysics.Core.QuantumInformation

open Quantum

/-- Partial trace over second subsystem -/
axiom partialTrace2 {H1 H2 : Type _} [QuantumStateSpace H1] [QuantumStateSpace H2] :
  DensityOperator (TensorProduct H1 H2) → DensityOperator H1

/-- Partial trace over first subsystem -/
axiom partialTrace1 {H1 H2 : Type _} [QuantumStateSpace H1] [QuantumStateSpace H2] :
  DensityOperator (TensorProduct H1 H2) → DensityOperator H2

end ModularPhysics.Core.QuantumInformation
