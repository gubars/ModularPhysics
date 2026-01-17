import ModularPhysics.Core.Quantum
import ModularPhysics.Core.QuantumInformation.PartialTrace

namespace ModularPhysics.Core.QuantumInformation

open Quantum

/-- Quantum channel (CPTP map) -/
axiom QuantumChannel (H1 H2 : Type _) [QuantumStateSpace H1] [QuantumStateSpace H2] : Type _

/-- Apply quantum channel -/
axiom applyChannel {H1 H2 : Type _} [QuantumStateSpace H1] [QuantumStateSpace H2] :
  QuantumChannel H1 H2 → DensityOperator H1 → DensityOperator H2

/-- Identity channel -/
axiom identityChannel {H : Type _} [QuantumStateSpace H] : QuantumChannel H H

/-- Composition of channels -/
axiom composeChannels {H1 H2 H3 : Type _}
  [QuantumStateSpace H1] [QuantumStateSpace H2] [QuantumStateSpace H3] :
  QuantumChannel H2 H3 → QuantumChannel H1 H2 → QuantumChannel H1 H3

/-- Partial trace is a quantum channel -/
axiom partialTrace_is_channel {H1 H2 : Type _} [QuantumStateSpace H1] [QuantumStateSpace H2] :
  QuantumChannel (TensorProduct H1 H2) H1

/-- Maximally mixed state -/
axiom maximallyMixed {H : Type _} [QuantumStateSpace H] (dim : ℕ) : DensityOperator H

/-- Completely dephased state -/
axiom dephase {H : Type _} [QuantumStateSpace H] : DensityOperator H → DensityOperator H

end ModularPhysics.Core.QuantumInformation
