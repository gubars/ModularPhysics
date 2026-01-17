import ModularPhysics.Core.Quantum
import ModularPhysics.Core.QuantumInformation.Entropy

namespace ModularPhysics.Core.QuantumInformation

open Quantum

/-- Mutual information -/
axiom mutualInformation {H1 H2 : Type _}
  [QuantumStateSpace H1] [QuantumStateSpace H2] :
  DensityOperator (TensorProduct H1 H2) → ℝ

/-- Mutual information is non-negative -/
axiom mutual_information_nonneg {H1 H2 : Type _}
  [QuantumStateSpace H1] [QuantumStateSpace H2]
  (rho : DensityOperator (TensorProduct H1 H2)) :
  mutualInformation rho ≥ 0

/-- Conditional mutual information -/
axiom conditionalMutualInformation {HA HB HC : Type _}
  [QuantumStateSpace HA] [QuantumStateSpace HB] [QuantumStateSpace HC] :
  DensityOperator (TensorProduct HA (TensorProduct HB HC)) → ℝ

/-- Quantum CMI is non-negative (consequence of SSA) -/
axiom quantum_cmi_nonneg {HA HB HC : Type _}
  [QuantumStateSpace HA] [QuantumStateSpace HB] [QuantumStateSpace HC]
  (rho : DensityOperator (TensorProduct HA (TensorProduct HB HC))) :
  conditionalMutualInformation rho ≥ 0

/-- Monogamy inequality -/
axiom monogamy_inequality {HA HB HC : Type _}
  [QuantumStateSpace HA] [QuantumStateSpace HB] [QuantumStateSpace HC]
  (I_AB I_AC I_BC : ℝ) :
  I_AB + I_AC ≥ I_BC

/-- Quantum discord -/
axiom quantumDiscord {H1 H2 : Type _}
  [QuantumStateSpace H1] [QuantumStateSpace H2] :
  DensityOperator (TensorProduct H1 H2) → ℝ

/-- Discord is non-negative -/
axiom discord_nonneg {H1 H2 : Type _} [QuantumStateSpace H1] [QuantumStateSpace H2]
  (rho : DensityOperator (TensorProduct H1 H2)) :
  quantumDiscord rho ≥ 0

/-- Discord bounded by mutual information -/
axiom discord_bound {H1 H2 : Type _} [QuantumStateSpace H1] [QuantumStateSpace H2]
  (rho : DensityOperator (TensorProduct H1 H2)) :
  quantumDiscord rho ≤ mutualInformation rho

/-- Quantum fidelity -/
axiom fidelity {H : Type _} [QuantumStateSpace H] :
  DensityOperator H → DensityOperator H → ℝ

/-- Fidelity bounds -/
axiom fidelity_bounds {H : Type _} [QuantumStateSpace H] (rho sigma : DensityOperator H) :
  0 ≤ fidelity rho sigma ∧ fidelity rho sigma ≤ 1

/-- Fidelity is symmetric -/
axiom fidelity_symmetric {H : Type _} [QuantumStateSpace H] (rho sigma : DensityOperator H) :
  fidelity rho sigma = fidelity sigma rho

/-- Pure state fidelity is amplitude squared -/
axiom pure_fidelity {H : Type _} [QuantumStateSpace H] (psi phi : PureState H) :
  fidelity (pureToDensity psi) (pureToDensity phi) = bornRule psi phi

/-- Uhlmann's theorem: fidelity achieved by purifications -/
axiom uhlmann_theorem {H : Type _} [QuantumStateSpace H] (rho sigma : DensityOperator H) :
  ∃ (psi phi : PureState (TensorProduct H H)),
    fidelity rho sigma = bornRule psi phi

/-- Trace distance -/
axiom traceDistance {H : Type _} [QuantumStateSpace H] :
  DensityOperator H → DensityOperator H → ℝ

/-- Trace distance bounds -/
axiom trace_distance_bounds {H : Type _} [QuantumStateSpace H] (rho sigma : DensityOperator H) :
  0 ≤ traceDistance rho sigma ∧ traceDistance rho sigma ≤ 1

/-- Trace distance is a metric -/
axiom trace_distance_triangle {H : Type _} [QuantumStateSpace H]
  (rho sigma tau : DensityOperator H) :
  traceDistance rho tau ≤ traceDistance rho sigma + traceDistance sigma tau

/-- Fuchs-van de Graaf inequalities -/
axiom fuchs_van_de_graaf_lower {H : Type _} [QuantumStateSpace H] (rho sigma : DensityOperator H) :
  1 - fidelity rho sigma ≤ traceDistance rho sigma

axiom fuchs_van_de_graaf_upper {H : Type _} [QuantumStateSpace H] (rho sigma : DensityOperator H) :
  traceDistance rho sigma ≤ Real.sqrt (1 - (fidelity rho sigma)^2)

end ModularPhysics.Core.QuantumInformation
