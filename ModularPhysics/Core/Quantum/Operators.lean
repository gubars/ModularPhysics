import ModularPhysics.Core.Quantum.Basic

namespace ModularPhysics.Core.Quantum

/-- Density operator for mixed states -/
axiom DensityOperator (H : Type _) [QuantumStateSpace H] : Type _

/-- Convert pure state to density operator -/
axiom pureToDensity {H : Type _} [QuantumStateSpace H] : PureState H → DensityOperator H

/-- Unitary evolution operator -/
axiom UnitaryOp (H : Type _) [QuantumStateSpace H] : Type _

/-- Time evolution is unitary -/
axiom timeEvolution {H : Type _} [QuantumStateSpace H] : ℝ → UnitaryOp H

/-- Apply unitary operator -/
axiom applyUnitary {H : Type _} [QuantumStateSpace H] : UnitaryOp H → H → H

end ModularPhysics.Core.Quantum
