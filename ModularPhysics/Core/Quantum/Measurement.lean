import ModularPhysics.Core.Quantum.Basic

namespace ModularPhysics.Core.Quantum

/-- Probability (Born rule) -/
noncomputable def bornRule {H : Type _} [QuantumStateSpace H]
    (ψ φ : PureState H) : ℝ :=
  let z := innerProduct ψ.vec φ.vec
  z.re ^ 2 + z.im ^ 2

/-- Two states are orthogonal -/
def orthogonal {H : Type _} [QuantumStateSpace H] (ψ φ : H) : Prop :=
  innerProduct ψ φ = 0

/-- Orthogonal basis states -/
axiom ket0_ket1_orthogonal : orthogonal ket0 ket1

/-- Orthogonal states have zero probability -/
theorem orthogonal_zero_prob {H : Type _} [QuantumStateSpace H]
    (ψ φ : PureState H)
    (h : orthogonal ψ.vec φ.vec) :
    bornRule ψ φ = 0 := by
  unfold bornRule orthogonal innerProduct at *
  simp [h]

end ModularPhysics.Core.Quantum
