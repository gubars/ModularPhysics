import ModularPhysics.Core.SpaceTime.Basic
import ModularPhysics.Core.Quantum

namespace ModularPhysics.Core.QFT.Wightman

open SpaceTime Quantum

/-- Schwartz space test function on d-dimensional Minkowski spacetime.
    These are smooth rapidly decreasing functions used to smear field operators. -/
axiom SchwartzFunction (d : ℕ) : Type _

/-- Smeared quantum field operator φ(f) = ∫ d^d x f(x) φ(x).
    The integral is over Minkowski spacetime with measure d^d x.
    This is a well-defined bounded operator on the Hilbert space. -/
axiom SmearedFieldOperator (H : Type _) [QuantumStateSpace H] (d : ℕ) : Type _

/-- Smearing a field with a test function gives an operator on H -/
axiom smear {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (field : SmearedFieldOperator H d)
  (f : SchwartzFunction d) : (H → H)

/-- Vacuum state |0⟩ -/
axiom vacuum {H : Type _} [QuantumStateSpace H] : H

/-- Vacuum is normalized: ⟨0|0⟩ = 1 -/
axiom vacuum_normalized {H : Type _} [QuantumStateSpace H] :
  ‖@vacuum H _‖ = 1

/-- Hermitian adjoint of smeared field operator -/
axiom fieldAdjoint {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : SmearedFieldOperator H d) : SmearedFieldOperator H d

/-- Adjoint of smeared field: φ(f)† = φ(f̄) where f̄ is complex conjugate -/
axiom adjoint_smearing {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : SmearedFieldOperator H d)
  (f : SchwartzFunction d) :
  ∀ ψ χ : H,
    innerProduct ψ (smear phi f χ) = innerProduct (smear (fieldAdjoint phi) f ψ) χ

/-- Reality condition: φ† = φ for Hermitian (real) scalar fields -/
axiom reality_condition {H : Type _} [QuantumStateSpace H] {d : ℕ}
  (phi : SmearedFieldOperator H d) :
  fieldAdjoint phi = phi

/-- Formal notation: φ(x) as operator-valued distribution.
    This is NOT a function but a distribution - only makes sense when integrated
    against test functions. W_n(x₁,...,xₙ) = ⟨0|φ(x₁)...φ(xₙ)|0⟩ are tempered distributions. -/
axiom FieldDistribution (H : Type _) [QuantumStateSpace H] (d : ℕ) : Type _

/-- The smeared field φ(f) corresponds to integrating the distribution φ(x) against f(x) -/
axiom distribution_to_smeared {H : Type _} [QuantumStateSpace H] {d : ℕ} :
  FieldDistribution H d → SmearedFieldOperator H d

end ModularPhysics.Core.QFT.Wightman
