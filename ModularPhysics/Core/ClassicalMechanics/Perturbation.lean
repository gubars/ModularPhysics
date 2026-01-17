import ModularPhysics.Core.ClassicalMechanics.Integrable

namespace ModularPhysics.Core.ClassicalMechanics

/-- Perturbed Hamiltonian H = H₀ + εH₁ -/
noncomputable def perturbedHamiltonian {n : ℕ}
  (H₀ : PhaseSpace n → ℝ)
  (H₁ : PhaseSpace n → ℝ)
  (ε : ℝ) : PhaseSpace n → ℝ :=
  fun x => H₀ x + ε * H₁ x

/-- Canonical perturbation theory to given order -/
axiom canonicalPerturbationTheory {n : ℕ}
  (H₀ H₁ : PhaseSpace n → ℝ)
  (order : ℕ) :
  PhaseSpace n → ℝ

end ModularPhysics.Core.ClassicalMechanics
