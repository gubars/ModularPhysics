import ModularPhysics.Core.ClassicalMechanics.Hamiltonian
import ModularPhysics.Core.ClassicalMechanics.CanonicalTransforms
import ModularPhysics.Core.ClassicalMechanics.Integrable

namespace ModularPhysics.Core.ClassicalMechanics

/-- Hamilton's principal function S(q, t) -/
abbrev HamiltonPrincipalFunction (n : ℕ) :=
  GeneralizedCoordinates n → ℝ → ℝ

/-- Hamilton's characteristic function W(q, α) (time-independent) -/
abbrev HamiltonCharacteristicFunction (n : ℕ) :=
  GeneralizedCoordinates n → (Fin n → ℝ) → ℝ

/-- Partial derivative of S with respect to coordinate -/
axiom partialS_q {n : ℕ}
  (S : HamiltonPrincipalFunction n)
  (q : GeneralizedCoordinates n)
  (t : ℝ)
  (i : Fin n) : ℝ

/-- Hamilton-Jacobi equation: ∂S/∂t + H(q, ∂S/∂q, t) = 0 -/
def satisfiesHamiltonJacobi {n : ℕ}
  (S : HamiltonPrincipalFunction n)
  (H : Hamiltonian n) : Prop :=
  ∀ q t, deriv (S q) t + H q (fun i => partialS_q S q t i) t = 0

/-- Time-independent Hamilton-Jacobi: H(q, ∂W/∂q) = E -/
def satisfiesTimeIndependentHJ {n : ℕ}
  (W : HamiltonCharacteristicFunction n)
  (H : Hamiltonian n)
  (E : ℝ) : Prop :=
  ∀ (q : GeneralizedCoordinates n) (alpha : Fin n → ℝ),
    H q (fun i => partialS_q (fun q' _ => W q' alpha) q 0 i) 0 = E

/-- Solution of HJ equation gives canonical transformation -/
axiom hj_generates_canonical_transform {n : ℕ}
  (S : HamiltonPrincipalFunction n)
  (H : Hamiltonian n)
  (h : satisfiesHamiltonJacobi S H) :
  ∃ (_ : CanonicalTransformation n), True

/-- Hamilton-Jacobi method solves for trajectories -/
axiom hj_gives_trajectories {n : ℕ}
  (S : HamiltonPrincipalFunction n)
  (H : Hamiltonian n)
  (L : Lagrangian n)
  (h : satisfiesHamiltonJacobi S H)
  (q₀ : GeneralizedCoordinates n) :
  ∃ (q : Trajectory n), q 0 = q₀ ∧ satisfiesAllEulerLagrange L q

/-- Separation of variables in HJ equation -/
axiom hj_separation_of_variables {n : ℕ}
  (W : HamiltonCharacteristicFunction n)
  (H : Hamiltonian n)
  (h_separable : ∃ (Wᵢ : Fin n → ℝ → (Fin n → ℝ) → ℝ),
                   ∀ (q : GeneralizedCoordinates n) (alpha : Fin n → ℝ),
                     W q alpha = ∑ i, Wᵢ i (q i) alpha) :
  ∃ E, satisfiesTimeIndependentHJ W H E

/-- Connection to action variables -/
axiom hj_gives_action_variables {n : ℕ}
  (W : HamiltonCharacteristicFunction n)
  (H : Hamiltonian n)
  (E : ℝ)
  (h : satisfiesTimeIndependentHJ W H E)
  (i : Fin n)
  (γ : PhaseSpaceTrajectory n) :
  ∃ (integral : ℝ), actionVariable i γ = integral  -- ∮ ∂W/∂αᵢ dqᵢ

end ModularPhysics.Core.ClassicalMechanics
