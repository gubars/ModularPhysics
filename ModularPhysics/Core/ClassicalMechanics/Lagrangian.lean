import ModularPhysics.Core.ClassicalMechanics.PhaseSpace
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ModularPhysics.Core.ClassicalMechanics

/-- Lagrangian function type: L(q, q̇, t) -/
abbrev Lagrangian (n : ℕ) := GeneralizedCoordinates n → GeneralizedVelocities n → ℝ → ℝ

/-- Kinetic energy T(q, q̇) -/
axiom kineticEnergy (n : ℕ) :
  GeneralizedCoordinates n → GeneralizedVelocities n → ℝ

/-- Potential energy V(q, t) -/
axiom potentialEnergy (n : ℕ) :
  GeneralizedCoordinates n → ℝ → ℝ

/-- Standard Lagrangian: L = T - V -/
def standardLagrangian {n : ℕ}
  (T : GeneralizedCoordinates n → GeneralizedVelocities n → ℝ)
  (V : GeneralizedCoordinates n → ℝ → ℝ) : Lagrangian n :=
  fun q v t => T q v - V q t

/-- Action functional S[q] = ∫_{t₁}^{t₂} L(q, q̇, t) dt -/
axiom action {n : ℕ} (L : Lagrangian n) :
  Trajectory n → ℝ → ℝ → ℝ

/-- Partial derivative ∂L/∂qᵢ -/
axiom partialL_q {n : ℕ}
  (L : Lagrangian n)
  (q : GeneralizedCoordinates n)
  (v : GeneralizedVelocities n)
  (t : ℝ)
  (i : Fin n) : ℝ

/-- Partial derivative ∂L/∂q̇ᵢ -/
axiom partialL_v {n : ℕ}
  (L : Lagrangian n)
  (q : GeneralizedCoordinates n)
  (v : GeneralizedVelocities n)
  (t : ℝ)
  (i : Fin n) : ℝ

/-- Euler-Lagrange equation for coordinate i:
    d/dt(∂L/∂q̇ᵢ) - ∂L/∂qᵢ = 0
-/
def satisfiesEulerLagrange {n : ℕ}
  (L : Lagrangian n)
  (q : Trajectory n)
  (i : Fin n) : Prop :=
  ∀ t, deriv (fun s => partialL_v L (q s) (fun j => trajectoryDerivative q s j) s i) t =
       partialL_q L (q t) (fun j => trajectoryDerivative q t j) t i

/-- System satisfies all Euler-Lagrange equations -/
def satisfiesAllEulerLagrange {n : ℕ}
  (L : Lagrangian n)
  (q : Trajectory n) : Prop :=
  ∀ i, satisfiesEulerLagrange L q i

/-- Principle of stationary action (Hamilton's principle) -/
axiom principle_of_stationary_action {n : ℕ}
  (L : Lagrangian n)
  (q : Trajectory n)
  (t₁ t₂ : ℝ) :
  satisfiesAllEulerLagrange L q ↔
  (∀ (δq : Trajectory n),
    (δq t₁ = fun _ => 0) → (δq t₂ = fun _ => 0) →
    deriv (fun ε => action L (fun t i => q t i + ε * δq t i) t₁ t₂) 0 = 0)

/-- Generalized force Qᵢ (non-conservative) -/
axiom generalizedForce (n : ℕ) :
  GeneralizedCoordinates n → ℝ → Fin n → ℝ

/-- Euler-Lagrange with external forces:
    d/dt(∂L/∂q̇ᵢ) - ∂L/∂qᵢ = Qᵢ
-/
def satisfiesEulerLagrangeWithForces {n : ℕ}
  (L : Lagrangian n)
  (Q : GeneralizedCoordinates n → ℝ → Fin n → ℝ)
  (q : Trajectory n)
  (i : Fin n) : Prop :=
  ∀ t, deriv (fun s => partialL_v L (q s) (fun j => trajectoryDerivative q s j) s i) t =
       partialL_q L (q t) (fun j => trajectoryDerivative q t j) t i + Q (q t) t i

/-- Cyclic (ignorable) coordinate: ∂L/∂qᵢ = 0 -/
def isCyclicCoordinate {n : ℕ}
  (L : Lagrangian n)
  (i : Fin n) : Prop :=
  ∀ q v t, partialL_q L q v t i = 0

/-- Conserved momentum for cyclic coordinate -/
axiom cyclic_conserved_momentum {n : ℕ}
  (L : Lagrangian n)
  (q : Trajectory n)
  (i : Fin n)
  (h_cyclic : isCyclicCoordinate L i)
  (h_el : satisfiesAllEulerLagrange L q) :
  ∀ t₁ t₂, partialL_v L (q t₁) (fun j => trajectoryDerivative q t₁ j) t₁ i =
           partialL_v L (q t₂) (fun j => trajectoryDerivative q t₂ j) t₂ i

end ModularPhysics.Core.ClassicalMechanics
