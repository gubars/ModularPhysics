import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

namespace ModularPhysics.Core.ClassicalMechanics

/-- Configuration space for n degrees of freedom -/
def ConfigurationSpace (n : ℕ) := Fin n → ℝ

/-- Generalized coordinates q -/
abbrev GeneralizedCoordinates (n : ℕ) := ConfigurationSpace n

/-- Generalized velocities q̇ -/
abbrev GeneralizedVelocities (n : ℕ) := Fin n → ℝ

/-- Generalized momenta p -/
abbrev GeneralizedMomenta (n : ℕ) := Fin n → ℝ

/-- Phase space (q, p) - THE fundamental structure of classical mechanics -/
def PhaseSpace (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ)

/-- State space (q, q̇) - for Lagrangian formulation -/
def StateSpace (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ)

/-- Position component of phase space point -/
def position {n : ℕ} (x : PhaseSpace n) : GeneralizedCoordinates n := x.1

/-- Momentum component of phase space point -/
def momentum {n : ℕ} (x : PhaseSpace n) : GeneralizedMomenta n := x.2

/-- Trajectory in configuration space -/
def Trajectory (n : ℕ) := ℝ → GeneralizedCoordinates n

/-- Trajectory in phase space -/
def PhaseSpaceTrajectory (n : ℕ) := ℝ → PhaseSpace n

/-- Time derivative of a trajectory -/
axiom trajectoryDerivative {n : ℕ}
  (q : Trajectory n) (t : ℝ) (i : Fin n) : ℝ

end ModularPhysics.Core.ClassicalMechanics
