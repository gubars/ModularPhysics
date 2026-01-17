import Mathlib.Data.Real.Basic

namespace ModularPhysics.Core.SpaceTime

/-- Spacetime dimension (always 4) -/
def spacetimeDim : ℕ := 4

/-- A point (event) in spacetime -/
abbrev SpaceTimePoint := Fin 4 → ℝ

/-- Time coordinate (in some coordinate system) -/
def time (x : SpaceTimePoint) : ℝ := x 0

/-- Spatial coordinates (in some coordinate system) -/
def spatial (x : SpaceTimePoint) : Fin 3 → ℝ := fun i => x i.succ

end ModularPhysics.Core.SpaceTime
