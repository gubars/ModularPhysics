/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.SPDE

/-!
# The Φ⁴ Model

The dynamic Φ⁴ model: ∂_t φ = Δφ - φ³ + ξ.
This is the stochastic quantization of scalar field theory.

## Main Definitions

* `Phi4Model` - The Φ⁴ model in d dimensions
* `Phi4_2` - The 2D Φ⁴ model (Da Prato-Debussche)
* `Phi4_3` - The 3D Φ⁴ model (Hairer 2014)

## References

* Hairer, "A theory of regularity structures" (Inventiones 2014)
* Da Prato, Debussche, "Strong solutions to the stochastic quantization equations"
* Mourrat, Weber, "The dynamic Φ⁴₃ model comes down from infinity"
-/

namespace SPDE.Examples

open MeasureTheory

/-! ## The Φ⁴ Model -/

/-- The Φ⁴ model: ∂_t φ = Δφ - m²φ - λφ³ + ξ
    This is the Langevin dynamics for ∫ (1/2)|∇φ|² + (m²/2)φ² + (λ/4)φ⁴ dx -/
structure Phi4Model (d : ℕ) where
  /-- The domain (usually torus 𝕋^d) -/
  domain : Set (Fin d → ℝ)
  /-- The mass parameter m² -/
  mass_squared : ℝ
  /-- The coupling constant λ (coefficient of φ⁴ in potential) -/
  coupling : ℝ
  /-- Positive coupling for stability -/
  coupling_pos : 0 < coupling

namespace Phi4Model

variable {d : ℕ}

/-- The subcritical dimension bound -/
def isSubcritical (_phi : Phi4Model d) : Prop := d < 4

/-- The critical dimension -/
def isCritical (_phi : Phi4Model d) : Prop := d = 4

/-- The supercritical dimension (not expected to be well-posed) -/
def isSupercritical (_phi : Phi4Model d) : Prop := d > 4

/-- Φ⁴ is subcritical in d < 4 -/
theorem subcritical_d_lt_4 (phi : Phi4Model d) (hd : d < 4) :
    phi.isSubcritical := hd

/-- The noise regularity: α = -(d+2)/2 -/
noncomputable def noiseRegularity (_phi : Phi4Model d) : ℝ := -((d : ℝ) + 2)/2

/-- The expected solution regularity: 1 - d/2 (before renormalization) -/
noncomputable def solutionRegularity (_phi : Phi4Model d) : ℝ := 1 - (d : ℝ)/2

/-- The scaling dimension of φ³ -/
noncomputable def cubicScalingDimension (phi : Phi4Model d) : ℝ := 3 * phi.solutionRegularity

/-- φ³ is a well-defined distribution if 3α > -d/2 (roughly d < 10/3) -/
def cubicWellDefined (phi : Phi4Model d) : Prop :=
  3 * phi.solutionRegularity > -(d : ℝ)/2

end Phi4Model

/-! ## Φ⁴ in 2D -/

/-- The 2D Φ⁴ model (solved by Da Prato-Debussche 2003) -/
structure Phi4_2 extends Phi4Model 2 where
  /-- 2D constraint -/
  dim_constraint : True := trivial

namespace Phi4_2

/-- In 2D, the cubic term is a well-defined distribution -/
theorem cubic_well_defined (_phi : Phi4_2) :
    _phi.toPhi4Model.cubicWellDefined := by
  simp [Phi4Model.cubicWellDefined, Phi4Model.solutionRegularity]

/-- The Da Prato-Debussche trick: write u = Z + v where Z solves linear SHE.
    This decomposition allows treating the singular terms :Z²:, :Z³: separately
    from the regular remainder v. -/
structure DaPratoDebussche (phi : Phi4_2) where
  /-- The Hölder regularity of the linear solution Z (α < 0 in 2D) -/
  linear_regularity : ℝ
  /-- Z has negative Hölder regularity in 2D -/
  linear_regularity_neg : linear_regularity < 0
  /-- The Hölder regularity of the remainder v (β > 0) -/
  remainder_regularity : ℝ
  /-- The remainder has positive regularity -/
  remainder_regularity_pos : remainder_regularity > 0
  /-- The regularity gain: v is more regular than Z -/
  regularity_gain : remainder_regularity > -linear_regularity
  /-- The Wick renormalization constant for :Z²:.
      In 2D, 𝔼[Z(x)²] is logarithmically divergent and :Z²: = Z² - 𝔼[Z²] -/
  wick_constant_2 : ℝ
  /-- The Wick renormalization constant for :Z³: -/
  wick_constant_3 : ℝ

/-- The invariant measure for Φ⁴₂ is characterized by the Euclidean QFT measure.
    This measure is formally dμ = (1/Z) exp(-∫ (1/2)|∇φ|² + (m²/2)φ² + (λ/4)φ⁴ dx) Dφ -/
structure InvariantMeasureQFT (phi : Phi4_2) where
  /-- The partition function (normalization constant) -/
  partition_function : ℝ
  /-- The partition function is positive -/
  partition_pos : partition_function > 0
  /-- The measure is a probability measure -/
  is_probability : True  -- Full formalization requires constructive QFT

/-- Global well-posedness for Φ⁴₂: existence, uniqueness, and continuous dependence
    for all time and all initial data in appropriate spaces. -/
structure GlobalWellPosedness2D (phi : Phi4_2) where
  /-- The solution regularity (α < 0 in 2D) -/
  solution_regularity : ℝ
  /-- Negative regularity -/
  regularity_bound : solution_regularity < 0
  /-- Existence: for any initial data, a solution exists for all time -/
  global_existence : ∀ T : ℝ, T > 0 → True  -- Placeholder for solution existence
  /-- Uniqueness: solutions are unique in the appropriate class -/
  uniqueness : True  -- Placeholder for uniqueness statement

end Phi4_2

/-! ## Φ⁴ in 3D -/

/-- The 3D Φ⁴ model (Hairer 2014, Catellier-Chouk 2018) -/
structure Phi4_3 extends Phi4Model 3 where
  /-- 3D constraint -/
  dim_constraint : True := trivial

namespace Phi4_3

/-- In 3D, the cubic term requires renormalization -/
theorem cubic_requires_renormalization (phi : Phi4_3) :
    ¬ phi.toPhi4Model.cubicWellDefined := by
  simp [Phi4Model.cubicWellDefined, Phi4Model.solutionRegularity]
  norm_num

/-- The regularity structure for Φ⁴₃.
    The index set contains the regularities needed for the solution theory:
    - ξ has regularity α = -5/2 - ε
    - Φ has regularity 1/2 - ε
    - Products like Φ², Φ³ have correspondingly lower regularities -/
noncomputable def regularity_structure : RegularityStructure 3 where
  A := {
    indices := {-5/2, -3/2, -1/2, -1, 0, 1/2, 1}
    bdd_below := ⟨-5/2, by intro x hx; simp only [Set.mem_insert_iff] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num⟩
    locally_finite := fun _ => Set.toFinite _
    contains_zero := by simp
  }
  T := fun α _ => ℝ  -- Simplified: in full theory, T_α is spanned by abstract symbols
  banach := fun _ _ => inferInstance
  normed_space := fun _ _ => inferInstance
  fin_dim := fun _ _ => inferInstance
  G := Unit  -- Trivial structure group for this simplified example
  group := inferInstance
  action := fun _ _ _ => LinearMap.id
  action_mul := fun _ _ _ _ => rfl
  action_one := fun _ _ => rfl
  triangular_unipotent := fun _ _ _ => ⟨1, fun τ => by simp⟩

/-- Renormalization constants for Φ⁴₃.
    The mass counterterm diverges logarithmically as the UV cutoff ε → 0. -/
structure Renormalization (phi : Phi4_3) where
  /-- The mass counterterm δm²(ε) as a function of the UV cutoff ε > 0 -/
  mass_counterterm : ℝ → ℝ
  /-- Coefficient of the logarithmic divergence in mass counterterm -/
  log_coefficient : ℝ
  /-- The mass diverges logarithmically: |δm²(ε) - c log(1/ε)| bounded as ε → 0 -/
  log_divergence : ∃ C ε₀ : ℝ, C > 0 ∧ ε₀ > 0 ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    |mass_counterterm ε - log_coefficient * Real.log (1/ε)| ≤ C
  /-- The coupling constant renormalization (finite in 3D) -/
  coupling_renorm : ℝ → ℝ
  /-- Coupling renormalization has a finite limit as ε → 0 -/
  coupling_finite : ∃ coupling_limit : ℝ,
    Filter.Tendsto coupling_renorm (nhdsWithin 0 (Set.Ioi 0)) (nhds coupling_limit)

/-- Local well-posedness for Φ⁴₃: the renormalized equation has unique local solutions -/
structure LocalWellPosedness3D (phi : Phi4_3) (r : Renormalization phi) where
  /-- The solution regularity (1/2 - ε in 3D) -/
  solution_regularity : ℝ
  /-- The regularity is close to 1/2 -/
  regularity_bound : solution_regularity < 1/2 ∧ solution_regularity > 0
  /-- Local existence time depends on initial data norm -/
  existence_time : ℝ → ℝ  -- initial_norm → existence_time
  /-- Existence time is positive for bounded data -/
  existence_time_pos : ∀ R : ℝ, R > 0 → existence_time R > 0

/-- Coming down from infinity (Mourrat-Weber): solutions starting from rough initial
    data instantaneously regularize. The solution at any positive time t > 0 is
    independent of the precise initial condition in the class of "coming from infinity". -/
structure ComingDownFromInfinity (phi : Phi4_3) where
  /-- The regularization time: solutions become regular after time ε -/
  regularization : ∀ ε : ℝ, ε > 0 → True  -- Solutions at time ε are well-defined
  /-- Independence of initial condition in the limit: two solutions with different
      "infinite" initial conditions agree for t > 0 -/
  independence : True  -- Full statement requires abstract initial conditions

/-- The invariant measure for Φ⁴₃ exists and is unique -/
structure InvariantMeasure3D (phi : Phi4_3) where
  /-- Existence: there is an invariant probability measure -/
  existence : True  -- Full statement requires constructive proof
  /-- Uniqueness: the invariant measure is unique -/
  uniqueness : True  -- Follows from "coming down from infinity"
  /-- The measure is related to the Φ⁴₃ Euclidean QFT (if it exists) -/
  qft_relation : True

end Phi4_3

end SPDE.Examples
