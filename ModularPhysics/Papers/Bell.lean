import ModularPhysics.Core.Quantum
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.RingEquiv
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Finset.Basic

namespace Bell

open ModularPhysics.Core.Quantum
open BigOperators

set_option autoImplicit false

/-- Measurement setting (detector angle) -/
def Setting : Type := ℝ

/-- Measurement outcome -/
inductive Outcome where
  | plus : Outcome
  | minus : Outcome
  deriving DecidableEq

def Outcome.toReal : Outcome → ℝ
  | Outcome.plus => 1
  | Outcome.minus => -1

def Correlation := Setting → Setting → ℝ

-- ========================================
-- LOCAL HIDDEN VARIABLE THEORIES - FINITE VERSION
-- ========================================

structure HiddenVariableDistribution (Λ : Type*) [Fintype Λ] where
  ρ : Λ → ℝ
  nonneg : ∀ (lam : Λ), ρ lam ≥ 0
  normalized : ∑ lam, ρ lam = 1

def OutcomeFunction (Λ : Type*) := Setting → Λ → Outcome

structure LocalOutcomeFunctions (Λ : Type*) where
  A : OutcomeFunction Λ
  B : OutcomeFunction Λ

structure LHVT where
  Λ : Type*
  fintype_inst : Fintype Λ
  dist : @HiddenVariableDistribution Λ fintype_inst
  outcomes : LocalOutcomeFunctions Λ

attribute [instance] LHVT.fintype_inst

def lhvt_correlation (theory : LHVT) (a b : Setting) : ℝ :=
  ∑ lam : theory.Λ, theory.dist.ρ lam *
    (theory.outcomes.A a lam).toReal *
    (theory.outcomes.B b lam).toReal

-- ========================================
-- CHSH INEQUALITY - FULLY PROVEN
-- ========================================

def chsh_parameter (E : Correlation) (a a' b b' : Setting) : ℝ :=
  E a b + E a b' + E a' b - E a' b'

lemma outcome_chsh_bound
  (A_a A_a' B_b B_b' : Outcome) :
  |A_a.toReal * B_b.toReal +
   A_a.toReal * B_b'.toReal +
   A_a'.toReal * B_b.toReal -
   A_a'.toReal * B_b'.toReal| ≤ 2 := by
  cases A_a <;> cases A_a' <;> cases B_b <;> cases B_b'
  all_goals {
    unfold Outcome.toReal
    norm_num
  }

theorem chsh_inequality (theory : LHVT) (a a' b b' : Setting) :
  |chsh_parameter (lhvt_correlation theory) a a' b b'| ≤ 2 := by
  unfold chsh_parameter lhvt_correlation
  let f := fun (lam : theory.Λ) =>
    (theory.outcomes.A a lam).toReal * (theory.outcomes.B b lam).toReal +
    (theory.outcomes.A a lam).toReal * (theory.outcomes.B b' lam).toReal +
    (theory.outcomes.A a' lam).toReal * (theory.outcomes.B b lam).toReal -
    (theory.outcomes.A a' lam).toReal * (theory.outcomes.B b' lam).toReal
  have h_rewrite : (∑ lam, theory.dist.ρ lam * (theory.outcomes.A a lam).toReal * (theory.outcomes.B b lam).toReal) +
                   (∑ lam, theory.dist.ρ lam * (theory.outcomes.A a lam).toReal * (theory.outcomes.B b' lam).toReal) +
                   (∑ lam, theory.dist.ρ lam * (theory.outcomes.A a' lam).toReal * (theory.outcomes.B b lam).toReal) -
                   (∑ lam, theory.dist.ρ lam * (theory.outcomes.A a' lam).toReal * (theory.outcomes.B b' lam).toReal) =
                   ∑ lam, theory.dist.ρ lam * f lam := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    congr 1
    funext lam
    simp [f]
    ring
  rw [h_rewrite]
  calc |∑ lam : theory.Λ, theory.dist.ρ lam * f lam|
    ≤ ∑ lam : theory.Λ, |theory.dist.ρ lam * f lam| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ lam : theory.Λ, theory.dist.ρ lam * |f lam| := by
      congr 1
      funext lam
      rw [abs_mul, abs_of_nonneg (theory.dist.nonneg lam)]
    _ ≤ ∑ lam : theory.Λ, theory.dist.ρ lam * 2 := by
      apply Finset.sum_le_sum
      intro lam _
      apply mul_le_mul_of_nonneg_left _ (theory.dist.nonneg lam)
      exact outcome_chsh_bound _ _ _ _
    _ = 2 * ∑ lam : theory.Λ, theory.dist.ρ lam := by
      rw [← Finset.sum_mul]
      ring
    _ = 2 * 1 := by rw [theory.dist.normalized]
    _ = 2 := by norm_num

-- ========================================
-- QUANTUM PREDICTIONS
-- ========================================

noncomputable def singlet : PureState (TensorProduct Qubit Qubit) :=
  ⟨bellState, bellState_norm⟩

noncomputable def quantum_correlation_singlet (a b : ℝ) : ℝ :=
  -Real.cos (a - b)

theorem quantum_correlation_bounded (a b : ℝ) :
  -1 ≤ quantum_correlation_singlet a b ∧
  quantum_correlation_singlet a b ≤ 1 := by
  constructor
  · simp [quantum_correlation_singlet]
    have h := Real.cos_le_one (a - b)
    linarith
  · simp [quantum_correlation_singlet]
    have h := Real.neg_one_le_cos (a - b)
    linarith

noncomputable def optimal_settings : Setting × Setting × Setting × Setting :=
  ((0 : ℝ), -Real.pi / 2, 3 * Real.pi / 4, -3 * Real.pi / 4)

theorem quantum_chsh_equals :
  chsh_parameter quantum_correlation_singlet (0:ℝ) (-Real.pi / 2) (3 * Real.pi / 4) (-3 * Real.pi / 4) = 2 * Real.sqrt 2 := by
  unfold chsh_parameter quantum_correlation_singlet
  -- Just compute directly with ring simplification
  have h1 : (0:ℝ) - 3 * Real.pi / 4 = -(3 * Real.pi / 4) := by ring
  have h2 : (0:ℝ) - (-3 * Real.pi / 4) = 3 * Real.pi / 4 := by ring
  have h3 : -Real.pi / 2 - 3 * Real.pi / 4 = -(5 * Real.pi / 4) := by ring
  have h4 : -Real.pi / 2 - (-3 * Real.pi / 4) = Real.pi / 4 := by ring
  -- Rewrite to get clean angles
  simp only [h1, h2, h3, h4, Real.cos_neg]
  -- Now have: -cos(3π/4) - cos(3π/4) - cos(5π/4) + cos(π/4)
  have cos_3pi4 : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    have : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
    rw [this, Real.cos_pi_sub, Real.cos_pi_div_four]
  have cos_5pi4 : Real.cos (5 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    have : 5 * Real.pi / 4 = Real.pi / 4 + Real.pi := by ring
    rw [this, Real.cos_add_pi, Real.cos_pi_div_four]
  rw [cos_3pi4, cos_5pi4, Real.cos_pi_div_four]
  ring

theorem quantum_chsh_greater :
  chsh_parameter quantum_correlation_singlet (0:ℝ) (-Real.pi / 2) (3 * Real.pi / 4) (-3 * Real.pi / 4) > 2 := by
  rw [quantum_chsh_equals]
  have : Real.sqrt 2 > 1 := by
    have h1 : (1 : ℝ) < 2 := by norm_num
    have h2 : (0 : ℝ) ≤ 1 := by norm_num
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt h2 h1
  linarith

theorem quantum_violates_chsh :
  let (a, a', b, b') := optimal_settings
  let E := quantum_correlation_singlet
  let S := chsh_parameter E a a' b b'
  S = 2 * Real.sqrt 2 ∧ S > 2 := by
  unfold optimal_settings
  exact ⟨quantum_chsh_equals, quantum_chsh_greater⟩

-- ========================================
-- BELL'S THEOREM - FULLY PROVEN
-- ========================================

theorem bell_theorem :
  ¬∃ (theory : LHVT),
    ∀ (a b : Setting),
      lhvt_correlation theory a b = quantum_correlation_singlet a b := by
  intro ⟨theory, h_match⟩
  have h_lhvt : |chsh_parameter (lhvt_correlation theory)
                    (0 : ℝ) (-Real.pi / 2) (3 * Real.pi / 4) (-3 * Real.pi / 4)| ≤ 2 :=
    chsh_inequality theory (0 : ℝ) (-Real.pi / 2) (3 * Real.pi / 4) (-3 * Real.pi / 4)
  have h_qm : chsh_parameter (lhvt_correlation theory)
                (0 : ℝ) (-Real.pi / 2) (3 * Real.pi / 4) (-3 * Real.pi / 4) =
              2 * Real.sqrt 2 := by
    unfold chsh_parameter
    rw [h_match, h_match, h_match, h_match]
    exact quantum_violates_chsh.1
  rw [h_qm] at h_lhvt
  have h_sqrt2 : Real.sqrt 2 > 1 := by
    have h1 : (1 : ℝ) < 2 := by norm_num
    have h2 : (0 : ℝ) ≤ 1 := by norm_num
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt h2 h1
  have h_contradiction : 2 * Real.sqrt 2 > 2 := by linarith
  have h_abs : |2 * Real.sqrt 2| = 2 * Real.sqrt 2 := by
    apply abs_of_pos
    linarith
  rw [h_abs] at h_lhvt
  linarith

noncomputable def singlet_density : DensityOperator (TensorProduct Qubit Qubit) :=
  pureToDensity singlet

-- ========================================
-- CONNECTION TO QUANTUM MECHANICS
-- ========================================

/-- The correlation function we analyzed IS what quantum mechanics predicts -/
theorem quantum_correlation_is_physical (a b : ℝ) :
  quantum_correlation_singlet a b =
  expectation_value singlet (pauli_direction (Real.pi/2) a ⊗ᴼ pauli_direction (Real.pi/2) b) := by
  unfold quantum_correlation_singlet
  rw [singlet_pauli_correlation]

/-- **MAIN RESULT**: Quantum mechanics violates local hidden variable theories

    This is Bell's theorem applied to actual quantum mechanics:
    No local realistic theory can reproduce the predictions of quantum mechanics
    for measurements on entangled particles (the singlet state).

    Combines:
    1. Bell's inequality (fully proven) - |S| ≤ 2 for any LHVT
    2. Quantum calculation (axiomatized) - QM gives S = 2√2
    3. Contradiction - 2√2 > 2
-/
theorem quantum_mechanics_violates_local_realism :
  ¬∃ (theory : LHVT),
    ∀ (a b : Setting),
      lhvt_correlation theory a b =
      expectation_value singlet (pauli_direction (Real.pi/2) a ⊗ᴼ pauli_direction (Real.pi/2) b) := by
  intro ⟨theory, h_match⟩
  apply bell_theorem
  use theory
  intro a b
  rw [quantum_correlation_is_physical]
  exact h_match a b

end Bell
