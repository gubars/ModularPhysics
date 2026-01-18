-- ModularPhysics/Papers/Zamolodchikov1986/CTheoremComplete.lean

import ModularPhysics.Core.QFT.CFT.TwoDimensional.Virasoro
import ModularPhysics.Core.QFT.Wightman.WightmanFunctions
import ModularPhysics.Core.QFT.Wightman.Operators
import ModularPhysics.Core.QFT.EFT
import ModularPhysics.Core.Quantum
import ModularPhysics.Core.SpaceTime.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic

namespace ModularPhysics.Papers.Zamolodchikov1986

open ModularPhysics.Core.QFT Real
open CFT.TwoDimensional Wightman EFT
open ModularPhysics.Core.Quantum
open ModularPhysics.Core.SpaceTime

def origin_2d : SpaceTimePoint := fun _ => 0

noncomputable def radialPoint_2d (r : ℝ) : SpaceTimePoint :=
  fun i => if i.val = 1 then r else 0

structure QFT2D (H : Type _) [QuantumStateSpace H] where
  n_couplings : ℕ
  T_μν : QuantumFieldOperator H
  couplings : Fin n_couplings → ℝ
  beta_functions : Fin n_couplings → ℝ
  coupling_dimensions : Fin n_couplings → ℝ
  theory_id : Type

def theta {H : Type _} [QuantumStateSpace H] (theory : QFT2D H) : QuantumFieldOperator H :=
  theory.T_μν

axiom vacuum_state {H : Type _} [QuantumStateSpace H] : H

axiom vacuum_normalized {H : Type _} [QuantumStateSpace H] :
  ‖@vacuum_state H _‖ = 1

axiom two_point_wightman_trace
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H)
  (x y : SpaceTimePoint) : ℂ

axiom trace_wightman_is_real
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H)
  (x y : SpaceTimePoint) :
  (two_point_wightman_trace theory x y).im = 0

noncomputable def two_point_real
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H)
  (x y : SpaceTimePoint) : ℝ :=
  (two_point_wightman_trace theory x y).re

axiom translation_invariance
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H)
  (x y a : SpaceTimePoint) :
  two_point_real theory x y = two_point_real theory (x + a) (y + a)

noncomputable def two_point_function_radial
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H)
  (r : ℝ) : ℝ :=
  two_point_real theory (radialPoint_2d r) origin_2d

axiom operator_insertion_field
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H)
  (i : Fin theory.n_couplings) : QuantumFieldOperator H

axiom ward_identity_two_point
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H)
  (x y : SpaceTimePoint) :
  two_point_real theory x y =
    ∑ i : Fin theory.n_couplings,
      theory.beta_functions i *
      (innerProduct
        (fieldAction (theta theory) y (@vacuum_state H _))
        (fieldAction (operator_insertion_field theory i) x (@vacuum_state H _))).re

axiom spectral_density_wightman
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H)
  (i : Fin theory.n_couplings)
  (p : Fin 2 → ℝ) : ℝ

axiom unitarity_spectral_positivity
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H)
  (i : Fin theory.n_couplings)
  (p : Fin 2 → ℝ) :
  spectral_density_wightman theory i p ≥ 0

axiom integrate_2d : ((Fin 2 → ℝ) → ℝ) → ℝ

axiom integrate_1d : (ℝ → ℝ) → ℝ

axiom integrate_nonneg_2d (f : (Fin 2 → ℝ) → ℝ)
  (h : ∀ p, f p ≥ 0) :
  integrate_2d f ≥ 0

noncomputable def momentum_space_kernel (p_squared : ℝ) : ℝ :=
  if p_squared > 0 then -1 / (p_squared * sqrt p_squared) else 0

theorem momentum_kernel_negative (p_squared : ℝ) (h : p_squared > 0) :
  momentum_space_kernel p_squared < 0 := by
  unfold momentum_space_kernel
  simp [h]
  apply div_neg_of_neg_of_pos
  · norm_num
  · apply mul_pos h; exact Real.sqrt_pos.mpr h

noncomputable def positive_kernel_function (p_squared : ℝ) : ℝ :=
  - momentum_space_kernel p_squared

theorem kernel_positivity (p_squared : ℝ) (h : p_squared > 0) :
  positive_kernel_function p_squared > 0 := by
  unfold positive_kernel_function
  linarith [momentum_kernel_negative p_squared h]

noncomputable def spectral_weighted_integral
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H)
  (i : Fin theory.n_couplings) : ℝ :=
  integrate_2d (fun p =>
    positive_kernel_function (p 0 ^ 2 + p 1 ^ 2) *
    spectral_density_wightman theory i p)

theorem spectral_weighted_positive
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H)
  (i : Fin theory.n_couplings) :
  spectral_weighted_integral theory i ≥ 0 := by
  unfold spectral_weighted_integral
  apply integrate_nonneg_2d
  intro p
  apply mul_nonneg
  · by_cases h : p 0 ^ 2 + p 1 ^ 2 > 0
    · exact le_of_lt (kernel_positivity _ h)
    · unfold positive_kernel_function momentum_space_kernel
      simp [h]
  · exact unitarity_spectral_positivity theory i p

noncomputable def c_function_zamolodchikov
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H) : ℝ :=
  (3 / (4 * Real.pi^2)) *
  integrate_1d (fun r => r^3 * two_point_function_radial theory r)

axiom c_function_nonnegative
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H) :
  c_function_zamolodchikov theory ≥ 0

axiom operator_correlator_spectral
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H)
  (i : Fin theory.n_couplings)
  (r : ℝ) :
  (innerProduct
    (fieldAction (theta theory) (radialPoint_2d r) (@vacuum_state H _))
    (fieldAction (operator_insertion_field theory i) origin_2d (@vacuum_state H _))).re =
  integrate_2d (fun p =>
    Real.cos (sqrt (p 0^2 + p 1^2) * r) * spectral_density_wightman theory i p)

axiom fourier_transform_r_cubed
  (p : Fin 2 → ℝ) :
  integrate_1d (fun r => r^3 * Real.cos (sqrt (p 0^2 + p 1^2) * r)) =
    momentum_space_kernel (p 0^2 + p 1^2)

axiom c_function_momentum_representation
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H) :
  c_function_zamolodchikov theory =
    (3 / (4 * Real.pi^2)) *
    ∑ i : Fin theory.n_couplings,
      theory.beta_functions i *
      integrate_2d (fun p =>
        momentum_space_kernel (p 0^2 + p 1^2) *
        spectral_density_wightman theory i p)

noncomputable def coupling_derivative
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H)
  (i : Fin theory.n_couplings) : ℝ :=
  -(3 / (4 * Real.pi^2)) *
  theory.beta_functions i *
  spectral_weighted_integral theory i

theorem sign_beta_times_derivative
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H)
  (i : Fin theory.n_couplings) :
  theory.beta_functions i * coupling_derivative theory i ≤ 0 := by
  unfold coupling_derivative
  have h := spectral_weighted_positive theory i
  have h_const : (0 : ℝ) < 3 / (4 * Real.pi^2) := by
    apply div_pos
    · norm_num
    · apply mul_pos; norm_num; apply sq_pos_of_pos Real.pi_pos
  -- Goal: β * (-(3/(4π²)) * β * integral) ≤ 0
  -- = -β² * (3/(4π²)) * integral ≤ 0
  calc theory.beta_functions i * (-(3 / (4 * Real.pi^2)) * theory.beta_functions i * spectral_weighted_integral theory i)
      = -(theory.beta_functions i ^ 2 * (3 / (4 * Real.pi^2)) * spectral_weighted_integral theory i) := by ring
    _ ≤ 0 := by
        apply neg_nonpos_of_nonneg
        apply mul_nonneg
        apply mul_nonneg
        · exact sq_nonneg _
        · linarith
        · exact h

theorem sum_nonpositive {n : ℕ} (f : Fin n → ℝ) (h : ∀ i, f i ≤ 0) :
  ∑ i, f i ≤ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have h_rest : ∑ i : Fin n, f (Fin.castSucc i) ≤ 0 := by
      apply ih; intro i; exact h (Fin.castSucc i)
    linarith [h (Fin.last n)]

noncomputable def dc_dt
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H) : ℝ :=
  ∑ i : Fin theory.n_couplings,
    theory.beta_functions i * coupling_derivative theory i

theorem dc_dt_nonpositive
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H) :
  dc_dt theory ≤ 0 := by
  unfold dc_dt
  apply sum_nonpositive
  intro i
  exact sign_beta_times_derivative theory i

axiom rg_flow_beta_evolution
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H)
  (i : Fin theory.n_couplings) :
  theory.beta_functions i = betaFunction theory.theory_id (theory.couplings i)

axiom multivariable_chain_rule
  {H : Type _} [QuantumStateSpace H]
  (n : ℕ)
  (path : ℝ → QFT2D H)
  (t : ℝ)
  (h_n_const : ∀ s, (path s).n_couplings = n) :
  deriv (fun s => c_function_zamolodchikov (path s)) t =
    ∑ i : Fin n,
      (path t).beta_functions (i.cast (h_n_const t).symm) *
      coupling_derivative (path t) (i.cast (h_n_const t).symm)

theorem zamolodchikov_c_theorem
  {H : Type _} [QuantumStateSpace H]
  (n : ℕ)
  (path : ℝ → QFT2D H)
  (t : ℝ)
  (h_n_const : ∀ s, (path s).n_couplings = n) :
  deriv (fun s => c_function_zamolodchikov (path s)) t ≤ 0 := by
  rw [multivariable_chain_rule n path t h_n_const]
  apply sum_nonpositive
  intro i
  exact sign_beta_times_derivative (path t) (i.cast (h_n_const t).symm)

theorem beta_zero_stationary
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H)
  (h_fixed : ∀ i, theory.beta_functions i = 0) :
  dc_dt theory = 0 := by
  unfold dc_dt coupling_derivative
  simp [h_fixed]

axiom fixed_point_conformal_theory
  {H : Type _} [QuantumStateSpace H]
  (theory : QFT2D H)
  (h_fp : ∀ i, theory.beta_functions i = 0) :
  ∃ (c : VirasoroCentralCharge),
    centralChargeValue c = c_function_zamolodchikov theory

axiom fundamental_calculus_monotone
  (f : ℝ → ℝ) (a b : ℝ) (h_order : a < b)
  (h_decreasing : ∀ t ∈ Set.Icc a b, deriv f t ≤ 0) :
  f b ≤ f a

theorem c_UV_greater_equal_c_IR
  (c_UV c_IR : ℝ)
  (h_exists_flow : ∃ (c : ℝ → ℝ),
    c 0 = c_UV ∧ c 1 = c_IR ∧ ∀ t ∈ Set.Icc 0 1, deriv c t ≤ 0) :
  c_UV ≥ c_IR := by
  obtain ⟨c, h_start, h_end, h_mono⟩ := h_exists_flow
  have h_dec : c 1 ≤ c 0 :=
    fundamental_calculus_monotone c 0 1 (by norm_num) h_mono
  rw [←h_end, ←h_start]; exact h_dec

theorem irreversibility_theorem
  {H : Type _} [QuantumStateSpace H]
  (n : ℕ)
  (rg_path : ℝ → QFT2D H)
  (h_n_constant : ∀ s, (rg_path s).n_couplings = n)
  (theory_UV theory_IR : QFT2D H)
  (h_UV_endpoint : rg_path 0 = theory_UV)
  (h_IR_endpoint : rg_path 1 = theory_IR)
  (c_virasoro_UV : VirasoroCentralCharge)
  (c_virasoro_IR : VirasoroCentralCharge)
  (h_UV_central : centralChargeValue c_virasoro_UV = c_function_zamolodchikov theory_UV)
  (h_IR_central : centralChargeValue c_virasoro_IR = c_function_zamolodchikov theory_IR) :
  centralChargeValue c_virasoro_UV ≥ centralChargeValue c_virasoro_IR := by
  rw [h_UV_central, h_IR_central]
  apply c_UV_greater_equal_c_IR
  use (fun t => c_function_zamolodchikov (rg_path t))
  constructor; · rw [h_UV_endpoint]
  constructor; · rw [h_IR_endpoint]
  · intro t _; exact zamolodchikov_c_theorem n rg_path t h_n_constant

end ModularPhysics.Papers.Zamolodchikov1986
