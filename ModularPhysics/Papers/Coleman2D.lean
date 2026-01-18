-- ModularPhysics/Papers/Coleman2D.lean
import ModularPhysics.Core.QFT.Euclidean.SchwingerFunctions
import ModularPhysics.Core.QFT.PathIntegral.Symmetries
import ModularPhysics.Core.QFT.PathIntegral.ActionAndMeasure
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ModularPhysics.Papers.Coleman2D

open ModularPhysics.Core.QFT.Euclidean
open ModularPhysics.Core.QFT.PathIntegral
open Real

set_option linter.unusedVariables false

axiom orderParameter {F : Type _} (S : EuclideanAction F) : ℝ

axiom fieldMeasure {F : Type _} (S : EuclideanAction F) : FieldMeasure F

structure ContinuousSymmetry {F : Type _} (S : EuclideanAction F) where
  symmetry : InvariantSymmetry S.toActionFunctional (fieldMeasure S)
  continuous : Prop

structure GoldstoneMode {F : Type _} (S : EuclideanAction F) where
  propagator : EuclideanPoint → ℝ
  massless : ∀ k : EuclideanPoint, propagator k = 1 / (k 0 ^ 2 + k 1 ^ 2)

def hasLongRangeOrder {F : Type _} (S : EuclideanAction F) : Prop :=
  ∃ c > 0, ∀ x : EuclideanPoint,
    |twoPointSchwinger x (fun _ => 0) - (orderParameter S)^2| < c

def HasSSB {F : Type _} (S : EuclideanAction F) : Prop :=
  orderParameter S ≠ 0 ∧ hasLongRangeOrder S

axiom C_2d : ℝ
axiom C_2d_pos : C_2d > 0

noncomputable def infraredIntegral_2d (k_min Λ : ℝ) : ℝ :=
  C_2d * (log Λ - log k_min)

theorem infrared_diverges_2d :
  ∀ k_min > 0, ∀ M : ℝ, ∃ Λ > k_min, infraredIntegral_2d k_min Λ > M := by
  intro k_min hk M
  let M' := max M 0 + 1
  use k_min * exp (M' / C_2d)
  have hM' : M' > 0 := by unfold M'; linarith [le_max_right M 0]
  constructor
  · calc k_min * exp (M' / C_2d)
        > k_min * 1 := by {
          apply mul_lt_mul_of_pos_left _ hk
          exact one_lt_exp_iff.mpr (div_pos hM' C_2d_pos)
        }
      _ = k_min := by ring
  · unfold infraredIntegral_2d
    calc C_2d * (log (k_min * exp (M' / C_2d)) - log k_min)
        = C_2d * (log k_min + log (exp (M' / C_2d)) - log k_min) := by
          rw [log_mul (ne_of_gt hk) (ne_of_gt (exp_pos _))]
      _ = C_2d * log (exp (M' / C_2d)) := by ring
      _ = C_2d * (M' / C_2d) := by rw [log_exp]
      _ = M' := mul_div_cancel₀ M' (ne_of_gt C_2d_pos)
      _ > M := by unfold M'; linarith [le_max_left M 0]

axiom fourier_transform_massless_propagator
  {F : Type _}
  (S : EuclideanAction F)
  (goldstone : GoldstoneMode S)
  (x : EuclideanPoint)
  (k_min k_max : ℝ)
  (h_reg : 0 < k_min ∧ k_min < k_max)
  (h_large : sqrt (x 0 ^ 2 + x 1 ^ 2) > 1 / k_min) :
  let G := goldstone.propagator
  (∀ k, G k = 1 / (k 0 ^ 2 + k 1 ^ 2)) →
  ∃ C > 0, |twoPointSchwinger x (fun _ => 0) -
            (twoPointSchwinger (fun _ => 0) (fun _ => 0) -
             C * log (sqrt (x 0 ^ 2 + x 1 ^ 2)))| < 1

noncomputable def meanSquareFluctuation
  {F : Type _}
  (S : EuclideanAction F)
  (x : EuclideanPoint) : ℝ :=
  2 * twoPointSchwinger (fun _ => 0) (fun _ => 0) -
  2 * twoPointSchwinger x (fun _ => 0)

theorem fluctuations_unbounded_2d
  {F : Type _}
  (S : EuclideanAction F)
  (goldstone : GoldstoneMode S)
  (k_min k_max : ℝ)
  (h_reg : 0 < k_min ∧ k_min < k_max) :
  ∀ M : ℝ, ∃ x : EuclideanPoint, meanSquareFluctuation S x > M := by
  intro M
  sorry

axiom goldstone_theorem
  {F : Type _}
  (S : EuclideanAction F)
  (h_ssb : HasSSB S) :
  GoldstoneMode S

lemma unbounded_fluctuations_no_long_range_order
  {F : Type _}
  (S : EuclideanAction F)
  (goldstone : GoldstoneMode S)
  (k_min k_max : ℝ)
  (h_reg : 0 < k_min ∧ k_min < k_max)
  (h_unbounded : ∀ M : ℝ, ∃ x : EuclideanPoint, meanSquareFluctuation S x > M) :
  ¬ hasLongRangeOrder S := by
  intro ⟨c, hc_pos, hc⟩
  let φ_sq := twoPointSchwinger (fun _ => 0) (fun _ => 0)
  let v₀ := (orderParameter S)^2
  let upper_bound := 2 * φ_sq - 2 * (v₀ - c)
  have ⟨x, hx⟩ := h_unbounded (upper_bound + 1)
  unfold meanSquareFluctuation at hx
  have bound_abs := hc x
  have lower_bound : v₀ - c < twoPointSchwinger x (fun _ => 0) := by
    have h := abs_sub_lt_iff.mp bound_abs
    linarith
  have fluct_bounded : 2 * φ_sq - 2 * twoPointSchwinger x (fun _ => 0) < upper_bound := by
    linarith
  linarith

theorem coleman_no_goldstone_2d
  {F : Type _}
  (S : EuclideanAction F)
  (symmetry : ContinuousSymmetry S)
  (k_min k_max : ℝ)
  (h_reg : 0 < k_min ∧ k_min < k_max) :
  ¬ HasSSB S := by
  intro ⟨h_order, has_lro⟩
  have h_ssb : HasSSB S := ⟨h_order, has_lro⟩
  have goldstone := goldstone_theorem S h_ssb
  have unbounded := fluctuations_unbounded_2d S goldstone k_min k_max h_reg
  have no_lro := unbounded_fluctuations_no_long_range_order S goldstone k_min k_max h_reg unbounded
  exact no_lro has_lro

theorem dimension_criticality :
  ∀ (k_min Λ : ℝ), 0 < k_min → k_min < Λ →
  infraredIntegral_2d k_min Λ = C_2d * log (Λ / k_min) := by
  intro k_min Λ h1 h2
  unfold infraredIntegral_2d
  rw [log_div (ne_of_gt (by linarith : 0 < Λ)) (ne_of_gt h1)]

end ModularPhysics.Papers.Coleman2D
