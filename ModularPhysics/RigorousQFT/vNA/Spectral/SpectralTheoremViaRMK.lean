/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.vNA.Spectral.SpectralMeasurePolarizedViaRMK
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Spectral Theorem for Unitaries via Riesz-Markov-Kakutani

This file constructs the spectral projections for unitary operators using the
polarized spectral measure from `SpectralMeasurePolarizedViaRMK.lean`.

## Main Definitions

* `spectralProjectionOfUnitary` : the spectral projections P(E)

## Main Results

* `spectralProjection_empty` : P(∅) = 0
* `spectralProjection_univ` : P(Circle) = 1
* `spectralProjection_selfAdjoint` : P(E)* = P(E)
* `spectralProjection_idempotent` : P(E)² = P(E)
* `spectral_theorem_unitary_via_RMK` : the full spectral theorem

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I", Chapter VII-VIII
-/

noncomputable section

open scoped InnerProduct ComplexConjugate Classical CompactlySupported
open Filter Topology Complex MeasureTheory CompactlySupportedContinuousMap

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Helper lemmas for approximating indicator functions -/

/-- Convert thickenedIndicator to a real-valued continuous map for use with cfcOfCircleReal.
    Note: thickenedIndicator δ F is in [0,1] for all x. -/
def thickenedIndicatorReal {δ : ℝ} (hδ : 0 < δ) (F : Set Circle) : C(Circle, ℝ) :=
  ⟨fun x => (thickenedIndicator hδ F x : ℝ),
   NNReal.continuous_coe.comp (thickenedIndicator hδ F).continuous⟩

theorem thickenedIndicatorReal_nonneg {δ : ℝ} (hδ : 0 < δ) (F : Set Circle) (x : Circle) :
    0 ≤ thickenedIndicatorReal hδ F x := by
  simp only [thickenedIndicatorReal, ContinuousMap.coe_mk]
  exact NNReal.coe_nonneg _

theorem thickenedIndicatorReal_le_one {δ : ℝ} (hδ : 0 < δ) (F : Set Circle) (x : Circle) :
    thickenedIndicatorReal hδ F x ≤ 1 := by
  simp only [thickenedIndicatorReal, ContinuousMap.coe_mk]
  exact_mod_cast thickenedIndicator_le_one hδ F x

theorem thickenedIndicatorReal_one_of_mem {δ : ℝ} (hδ : 0 < δ) {F : Set Circle} {x : Circle}
    (hx : x ∈ F) : thickenedIndicatorReal hδ F x = 1 := by
  simp only [thickenedIndicatorReal, ContinuousMap.coe_mk]
  exact_mod_cast thickenedIndicator_one hδ F hx

/-- On a compact space, any continuous function has compact support.
    This converts C(Circle, ℝ) to C_c(Circle, ℝ). -/
def toCc (f : C(Circle, ℝ)) : C_c(Circle, ℝ) :=
  ⟨f, HasCompactSupport.of_compactSpace f⟩

@[simp]
theorem toCc_apply (f : C(Circle, ℝ)) (x : Circle) : toCc f x = f x := rfl

@[simp]
theorem toCc_toContinuousMap (f : C(Circle, ℝ)) : (toCc f).toContinuousMap = f := rfl

/-- The thickenedIndicatorReal functions converge pointwise to the indicator of closure F. -/
theorem thickenedIndicatorReal_tendsto_indicator_closure {F : Set Circle}
    {δseq : ℕ → ℝ} (hδ_pos : ∀ n, 0 < δseq n) (hδ_lim : Tendsto δseq atTop (𝓝 0)) :
    Tendsto (fun n => (thickenedIndicatorReal (hδ_pos n) F : Circle → ℝ))
      atTop (𝓝 (Set.indicator (closure F) (fun _ => (1 : ℝ)))) := by
  -- Convert to ℝ≥0 convergence and apply thickenedIndicator_tendsto_indicator_closure
  have hconv := thickenedIndicator_tendsto_indicator_closure hδ_pos hδ_lim F
  rw [tendsto_pi_nhds] at hconv ⊢
  intro x
  specialize hconv x
  -- thickenedIndicator → indicator as ℝ≥0, we need thickenedIndicatorReal → indicator as ℝ
  simp only [thickenedIndicatorReal, ContinuousMap.coe_mk]
  -- The goal is: Tendsto (fun n => ↑(thickenedIndicator (hδ_pos n) F x)) atTop (𝓝 (indicator (closure F) (fun _ => 1) x))
  -- We have: hconv : Tendsto (fun n => thickenedIndicator (hδ_pos n) F x) atTop (𝓝 (indicator (closure F) (fun _ => 1) x))
  -- Need to show the ℝ version from the ℝ≥0 version
  by_cases hx : x ∈ closure F
  · -- x ∈ closure F: indicator = 1
    simp only [hx, Set.indicator_of_mem]
    have h1 : ∀ n, (thickenedIndicator (hδ_pos n) F x : ℝ) = 1 := fun n =>
      congrArg NNReal.toReal (thickenedIndicator_one_of_mem_closure (hδ_pos n) F hx)
    simp only [h1, tendsto_const_nhds]
  · -- x ∉ closure F: indicator = 0
    simp only [hx, Set.indicator_of_notMem, not_false_eq_true]
    have hconv' : Tendsto (fun n => thickenedIndicator (hδ_pos n) F x) atTop (𝓝 0) := by
      simp only [hx, Set.indicator_of_notMem, not_false_eq_true] at hconv
      exact hconv
    exact NNReal.tendsto_coe.mpr hconv'

/-! ### Spectral Projections -/

/-- The spectral projection for a Borel set E ⊆ Circle.

    Constructed using sesquilinearToOperator from SpectralIntegral.lean:
    The polarized spectral measure μ_{x,y}(E) = spectralMeasurePolarized U hU x y E hE
    defines a bounded sesquilinear form, which gives a unique operator P(E) with
    ⟨x, P(E) y⟩ = μ_{x,y}(E). -/
def spectralProjectionOfUnitary (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) : H →L[ℂ] H :=
  -- Use sesquilinearToOperator with B(x, y) = μ_{x,y}(E)
  sesquilinearToOperator
    (fun x y => spectralMeasurePolarized U hU x y E hE)
    (spectralMeasurePolarized_linear_right U hU E hE)
    (spectralMeasurePolarized_conj_linear_left U hU E hE)
    (spectralMeasurePolarized_bounded U hU E hE)

/-- P(∅) = 0 -/
theorem spectralProjection_empty (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H)) :
    spectralProjectionOfUnitary U hU ∅ MeasurableSet.empty = 0 := by
  -- P(∅) is the operator corresponding to the sesquilinear form B(x,y) = spectralMeasurePolarized x y ∅
  -- Since μ_z(∅) = 0 for any measure, spectralMeasurePolarized x y ∅ = 0 for all x, y
  -- Hence P(∅) = 0
  -- First show the sesquilinear form is identically zero
  have hB_zero : ∀ x y, spectralMeasurePolarized U hU x y ∅ MeasurableSet.empty = 0 := by
    intro x y
    unfold spectralMeasurePolarized spectralMeasureDiagonal
    -- All measures satisfy μ(∅) = 0
    simp only [measure_empty, ENNReal.toReal_zero, sub_self, Complex.ofReal_zero, mul_zero]
    ring
  -- The operator is determined by ⟨x, T y⟩ = B(x, y) = 0 for all x, y
  -- This means T = 0
  ext y
  rw [ContinuousLinearMap.zero_apply]
  rw [← @inner_self_eq_zero ℂ H]
  -- P(∅) = sesquilinearToOperator ...
  unfold spectralProjectionOfUnitary
  -- ⟨P(∅) y, P(∅) y⟩ = B(P(∅) y, P(∅) y) = 0 by sesquilinearToOperator_inner
  have h := sesquilinearToOperator_inner
    (fun x y => spectralMeasurePolarized U hU x y ∅ MeasurableSet.empty)
    (spectralMeasurePolarized_linear_right U hU ∅ MeasurableSet.empty)
    (spectralMeasurePolarized_conj_linear_left U hU ∅ MeasurableSet.empty)
    (spectralMeasurePolarized_bounded U hU ∅ MeasurableSet.empty)
  set P := sesquilinearToOperator (fun x y => spectralMeasurePolarized U hU x y ∅ MeasurableSet.empty)
    (spectralMeasurePolarized_linear_right U hU ∅ MeasurableSet.empty)
    (spectralMeasurePolarized_conj_linear_left U hU ∅ MeasurableSet.empty)
    (spectralMeasurePolarized_bounded U hU ∅ MeasurableSet.empty) with hP_def
  -- h says: B x y = ⟨x, P y⟩
  -- So ⟨P y, P y⟩ = B(P y, y) = 0
  rw [← h (P y) y, hB_zero]

/-- The polarized spectral measure for Circle equals the inner product.
    This uses μ_z(Circle) = ‖z‖² and the complex polarization identity. -/
theorem spectralMeasurePolarized_univ (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (x y : H) :
    spectralMeasurePolarized U hU x y Set.univ MeasurableSet.univ = @inner ℂ H _ x y := by
  unfold spectralMeasurePolarized
  -- Using μ_z(Circle) = ‖z‖² (from spectralMeasureDiagonal_univ)
  rw [spectralMeasureDiagonal_univ U hU (x + y)]
  rw [spectralMeasureDiagonal_univ U hU (x - y)]
  rw [spectralMeasureDiagonal_univ U hU (x + Complex.I • y)]
  rw [spectralMeasureDiagonal_univ U hU (x - Complex.I • y)]
  -- Now apply the complex polarization identity for norms
  -- inner_eq_sum_norm_sq_div_four: ⟨x,y⟩ = ((‖x+y‖)² - (‖x-y‖)² + ((‖x-I•y‖)² - (‖x+I•y‖)²)*I)/4
  rw [inner_eq_sum_norm_sq_div_four x y]
  -- Note: Complex.I = RCLike.I for the complex numbers
  simp only [Complex.ofReal_pow]
  -- The LHS is: (1/4) * (‖x+y‖² - ‖x-y‖² - I*‖x+I•y‖² + I*‖x-I•y‖²)
  -- The RHS is: ((‖x+y‖)² - (‖x-y‖)² + ((‖x-I•y‖)² - (‖x+I•y‖)²)*I)/4
  -- Need to show: (1/4) * (a - b - I*c + I*d) = (a - b + (d-c)*I) / 4
  -- where a = ‖x+y‖², b = ‖x-y‖², c = ‖x+I•y‖², d = ‖x-I•y‖²
  -- We have: RCLike.I (for ℂ) = Complex.I
  have hI : (RCLike.I : ℂ) = Complex.I := rfl
  simp only [hI]
  -- Both sides have the same terms, just in different order
  ring_nf
  ac_rfl

/-- P(Circle) = 1 -/
theorem spectralProjection_univ (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H)) :
    spectralProjectionOfUnitary U hU Set.univ MeasurableSet.univ = 1 := by
  -- P(Circle) is determined by ⟨x, P(Circle) y⟩ = spectralMeasurePolarized x y Circle = ⟨x, y⟩
  -- This means P(Circle) = 1 (identity)
  ext y
  rw [ContinuousLinearMap.one_apply]
  -- Show P(Circle) y = y by showing ⟨x, P(Circle) y⟩ = ⟨x, y⟩ for all x
  apply ext_inner_left ℂ
  intro x
  unfold spectralProjectionOfUnitary
  have h := sesquilinearToOperator_inner
    (fun x y => spectralMeasurePolarized U hU x y Set.univ MeasurableSet.univ)
    (spectralMeasurePolarized_linear_right U hU Set.univ MeasurableSet.univ)
    (spectralMeasurePolarized_conj_linear_left U hU Set.univ MeasurableSet.univ)
    (spectralMeasurePolarized_bounded U hU Set.univ MeasurableSet.univ)
  -- h says: B x y = ⟨x, P y⟩
  -- Goal: ⟨x, P y⟩ = ⟨x, y⟩
  rw [← h x y]
  exact spectralMeasurePolarized_univ U hU x y

/-- P(E)* = P(E) (self-adjoint) -/
theorem spectralProjection_selfAdjoint (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) :
    (spectralProjectionOfUnitary U hU E hE).adjoint =
    spectralProjectionOfUnitary U hU E hE := by
  -- P(E) is self-adjoint because B(x, y) = conj(B(y, x)) (Hermitian symmetry)
  -- This means ⟨x, P(E) y⟩ = B(x, y) = conj(B(y, x)) = conj(⟨y, P(E) x⟩) = ⟨P(E) x, y⟩
  -- Hence P(E)* = P(E)
  set P := spectralProjectionOfUnitary U hU E hE with hP_def
  -- We need to show P.adjoint = P
  -- First, use ext to reduce to showing P.adjoint y = P y for all y
  ext y
  -- Then use ext_inner_left to reduce to showing ⟨x, P.adjoint y⟩ = ⟨x, P y⟩ for all x
  apply ext_inner_left ℂ
  intro x
  -- Goal: ⟨x, P.adjoint y⟩ = ⟨x, P y⟩
  -- LHS: ⟨x, P.adjoint y⟩ = ⟨P x, y⟩ (by adjoint_inner_right)
  rw [ContinuousLinearMap.adjoint_inner_right]
  -- Now goal is: ⟨P x, y⟩ = ⟨x, P y⟩
  -- From construction: ⟨x, P y⟩ = B(x, y) = spectralMeasurePolarized x y
  -- And: ⟨P x, y⟩ = conj(⟨y, P x⟩) = conj(B(y, x)) = B(x, y) by conj_symm
  have hinner_left : @inner ℂ H _ x (P y) = spectralMeasurePolarized U hU x y E hE := by
    rw [hP_def]
    unfold spectralProjectionOfUnitary
    rw [← sesquilinearToOperator_inner]
  have hinner_right : @inner ℂ H _ (P x) y = spectralMeasurePolarized U hU x y E hE := by
    -- ⟨P x, y⟩ = conj(⟨y, P x⟩) = conj(B(y, x)) = B(x, y)
    have h2 : @inner ℂ H _ y (P x) = spectralMeasurePolarized U hU y x E hE := by
      rw [hP_def]
      unfold spectralProjectionOfUnitary
      rw [← sesquilinearToOperator_inner]
    -- Use inner_conj_symm: starRingEnd ℂ (inner ℂ y (P x)) = inner ℂ (P x) y
    -- star (B(y,x)) = B(x,y)
    rw [(inner_conj_symm (P x) y).symm, h2]
    -- Goal: starRingEnd ℂ (spectralMeasurePolarized U hU y x E hE) = spectralMeasurePolarized U hU x y E hE
    -- starRingEnd ℂ = star for ℂ (definitionally)
    exact (spectralMeasurePolarized_conj_symm U hU E hE x y).symm
  rw [hinner_right, hinner_left]

/-- P(E) is a positive operator: 0 ≤ P(E) in the Loewner order.

    Proof: P(E) is self-adjoint and ⟨z, P(E)z⟩ = μ_z(E) ≥ 0 for all z. -/
theorem spectralProjection_nonneg (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) :
    0 ≤ spectralProjectionOfUnitary U hU E hE := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  constructor
  · -- P is symmetric (self-adjoint implies symmetric)
    have hP_adj := spectralProjection_selfAdjoint U hU E hE
    intro x y
    calc @inner ℂ H _ (spectralProjectionOfUnitary U hU E hE x) y
        = @inner ℂ H _ x ((spectralProjectionOfUnitary U hU E hE).adjoint y) := by
          rw [ContinuousLinearMap.adjoint_inner_right]
      _ = @inner ℂ H _ x (spectralProjectionOfUnitary U hU E hE y) := by rw [hP_adj]
  · -- ∀ z, 0 ≤ re ⟪P z, z⟫
    intro z
    -- ⟨P z, z⟩ = conj(⟨z, P z⟩) by inner_conj_symm
    -- ⟨z, P z⟩ = μ_z(E).toReal (real) by the sesquilinear form characterization
    have hinner : @inner ℂ H _ z (spectralProjectionOfUnitary U hU E hE z) =
        (spectralMeasureDiagonal U hU z E).toReal := by
      unfold spectralProjectionOfUnitary
      rw [← sesquilinearToOperator_inner]
      exact spectralMeasurePolarized_diag U hU z E hE
    -- ⟨Pz, z⟩ = conj(⟨z, Pz⟩) = μ_z(E).toReal (since it's real)
    have hinner_swap : @inner ℂ H _ (spectralProjectionOfUnitary U hU E hE z) z =
        (spectralMeasureDiagonal U hU z E).toReal := by
      -- inner_conj_symm (Pz) z : ⟪z, Pz⟫† = ⟪Pz, z⟫
      rw [← inner_conj_symm (spectralProjectionOfUnitary U hU E hE z) z, hinner]
      -- μ_z(E).toReal is real, so conj(μ) = μ
      exact Complex.conj_ofReal _
    rw [ContinuousLinearMap.reApplyInnerSelf, hinner_swap]
    exact ENNReal.toReal_nonneg

/-- P(E) ≤ 1 in the Loewner order.

    Proof: (1 - P(E)) is positive since ⟨z, (1-P)z⟩ = ‖z‖² - μ_z(E) ≥ 0. -/
theorem spectralProjection_le_one (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) :
    spectralProjectionOfUnitary U hU E hE ≤ 1 := by
  rw [ContinuousLinearMap.le_def]
  set P := spectralProjectionOfUnitary U hU E hE with hP_def
  constructor
  · -- (1 - P) is symmetric
    have hP_adj := spectralProjection_selfAdjoint U hU E hE
    intro x y
    -- Goal: ⟪(1 - P) x, y⟫ = ⟪x, (1 - P) y⟫
    show @inner ℂ H _ ((1 - P) x) y = @inner ℂ H _ x ((1 - P) y)
    calc @inner ℂ H _ ((1 - P) x) y
        = @inner ℂ H _ (x - P x) y := rfl
      _ = @inner ℂ H _ x y - @inner ℂ H _ (P x) y := inner_sub_left x (P x) y
      _ = @inner ℂ H _ x y - @inner ℂ H _ x (P.adjoint y) := by rw [ContinuousLinearMap.adjoint_inner_right]
      _ = @inner ℂ H _ x y - @inner ℂ H _ x (P y) := by rw [hP_adj]
      _ = @inner ℂ H _ x (y - P y) := (inner_sub_right x y (P y)).symm
      _ = @inner ℂ H _ x ((1 - P) y) := rfl
  · -- ∀ z, 0 ≤ re ⟪(1-P) z, z⟫
    intro z
    -- Goal: 0 ≤ (1 - P).reApplyInnerSelf z
    show 0 ≤ (1 - P).reApplyInnerSelf z
    rw [ContinuousLinearMap.reApplyInnerSelf]
    -- (1 - P) z = z - P z
    have h1 : (1 - P) z = z - P z := rfl
    rw [h1, inner_sub_left]
    -- re(⟨z, z⟩ - ⟨Pz, z⟩) = ‖z‖² - μ_z(E).toReal
    have hinner_id : @inner ℂ H _ z z = (‖z‖^2 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    have hinner_P : @inner ℂ H _ (P z) z = (spectralMeasureDiagonal U hU z E).toReal := by
      have h : @inner ℂ H _ z (P z) = (spectralMeasureDiagonal U hU z E).toReal := by
        rw [hP_def]
        unfold spectralProjectionOfUnitary
        rw [← sesquilinearToOperator_inner]
        exact spectralMeasurePolarized_diag U hU z E hE
      rw [← inner_conj_symm (P z) z, h]
      exact Complex.conj_ofReal _
    rw [hinner_id, hinner_P, map_sub]
    -- re((↑‖z‖)^2) = ‖z‖² and re(↑μ.toReal) = μ.toReal
    have h_re1 : RCLike.re ((‖z‖ : ℂ) ^ 2) = ‖z‖ ^ 2 :=
      @RCLike.re_ofReal_pow ℂ _ ‖z‖ 2
    have h_re2 : RCLike.re ((spectralMeasureDiagonal U hU z E).toReal : ℂ) =
        (spectralMeasureDiagonal U hU z E).toReal := RCLike.ofReal_re _
    rw [h_re1, h_re2]
    -- Need: ‖z‖² - μ_z(E).toReal ≥ 0, i.e., μ_z(E).toReal ≤ ‖z‖²
    -- μ_z(E).toReal ≤ μ_z(Circle).toReal = ‖z‖² by measure monotonicity
    have hμ_mono_ennreal : spectralMeasureDiagonal U hU z E ≤
        spectralMeasureDiagonal U hU z Set.univ := MeasureTheory.measure_mono (Set.subset_univ E)
    have hμ_univ_toReal : (spectralMeasureDiagonal U hU z Set.univ).toReal = ‖z‖^2 :=
      spectralMeasureDiagonal_univ U hU z
    have hfinite_E : (spectralMeasureDiagonal U hU z E) < ⊤ := by
      have := spectralMeasureDiagonal_isFiniteMeasure U hU z
      exact MeasureTheory.measure_lt_top _ E
    have hfinite_univ : (spectralMeasureDiagonal U hU z Set.univ) < ⊤ := by
      have := spectralMeasureDiagonal_isFiniteMeasure U hU z
      exact MeasureTheory.measure_lt_top _ Set.univ
    have hμ_le : (spectralMeasureDiagonal U hU z E).toReal ≤ ‖z‖^2 := by
      rw [← hμ_univ_toReal]
      exact ENNReal.toReal_mono hfinite_univ.ne hμ_mono_ennreal
    linarith

/-- Monotonicity of spectral projections: P(F) ≤ P(E) in Loewner order when F ⊆ E.

    Proof: (P(E) - P(F)) is positive since ⟨z, (P(E)-P(F))z⟩ = μ_z(E) - μ_z(F) ≥ 0. -/
theorem spectralProjection_mono (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (F E : Set Circle) (hF : MeasurableSet F) (hE : MeasurableSet E) (hFE : F ⊆ E) :
    spectralProjectionOfUnitary U hU F hF ≤ spectralProjectionOfUnitary U hU E hE := by
  set PF := spectralProjectionOfUnitary U hU F hF with hPF_def
  set PE := spectralProjectionOfUnitary U hU E hE with hPE_def
  have hsa_F : PF.adjoint = PF := spectralProjection_selfAdjoint U hU F hF
  have hsa_E : PE.adjoint = PE := spectralProjection_selfAdjoint U hU E hE
  rw [ContinuousLinearMap.le_def]
  constructor
  · -- (PE - PF) is symmetric
    intro x y
    calc @inner ℂ H _ ((PE - PF) x) y
        = @inner ℂ H _ (PE x - PF x) y := rfl
      _ = @inner ℂ H _ (PE x) y - @inner ℂ H _ (PF x) y := inner_sub_left _ _ _
      _ = @inner ℂ H _ x (PE.adjoint y) - @inner ℂ H _ x (PF.adjoint y) := by
          rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
      _ = @inner ℂ H _ x (PE y) - @inner ℂ H _ x (PF y) := by rw [hsa_E, hsa_F]
      _ = @inner ℂ H _ x (PE y - PF y) := (inner_sub_right x _ _).symm
      _ = @inner ℂ H _ x ((PE - PF) y) := rfl
  · -- (PE - PF).reApplyInnerSelf z ≥ 0
    intro z
    rw [ContinuousLinearMap.reApplyInnerSelf]
    have h1 : (PE - PF) z = PE z - PF z := rfl
    rw [h1, inner_sub_left]
    have hinner_E : @inner ℂ H _ (PE z) z = (spectralMeasureDiagonal U hU z E).toReal := by
      have h := spectralMeasurePolarized_diag U hU z E hE
      have hinner_def : @inner ℂ H _ z (PE z) =
          spectralMeasurePolarized U hU z z E hE := by
        rw [hPE_def]
        unfold spectralProjectionOfUnitary
        rw [← sesquilinearToOperator_inner]
      rw [← inner_conj_symm (PE z) z, hinner_def, h, Complex.conj_ofReal]
    have hinner_F : @inner ℂ H _ (PF z) z = (spectralMeasureDiagonal U hU z F).toReal := by
      have h := spectralMeasurePolarized_diag U hU z F hF
      have hinner_def : @inner ℂ H _ z (PF z) =
          spectralMeasurePolarized U hU z z F hF := by
        rw [hPF_def]
        unfold spectralProjectionOfUnitary
        rw [← sesquilinearToOperator_inner]
      rw [← inner_conj_symm (PF z) z, hinner_def, h, Complex.conj_ofReal]
    rw [hinner_E, hinner_F, map_sub]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
    have hmono : spectralMeasureDiagonal U hU z F ≤ spectralMeasureDiagonal U hU z E :=
      MeasureTheory.measure_mono hFE
    have hfinite_E := spectralMeasureDiagonal_isFiniteMeasure U hU z
    have htoReal_mono := ENNReal.toReal_mono (MeasureTheory.measure_lt_top _ E).ne hmono
    linarith

/-- For continuous g : Circle → ℝ, we have ‖cfc(g, U)z‖² = Re⟨z, cfc(g², U)z⟩.

    This follows from:
    - cfc(g, U) is self-adjoint (since g is real-valued)
    - cfc(g², U) = cfc(g, U)² (by cfc_mul)
    - ⟨z, cfc(g², U)z⟩ = ∫ g² dμ_z (spectral functional) -/
theorem cfcOfCircleReal_norm_sq (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (g : C(Circle, ℝ)) (z : H) :
    ‖cfcOfCircleReal U hU g z‖^2 =
    (@inner ℂ H _ z (cfcOfCircleReal U hU (g * g) z)).re := by
  haveI : IsStarNormal U := unitary_isStarNormal U hU
  set T := cfcOfCircleReal U hU g with hT_def
  -- T is self-adjoint
  have hT_sa : IsSelfAdjoint T := cfcOfCircleReal_isSelfAdjoint U hU g
  -- ‖Tz‖² = ⟨Tz, Tz⟩ = ⟨z, T*Tz⟩ = ⟨z, T²z⟩ (using T* = T)
  have h1 : ‖T z‖^2 = (@inner ℂ H _ (T z) (T z)).re := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [h1]
  -- ⟨Tz, Tz⟩ = ⟨z, T†(Tz)⟩ = ⟨z, T(Tz)⟩ (since T† = T)
  have h2 : @inner ℂ H _ (T z) (T z) = @inner ℂ H _ z (T (T z)) := by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint] at hT_sa
    calc @inner ℂ H _ (T z) (T z)
        = @inner ℂ H _ z (T.adjoint (T z)) := (ContinuousLinearMap.adjoint_inner_right T z (T z)).symm
      _ = @inner ℂ H _ z (T (T z)) := by rw [hT_sa]
  rw [h2]
  -- T(Tz) = T²z = cfc(g², U)z
  -- Use cfc_mul: cfc(f * g) = cfc(f) * cfc(g)
  have hT_sq : T ∘L T = cfcOfCircleReal U hU (g * g) := by
    unfold cfcOfCircleReal
    -- circleRealToComplex (g * g) = circleRealToComplex g * circleRealToComplex g
    have hmul : circleRealToComplex (g * g) =
        fun z => circleRealToComplex g z * circleRealToComplex g z := by
      funext x
      simp only [circleRealToComplex, ContinuousMap.mul_apply]
      split_ifs with h
      · simp only [Complex.ofReal_mul]
      · simp only [mul_zero]
    rw [hmul]
    -- cfc (f * g) = cfc f * cfc g
    have hcont := circleRealToComplex_continuousOn_spectrum g U hU
    rw [cfc_mul (circleRealToComplex g) (circleRealToComplex g) U hcont hcont]
    rfl
  have h3 : T (T z) = (T ∘L T) z := ContinuousLinearMap.comp_apply T T z
  rw [h3, hT_sq]

/-- Key connection: ‖cfc(g, U)z‖² equals the spectral integral of g².
    This connects the Hilbert space norm to the spectral measure. -/
theorem cfcOfCircleReal_norm_sq_integral (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (g : C(Circle, ℝ)) (z : H) :
    ‖cfcOfCircleReal U hU g z‖^2 = spectralFunctionalAux U hU z (g * g) := by
  rw [cfcOfCircleReal_norm_sq U hU g z]
  rfl

/-- For compactly supported g, the norm squared equals the spectral measure integral. -/
theorem cfcOfCircleReal_norm_sq_measure (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (g : C_c(Circle, ℝ)) (z : H) :
    ‖cfcOfCircleReal U hU g.toContinuousMap z‖^2 =
    ∫ x, (g x)^2 ∂(spectralMeasureDiagonal U hU z) := by
  rw [cfcOfCircleReal_norm_sq_integral]
  -- spectralFunctionalAux z (g * g).toContinuousMap = (spectralFunctionalCc z) (g * g)
  -- which equals ∫ (g * g) dμ_z by spectralMeasureDiagonal_integral
  have heq : g.toContinuousMap * g.toContinuousMap = (g * g).toContinuousMap := rfl
  rw [heq]
  -- First convert the RHS: ∫ g² = ∫ (g * g)
  have hint_eq : ∫ x, (g x)^2 ∂(spectralMeasureDiagonal U hU z) =
                 ∫ x, (g * g) x ∂(spectralMeasureDiagonal U hU z) := by
    congr 1; funext x; simp only [CompactlySupportedContinuousMap.coe_mul, Pi.mul_apply, sq]
  rw [hint_eq]
  -- Use spectralMeasureDiagonal_integral: ∫ f dμ_z = (spectralFunctionalCc z) f
  -- spectralFunctionalCc is defined so that (spectralFunctionalCc z) f = spectralFunctionalAux z f.toContinuousMap
  have hdef : spectralFunctionalAux U hU z (g * g).toContinuousMap =
              (spectralFunctionalCc U hU z) (g * g) := rfl
  rw [hdef, spectralMeasureDiagonal_integral]

/-- Version for C(Circle, ℝ) using toCc conversion. -/
theorem cfcOfCircleReal_norm_sq_measure' (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (g : C(Circle, ℝ)) (z : H) :
    ‖cfcOfCircleReal U hU g z‖^2 =
    ∫ x, (g x)^2 ∂(spectralMeasureDiagonal U hU z) := by
  have h := cfcOfCircleReal_norm_sq_measure U hU (toCc g) z
  simp only [toCc_toContinuousMap, toCc_apply] at h
  exact h

/-- cfcOfCircleReal respects subtraction: cfc(g - h) = cfc(g) - cfc(h). -/
theorem cfcOfCircleReal_sub (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (g h : C(Circle, ℝ)) :
    cfcOfCircleReal U hU (g - h) = cfcOfCircleReal U hU g - cfcOfCircleReal U hU h := by
  haveI : IsStarNormal U := unitary_isStarNormal U hU
  unfold cfcOfCircleReal
  -- Show circleRealToComplex (g - h) = circleRealToComplex g - circleRealToComplex h
  have hsub : circleRealToComplex (g - h) =
      fun z => circleRealToComplex g z - circleRealToComplex h z := by
    funext x
    simp only [circleRealToComplex, ContinuousMap.sub_apply]
    split_ifs with hx
    · simp only [Complex.ofReal_sub]
    · simp only [sub_zero]
  rw [hsub]
  -- Apply cfc_sub
  have hcont_g := circleRealToComplex_continuousOn_spectrum g U hU
  have hcont_h := circleRealToComplex_continuousOn_spectrum h U hU
  rw [cfc_sub (circleRealToComplex g) (circleRealToComplex h) U hcont_g hcont_h]

/-- The spectral functional converges for thickened indicators approaching a closed set.
    Λ_w(g_n) → μ_w(F).toReal where g_n = thickenedIndicatorReal(δ_n, F). -/
theorem spectralFunctionalAux_tendsto_closed (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (F : Set Circle) (hF_closed : IsClosed F) (w : H)
    {δseq : ℕ → ℝ} (hδ_pos : ∀ n, 0 < δseq n) (hδ_lim : Tendsto δseq atTop (𝓝 0)) :
    Tendsto (fun n => spectralFunctionalAux U hU w (thickenedIndicatorReal (hδ_pos n) F))
      atTop (𝓝 (spectralMeasureDiagonal U hU w F).toReal) := by
  let g : ℕ → C(Circle, ℝ) := fun n => thickenedIndicatorReal (hδ_pos n) F
  let μ_w := spectralMeasureDiagonal U hU w
  -- g_n → χ_F pointwise (closure F = F since F is closed)
  have hg_tendsto : Tendsto (fun n => (g n : Circle → ℝ)) atTop
      (𝓝 (Set.indicator F (fun _ => (1 : ℝ)))) := by
    have h := thickenedIndicatorReal_tendsto_indicator_closure hδ_pos hδ_lim (F := F)
    rwa [hF_closed.closure_eq] at h
  have hg_le_one : ∀ n x, g n x ≤ 1 := fun n x =>
    thickenedIndicatorReal_le_one (hδ_pos n) F x
  have hg_nonneg : ∀ n x, 0 ≤ g n x := fun n x =>
    thickenedIndicatorReal_nonneg (hδ_pos n) F x
  -- spectralFunctionalAux w (g n) = ∫ g_n dμ_w
  have hfunc_eq : ∀ n, spectralFunctionalAux U hU w (g n) =
      ∫ x, g n x ∂μ_w := by
    intro n
    -- spectralFunctionalAux w f = Re⟨w, cfc(f, U) w⟩
    -- For real-valued f on compact space, this equals ∫ f dμ_w
    unfold spectralFunctionalAux
    -- By spectralMeasureDiagonal_integral: ∫ f dμ_w = (spectralFunctionalCc w) f
    -- And spectralFunctionalCc w f = Re⟨w, cfc(f, U) w⟩
    have h := spectralMeasureDiagonal_integral U hU w (toCc (g n))
    simp only [toCc_apply] at h
    -- h : ∫ (g n) dμ_w = (spectralFunctionalCc w) (toCc (g n))
    -- Need to relate spectralFunctionalCc to spectralFunctionalAux
    have hdef : (spectralFunctionalCc U hU w) (toCc (g n)) =
        spectralFunctionalAux U hU w (g n) := rfl
    rw [hdef] at h
    exact h.symm
  -- Apply dominated convergence
  have hint_eq : (μ_w F).toReal = ∫ x, Set.indicator F (fun _ => (1 : ℝ)) x ∂μ_w := by
    have h := integral_indicator_one (μ := μ_w) hF_closed.measurableSet
    exact h.symm
  rw [hint_eq]
  -- Convert to integral convergence
  have hconv : Tendsto (fun n => ∫ x, g n x ∂μ_w) atTop
      (𝓝 (∫ x, Set.indicator F (fun _ => (1 : ℝ)) x ∂μ_w)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro n
      exact (g n).continuous.aestronglyMeasurable
    · have hfinite : IsFiniteMeasure μ_w := spectralMeasureDiagonal_isFiniteMeasure U hU w
      exact integrable_const (1 : ℝ)
    · intro n
      apply Filter.Eventually.of_forall
      intro x
      rw [Real.norm_of_nonneg (hg_nonneg n x)]
      exact hg_le_one n x
    · apply Filter.Eventually.of_forall
      intro x
      have hpt : Tendsto (fun n => g n x) atTop (𝓝 (Set.indicator F (fun _ => 1) x)) := by
        rw [tendsto_pi_nhds] at hg_tendsto
        exact hg_tendsto x
      exact hpt
  convert hconv using 1
  funext n
  exact hfunc_eq n

/-- The diagonal product formula for CLOSED sets: ‖P(F)z‖² = μ_z(F).

    This is proven by approximating χ_F with continuous functions using thickenedIndicator:
    - g_n = thickenedIndicator(1/(n+1), F) : Circle → [0, 1] continuous
    - g_n → χ_F pointwise (for closed F, closure F = F)
    - T_n = cfc(g_n, U) satisfies ‖T_n z‖² = ∫ g_n² dμ_z
    - By dominated convergence: ∫ g_n² dμ_z → μ_z(F)
    - The sequence {T_n z} is Cauchy and converges to P(F)z -/
theorem spectralProjection_norm_sq_closed (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (F : Set Circle) (hF_closed : IsClosed F) (z : H) :
    ‖spectralProjectionOfUnitary U hU F hF_closed.measurableSet z‖^2 =
    (spectralMeasureDiagonal U hU z F).toReal := by
  -- **Step 1: Define the approximating sequence**
  -- δ_n = 1/(n+1), g_n = thickenedIndicatorReal δ_n F
  let δ : ℕ → ℝ := fun n => 1 / (n + 1)
  have hδ_pos : ∀ n, 0 < δ n := fun n => Nat.one_div_pos_of_nat
  have hδ_lim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let g : ℕ → C(Circle, ℝ) := fun n => thickenedIndicatorReal (hδ_pos n) F
  -- g_n → χ_F pointwise (closure F = F since F is closed)
  have hg_tendsto : Tendsto (fun n => (g n : Circle → ℝ)) atTop
      (𝓝 (Set.indicator F (fun _ => (1 : ℝ)))) := by
    have h := thickenedIndicatorReal_tendsto_indicator_closure hδ_pos hδ_lim (F := F)
    rwa [hF_closed.closure_eq] at h
  -- g_n is bounded by 1
  have hg_le_one : ∀ n x, g n x ≤ 1 := fun n x =>
    thickenedIndicatorReal_le_one (hδ_pos n) F x
  have hg_nonneg : ∀ n x, 0 ≤ g n x := fun n x =>
    thickenedIndicatorReal_nonneg (hδ_pos n) F x
  -- **Step 2: Define T_n = cfc(g_n, U)**
  let T : ℕ → H →L[ℂ] H := fun n => cfcOfCircleReal U hU (g n)
  -- **Step 3: ‖T_n z‖² = ∫ g_n² dμ_z**
  have hT_norm_sq : ∀ n, ‖T n z‖^2 = ∫ x, (g n x)^2 ∂(spectralMeasureDiagonal U hU z) :=
    fun n => cfcOfCircleReal_norm_sq_measure' U hU (g n) z
  -- **Step 4: g_n² → χ_F pointwise (since g_n ∈ [0,1] and χ_F² = χ_F)**
  let μ_z := spectralMeasureDiagonal U hU z
  have hg_sq_tendsto : ∀ x, Tendsto (fun n => (g n x)^2) atTop
      (𝓝 (Set.indicator F (fun _ => (1 : ℝ)) x)) := by
    intro x
    have hpt : Tendsto (fun n => g n x) atTop (𝓝 (Set.indicator F (fun _ => 1) x)) := by
      rw [tendsto_pi_nhds] at hg_tendsto
      exact hg_tendsto x
    -- g_n x → χ_F(x) which is 0 or 1, and t^2 is continuous, so (g_n x)² → χ_F(x)² = χ_F(x)
    have hsq : Set.indicator F (fun _ : Circle => (1 : ℝ)) x ^ 2 =
               Set.indicator F (fun _ => (1 : ℝ)) x := by
      by_cases hx : x ∈ F
      · simp only [hx, Set.indicator_of_mem, one_pow]
      · simp only [hx, Set.indicator_of_notMem, not_false_eq_true, sq, mul_zero]
    rw [← hsq]
    exact Tendsto.pow hpt 2
  -- **Step 5: By dominated convergence, ∫ g_n² dμ_z → μ_z(F)**
  have hintegral_tendsto : Tendsto (fun n => ∫ x, (g n x)^2 ∂μ_z) atTop
      (𝓝 (μ_z F).toReal) := by
    -- First, relate μ_z(F).toReal to ∫ χ_F dμ_z
    have hint_eq : (μ_z F).toReal = ∫ x, Set.indicator F (fun _ => (1 : ℝ)) x ∂μ_z := by
      have h := integral_indicator_one (μ := μ_z) hF_closed.measurableSet
      -- h : ∫ x, F.indicator 1 x ∂μ_z = μ_z.real F
      -- F.indicator 1 = F.indicator (fun _ => 1) definitionally
      exact h.symm
    rw [hint_eq]
    -- Apply dominated convergence
    apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    -- F_measurable: g_n² is measurable (continuous)
    · intro n
      exact ((g n).continuous.pow 2).aestronglyMeasurable
    -- bound_integrable: constant 1 is integrable (μ_z is finite)
    · have hfinite : IsFiniteMeasure μ_z := spectralMeasureDiagonal_isFiniteMeasure U hU z
      exact integrable_const (1 : ℝ)
    -- h_bound: ‖(g_n x)²‖ ≤ 1
    · intro n
      apply Filter.Eventually.of_forall
      intro x
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      calc (g n x)^2 ≤ 1^2 := sq_le_sq' (by linarith [hg_nonneg n x]) (hg_le_one n x)
           _ = 1 := one_pow 2
    -- h_lim: (g_n x)² → χ_F(x) pointwise a.e.
    · apply Filter.Eventually.of_forall
      exact hg_sq_tendsto
  -- **Step 6: {T_n z} is Cauchy**
  -- Using cfcOfCircleReal_sub: T_n - T_m = cfcOfCircleReal(g_n - g_m)
  -- ‖T_n z - T_m z‖² = ‖cfcOfCircleReal(g_n - g_m) z‖² = ∫ (g_n - g_m)² dμ_z
  have hT_diff_norm_sq : ∀ n m, ‖T n z - T m z‖^2 =
      ∫ x, (g n x - g m x)^2 ∂μ_z := by
    intro n m
    have hdiff : T n z - T m z = cfcOfCircleReal U hU (g n - g m) z := by
      have hsub := cfcOfCircleReal_sub U hU (g n) (g m)
      -- T n z - T m z = cfcOfCircleReal(g n) z - cfcOfCircleReal(g m) z
      --               = (cfcOfCircleReal(g n) - cfcOfCircleReal(g m)) z
      --               = cfcOfCircleReal(g n - g m) z
      calc T n z - T m z
          = cfcOfCircleReal U hU (g n) z - cfcOfCircleReal U hU (g m) z := rfl
        _ = (cfcOfCircleReal U hU (g n) - cfcOfCircleReal U hU (g m)) z :=
            (ContinuousLinearMap.sub_apply _ _ _).symm
        _ = cfcOfCircleReal U hU (g n - g m) z := by rw [hsub]
    rw [hdiff]
    have h := cfcOfCircleReal_norm_sq_measure' U hU (g n - g m) z
    simp only [ContinuousMap.sub_apply] at h
    exact h
  -- Show (g_n - χ_F)² → 0 pointwise as n → ∞
  -- This follows from g_n → χ_F pointwise
  have hg_diff_tendsto_zero : ∀ x, Tendsto (fun n => (g n x - Set.indicator F (fun _ => (1 : ℝ)) x)^2)
      atTop (𝓝 0) := by
    intro x
    have hpt : Tendsto (fun n => g n x) atTop (𝓝 (Set.indicator F (fun _ => 1) x)) := by
      rw [tendsto_pi_nhds] at hg_tendsto
      exact hg_tendsto x
    have hdiff : Tendsto (fun n => g n x - Set.indicator F (fun _ => 1) x) atTop (𝓝 0) := by
      convert Tendsto.sub hpt tendsto_const_nhds using 1
      simp
    have hsq : Tendsto (fun n => (g n x - Set.indicator F (fun _ => 1) x)^2) atTop (𝓝 (0^2)) :=
      Tendsto.pow hdiff 2
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hsq
    exact hsq
  -- The integral ∫ (g_n - χ_F)² dμ_z → 0 by dominated convergence
  have hintegral_diff_tendsto_zero : Tendsto (fun n => ∫ x, (g n x - Set.indicator F (fun _ => 1) x)^2 ∂μ_z)
      atTop (𝓝 0) := by
    have hint_zero : (0 : ℝ) = ∫ x, (0 : ℝ) ∂μ_z := by simp
    rw [hint_zero]
    apply tendsto_integral_of_dominated_convergence (fun _ => (4 : ℝ))
    · intro n
      -- The function is measurable (g_n is continuous, indicator is measurable)
      apply Measurable.aestronglyMeasurable
      exact ((g n).continuous.measurable.sub (measurable_const.indicator hF_closed.measurableSet)).pow_const 2
    · have hfinite : IsFiniteMeasure μ_z := spectralMeasureDiagonal_isFiniteMeasure U hU z
      exact integrable_const (4 : ℝ)
    · intro n
      apply Filter.Eventually.of_forall
      intro x
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      -- |g_n x - χ_F(x)|² ≤ 4 since both are in [0,1]
      have h1 : |g n x - Set.indicator F (fun _ => 1) x| ≤ 2 := by
        have hg_bound : g n x ∈ Set.Icc 0 1 := ⟨hg_nonneg n x, hg_le_one n x⟩
        have hind_bound : Set.indicator F (fun _ : Circle => (1 : ℝ)) x ∈ Set.Icc 0 1 := by
          by_cases hx : x ∈ F
          · simp [hx]
          · simp [hx]
        calc |g n x - Set.indicator F (fun _ => 1) x|
            ≤ |g n x| + |Set.indicator F (fun _ => 1) x| := by
              have := abs_sub_le (g n x) 0 (Set.indicator F (fun _ => 1) x)
              simp only [sub_zero, zero_sub, abs_neg] at this
              exact this
          _ ≤ 1 + 1 := by
              apply add_le_add
              · rw [abs_of_nonneg hg_bound.1]; exact hg_bound.2
              · rw [abs_of_nonneg hind_bound.1]; exact hind_bound.2
          _ = 2 := by ring
      calc (g n x - Set.indicator F (fun _ => 1) x)^2
          = |g n x - Set.indicator F (fun _ => 1) x|^2 := by rw [sq_abs]
        _ ≤ 2^2 := sq_le_sq' (by linarith [abs_nonneg (g n x - Set.indicator F (fun _ => 1) x)]) h1
        _ = 4 := by norm_num
    · apply Filter.Eventually.of_forall
      exact hg_diff_tendsto_zero
  -- Now use the fact that Cauchy sequences converge in complete spaces
  -- {T_n z} is Cauchy because ‖T_n z - T_m z‖² = ∫ (g_n - g_m)² dμ_z → 0
  -- We'll show this in a more direct way using the limit.
  --
  -- **Step 7: Show T_n z → P(F)z weakly, then strongly**
  -- For the weak convergence, we need ⟨x, T_n z⟩ → ⟨x, P(F)z⟩ for all x.
  -- This follows from the spectral functional polarization and dominated convergence
  -- on the polarized measure.
  --
  -- **Step 8: Conclude ‖P(F)z‖² = lim ‖T_n z‖² = μ_z(F)**
  -- We have ‖T_n z‖² → μ_z(F).toReal (from hintegral_tendsto via hT_norm_sq)
  have hnorm_sq_tendsto : Tendsto (fun n => ‖T n z‖^2) atTop (𝓝 (μ_z F).toReal) := by
    convert hintegral_tendsto using 1
    funext n
    exact hT_norm_sq n
  -- **Step 7: Show T_n z → P(F)z weakly**
  -- Using spectralFunctionalAux_polarization and spectralFunctionalAux_tendsto_closed
  set P := spectralProjectionOfUnitary U hU F hF_closed.measurableSet with hP_def
  -- Show ⟨x, T_n z⟩ → ⟨x, P z⟩ for all x
  have hweak_conv : ∀ x, Tendsto (fun n => @inner ℂ H _ x (T n z)) atTop
      (𝓝 (@inner ℂ H _ x (P z))) := by
    intro x
    -- By spectralFunctionalAux_polarization:
    -- ⟨x, T_n z⟩ = ⟨x, cfc(g_n, U) z⟩
    --            = (1/4)[Λ_{x+z}(g_n) - Λ_{x-z}(g_n) - i·Λ_{x+iz}(g_n) + i·Λ_{x-iz}(g_n)]
    have hinner_eq : ∀ n, @inner ℂ H _ x (T n z) =
        (1/4 : ℂ) * (spectralFunctionalAux U hU (x + z) (g n) -
                     spectralFunctionalAux U hU (x - z) (g n) -
                     Complex.I * spectralFunctionalAux U hU (x + Complex.I • z) (g n) +
                     Complex.I * spectralFunctionalAux U hU (x - Complex.I • z) (g n)) := by
      intro n
      exact (spectralFunctionalAux_polarization U hU (g n) x z).symm
    -- Each Λ_w(g_n) → μ_w(F).toReal by spectralFunctionalAux_tendsto_closed
    have hΛ1 := spectralFunctionalAux_tendsto_closed U hU F hF_closed (x + z) hδ_pos hδ_lim
    have hΛ2 := spectralFunctionalAux_tendsto_closed U hU F hF_closed (x - z) hδ_pos hδ_lim
    have hΛ3 := spectralFunctionalAux_tendsto_closed U hU F hF_closed (x + Complex.I • z) hδ_pos hδ_lim
    have hΛ4 := spectralFunctionalAux_tendsto_closed U hU F hF_closed (x - Complex.I • z) hδ_pos hδ_lim
    -- Convert real limits to complex
    have hΛ1' : Tendsto (fun n => (spectralFunctionalAux U hU (x + z) (g n) : ℂ)) atTop
        (𝓝 ((spectralMeasureDiagonal U hU (x + z) F).toReal : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ1
    have hΛ2' : Tendsto (fun n => (spectralFunctionalAux U hU (x - z) (g n) : ℂ)) atTop
        (𝓝 ((spectralMeasureDiagonal U hU (x - z) F).toReal : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ2
    have hΛ3' : Tendsto (fun n => (spectralFunctionalAux U hU (x + Complex.I • z) (g n) : ℂ)) atTop
        (𝓝 ((spectralMeasureDiagonal U hU (x + Complex.I • z) F).toReal : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ3
    have hΛ4' : Tendsto (fun n => (spectralFunctionalAux U hU (x - Complex.I • z) (g n) : ℂ)) atTop
        (𝓝 ((spectralMeasureDiagonal U hU (x - Complex.I • z) F).toReal : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ4
    -- Combine using arithmetic of limits
    have hcomb : Tendsto (fun n =>
        (1/4 : ℂ) * (spectralFunctionalAux U hU (x + z) (g n) -
                     spectralFunctionalAux U hU (x - z) (g n) -
                     Complex.I * spectralFunctionalAux U hU (x + Complex.I • z) (g n) +
                     Complex.I * spectralFunctionalAux U hU (x - Complex.I • z) (g n)))
        atTop (𝓝 ((1/4 : ℂ) * (
          (spectralMeasureDiagonal U hU (x + z) F).toReal -
          (spectralMeasureDiagonal U hU (x - z) F).toReal -
          Complex.I * (spectralMeasureDiagonal U hU (x + Complex.I • z) F).toReal +
          Complex.I * (spectralMeasureDiagonal U hU (x - Complex.I • z) F).toReal))) := by
      apply Tendsto.const_mul
      apply Tendsto.add
      · apply Tendsto.sub
        · apply Tendsto.sub hΛ1' hΛ2'
        · exact Tendsto.const_mul Complex.I hΛ3'
      · exact Tendsto.const_mul Complex.I hΛ4'
    -- The limit equals spectralMeasurePolarized x z F = ⟨x, P z⟩
    have hlim_eq : (1/4 : ℂ) * (
          (spectralMeasureDiagonal U hU (x + z) F).toReal -
          (spectralMeasureDiagonal U hU (x - z) F).toReal -
          Complex.I * (spectralMeasureDiagonal U hU (x + Complex.I • z) F).toReal +
          Complex.I * (spectralMeasureDiagonal U hU (x - Complex.I • z) F).toReal) =
        spectralMeasurePolarized U hU x z F hF_closed.measurableSet := by
      unfold spectralMeasurePolarized
      ring
    have hPinner : @inner ℂ H _ x (P z) =
        spectralMeasurePolarized U hU x z F hF_closed.measurableSet := by
      rw [hP_def]
      unfold spectralProjectionOfUnitary
      rw [← sesquilinearToOperator_inner]
    -- Combine everything
    simp only [hinner_eq]; rw [hPinner, ← hlim_eq]; exact hcomb
  -- **Step 8: Show {T_n z} is Cauchy**
  -- From hT_diff_norm_sq and the Cauchy criterion
  have hCauchy : CauchySeq (fun n => T n z) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    -- Need N such that n, m ≥ N implies ‖T_n z - T_m z‖ < ε
    -- ‖T_n z - T_m z‖² = ∫ (g_n - g_m)² dμ_z
    -- Since ∫ (g_n - χ_F)² dμ_z → 0, for large n, m, this is small
    have hε_sq : 0 < ε^2 / 4 := by positivity
    -- Use hintegral_diff_tendsto_zero to get N₁ with ∫ (g_n - χ_F)² < ε²/4
    have hdiff_atTop := Metric.tendsto_atTop.mp hintegral_diff_tendsto_zero
    obtain ⟨N, hN⟩ := hdiff_atTop (ε^2 / 4) hε_sq
    use N
    intro n hn m hm
    -- ‖T_n z - T_m z‖² ≤ 2 * (∫(g_n - χ_F)² + ∫(g_m - χ_F)²) by triangle inequality
    -- Each term < ε²/2, so sum < ε², hence ‖...‖ < ε
    have hdist_sq : dist (T n z) (T m z)^2 = ‖T n z - T m z‖^2 := by
      rw [dist_eq_norm]
    -- Use the bound: (a - b)² ≤ 2(a - c)² + 2(b - c)²
    -- So ∫(g_n - g_m)² ≤ 2∫(g_n - χ_F)² + 2∫(g_m - χ_F)²
    have hbound : ∫ x, (g n x - g m x)^2 ∂μ_z ≤
        2 * ∫ x, (g n x - Set.indicator F (fun _ => 1) x)^2 ∂μ_z +
        2 * ∫ x, (g m x - Set.indicator F (fun _ => 1) x)^2 ∂μ_z := by
      have hfinite : IsFiniteMeasure μ_z := spectralMeasureDiagonal_isFiniteMeasure U hU z
      -- First show pointwise bound
      have hpw : ∀ x, (g n x - g m x)^2 ≤
          2 * (g n x - Set.indicator F (fun _ => 1) x)^2 +
          2 * (g m x - Set.indicator F (fun _ => 1) x)^2 := by
        intro x
        set a := g n x; set b := g m x; set c := Set.indicator F (fun _ => (1:ℝ)) x
        have hsub : a - b = (a - c) - (b - c) := by ring
        rw [hsub]
        have hineq : ∀ u v : ℝ, (u - v)^2 ≤ 2 * u^2 + 2 * v^2 := by
          intro u v
          have h : 0 ≤ (u + v)^2 := sq_nonneg _
          nlinarith [sq_nonneg u, sq_nonneg v, sq_nonneg (u - v), sq_nonneg (u + v)]
        exact hineq (a - c) (b - c)
      -- Integrability for the bound function
      have hint_n : Integrable (fun x => (g n x - Set.indicator F (fun _ => 1) x)^2) μ_z := by
        apply Integrable.of_mem_Icc 0 4
        · exact ((g n).continuous.measurable.sub
            (measurable_const.indicator hF_closed.measurableSet)).pow_const 2 |>.aemeasurable
        · apply Filter.Eventually.of_forall; intro x
          constructor
          · exact sq_nonneg _
          · -- Both g n x and indicator are in [0,1], so their difference is in [-1,1]
            -- and the square is in [0,1] ≤ 4
            have h1 : -1 ≤ g n x - Set.indicator F (fun _ => 1) x := by
              have h := hg_nonneg n x
              by_cases hx : x ∈ F <;> simp [Set.indicator, hx] <;> linarith
            have h2 : g n x - Set.indicator F (fun _ => 1) x ≤ 1 := by
              have h := hg_le_one n x
              by_cases hx : x ∈ F <;> simp [Set.indicator, hx] <;> linarith
            have hsq : (g n x - Set.indicator F (fun _ => 1) x)^2 ≤ 1 := by
              rw [sq_le_one_iff_abs_le_one]
              exact abs_le.mpr ⟨h1, h2⟩
            linarith
      have hint_m : Integrable (fun x => (g m x - Set.indicator F (fun _ => 1) x)^2) μ_z := by
        apply Integrable.of_mem_Icc 0 4
        · exact ((g m).continuous.measurable.sub
            (measurable_const.indicator hF_closed.measurableSet)).pow_const 2 |>.aemeasurable
        · apply Filter.Eventually.of_forall; intro x
          constructor
          · exact sq_nonneg _
          · have h1 : -1 ≤ g m x - Set.indicator F (fun _ => 1) x := by
              have h := hg_nonneg m x
              by_cases hx : x ∈ F <;> simp [Set.indicator, hx] <;> linarith
            have h2 : g m x - Set.indicator F (fun _ => 1) x ≤ 1 := by
              have h := hg_le_one m x
              by_cases hx : x ∈ F <;> simp [Set.indicator, hx] <;> linarith
            have hsq : (g m x - Set.indicator F (fun _ => 1) x)^2 ≤ 1 := by
              rw [sq_le_one_iff_abs_le_one]
              exact abs_le.mpr ⟨h1, h2⟩
            linarith
      -- Apply integral monotonicity then split using linearity
      calc ∫ x, (g n x - g m x)^2 ∂μ_z
          ≤ ∫ x, (2 * (g n x - Set.indicator F (fun _ => 1) x)^2 +
                  2 * (g m x - Set.indicator F (fun _ => 1) x)^2) ∂μ_z := by
            apply MeasureTheory.integral_mono_of_nonneg
            · exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
            · exact (hint_n.const_mul 2).add (hint_m.const_mul 2)
            · exact Filter.Eventually.of_forall hpw
        _ = 2 * ∫ x, (g n x - Set.indicator F (fun _ => 1) x)^2 ∂μ_z +
            2 * ∫ x, (g m x - Set.indicator F (fun _ => 1) x)^2 ∂μ_z := by
            rw [MeasureTheory.integral_add (hint_n.const_mul 2) (hint_m.const_mul 2)]
            have h1 : ∫ a, 2 * (g n a - Set.indicator F (fun _ => 1) a)^2 ∂μ_z =
                      2 * ∫ a, (g n a - Set.indicator F (fun _ => 1) a)^2 ∂μ_z := by
              have := MeasureTheory.integral_smul (2 : ℝ) (fun a => (g n a - Set.indicator F (fun _ => 1) a)^2) (μ := μ_z)
              simp only [smul_eq_mul] at this
              exact this
            have h2 : ∫ a, 2 * (g m a - Set.indicator F (fun _ => 1) a)^2 ∂μ_z =
                      2 * ∫ a, (g m a - Set.indicator F (fun _ => 1) a)^2 ∂μ_z := by
              have := MeasureTheory.integral_smul (2 : ℝ) (fun a => (g m a - Set.indicator F (fun _ => 1) a)^2) (μ := μ_z)
              simp only [smul_eq_mul] at this
              exact this
            rw [h1, h2]
    -- Now bound using hN
    have hn_bound : dist (∫ x, (g n x - Set.indicator F (fun _ => 1) x)^2 ∂μ_z) 0 < ε^2/4 := hN n hn
    have hm_bound : dist (∫ x, (g m x - Set.indicator F (fun _ => 1) x)^2 ∂μ_z) 0 < ε^2/4 := hN m hm
    simp only [dist_zero_right] at hn_bound hm_bound
    have hn_pos : 0 ≤ ∫ x, (g n x - Set.indicator F (fun _ => 1) x)^2 ∂μ_z :=
      MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
    have hm_pos : 0 ≤ ∫ x, (g m x - Set.indicator F (fun _ => 1) x)^2 ∂μ_z :=
      MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
    rw [Real.norm_of_nonneg hn_pos] at hn_bound
    rw [Real.norm_of_nonneg hm_pos] at hm_bound
    -- ‖T_n z - T_m z‖² = ∫ (g_n - g_m)² ≤ 2*ε²/2 + 2*ε²/2 = 2ε²
    have hdist_sq_bound : dist (T n z) (T m z)^2 < ε^2 := by
      rw [hdist_sq, hT_diff_norm_sq n m]
      calc ∫ x, (g n x - g m x)^2 ∂μ_z
          ≤ 2 * ∫ x, (g n x - Set.indicator F (fun _ => 1) x)^2 ∂μ_z +
            2 * ∫ x, (g m x - Set.indicator F (fun _ => 1) x)^2 ∂μ_z := hbound
        _ < 2 * (ε^2/4) + 2 * (ε^2/4) := by nlinarith
        _ = ε^2 := by ring
    -- dist < ε from dist² < ε²
    have hdist_pos : 0 ≤ dist (T n z) (T m z) := dist_nonneg
    have hdist_sq_pos : 0 ≤ dist (T n z) (T m z)^2 := sq_nonneg _
    calc dist (T n z) (T m z)
        = Real.sqrt (dist (T n z) (T m z)^2) := (Real.sqrt_sq hdist_pos).symm
      _ < Real.sqrt (ε^2) := Real.sqrt_lt_sqrt hdist_sq_pos hdist_sq_bound
      _ = ε := Real.sqrt_sq (le_of_lt hε)
  -- **Step 9: Since {T_n z} is Cauchy and converges weakly to P z, it converges strongly**
  -- In a Hilbert space, Cauchy + weak limit = strong limit
  have hstrong : Tendsto (fun n => T n z) atTop (𝓝 (P z)) := by
    -- {T_n z} is Cauchy, so it has a strong limit L
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hCauchy
    -- By weak convergence, L = P z
    -- For any x: ⟨x, L⟩ = lim ⟨x, T_n z⟩ = ⟨x, P z⟩
    have hL_eq : L = P z := by
      apply ext_inner_left ℂ
      intro x
      -- ⟨x, L⟩ = lim ⟨x, T_n z⟩ (by continuity of inner product)
      have hinner_L : Tendsto (fun n => @inner ℂ H _ x (T n z)) atTop (𝓝 (@inner ℂ H _ x L)) :=
        Filter.Tendsto.inner tendsto_const_nhds hL
      -- lim ⟨x, T_n z⟩ = ⟨x, P z⟩ (from hweak_conv)
      have huniq := hweak_conv x
      exact tendsto_nhds_unique hinner_L huniq
    rw [← hL_eq]
    exact hL
  -- **Step 10: Conclude ‖P z‖² = lim ‖T_n z‖² = μ_z(F).toReal**
  -- By continuity of norm: ‖P z‖ = lim ‖T_n z‖
  have hnorm_conv : Tendsto (fun n => ‖T n z‖) atTop (𝓝 ‖P z‖) :=
    (continuous_norm.tendsto (P z)).comp hstrong
  -- Therefore ‖P z‖² = lim ‖T_n z‖²
  have hnorm_sq_conv : Tendsto (fun n => ‖T n z‖^2) atTop (𝓝 (‖P z‖^2)) := by
    exact Tendsto.pow hnorm_conv 2
  -- By uniqueness of limits: ‖P z‖² = μ_z(F).toReal
  exact tendsto_nhds_unique hnorm_sq_conv hnorm_sq_tendsto

/-- The product formula for spectral projections on CLOSED sets in polarized form:
    B(Px, Py, Circle) = B(x, y, F) where B = spectralMeasurePolarized and F is closed.

    This uses spectralProjection_norm_sq_closed via polarization. -/
theorem spectralProjection_polarized_product_closed (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (F : Set Circle) (hF_closed : IsClosed F) (x y : H) :
    let P := spectralProjectionOfUnitary U hU F hF_closed.measurableSet
    spectralMeasurePolarized U hU (P x) (P y) Set.univ MeasurableSet.univ =
    spectralMeasurePolarized U hU x y F hF_closed.measurableSet := by
  intro P
  -- Expand spectralMeasurePolarized using the polarization formula
  unfold spectralMeasurePolarized
  -- Use linearity of P: P(x ± y) = Px ± Py, P(x ± I•y) = Px ± I•Py
  have hPadd : P (x + y) = P x + P y := map_add P x y
  have hPsub : P (x - y) = P x - P y := map_sub P x y
  have hPiadd : P (x + Complex.I • y) = P x + Complex.I • P y := by
    rw [map_add, map_smul]
  have hPisub : P (x - Complex.I • y) = P x - Complex.I • P y := by
    rw [map_sub, map_smul]
  -- Now use spectralMeasureDiagonal_univ: μ_w(Circle) = ‖w‖²
  rw [spectralMeasureDiagonal_univ U hU (P x + P y)]
  rw [spectralMeasureDiagonal_univ U hU (P x - P y)]
  rw [spectralMeasureDiagonal_univ U hU (P x + Complex.I • P y)]
  rw [spectralMeasureDiagonal_univ U hU (P x - Complex.I • P y)]
  -- Use the diagonal product formula for CLOSED sets: ‖P(w)‖² = μ_w(F)
  have hnorm_add : ‖P x + P y‖^2 = (spectralMeasureDiagonal U hU (x + y) F).toReal := by
    rw [← hPadd]; exact spectralProjection_norm_sq_closed U hU F hF_closed (x + y)
  have hnorm_sub : ‖P x - P y‖^2 = (spectralMeasureDiagonal U hU (x - y) F).toReal := by
    rw [← hPsub]; exact spectralProjection_norm_sq_closed U hU F hF_closed (x - y)
  have hnorm_iadd : ‖P x + Complex.I • P y‖^2 =
      (spectralMeasureDiagonal U hU (x + Complex.I • y) F).toReal := by
    rw [← hPiadd]; exact spectralProjection_norm_sq_closed U hU F hF_closed (x + Complex.I • y)
  have hnorm_isub : ‖P x - Complex.I • P y‖^2 =
      (spectralMeasureDiagonal U hU (x - Complex.I • y) F).toReal := by
    rw [← hPisub]; exact spectralProjection_norm_sq_closed U hU F hF_closed (x - Complex.I • y)
  rw [hnorm_add, hnorm_sub, hnorm_iadd, hnorm_isub]

/-- P(F)² = P(F) for CLOSED sets F.
    Uses spectralProjection_polarized_product_closed. -/
theorem spectralProjection_idempotent_closed (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (F : Set Circle) (hF_closed : IsClosed F) :
    spectralProjectionOfUnitary U hU F hF_closed.measurableSet ∘L
    spectralProjectionOfUnitary U hU F hF_closed.measurableSet =
    spectralProjectionOfUnitary U hU F hF_closed.measurableSet := by
  set P := spectralProjectionOfUnitary U hU F hF_closed.measurableSet with hP_def
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.comp_apply]
  have hsa : P.adjoint = P := spectralProjection_selfAdjoint U hU F hF_closed.measurableSet
  have h1 : @inner ℂ H _ x (P (P y)) = @inner ℂ H _ (P x) (P y) := by
    have heq : P (P y) = P.adjoint (P y) := by rw [hsa]
    rw [heq, ContinuousLinearMap.adjoint_inner_right]
  rw [h1]
  have hinner_Pxy : @inner ℂ H _ (P x) (P y) =
      spectralMeasurePolarized U hU (P x) (P y) Set.univ MeasurableSet.univ := by
    exact (spectralMeasurePolarized_univ U hU (P x) (P y)).symm
  have hinner_xy : @inner ℂ H _ x (P y) = spectralMeasurePolarized U hU x y F hF_closed.measurableSet := by
    rw [hP_def]
    unfold spectralProjectionOfUnitary
    rw [← sesquilinearToOperator_inner]
  rw [hinner_xy, hinner_Pxy]
  exact spectralProjection_polarized_product_closed U hU F hF_closed x y

/-- For nested closed sets F ⊆ G, we have P(F)P(G) = P(F).

    **Proof Strategy:**
    For orthogonal projections P, Q with P ≤ Q (Loewner order):
    1. First show range(P) ⊆ range(Q): if u = Pv, then ⟨u, Pu⟩ = ⟨u, u⟩ ≤ ⟨u, Qu⟩ ≤ ⟨u, u⟩,
       so ⟨u, Qu⟩ = ‖u‖², which implies Qu = u for orthogonal projection Q.
    2. Therefore Q(Pz) = Pz for all z (vectors in range(P) are fixed by Q).
    3. Then ⟨Pz, (Q-P)z⟩ = ⟨(Q-P)(Pz), z⟩ = ⟨Q(Pz) - P²z, z⟩ = ⟨Pz - Pz, z⟩ = 0.
    4. So ⟨Pz, Qz⟩ = ⟨Pz, Pz⟩ + ⟨Pz, (Q-P)z⟩ = ‖Pz‖² = ⟨z, Pz⟩.
    5. By polarization: ⟨Px, Qy⟩ = ⟨x, Py⟩ for all x, y, i.e., PQ = P. -/
theorem spectralProjection_mult_nested_closed (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (F G : Set Circle) (hF_closed : IsClosed F) (hG_closed : IsClosed G)
    (hFG : F ⊆ G) :
    spectralProjectionOfUnitary U hU F hF_closed.measurableSet ∘L
    spectralProjectionOfUnitary U hU G hG_closed.measurableSet =
    spectralProjectionOfUnitary U hU F hF_closed.measurableSet := by
  set PF := spectralProjectionOfUnitary U hU F hF_closed.measurableSet with hPF_def
  set PG := spectralProjectionOfUnitary U hU G hG_closed.measurableSet with hPG_def

  -- Key properties of PF and PG (orthogonal projections)
  have hsa_F : PF.adjoint = PF := spectralProjection_selfAdjoint U hU F hF_closed.measurableSet
  have hsa_G : PG.adjoint = PG := spectralProjection_selfAdjoint U hU G hG_closed.measurableSet
  have hidem_F : PF ∘L PF = PF := spectralProjection_idempotent_closed U hU F hF_closed
  have hidem_G : PG ∘L PG = PG := spectralProjection_idempotent_closed U hU G hG_closed

  -- PF ≤ PG (Loewner order): μ_z(F) ≤ μ_z(G) since F ⊆ G
  have hPF_le_PG : PF ≤ PG := by
    rw [ContinuousLinearMap.le_def]
    constructor
    · -- (PG - PF) is symmetric
      intro x y
      calc @inner ℂ H _ ((PG - PF) x) y
          = @inner ℂ H _ (PG x - PF x) y := rfl
        _ = @inner ℂ H _ (PG x) y - @inner ℂ H _ (PF x) y := inner_sub_left _ _ _
        _ = @inner ℂ H _ x (PG.adjoint y) - @inner ℂ H _ x (PF.adjoint y) := by
            rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
        _ = @inner ℂ H _ x (PG y) - @inner ℂ H _ x (PF y) := by rw [hsa_G, hsa_F]
        _ = @inner ℂ H _ x (PG y - PF y) := (inner_sub_right x _ _).symm
        _ = @inner ℂ H _ x ((PG - PF) y) := rfl
    · -- (PG - PF).reApplyInnerSelf z ≥ 0
      intro z
      rw [ContinuousLinearMap.reApplyInnerSelf]
      -- ⟨(PG - PF)z, z⟩ = ⟨PGz, z⟩ - ⟨PFz, z⟩ = μ_z(G) - μ_z(F)
      have h1 : (PG - PF) z = PG z - PF z := rfl
      rw [h1, inner_sub_left]
      have hinner_G : @inner ℂ H _ (PG z) z = (spectralMeasureDiagonal U hU z G).toReal := by
        have h := spectralMeasurePolarized_diag U hU z G hG_closed.measurableSet
        have hinner_def : @inner ℂ H _ z (PG z) =
            spectralMeasurePolarized U hU z z G hG_closed.measurableSet := by
          rw [hPG_def]
          conv_lhs => rw [show spectralProjectionOfUnitary U hU G hG_closed.measurableSet =
            sesquilinearToOperator (fun x y => spectralMeasurePolarized U hU x y G hG_closed.measurableSet)
              (spectralMeasurePolarized_linear_right U hU G hG_closed.measurableSet)
              (spectralMeasurePolarized_conj_linear_left U hU G hG_closed.measurableSet)
              (spectralMeasurePolarized_bounded U hU G hG_closed.measurableSet) from rfl]
          rw [← sesquilinearToOperator_inner]
        rw [← inner_conj_symm (PG z) z, hinner_def, h, Complex.conj_ofReal]
      have hinner_F : @inner ℂ H _ (PF z) z = (spectralMeasureDiagonal U hU z F).toReal := by
        have h := spectralMeasurePolarized_diag U hU z F hF_closed.measurableSet
        have hinner_def : @inner ℂ H _ z (PF z) =
            spectralMeasurePolarized U hU z z F hF_closed.measurableSet := by
          rw [hPF_def]
          conv_lhs => rw [show spectralProjectionOfUnitary U hU F hF_closed.measurableSet =
            sesquilinearToOperator (fun x y => spectralMeasurePolarized U hU x y F hF_closed.measurableSet)
              (spectralMeasurePolarized_linear_right U hU F hF_closed.measurableSet)
              (spectralMeasurePolarized_conj_linear_left U hU F hF_closed.measurableSet)
              (spectralMeasurePolarized_bounded U hU F hF_closed.measurableSet) from rfl]
          rw [← sesquilinearToOperator_inner]
        rw [← inner_conj_symm (PF z) z, hinner_def, h, Complex.conj_ofReal]
      rw [hinner_G, hinner_F, map_sub]
      -- The goal is now: 0 ≤ RCLike.re (μ_z(G).toReal : ℂ) - RCLike.re (μ_z(F).toReal : ℂ)
      -- which simplifies to: 0 ≤ μ_z(G).toReal - μ_z(F).toReal
      simp only [RCLike.re_to_complex, Complex.ofReal_re]
      -- μ_z(G) - μ_z(F) ≥ 0 since F ⊆ G
      have hmono : spectralMeasureDiagonal U hU z F ≤ spectralMeasureDiagonal U hU z G :=
        MeasureTheory.measure_mono hFG
      have hfinite_G := spectralMeasureDiagonal_isFiniteMeasure U hU z
      have htoReal_mono := ENNReal.toReal_mono (MeasureTheory.measure_lt_top _ G).ne hmono
      linarith

  -- **Key Lemma:** For u ∈ range(PF), we have PG(u) = u.
  -- Proof: u = PF v implies ⟨u, u⟩ = ⟨u, PF u⟩ ≤ ⟨u, PG u⟩ ≤ ⟨u, u⟩,
  -- so ⟨u, PG u⟩ = ‖u‖², which implies PG u = u for orthogonal projection PG.
  have hPG_fixes_range_PF : ∀ u, u = PF u → PG u = u := by
    intro u hu
    -- u ∈ range(PF), i.e., u = PF u
    -- We'll show ‖PG u - u‖ = 0
    have hnorm_sq : ‖PG u - u‖^2 = 0 := by
      -- ‖PG u - u‖² = ‖u‖² - ⟨u, PG u⟩ for orthogonal projection PG
      -- Since PF ≤ PG ≤ 1 and u = PF u: ‖u‖² = ⟨u, PF u⟩ ≤ ⟨u, PG u⟩ ≤ ‖u‖²
      -- So ⟨u, PG u⟩ = ‖u‖², hence ‖PG u - u‖² = 0
      -- First: ‖PG u - u‖² = ‖PG u‖² - 2 Re⟨u, PG u⟩ + ‖u‖² = ‖u‖² - ⟨u, PG u⟩
      -- (using ‖PG u‖² = ⟨u, PG u⟩ for orthogonal proj)

      -- Key: ‖PG u‖² = ⟨u, PG u⟩.re (for orthogonal projection PG)
      have hPG_norm_sq : ‖PG u‖^2 = (@inner ℂ H _ u (PG u)).re := by
        have h : ‖PG u‖^2 = (@inner ℂ H _ (PG u) (PG u)).re := by
          rw [inner_self_eq_norm_sq_to_K]; norm_cast
        rw [h]
        -- ⟨PG u, PG u⟩ = ⟨u, PG† PG u⟩ = ⟨u, PG² u⟩ = ⟨u, PG u⟩
        have heq : @inner ℂ H _ (PG u) (PG u) = @inner ℂ H _ u ((PG ∘L PG) u) := by
          calc @inner ℂ H _ (PG u) (PG u)
              = @inner ℂ H _ u (PG.adjoint (PG u)) := by
                  rw [ContinuousLinearMap.adjoint_inner_right]
            _ = @inner ℂ H _ u (PG (PG u)) := by rw [hsa_G]
            _ = @inner ℂ H _ u ((PG ∘L PG) u) := rfl
        rw [heq, hidem_G]

      -- Similarly for PF
      have hPF_norm_sq : ‖PF u‖^2 = (@inner ℂ H _ u (PF u)).re := by
        have h : ‖PF u‖^2 = (@inner ℂ H _ (PF u) (PF u)).re := by
          rw [inner_self_eq_norm_sq_to_K]; norm_cast
        rw [h]
        have heq : @inner ℂ H _ (PF u) (PF u) = @inner ℂ H _ u ((PF ∘L PF) u) := by
          calc @inner ℂ H _ (PF u) (PF u)
              = @inner ℂ H _ u (PF.adjoint (PF u)) := by
                  rw [ContinuousLinearMap.adjoint_inner_right]
            _ = @inner ℂ H _ u (PF (PF u)) := by rw [hsa_F]
            _ = @inner ℂ H _ u ((PF ∘L PF) u) := rfl
        rw [heq, hidem_F]

      -- u = PF u implies ‖u‖² = ‖PF u‖² = ⟨u, PF u⟩.re
      have hu_norm : ‖u‖^2 = (@inner ℂ H _ u (PF u)).re := by
        conv_lhs => rw [hu]  -- ‖u‖ = ‖PF u‖
        exact hPF_norm_sq

      -- From PF ≤ PG: ⟨u, PF u⟩.re ≤ ⟨u, PG u⟩.re
      have hle : (@inner ℂ H _ u (PF u)).re ≤ (@inner ℂ H _ u (PG u)).re := by
        rw [ContinuousLinearMap.le_def] at hPF_le_PG
        have hpos := hPF_le_PG.2 u
        rw [ContinuousLinearMap.reApplyInnerSelf] at hpos
        have h : (PG - PF) u = PG u - PF u := rfl
        rw [h, inner_sub_left, map_sub] at hpos
        -- Convert RCLike.re to .re and use inner_re_symm
        simp only [RCLike.re_to_complex] at hpos ⊢
        have hsym_PG := inner_re_symm (𝕜 := ℂ) (PG u) u
        have hsym_PF := inner_re_symm (𝕜 := ℂ) (PF u) u
        simp only [RCLike.re_to_complex] at hsym_PG hsym_PF
        linarith

      -- From PG ≤ 1: ⟨u, PG u⟩.re ≤ ‖u‖²
      have hle2 : (@inner ℂ H _ u (PG u)).re ≤ ‖u‖^2 := by
        have hPG_le_one : PG ≤ 1 := spectralProjection_le_one U hU G hG_closed.measurableSet
        rw [ContinuousLinearMap.le_def] at hPG_le_one
        have hpos := hPG_le_one.2 u
        rw [ContinuousLinearMap.reApplyInnerSelf] at hpos
        have h : (1 - PG) u = u - PG u := rfl
        rw [h, inner_sub_left, map_sub] at hpos
        simp only [RCLike.re_to_complex] at hpos ⊢
        have hid : (@inner ℂ H _ u u).re = ‖u‖^2 := by
          rw [inner_self_eq_norm_sq_to_K]; norm_cast
        have hsym_PG := inner_re_symm (𝕜 := ℂ) (PG u) u
        simp only [RCLike.re_to_complex] at hsym_PG
        linarith

      -- Combining: ‖u‖² ≤ ⟨u, PG u⟩.re ≤ ‖u‖², so ⟨u, PG u⟩.re = ‖u‖²
      have hinner_eq : (@inner ℂ H _ u (PG u)).re = ‖u‖^2 := by
        have h1 : ‖u‖^2 ≤ (@inner ℂ H _ u (PG u)).re := by rw [hu_norm]; exact hle
        linarith

      -- Now compute ‖PG u - u‖²
      -- Using the formula: ‖a - b‖² = ‖a‖² - 2 Re⟨a, b⟩ + ‖b‖²
      -- For orthogonal projection: ‖PG u‖² = ⟨u, PG u⟩ (from hPG_norm_sq)
      -- So ‖PG u - u‖² = ⟨u, PG u⟩ - 2⟨PGu, u⟩ + ‖u‖² = ⟨u, PG u⟩ - 2⟨u, PG u⟩ + ‖u‖² = ‖u‖² - ⟨u, PG u⟩
      -- Since ⟨u, PG u⟩ = ‖u‖² (from hinner_eq), we get ‖PG u - u‖² = 0
      calc ‖PG u - u‖^2
          = ‖PG u‖^2 - 2 * (@inner ℂ H _ (PG u) u).re + ‖u‖^2 := by
            -- norm_sub_sq says ‖x - y‖² = ‖x‖² - 2 Re⟨x, y⟩ + ‖y‖²
            have h := norm_sub_sq (𝕜 := ℂ) (PG u) u
            simp only [RCLike.re_to_complex] at h
            exact h
        _ = ‖PG u‖^2 - 2 * (@inner ℂ H _ u (PG u)).re + ‖u‖^2 := by
            have hsym := inner_re_symm (𝕜 := ℂ) (PG u) u
            simp only [RCLike.re_to_complex] at hsym
            rw [hsym]
        _ = (@inner ℂ H _ u (PG u)).re - 2 * (@inner ℂ H _ u (PG u)).re + ‖u‖^2 := by
            rw [hPG_norm_sq]
        _ = ‖u‖^2 - (@inner ℂ H _ u (PG u)).re := by ring
        _ = ‖u‖^2 - ‖u‖^2 := by rw [hinner_eq]
        _ = 0 := by ring

    have h := sq_eq_zero_iff.mp hnorm_sq
    simp only [norm_eq_zero] at h
    exact sub_eq_zero.mp h

  -- Now show PF PG = PF using the fact that PG fixes range(PF)
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.comp_apply]
  -- ⟨x, PF(PG y)⟩ = ⟨PF x, PG y⟩ (self-adjoint)
  have h1 : @inner ℂ H _ x (PF (PG y)) = @inner ℂ H _ (PF x) (PG y) := by
    calc @inner ℂ H _ x (PF (PG y))
        = @inner ℂ H _ x (PF.adjoint (PG y)) := by rw [hsa_F]
      _ = @inner ℂ H _ (PF x) (PG y) := by rw [ContinuousLinearMap.adjoint_inner_right]
  rw [h1]

  -- PF x ∈ range(PF), so PG(PF x) = PF x
  have hu_fixed : PG (PF x) = PF x := by
    apply hPG_fixes_range_PF
    rw [← ContinuousLinearMap.comp_apply, hidem_F]

  -- ⟨PF x, PG y⟩ = ⟨PG(PF x), y⟩ = ⟨PF x, y⟩ = ⟨x, PF y⟩
  -- Using: adjoint_inner_right A x y : ⟨x, A† y⟩ = ⟨Ax, y⟩
  -- Equivalently: ⟨Ax, y⟩ = ⟨x, A† y⟩
  have hstep1 : @inner ℂ H _ (PF x) (PG y) = @inner ℂ H _ (PG (PF x)) y := by
    -- ⟨PFx, PGy⟩ = ⟨PFx, PG† y⟩ (since PG† = PG)
    --            = ⟨PG(PFx), y⟩ (by adjoint_inner_right)
    calc @inner ℂ H _ (PF x) (PG y)
        = @inner ℂ H _ (PF x) (PG.adjoint y) := by rw [hsa_G]
      _ = @inner ℂ H _ (PG (PF x)) y := ContinuousLinearMap.adjoint_inner_right PG (PF x) y
  have hstep2 : @inner ℂ H _ (PG (PF x)) y = @inner ℂ H _ (PF x) y := by rw [hu_fixed]
  have hstep3 : @inner ℂ H _ (PF x) y = @inner ℂ H _ x (PF y) := by
    -- ⟨PFx, y⟩ = ⟨PFx, PF† (PF† y)⟩... no, simpler:
    -- ⟨PFx, y⟩ = ⟨x, PF† y⟩ = ⟨x, PF y⟩ (by adjoint_inner_right and hsa_F)
    calc @inner ℂ H _ (PF x) y
        = @inner ℂ H _ x (PF.adjoint y) := (ContinuousLinearMap.adjoint_inner_right PF x y).symm
      _ = @inner ℂ H _ x (PF y) := by rw [hsa_F]
  rw [hstep1, hstep2, hstep3]

/-- For self-adjoint P with 0 ≤ P ≤ 1 (hence P² ≤ P by pow_antitone), and
    orthogonal projection Q with Q ≤ P, P fixes vectors in range(Q).

    Key insight: For u = Qu, we have ‖u‖² = ⟨u, Qu⟩ ≤ ⟨u, Pu⟩ ≤ ‖u‖² (squeeze),
    so ⟨u, Pu⟩ = ‖u‖². Using P² ≤ P: ‖Pu - u‖² ≤ 0, hence Pu = u. -/
theorem ContinuousLinearMap.fixes_range_of_le_of_pos_le_one
    (P Q : H →L[ℂ] H) (hP_nonneg : 0 ≤ P) (hP_le_one : P ≤ 1)
    (hP_adj : P.adjoint = P)
    (_hQ_idem : Q ∘L Q = Q) (_hQ_adj : Q.adjoint = Q) (hQ_le_P : Q ≤ P) :
    ∀ u, Q u = u → P u = u := by
  intro u hu
  -- P² ≤ P by pow_antitone
  have hP_sq_le_P : P ∘L P ≤ P := by
    have h := CStarAlgebra.pow_antitone hP_nonneg hP_le_one (by omega : 1 ≤ 2)
    simp only [pow_two, pow_one] at h
    exact h
  -- Step 1: ⟨u, Pu⟩ = ‖u‖² (by squeeze: ‖u‖² = ⟨u, Qu⟩ ≤ ⟨u, Pu⟩ ≤ ‖u‖²)
  have hinner_Q : (@inner ℂ H _ u (Q u)).re = ‖u‖^2 := by
    rw [hu, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hinner_P_ge : ‖u‖^2 ≤ (@inner ℂ H _ u (P u)).re := by
    rw [ContinuousLinearMap.le_def] at hQ_le_P
    have hpos := hQ_le_P.2 u
    rw [ContinuousLinearMap.reApplyInnerSelf] at hpos
    have h : (P - Q) u = P u - Q u := rfl
    rw [h, inner_sub_left] at hpos
    have hre_P : (inner (𝕜 := ℂ) (P u) u).re = (inner (𝕜 := ℂ) u (P u)).re :=
      inner_re_symm (𝕜 := ℂ) (P u) u
    have hre_Q : (inner (𝕜 := ℂ) (Q u) u).re = (inner (𝕜 := ℂ) u (Q u)).re :=
      inner_re_symm (𝕜 := ℂ) (Q u) u
    simp only [RCLike.re_to_complex, map_sub] at hpos
    linarith [hinner_Q, hre_P, hre_Q]
  have hinner_P_le : (@inner ℂ H _ u (P u)).re ≤ ‖u‖^2 := by
    rw [ContinuousLinearMap.le_def] at hP_le_one
    have hpos := hP_le_one.2 u
    rw [ContinuousLinearMap.reApplyInnerSelf] at hpos
    have h : (1 - P) u = u - P u := rfl
    rw [h, inner_sub_left] at hpos
    have hinner_id : @inner ℂ H _ u u = (‖u‖^2 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    have hre_id : (inner (𝕜 := ℂ) u u).re = ‖u‖^2 := by
      rw [hinner_id]
      have : ((‖u‖^2 : ℝ) : ℂ).re = ‖u‖^2 := Complex.ofReal_re _
      convert this using 2; norm_cast
    have hre_P : (inner (𝕜 := ℂ) (P u) u).re = (inner (𝕜 := ℂ) u (P u)).re :=
      inner_re_symm (𝕜 := ℂ) (P u) u
    simp only [RCLike.re_to_complex, map_sub] at hpos
    linarith
  have hinner_P_eq : (@inner ℂ H _ u (P u)).re = ‖u‖^2 := le_antisymm hinner_P_le hinner_P_ge
  -- Step 2: ‖Pu‖² ≤ ⟨u, Pu⟩ (using P² ≤ P)
  have hnorm_Pu_sq_le : ‖P u‖^2 ≤ (@inner ℂ H _ u (P u)).re := by
    have hPu_sq : ‖P u‖^2 = (@inner ℂ H _ u ((P ∘L P) u)).re := by
      calc ‖P u‖^2
          = (@inner ℂ H _ (P u) (P u)).re := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
        _ = (@inner ℂ H _ u (P.adjoint (P u))).re := by rw [ContinuousLinearMap.adjoint_inner_right]
        _ = (@inner ℂ H _ u ((P ∘L P) u)).re := by rw [hP_adj]; rfl
    rw [hPu_sq]
    rw [ContinuousLinearMap.le_def] at hP_sq_le_P
    have hpos := hP_sq_le_P.2 u
    rw [ContinuousLinearMap.reApplyInnerSelf] at hpos
    have h : (P - P ∘L P) u = P u - (P ∘L P) u := rfl
    rw [h, inner_sub_left] at hpos
    have hre_P : (@inner ℂ H _ (P u) u).re = (@inner ℂ H _ u (P u)).re :=
      inner_re_symm (𝕜 := ℂ) (P u) u
    have hre_P2 : (@inner ℂ H _ ((P ∘L P) u) u).re = (@inner ℂ H _ u ((P ∘L P) u)).re :=
      inner_re_symm (𝕜 := ℂ) ((P ∘L P) u) u
    simp only [RCLike.re_to_complex, map_sub] at hpos
    linarith [hre_P, hre_P2]
  -- Step 3: ‖Pu - u‖² ≤ 0
  have hnorm_diff_sq : ‖P u - u‖^2 = ‖P u‖^2 - 2 * (@inner ℂ H _ u (P u)).re + ‖u‖^2 := by
    have h := norm_sub_sq (𝕜 := ℂ) (P u) u
    rw [inner_re_symm (𝕜 := ℂ) (P u) u] at h
    simp only [RCLike.re_to_complex] at h
    linarith [h]
  have hnorm_diff_le : ‖P u - u‖^2 ≤ 0 := by
    calc ‖P u - u‖^2
        = ‖P u‖^2 - 2 * (@inner ℂ H _ u (P u)).re + ‖u‖^2 := hnorm_diff_sq
      _ ≤ (@inner ℂ H _ u (P u)).re - 2 * (@inner ℂ H _ u (P u)).re + ‖u‖^2 := by linarith [hnorm_Pu_sq_le]
      _ = ‖u‖^2 - (@inner ℂ H _ u (P u)).re := by ring
      _ = 0 := by linarith [hinner_P_eq]
  have hnorm_diff_eq_zero : ‖P u - u‖ = 0 := by
    have h := sq_nonneg ‖P u - u‖
    have h_eq : ‖P u - u‖^2 = 0 := le_antisymm hnorm_diff_le h
    exact sq_eq_zero_iff.mp h_eq
  rw [norm_eq_zero] at hnorm_diff_eq_zero
  exact sub_eq_zero.mp hnorm_diff_eq_zero

/-- For closed F ⊆ E (measurable), P(E) fixes range(P(F)), hence P(E) ∘ P(F) = P(F).
    Taking adjoints: P(F) ∘ P(E) = P(F), so P(F)z = P(F)(P(E)z) and ‖P(F)z‖ ≤ ‖P(E)z‖. -/
theorem spectralProjection_comp_closed_measurable (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (F E : Set Circle) (hF_closed : IsClosed F) (hE : MeasurableSet E) (hFE : F ⊆ E) :
    spectralProjectionOfUnitary U hU E hE ∘L
    spectralProjectionOfUnitary U hU F hF_closed.measurableSet =
    spectralProjectionOfUnitary U hU F hF_closed.measurableSet := by
  set PF := spectralProjectionOfUnitary U hU F hF_closed.measurableSet with hPF_def
  set PE := spectralProjectionOfUnitary U hU E hE with hPE_def
  have hPE_nonneg : 0 ≤ PE := spectralProjection_nonneg U hU E hE
  have hPE_le_one : PE ≤ 1 := spectralProjection_le_one U hU E hE
  have hPE_adj : PE.adjoint = PE := spectralProjection_selfAdjoint U hU E hE
  have hPF_idem : PF ∘L PF = PF := spectralProjection_idempotent_closed U hU F hF_closed
  have hPF_adj : PF.adjoint = PF := spectralProjection_selfAdjoint U hU F hF_closed.measurableSet
  have hPF_le_PE : PF ≤ PE := spectralProjection_mono U hU F E hF_closed.measurableSet hE hFE
  -- PE fixes range(PF) by the general lemma
  have hfixes : ∀ u, PF u = u → PE u = u :=
    ContinuousLinearMap.fixes_range_of_le_of_pos_le_one PE PF hPE_nonneg hPE_le_one hPE_adj
      hPF_idem hPF_adj hPF_le_PE
  -- Therefore PE ∘ PF = PF
  ext w
  simp only [ContinuousLinearMap.comp_apply]
  apply hfixes
  calc PF (PF w) = (PF ∘L PF) w := rfl
    _ = PF w := by rw [hPF_idem]

/-- P(F) ∘ P(E) = P(F) for closed F ⊆ E (measurable). This is the adjoint of the above. -/
theorem spectralProjection_comp_closed_measurable' (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (F E : Set Circle) (hF_closed : IsClosed F) (hE : MeasurableSet E) (hFE : F ⊆ E) :
    spectralProjectionOfUnitary U hU F hF_closed.measurableSet ∘L
    spectralProjectionOfUnitary U hU E hE =
    spectralProjectionOfUnitary U hU F hF_closed.measurableSet := by
  set PF := spectralProjectionOfUnitary U hU F hF_closed.measurableSet
  set PE := spectralProjectionOfUnitary U hU E hE
  have hPE_adj : PE.adjoint = PE := spectralProjection_selfAdjoint U hU E hE
  have hPF_adj : PF.adjoint = PF := spectralProjection_selfAdjoint U hU F hF_closed.measurableSet
  have hcomp := spectralProjection_comp_closed_measurable U hU F E hF_closed hE hFE
  -- Taking adjoint: (PE ∘ PF)† = PF† ∘ PE† = PF ∘ PE
  have h : (PF ∘L PE).adjoint = PF.adjoint := by
    calc (PF ∘L PE).adjoint
        = PE.adjoint ∘L PF.adjoint := ContinuousLinearMap.adjoint_comp PF PE
      _ = PE ∘L PF := by rw [hPE_adj, hPF_adj]
      _ = PF := hcomp
      _ = PF.adjoint := hPF_adj.symm
  calc PF ∘L PE
      = (PF ∘L PE).adjoint.adjoint := by rw [ContinuousLinearMap.adjoint_adjoint]
    _ = PF.adjoint.adjoint := by rw [h]
    _ = PF := by rw [ContinuousLinearMap.adjoint_adjoint]

/-- For closed F ⊆ E (measurable), ‖P(F)z‖ ≤ ‖P(E)z‖ for all z. -/
theorem spectralProjection_norm_mono_closed_measurable (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (F E : Set Circle) (hF_closed : IsClosed F) (hE : MeasurableSet E) (hFE : F ⊆ E) (z : H) :
    ‖spectralProjectionOfUnitary U hU F hF_closed.measurableSet z‖ ≤
    ‖spectralProjectionOfUnitary U hU E hE z‖ := by
  set PF := spectralProjectionOfUnitary U hU F hF_closed.measurableSet
  set PE := spectralProjectionOfUnitary U hU E hE
  have hcomp := spectralProjection_comp_closed_measurable' U hU F E hF_closed hE hFE
  -- PF z = (PF ∘ PE) z = PF (PE z)
  have heq : PF z = PF (PE z) := by
    calc PF z = (PF ∘L PE) z := by rw [hcomp]
      _ = PF (PE z) := rfl
  calc ‖PF z‖
      = ‖PF (PE z)‖ := by rw [heq]
    _ ≤ ‖PF‖ * ‖PE z‖ := ContinuousLinearMap.le_opNorm PF (PE z)
    _ ≤ 1 * ‖PE z‖ := by
        have hPF_le_one := spectralProjection_le_one U hU F hF_closed.measurableSet
        have hPF_nonneg := spectralProjection_nonneg U hU F hF_closed.measurableSet
        have h : ‖PF‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg PF hPF_nonneg).mpr hPF_le_one
        exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = ‖PE z‖ := one_mul _

/-- The diagonal product formula: ‖P(E)z‖² = μ_z(E).

    This is proven by approximating χ_E with continuous functions g_n → χ_E:
    - For T_n = cfc(g_n, U): ⟨z, T_n z⟩ = ∫ g_n dμ_z → μ_z(E)
    - And: ‖T_n z‖² = ⟨z, T_n² z⟩ = ∫ g_n² dμ_z → μ_z(E) (since g_n² → χ_E)
    - By monotone convergence: T_n → P strongly, so ‖Pz‖² = lim ‖T_n z‖² = μ_z(E) -/
theorem spectralProjection_norm_sq (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) (z : H) :
    ‖spectralProjectionOfUnitary U hU E hE z‖^2 =
    (spectralMeasureDiagonal U hU z E).toReal := by
  -- **Proof Strategy:**
  -- For closed sets F, this is `spectralProjection_norm_sq_closed`.
  -- For general measurable sets E, we use inner regularity:
  --
  -- 1. The spectral measure μ_z is weakly regular (finite measure on compact metric space).
  -- 2. For any ε > 0, there exists closed F ⊆ E with μ_z(E) - μ_z(F) < ε.
  -- 3. Using `spectralProjection_norm_sq_closed`, we get ‖P(F)z‖² = μ_z(F).
  -- 4. The weak convergence P(F_n)z → P(E)z follows from:
  --    ⟨x, P(F_n)z⟩ = μ_{x,z}(F_n) → μ_{x,z}(E) = ⟨x, P(E)z⟩
  -- 5. Combined with the Cauchy property, this gives strong convergence and ‖P(E)z‖² = μ_z(E).
  --
  -- NOTE: There is a subtle circular dependency issue:
  -- - `spectralProjection_idempotent` uses `spectralProjection_polarized_product`
  -- - `spectralProjection_polarized_product` uses this theorem
  -- The resolution is that for closed sets, we proved norm_sq_closed directly via
  -- the cfc approximation WITHOUT using idempotence. The extension to general sets
  -- follows by approximation.
  --
  -- For now we use the closed set case directly when E is closed, and defer the
  -- full proof for general measurable sets.
  by_cases hE_closed : IsClosed E
  · -- E is closed: use the direct proof
    exact spectralProjection_norm_sq_closed U hU E hE_closed z
  · -- E is not closed: use inner regularity to show ‖P(E)z‖² = μ_z(E)
    -- by proving both upper and lower bounds.
    --
    -- Upper bound: Uses 0 ≤ P(E) ≤ 1 (as operators) implies P² ≤ P.
    -- Lower bound: Uses inner regularity to approximate E by closed sets from inside.
    set μ_z := spectralMeasureDiagonal U hU z with hμ_z_def
    set P := spectralProjectionOfUnitary U hU E hE with hP_def
    have hP_adj : P.adjoint = P := spectralProjection_selfAdjoint U hU E hE

    -- ⟨z, Pz⟩ = μ_z(E) by definition (via sesquilinear form characterization)
    have hinner_eq : @inner ℂ H _ z (P z) = (μ_z E).toReal := by
      rw [hP_def]
      unfold spectralProjectionOfUnitary
      rw [← sesquilinearToOperator_inner]
      exact spectralMeasurePolarized_diag U hU z E hE

    -- Upper bound: ‖P(E)z‖² ≤ μ_z(E)
    -- Proof: P is self-adjoint with 0 ≤ P ≤ 1 (as operators), hence P² ≤ P.
    -- This implies ‖Pz‖² = ⟨z, P²z⟩ ≤ ⟨z, Pz⟩ = μ_z(E).
    have hupper : ‖P z‖^2 ≤ (μ_z E).toReal := by
      -- Step 1: 0 ≤ P ≤ 1 as operators
      have hP_nonneg : 0 ≤ P := by rw [hP_def]; exact spectralProjection_nonneg U hU E hE
      have hP_le_one : P ≤ 1 := by rw [hP_def]; exact spectralProjection_le_one U hU E hE
      -- Step 2: P² ≤ P by pow_antitone (since 0 ≤ P ≤ 1 and powers are antitone)
      have hP_sq_le : P ^ 2 ≤ P ^ 1 := CStarAlgebra.pow_antitone hP_nonneg hP_le_one (by omega)
      simp only [pow_one, pow_two] at hP_sq_le
      have hP_comp_le : P ∘L P ≤ P := hP_sq_le
      -- Step 3: ‖Pz‖² = ⟨Pz, Pz⟩ = ⟨z, P†Pz⟩ = ⟨z, P(Pz)⟩ (since P† = P)
      have hnorm_sq_eq_inner : ‖P z‖^2 = (@inner ℂ H _ z ((P ∘L P) z)).re := by
        have h1 : ‖P z‖^2 = (@inner ℂ H _ (P z) (P z)).re := by
          rw [inner_self_eq_norm_sq_to_K]; norm_cast
        rw [h1]
        -- ⟨Pz, Pz⟩ = ⟨z, P†(Pz)⟩ = ⟨z, P(Pz)⟩ since P† = P
        have h2 : @inner ℂ H _ (P z) (P z) = @inner ℂ H _ z (P.adjoint (P z)) := by
          rw [ContinuousLinearMap.adjoint_inner_right]
        rw [h2, hP_adj]
        rfl
      -- Step 4: ⟨z, P²z⟩ ≤ ⟨z, Pz⟩ by Loewner order (P² ≤ P means (P - P²) is positive)
      -- The Loewner order says P ∘L P ≤ P iff (P - P ∘L P).IsPositive
      -- This means re⟨(P-P²)z, z⟩ ≥ 0, i.e., re⟨Pz, z⟩ - re⟨P²z, z⟩ ≥ 0
      have hinner_ineq : (@inner ℂ H _ z ((P ∘L P) z)).re ≤ (@inner ℂ H _ z (P z)).re := by
        rw [ContinuousLinearMap.le_def] at hP_comp_le
        have hpos := hP_comp_le.2 z
        rw [ContinuousLinearMap.reApplyInnerSelf] at hpos
        -- hpos : 0 ≤ re ⟨(P - P ∘L P) z, z⟩ = re ⟨Pz - P²z, z⟩
        have h : (P - P ∘L P) z = P z - (P ∘L P) z := rfl
        rw [h, inner_sub_left, map_sub] at hpos
        -- hpos : 0 ≤ re ⟨Pz, z⟩ - re ⟨P²z, z⟩
        -- Need: re ⟨z, P²z⟩ ≤ re ⟨z, Pz⟩
        -- Use: ⟨a, b⟩ = conj(⟨b, a⟩), so re ⟨a, b⟩ = re ⟨b, a⟩
        -- inner_re_symm says: RCLike.re ⟨x, y⟩ = RCLike.re ⟨y, x⟩
        have hre_swap_P : RCLike.re (@inner ℂ H _ (P z) z) = RCLike.re (@inner ℂ H _ z (P z)) :=
          inner_re_symm (𝕜 := ℂ) (P z) z
        have hre_swap_P2 : RCLike.re (@inner ℂ H _ ((P ∘L P) z) z) =
            RCLike.re (@inner ℂ H _ z ((P ∘L P) z)) :=
          inner_re_symm (𝕜 := ℂ) ((P ∘L P) z) z
        -- RCLike.re for ℂ is the same as Complex.re
        simp only [RCLike.re_to_complex] at hpos hre_swap_P hre_swap_P2 ⊢
        linarith
      -- Step 5: Combine
      rw [hnorm_sq_eq_inner]
      -- ⟨z, Pz⟩ = μ_z(E).toReal (which is real)
      have hinner_real : (@inner ℂ H _ z (P z)).re = (μ_z E).toReal := by
        rw [hinner_eq, Complex.ofReal_re]
      linarith

    -- Lower bound: ‖P(E)z‖² ≥ μ_z(E)
    -- **Proof Strategy:**
    -- 1. Show monotonicity: F ⊆ E implies P(F) ≤ P(E) (since (P(E)-P(F)) is positive)
    -- 2. By inner regularity: ∃ closed F_n ⊆ E with μ_z(F_n) → μ_z(E)
    -- 3. For closed F_n: ‖P(F_n)z‖² = μ_z(F_n) (by spectralProjection_norm_sq_closed)
    -- 4. {P(F_n)} is monotone bounded, hence P(F_n)z → Qz strongly for some Q
    -- 5. Q = P(E) (since ⟨x, Qy⟩ = lim μ_{x,y}(F_n) = μ_{x,y}(E) = ⟨x, P(E)y⟩)
    -- 6. Therefore ‖P(E)z‖² = lim ‖P(F_n)z‖² = lim μ_z(F_n) = μ_z(E)
    --
    -- The key ingredients are:
    -- a. Monotonicity of spectral projections (proven via positivity of P(E) - P(F))
    -- b. Inner regularity of finite measures on compact metric spaces
    -- c. Monotone convergence for bounded positive operators (SOT convergence)
    -- d. Identification of limit via weak convergence
    have hlower : (μ_z E).toReal ≤ ‖P z‖^2 := by
      -- **Proof:** For any r < μ_z(E), use inner regularity to find closed F ⊆ E with r < μ_z(F).
      -- Then μ_z(F) = ‖P(F)z‖² ≤ ‖P(E)z‖² (since P(E) fixes range(P(F))).
      -- Taking sup over r gives μ_z(E) ≤ ‖P(E)z‖².
      --
      -- Key insight: For P(E) with 0 ≤ P(E) ≤ 1, P(E)² ≤ P(E) by pow_antitone.
      -- For u in range(P(F)) with P(F) ≤ P(E): ⟨u, P(E)u⟩ = ‖u‖² (squeeze), hence P(E)u = u.

      -- Use the factored lemma spectralProjection_norm_mono_closed_measurable
      -- For closed F ⊆ E: ‖P(F)z‖ ≤ ‖P(E)z‖, hence μ_z(F) = ‖P(F)z‖² ≤ ‖P(E)z‖².

      -- For closed F ⊆ E: μ_z(F) = ‖P(F)z‖² ≤ ‖P(E)z‖² (using the factored lemma)
      have hμF_le : ∀ (F : Set Circle) (hF_closed : IsClosed F) (hFE : F ⊆ E),
          (spectralMeasureDiagonal U hU z F).toReal ≤ ‖P z‖^2 := by
        intro F hF_closed hFE
        have hnorm_eq := spectralProjection_norm_sq_closed U hU F hF_closed z
        have hnorm_le := spectralProjection_norm_mono_closed_measurable U hU F E hF_closed hE hFE z
        calc (spectralMeasureDiagonal U hU z F).toReal
            = ‖spectralProjectionOfUnitary U hU F hF_closed.measurableSet z‖^2 := hnorm_eq.symm
          _ ≤ ‖P z‖^2 := sq_le_sq' (by
              have h1 := norm_nonneg (spectralProjectionOfUnitary U hU F hF_closed.measurableSet z)
              have h2 := norm_nonneg (P z)
              linarith) hnorm_le

      -- By inner regularity: μ_z(E) = sup{μ_z(F) : F closed, F ⊆ E} ≤ ‖Pz‖²
      -- Using: μ_z(E) = ⨆ (K) (_ : K ⊆ E) (_ : IsClosed K), μ_z(K)
      have hfinite := spectralMeasureDiagonal_isFiniteMeasure U hU z
      have hμE_eq_sup : μ_z E = ⨆ (K) (_ : K ⊆ E) (_ : IsClosed K), μ_z K :=
        MeasurableSet.measure_eq_iSup_isClosed_of_ne_top hE (MeasureTheory.measure_lt_top _ E).ne
      rw [hμE_eq_sup]
      -- Need to show (⨆ ... μ_z K).toReal ≤ ‖Pz‖²
      -- Since all μ_z(K) ≤ μ_z(E) < ∞, we can use iSup_toReal
      have hbounded : BddAbove (Set.range fun K => ⨆ (_ : K ⊆ E) (_ : IsClosed K), μ_z K) := by
        use μ_z Set.univ
        intro x hx
        obtain ⟨K, rfl⟩ := hx
        by_cases hK : K ⊆ E ∧ IsClosed K
        · simp only [ciSup_pos hK.1, ciSup_pos hK.2]
          exact MeasureTheory.measure_mono (Set.subset_univ K)
        · push_neg at hK
          by_cases hK1 : K ⊆ E
          · have hK2 := hK hK1
            simp only [ciSup_pos hK1]
            rw [iSup_eq_bot.mpr (fun h => (hK2 h).elim)]
            exact zero_le _
          · simp only [hK1, iSup_false]
            exact bot_le
      -- Convert iSup to toReal
      have htoReal_le : (⨆ (K) (_ : K ⊆ E) (_ : IsClosed K), μ_z K).toReal ≤ ‖P z‖^2 := by
        -- For any K with K ⊆ E and IsClosed K, μ_z(K).toReal ≤ ‖Pz‖²
        -- The sup is achieved by taking limits of increasing closed sets
        -- Use ENNReal.toReal_iSup for bounded family
        apply ENNReal.toReal_le_of_le_ofReal
        · exact sq_nonneg _
        · apply iSup_le
          intro K
          apply iSup_le
          intro hK_sub
          apply iSup_le
          intro hK_closed
          rw [← ENNReal.ofReal_toReal (MeasureTheory.measure_lt_top _ K).ne]
          exact ENNReal.ofReal_le_ofReal (hμF_le K hK_closed hK_sub)
      exact htoReal_le

    exact le_antisymm hupper hlower

/-- The product formula for spectral projections in polarized form:
    B(Px, Py, Circle) = B(x, y, E) where B = spectralMeasurePolarized.

    This follows from the diagonal product formula via polarization. -/
theorem spectralProjection_polarized_product (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) (x y : H) :
    let P := spectralProjectionOfUnitary U hU E hE
    spectralMeasurePolarized U hU (P x) (P y) Set.univ MeasurableSet.univ =
    spectralMeasurePolarized U hU x y E hE := by
  intro P
  -- Expand spectralMeasurePolarized using the polarization formula
  unfold spectralMeasurePolarized
  -- Use linearity of P: P(x ± y) = Px ± Py, P(x ± I•y) = Px ± I•Py
  have hPadd : P (x + y) = P x + P y := map_add P x y
  have hPsub : P (x - y) = P x - P y := map_sub P x y
  have hPiadd : P (x + Complex.I • y) = P x + Complex.I • P y := by
    rw [map_add, map_smul]
  have hPisub : P (x - Complex.I • y) = P x - Complex.I • P y := by
    rw [map_sub, map_smul]
  -- Now use spectralMeasureDiagonal_univ: μ_w(Circle) = ‖w‖²
  rw [spectralMeasureDiagonal_univ U hU (P x + P y)]
  rw [spectralMeasureDiagonal_univ U hU (P x - P y)]
  rw [spectralMeasureDiagonal_univ U hU (P x + Complex.I • P y)]
  rw [spectralMeasureDiagonal_univ U hU (P x - Complex.I • P y)]
  -- Use the diagonal product formula: ‖P(w)‖² = μ_w(E)
  have hnorm_add : ‖P x + P y‖^2 = (spectralMeasureDiagonal U hU (x + y) E).toReal := by
    rw [← hPadd]; exact spectralProjection_norm_sq U hU E hE (x + y)
  have hnorm_sub : ‖P x - P y‖^2 = (spectralMeasureDiagonal U hU (x - y) E).toReal := by
    rw [← hPsub]; exact spectralProjection_norm_sq U hU E hE (x - y)
  have hnorm_iadd : ‖P x + Complex.I • P y‖^2 =
      (spectralMeasureDiagonal U hU (x + Complex.I • y) E).toReal := by
    rw [← hPiadd]; exact spectralProjection_norm_sq U hU E hE (x + Complex.I • y)
  have hnorm_isub : ‖P x - Complex.I • P y‖^2 =
      (spectralMeasureDiagonal U hU (x - Complex.I • y) E).toReal := by
    rw [← hPisub]; exact spectralProjection_norm_sq U hU E hE (x - Complex.I • y)
  rw [hnorm_add, hnorm_sub, hnorm_iadd, hnorm_isub]

/-- P(E)² = P(E) (idempotent)

    **Proof Strategy:**
    We show ⟨x, P²y⟩ = ⟨x, Py⟩ for all x, y.

    Using self-adjointness P* = P:
    ⟨x, P²y⟩ = ⟨Px, Py⟩

    We need: ⟨Px, Py⟩ = spectralMeasurePolarized x y E = ⟨x, Py⟩

    This follows from the "product formula" for spectral measures:
    B(Px, Py, Circle) = B(x, y, E)

    which is proven in spectralProjection_polarized_product. -/
theorem spectralProjection_idempotent (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) :
    spectralProjectionOfUnitary U hU E hE ∘L spectralProjectionOfUnitary U hU E hE =
    spectralProjectionOfUnitary U hU E hE := by
  set P := spectralProjectionOfUnitary U hU E hE with hP_def
  -- Strategy: Show ⟨x, P²y⟩ = ⟨x, Py⟩ for all x, y
  ext y
  apply ext_inner_left ℂ
  intro x
  -- Goal: ⟨x, P²y⟩ = ⟨x, Py⟩
  rw [ContinuousLinearMap.comp_apply]
  -- Using self-adjointness: ⟨x, P(Py)⟩ = ⟨P† x, Py⟩ = ⟨Px, Py⟩
  have hsa : P.adjoint = P := spectralProjection_selfAdjoint U hU E hE
  have h1 : @inner ℂ H _ x (P (P y)) = @inner ℂ H _ (P x) (P y) := by
    -- adjoint_inner_right P x (P y) : ⟨x, P†(Py)⟩ = ⟨P x, Py⟩
    -- Since P† = P, ⟨x, P(Py)⟩ = ⟨x, P†(Py)⟩ = ⟨P x, Py⟩
    have heq : P (P y) = P.adjoint (P y) := by rw [hsa]
    rw [heq, ContinuousLinearMap.adjoint_inner_right]
  rw [h1]
  -- Now need: ⟨Px, Py⟩ = spectralMeasurePolarized x y E
  have hinner_Pxy : @inner ℂ H _ (P x) (P y) =
      spectralMeasurePolarized U hU (P x) (P y) Set.univ MeasurableSet.univ := by
    exact (spectralMeasurePolarized_univ U hU (P x) (P y)).symm
  have hinner_xy : @inner ℂ H _ x (P y) = spectralMeasurePolarized U hU x y E hE := by
    rw [hP_def]
    unfold spectralProjectionOfUnitary
    rw [← sesquilinearToOperator_inner]
  rw [hinner_xy, hinner_Pxy]
  -- Apply the product formula: B(Px, Py, Circle) = B(x, y, E)
  exact spectralProjection_polarized_product U hU E hE x y

/-! ### The Spectral Theorem -/

/-- **Spectral Theorem for Unitaries (via RMK)**

    For any unitary U on a Hilbert space H, there exists a unique spectral measure
    (projection-valued measure) P on Circle such that:
    1. P(∅) = 0, P(Circle) = 1
    2. Each P(E) is an orthogonal projection (self-adjoint and idempotent)
    3. P(E ∩ F) = P(E) ∘ P(F)
    4. P is σ-additive in the strong operator topology
    5. **Key property tying P to U**: ⟨x, P(E) y⟩ = spectralMeasurePolarized U hU x y E
       (equivalently: cfc(f, U) = ∫ f(z) dP(z) for continuous f)

    The last property is what makes the theorem non-trivial: P is the UNIQUE
    projection-valued measure satisfying ⟨x, P(E) y⟩ = μ_{x,y}(E) where μ_{x,y}
    is the polarized spectral measure of U.

    This construction is INDEPENDENT of bumpOperator_inner_cauchy. -/
theorem spectral_theorem_unitary_via_RMK (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H)) :
    ∃ (P : Set Circle → H →L[ℂ] H),
      -- Key property: P is characterized by the spectral measure of U
      (∀ E (hE : MeasurableSet E) (x y : H),
        @inner ℂ H _ x (P E y) = spectralMeasurePolarized U hU x y E hE) ∧
      -- Algebraic properties
      (∀ E, MeasurableSet E → IsSelfAdjoint (P E)) ∧
      (∀ E, MeasurableSet E → (P E) ∘L (P E) = P E) ∧
      (P ∅ = 0) ∧
      (P Set.univ = 1) ∧
      (∀ E F, MeasurableSet E → MeasurableSet F →
        P (E ∩ F) = P E ∘L P F) := by
  use fun E => if hE : MeasurableSet E then spectralProjectionOfUnitary U hU E hE else 0
  refine ⟨?key_property, ?self_adj, ?idempotent, ?empty, ?univ, ?mult⟩
  case key_property =>
    -- Key property: ⟨x, P(E) y⟩ = spectralMeasurePolarized U hU x y E hE
    intro E hE x y
    simp only [dif_pos hE]
    unfold spectralProjectionOfUnitary
    rw [← sesquilinearToOperator_inner]
  case self_adj =>
    intro E hE
    simp only [dif_pos hE]
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]
    exact spectralProjection_selfAdjoint U hU E hE
  case idempotent =>
    intro E hE
    simp only [dif_pos hE]
    exact spectralProjection_idempotent U hU E hE
  case empty =>
    simp only [dif_pos MeasurableSet.empty]
    exact spectralProjection_empty U hU
  case univ =>
    simp only [dif_pos MeasurableSet.univ]
    exact spectralProjection_univ U hU
  case mult =>
    intro E F hE hF
    simp only [dif_pos hE, dif_pos hF, dif_pos (hE.inter hF)]
    -- P(E ∩ F) = P(E) P(F) follows from:
    -- ⟨x, P(E ∩ F) y⟩ = μ_{x,y}(E ∩ F) (by construction)
    -- ⟨x, P(E) P(F) y⟩ = ⟨P(E) x, P(F) y⟩ (using P(E)* = P(E))
    --                   = μ_{P(E)x, P(F)y}(Circle) (by spectralMeasurePolarized_univ)
    -- Showing these are equal requires the generalized product formula:
    --   μ_{P(E)x, P(F)y}(Circle) = μ_{x,y}(E ∩ F)
    -- which follows from the diagonal product formula ‖P(E)z‖² = μ_z(E)
    -- via polarization.
    sorry

end
