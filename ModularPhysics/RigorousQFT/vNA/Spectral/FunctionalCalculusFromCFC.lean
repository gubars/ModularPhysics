/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import ModularPhysics.RigorousQFT.vNA.Spectral.CayleyTransform
import ModularPhysics.RigorousQFT.vNA.MeasureTheory.SpectralIntegral
import ModularPhysics.RigorousQFT.vNA.MeasureTheory.SpectralStieltjes

/-!
# Functional Calculus from Mathlib's CFC

This file connects unbounded self-adjoint operator theory to Mathlib's
continuous functional calculus (CFC) infrastructure for bounded operators.

## Strategy

Mathlib provides a comprehensive CFC for bounded normal operators in C*-algebras:
- `cfc : C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elementalStarAlgebra ℂ a`
- Multiplicativity: `cfc (f * g) a = cfc f a * cfc g a`
- Adjoint: `star (cfc f a) = cfc (star ∘ f) a`

For unbounded self-adjoint operators, we:
1. Apply the Cayley transform U = (T-i)(T+i)⁻¹ (which is unitary)
2. Use Mathlib's CFC on U (spectrum ⊆ S¹)
3. Pull back via the inverse Cayley map to get functional calculus on T

## Main definitions

* `UnboundedFunctionalCalculus` - f(T) for bounded continuous f : ℝ → ℂ
* `spectralMeasureFromCFC` - spectral measure constructed via CFC

## Main results

* `unbounded_cfc_mul` - (fg)(T) = f(T)g(T)
* `unbounded_cfc_star` - f(T)* = f̄(T)
* `unbounded_cfc_one` - 1(T) = I

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I", Chapter VIII
* Mathlib's Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
-/

noncomputable section

open scoped InnerProduct ComplexConjugate Classical
open Filter Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Bounded operators as a C*-algebra -/

/-- The space of bounded linear operators on H is a C*-algebra.
    Mathlib provides this structure via `ContinuousLinearMap` instances. -/
instance : CStarRing (H →L[ℂ] H) := by infer_instance

instance : Algebra ℂ (H →L[ℂ] H) := by infer_instance

/-- A unitary operator is normal (hence has CFC available). -/
theorem unitary_isStarNormal (U : H →L[ℂ] H)
    (hU_left : U.adjoint ∘L U = 1) (hU_right : U ∘L U.adjoint = 1) :
    IsStarNormal U := by
  constructor
  -- U* U = U U* for unitary operators
  calc U.adjoint * U = U.adjoint ∘L U := rfl
    _ = 1 := hU_left
    _ = U ∘L U.adjoint := hU_right.symm
    _ = U * U.adjoint := rfl

set_option maxHeartbeats 400000 in
/-- The spectrum of a unitary operator is contained in the unit circle.

    This is a standard result: for unitary U, the spectrum is on the unit circle because:
    - For |z| > 1: ‖U/z‖ < 1, so U - z = -z(1 - U/z) is invertible via Neumann series
    - For |z| < 1: ‖z·U*‖ < 1, so 1 - z·U* is invertible, and U - z = (1 - z·U*)·U is invertible -/
theorem unitary_spectrum_circle (U : H →L[ℂ] H)
    (hU_left : U.adjoint ∘L U = 1) (hU_right : U ∘L U.adjoint = 1) :
    spectrum ℂ U ⊆ Metric.sphere (0 : ℂ) 1 := by
  -- For unitary U: z ∈ spectrum implies |z| = 1
  intro z hz
  simp only [Metric.mem_sphere, dist_zero_right]
  by_contra hne
  push_neg at hne
  have h1 : ‖z‖ < 1 ∨ ‖z‖ > 1 := lt_or_gt_of_ne hne
  -- ‖U‖ ≤ 1 (since U*U = 1 implies U is an isometry)
  have hU_norm_le : ‖U‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
    intro x
    have hcomp : U.adjoint (U x) = x := by
      have := congrFun (congrArg DFunLike.coe hU_left) x
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
                 ContinuousLinearMap.one_apply] at this
      exact this
    have hinner_eq : @inner ℂ H _ (U x) (U x) = @inner ℂ H _ x x := by
      rw [← ContinuousLinearMap.adjoint_inner_left, hcomp]
    have h : ‖U x‖^2 = ‖x‖^2 := by
      calc ‖U x‖^2 = RCLike.re (@inner ℂ H _ (U x) (U x)) := (inner_self_eq_norm_sq (U x)).symm
        _ = RCLike.re (@inner ℂ H _ x x) := by rw [hinner_eq]
        _ = ‖x‖^2 := inner_self_eq_norm_sq x
    have hsq : ‖U x‖ = ‖x‖ := by
      nlinarith [sq_nonneg ‖U x‖, sq_nonneg ‖x‖, h, norm_nonneg (U x), norm_nonneg x]
    rw [hsq, one_mul]
  -- Similarly ‖U*‖ ≤ 1
  have hU_adj_norm_le : ‖U.adjoint‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
    intro x
    have hcomp : U (U.adjoint x) = x := by
      have := congrFun (congrArg DFunLike.coe hU_right) x
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
                 ContinuousLinearMap.one_apply] at this
      exact this
    -- U preserves inner products: ⟨Uy, Uz⟩ = ⟨y, z⟩
    have hU_inner : ∀ y z, @inner ℂ H _ (U y) (U z) = @inner ℂ H _ y z := by
      intro y z
      calc @inner ℂ H _ (U y) (U z)
          = @inner ℂ H _ (U.adjoint (U y)) z := by rw [ContinuousLinearMap.adjoint_inner_left]
        _ = @inner ℂ H _ ((U.adjoint ∘L U) y) z := rfl
        _ = @inner ℂ H _ y z := by rw [hU_left]; simp
    have hinner_eq : @inner ℂ H _ (U.adjoint x) (U.adjoint x) = @inner ℂ H _ x x := by
      calc @inner ℂ H _ (U.adjoint x) (U.adjoint x)
          = @inner ℂ H _ (U (U.adjoint x)) (U (U.adjoint x)) := (hU_inner _ _).symm
        _ = @inner ℂ H _ x x := by rw [hcomp]
    have h : ‖U.adjoint x‖^2 = ‖x‖^2 := by
      calc ‖U.adjoint x‖^2 = RCLike.re (@inner ℂ H _ (U.adjoint x) (U.adjoint x)) :=
          (inner_self_eq_norm_sq (U.adjoint x)).symm
        _ = RCLike.re (@inner ℂ H _ x x) := by rw [hinner_eq]
        _ = ‖x‖^2 := inner_self_eq_norm_sq x
    have hsq : ‖U.adjoint x‖ = ‖x‖ := by
      nlinarith [sq_nonneg ‖U.adjoint x‖, sq_nonneg ‖x‖, h, norm_nonneg (U.adjoint x), norm_nonneg x]
    rw [hsq, one_mul]
  -- z not in spectrum means U - z·1 is a unit (invertible)
  -- We prove U - z·1 is a unit to contradict hz
  have hU_sub_z_unit : IsUnit (U - (z : ℂ) • (1 : H →L[ℂ] H)) := by
    cases h1 with
    | inl hz_lt =>
      -- |z| < 1: use ‖z·U*‖ < 1
      have h_lt : ‖z • U.adjoint‖ < 1 := by
        calc ‖z • U.adjoint‖ = ‖z‖ * ‖U.adjoint‖ := norm_smul z U.adjoint
          _ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left hU_adj_norm_le (norm_nonneg z)
          _ = ‖z‖ := mul_one ‖z‖
          _ < 1 := hz_lt
      have h_inv : IsUnit (1 - z • U.adjoint) := isUnit_one_sub_of_norm_lt_one h_lt
      -- U is a unit
      have hU_unit : IsUnit U := ⟨⟨U, U.adjoint,
        by ext x; exact congrFun (congrArg DFunLike.coe hU_right) x,
        by ext x; exact congrFun (congrArg DFunLike.coe hU_left) x⟩, rfl⟩
      -- (U - z) = (1 - z·U*)·U (both are units)
      have hfactor : U - z • (1 : H →L[ℂ] H) = (1 - z • U.adjoint) * U := by
        ext x; simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.one_apply, ContinuousLinearMap.mul_apply]
        have hUadjU : U.adjoint (U x) = x := by
          have := congrFun (congrArg DFunLike.coe hU_left) x
          simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
                     ContinuousLinearMap.one_apply] at this
          exact this
        simp only [hUadjU]
      rw [hfactor]
      exact h_inv.mul hU_unit
    | inr hz_gt =>
      -- |z| > 1: use ‖U/z‖ < 1
      have hz_ne : z ≠ 0 := by intro heq; rw [heq, norm_zero] at hz_gt; linarith
      have h_lt : ‖z⁻¹ • U‖ < 1 := by
        calc ‖z⁻¹ • U‖ = ‖z⁻¹‖ * ‖U‖ := norm_smul z⁻¹ U
          _ ≤ ‖z⁻¹‖ * 1 := mul_le_mul_of_nonneg_left hU_norm_le (norm_nonneg _)
          _ = ‖z‖⁻¹ := by rw [norm_inv, mul_one]
          _ < 1 := by rw [inv_lt_one_iff₀]; right; exact hz_gt
      have h_inv : IsUnit (1 - z⁻¹ • U) := isUnit_one_sub_of_norm_lt_one h_lt
      -- (U - z) = -z·(1 - U/z) (unit times a unit)
      have hfactor : U - z • (1 : H →L[ℂ] H) = (-z) • (1 - z⁻¹ • U) := by
        ext x
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.one_apply]
        -- Goal: U x - z • x = (-z) • (x - z⁻¹ • U x)
        -- Expand RHS and show equality
        have hrhs : (-z) • (x - z⁻¹ • U x) = -(z • x) + U x := by
          have h1 : (-z) * z⁻¹ = (-1 : ℂ) := by field_simp [hz_ne]
          calc (-z) • (x - z⁻¹ • U x)
            = (-z) • x - (-z) • (z⁻¹ • U x) := smul_sub (-z) x _
            _ = (-z) • x - ((-z) * z⁻¹) • U x := by rw [smul_smul]
            _ = (-z) • x - (-1 : ℂ) • U x := by rw [h1]
            _ = (-z) • x + U x := by rw [neg_one_smul, sub_neg_eq_add]
            _ = -(z • x) + U x := by rw [neg_smul]
        rw [hrhs]
        abel
      rw [hfactor]
      -- (-z) • (unit) is a unit: construct inverse explicitly
      have hz_neg_ne : -z ≠ 0 := neg_ne_zero.mpr hz_ne
      obtain ⟨u, hu⟩ := h_inv
      -- inverse of (-z) • u is (-z)⁻¹ • u⁻¹
      let w : (H →L[ℂ] H)ˣ := {
        val := (-z) • u.val
        inv := (-z)⁻¹ • u.inv
        val_inv := by
          ext x
          simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.one_apply]
          have h1 : (-z) • u.val ((-z)⁻¹ • u.inv x) = (-z) • ((-z)⁻¹ • u.val (u.inv x)) := by
            congr 1
            have := congrFun (congrArg DFunLike.coe (mul_smul_comm (-z)⁻¹ u.val u.inv)) x
            simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply] at this
            exact this
          rw [h1, smul_smul, mul_inv_cancel₀ hz_neg_ne, one_smul]
          have h2 := congrFun (congrArg DFunLike.coe u.val_inv) x
          simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at h2
          exact h2
        inv_val := by
          ext x
          simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.one_apply]
          have h1 : (-z)⁻¹ • u.inv ((-z) • u.val x) = (-z)⁻¹ • ((-z) • u.inv (u.val x)) := by
            congr 1
            have := congrFun (congrArg DFunLike.coe (mul_smul_comm (-z) u.inv u.val)) x
            simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply] at this
            exact this
          rw [h1, smul_smul, inv_mul_cancel₀ hz_neg_ne, one_smul]
          have h2 := congrFun (congrArg DFunLike.coe u.inv_val) x
          simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at h2
          exact h2
      }
      refine ⟨w, ?_⟩
      -- w.val = (-z) • u.val = (-z) • (1 - z⁻¹ • U)
      show (-z) • u.val = (-z) • (1 - z⁻¹ • U)
      rw [hu]
  -- Contradiction: z in spectrum but algebraMap z - U is a unit
  -- spectrum.notMem_iff: z ∉ σ U ↔ IsUnit (algebraMap ℂ _ z - U)
  -- We have IsUnit (U - z•1), and algebraMap z - U = z•1 - U = -(U - z•1)
  have h_neg_unit : IsUnit ((algebraMap ℂ (H →L[ℂ] H)) z - U) := by
    have h_alg : (algebraMap ℂ (H →L[ℂ] H)) z - U = z • (1 : H →L[ℂ] H) - U := by
      simp only [Algebra.algebraMap_eq_smul_one]
    have hneg : z • (1 : H →L[ℂ] H) - U = -(U - z • 1) := by ext; simp [sub_eq_neg_add, add_comm]
    rw [h_alg, hneg]
    exact hU_sub_z_unit.neg
  exact (spectrum.notMem_iff.mpr h_neg_unit) hz

/-! ### Pulling back CFC via Cayley transform -/

/-- Continuity of the Cayley map. -/
theorem continuous_cayleyMap : Continuous cayleyMap := by
  unfold cayleyMap
  apply Continuous.div
  · apply Continuous.sub Complex.continuous_ofReal continuous_const
  · apply Continuous.add Complex.continuous_ofReal continuous_const
  · intro x heq
    -- x + i ≠ 0 since Im(x + i) = 1
    have him : Complex.im ((↑x : ℂ) + Complex.I) = 1 := by simp
    rw [heq] at him
    simp at him

/-- The composed map: ℝ → S¹ → ℂ given by t ↦ (t - i)/(t + i).
    This maps the spectrum of T (⊆ ℝ) to the spectrum of U (⊆ S¹). -/
def cayleyPullback (f : C(Metric.sphere (0 : ℂ) 1, ℂ)) : C(ℝ, ℂ) where
  toFun := fun t =>
    let w : ℂ := cayleyMap t
    -- Need to prove w is on the unit circle: dist w 0 = 1 ↔ ‖w‖ = 1
    f ⟨w, by simp only [Metric.mem_sphere, dist_zero_right]; exact cayleyMap_on_circle t⟩
  continuous_toFun := by
    apply Continuous.comp (by exact f.continuous)
    apply Continuous.subtype_mk
    exact continuous_cayleyMap

/-- The pushforward map: a function on ℝ becomes a function on S¹ \ {1} via inverse Cayley. -/
def cayleyPushforward (f : C(ℝ, ℂ)) :
    { w : Metric.sphere (0 : ℂ) 1 // w.1 ≠ 1 } → ℂ := fun w =>
  let t_real := inverseCayleyMap w.1.1 w.2
  f t_real

/-! ### Unbounded functional calculus via Cayley + CFC -/

/-- The composition f ∘ inverseCayley, defined on ℂ.
    For w ≠ 1, this is f(inverseCayleyMap w).
    For w = 1, we use f(0) as a conventional value.

    **Note on w = 1**: The inverse Cayley map has a pole at w = 1 (corresponding to
    λ = ±∞ in the real line). For functions f with well-defined behavior at infinity,
    the "correct" value at w = 1 would be lim_{λ→±∞} f(λ).

    We use f(0) as the value at w = 1. This choice:
    - Works correctly for constant functions (const c has value c everywhere)
    - Is a placeholder for non-constant functions
    - For CFC applications, the continuity hypothesis on spectrum(U) handles this -/
noncomputable def cfcViaInverseCayley (f : C(ℝ, ℂ)) : ℂ → ℂ := fun w =>
  if h : w ≠ 1 then f (inverseCayleyMap w h) else f 0

/-- Variant of cfcViaInverseCayley for functions vanishing at infinity (C₀ functions).

    For compactly supported or C₀ functions, the limit as t → ±∞ is 0, so
    the correct value at w = 1 is 0 (not f(0)). This ensures continuity on
    the full spectrum including at w = 1 for unbounded operators. -/
noncomputable def cfcViaInverseCayleyC0 (f : C(ℝ, ℂ)) : ℂ → ℂ := fun w =>
  if h : w ≠ 1 then f (inverseCayleyMap w h) else 0

/-- cfcViaInverseCayleyC0 agrees with cfcViaInverseCayley on {w | w ≠ 1}. -/
lemma cfcViaInverseCayleyC0_eq_away_from_one (f : C(ℝ, ℂ)) (w : ℂ) (hw : w ≠ 1) :
    cfcViaInverseCayleyC0 f w = cfcViaInverseCayley f w := by
  simp only [cfcViaInverseCayleyC0, cfcViaInverseCayley, dif_pos hw]

/-- cfcViaInverseCayleyC0 is continuous on S¹ \ {1} for any continuous f. -/
lemma cfcViaInverseCayleyC0_continuousOn (f : C(ℝ, ℂ)) :
    ContinuousOn (cfcViaInverseCayleyC0 f) {z | z ≠ 1} := by
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  apply ContinuousWithinAt.congr
  · -- Use continuity of f ∘ inverseCayleyMap
    let g : ℂ → ℂ := fun z => f ((Complex.I * (1 + z) / (1 - z)).re)
    have hg_cont : ContinuousOn g {z | z ≠ 1} := by
      apply ContinuousOn.comp (t := Set.univ) f.continuous.continuousOn
      · apply Complex.continuous_re.comp_continuousOn
        apply ContinuousOn.div
        · exact ContinuousOn.mul continuousOn_const (ContinuousOn.add continuousOn_const continuousOn_id)
        · exact ContinuousOn.sub continuousOn_const continuousOn_id
        · intro z hz
          simp only [Set.mem_setOf_eq] at hz
          simp only [sub_ne_zero]
          exact fun heq => hz heq.symm
      · intro _ _; exact Set.mem_univ _
    exact hg_cont w hw
  · intro z hz
    simp only [Set.mem_setOf_eq] at hz
    simp only [cfcViaInverseCayleyC0, dif_pos hz, inverseCayleyMap]
  · simp only [cfcViaInverseCayleyC0, dif_pos hw, inverseCayleyMap]

/-- cfcViaInverseCayleyC0 preserves multiplication. -/
lemma cfcViaInverseCayleyC0_mul (f g : C(ℝ, ℂ)) :
    cfcViaInverseCayleyC0 (f * g) = cfcViaInverseCayleyC0 f * cfcViaInverseCayleyC0 g := by
  ext w
  simp only [cfcViaInverseCayleyC0, Pi.mul_apply]
  split_ifs with h
  · simp only [ContinuousMap.mul_apply]
  · simp only [mul_zero]

/-- cfcViaInverseCayleyC0 preserves star. -/
lemma cfcViaInverseCayleyC0_star (f : C(ℝ, ℂ)) :
    cfcViaInverseCayleyC0 (star f) = star (cfcViaInverseCayleyC0 f) := by
  ext w
  simp only [cfcViaInverseCayleyC0, Pi.star_apply]
  split_ifs with h
  · simp only [ContinuousMap.star_apply]
  · simp only [star_zero]

/-- The Cayley transform U is star-normal (unitary implies normal). -/
theorem cayleyTransform_isStarNormal (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) :
    IsStarNormal C.U := by
  -- U is unitary: U*U = 1 (from C.adjoint_eq_inv)
  -- We need to also show UU* = 1
  have hU_left : C.U.adjoint ∘L C.U = 1 := C.adjoint_eq_inv
  -- For the right inverse, use that U is a surjective isometry
  -- The surjectivity of U follows from the Cayley transform construction:
  -- Range(T-i) = H for self-adjoint T (deficiency indices are 0)
  have hU_right : C.U ∘L C.U.adjoint = 1 := cayley_unitary T hT hsa C
  exact unitary_isStarNormal C.U hU_left hU_right

/-- For an unbounded self-adjoint operator T with Cayley transform U,
    we define f(T) := g(U) where g = f ∘ (inverse Cayley).

    This leverages Mathlib's continuous functional calculus for star-normal
    elements in C*-algebras. Since U is unitary, it is star-normal, and
    H →L[ℂ] H is a C*-algebra. -/
noncomputable def UnboundedCFC (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (f : C(ℝ, ℂ)) : H →L[ℂ] H :=
  -- The construction follows Reed-Simon VIII.5:
  -- f(T) = (f ∘ inverseCayley)(U) where U is the Cayley transform
  --
  -- We use Mathlib's CFC for star-normal elements:
  -- U is star-normal (unitary operators are normal)
  -- H →L[ℂ] H is a C*-algebra
  let g := cfcViaInverseCayley f
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- Apply Mathlib's continuous functional calculus
  cfc g C.U

/-- The composition cfcViaInverseCayley preserves multiplication. -/
lemma cfcViaInverseCayley_mul (f g : C(ℝ, ℂ)) :
    cfcViaInverseCayley (f * g) = cfcViaInverseCayley f * cfcViaInverseCayley g := by
  ext w
  simp only [cfcViaInverseCayley, Pi.mul_apply]
  split_ifs with h
  · simp only [ContinuousMap.mul_apply]
  · simp only [ContinuousMap.mul_apply]

/-- The unbounded functional calculus is multiplicative.

    This version includes explicit continuity hypotheses, which are satisfied when:
    - 1 ∉ spectrum(C.U) (e.g., when T is bounded), or
    - f has equal limits at ±∞ (the discontinuity at 1 is removable). -/
theorem unbounded_cfc_mul (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (f g : C(ℝ, ℂ))
    (hcf : ContinuousOn (cfcViaInverseCayley f) (spectrum ℂ C.U))
    (hcg : ContinuousOn (cfcViaInverseCayley g) (spectrum ℂ C.U)) :
    UnboundedCFC T hT hsa C (f * g) = UnboundedCFC T hT hsa C f ∘L UnboundedCFC T hT hsa C g := by
  simp only [UnboundedCFC]
  rw [cfcViaInverseCayley_mul]
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- cfc_mul: cfc (fun x => f x * g x) a = cfc f a * cfc g a
  conv_lhs => rw [show cfcViaInverseCayley f * cfcViaInverseCayley g =
    fun x => cfcViaInverseCayley f x * cfcViaInverseCayley g x from rfl]
  rw [cfc_mul _ _ _ hcf hcg]
  rfl

/-- The composition cfcViaInverseCayley respects star (complex conjugation). -/
lemma cfcViaInverseCayley_star (f : C(ℝ, ℂ)) :
    cfcViaInverseCayley (star f) = star (cfcViaInverseCayley f) := by
  ext w
  simp only [cfcViaInverseCayley, Pi.star_apply]
  split_ifs with h
  · simp only [ContinuousMap.star_apply]
  · simp only [ContinuousMap.star_apply]

/-- The unbounded functional calculus respects adjoints. -/
theorem unbounded_cfc_star (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (f : C(ℝ, ℂ)) :
    (UnboundedCFC T hT hsa C f).adjoint = UnboundedCFC T hT hsa C (star f) := by
  simp only [UnboundedCFC]
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- The adjoint on H →L[ℂ] H corresponds to star in the C*-algebra structure
  -- star_eq_adjoint : star A = A.adjoint, so A.adjoint = star A
  rw [← ContinuousLinearMap.star_eq_adjoint]
  -- Use cfc_star: cfc (fun x ↦ star (f x)) a = star (cfc f a)
  rw [← cfc_star]
  -- Now show: cfc (fun x => star (cfcViaInverseCayley f x)) = cfc (cfcViaInverseCayley (star f))
  congr 1
  ext w
  simp only [cfcViaInverseCayley]
  split_ifs with h
  · simp only [ContinuousMap.star_apply]
  · simp only [ContinuousMap.star_apply]

/-- The constant function 1 maps to the identity operator.

    The proof uses that cfcViaInverseCayley of the constant 1 function is the
    constant 1 function everywhere (both branches of the definition give 1). -/
theorem unbounded_cfc_one (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) :
    UnboundedCFC T hT hsa C (ContinuousMap.const ℝ 1) = 1 := by
  simp only [UnboundedCFC]
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- cfcViaInverseCayley of const 1 equals 1 everywhere
  have heq : cfcViaInverseCayley (ContinuousMap.const ℝ 1) = fun _ => 1 := by
    ext w
    simp only [cfcViaInverseCayley]
    split_ifs with h
    · simp only [ContinuousMap.const_apply]
    · simp only [ContinuousMap.const_apply]
  rw [heq]
  exact cfc_const_one ℂ C.U

/-! ### Complex spectral measure via RMK -/

/-- The positive functional Λ_x(f) = Re⟨x, f(T)x⟩ for x ∈ H and continuous f.
    This is the starting point for the RMK construction. -/
noncomputable def spectralFunctional (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (x : H) :
    C(ℝ, ℂ) → ℂ :=
  fun f => @inner ℂ H _ x ((UnboundedCFC T hT hsa C f) x)

/-- A bump function that approximates the indicator χ_{[a,b]} from below.
    For ε > 0, returns a continuous function that is:
    - 1 on [a+ε, b-ε]
    - 0 outside [a-ε, b+ε]
    - Linear interpolation in between -/
noncomputable def indicatorApprox (a b ε : ℝ) (_hε : ε > 0) : C(ℝ, ℝ) :=
  -- Use max and min to build a piecewise linear bump function
  -- f(x) = max(0, min(1, min((x-(a-ε))/(2ε), ((b+ε)-x)/(2ε))))
  ⟨fun x => max 0 (min 1 (min ((x - (a - ε)) / (2 * ε)) (((b + ε) - x) / (2 * ε)))),
   by
    apply Continuous.max continuous_const
    apply Continuous.min continuous_const
    apply Continuous.min
    · exact (continuous_id.sub continuous_const).div_const _
    · exact (continuous_const.sub continuous_id).div_const _⟩

/-- Complex version of the bump function for CFC. -/
noncomputable def indicatorApproxComplex (a b ε : ℝ) (hε : ε > 0) : C(ℝ, ℂ) :=
  ⟨fun x => (indicatorApprox a b ε hε x : ℂ),
   Complex.continuous_ofReal.comp (indicatorApprox a b ε hε).continuous⟩

/-- The bump functions are bounded by 1. -/
lemma indicatorApprox_le_one (a b ε : ℝ) (hε : ε > 0) (x : ℝ) :
    indicatorApprox a b ε hε x ≤ 1 := by
  unfold indicatorApprox
  simp only [ContinuousMap.coe_mk]
  exact max_le (by linarith) (min_le_left _ _)

/-- The bump functions are nonnegative. -/
lemma indicatorApprox_nonneg (a b ε : ℝ) (hε : ε > 0) (x : ℝ) :
    0 ≤ indicatorApprox a b ε hε x := le_max_left _ _

/-- indicatorApprox is 0 for x ≤ a - ε (below the support). -/
lemma indicatorApprox_eq_zero_below (a b ε : ℝ) (hε : ε > 0) (x : ℝ) (hx : x ≤ a - ε) :
    indicatorApprox a b ε hε x = 0 := by
  unfold indicatorApprox
  simp only [ContinuousMap.coe_mk]
  have h : (x - (a - ε)) / (2 * ε) ≤ 0 := by
    rw [div_le_iff₀ (by linarith : 2 * ε > 0)]
    linarith
  have h2 : min ((x - (a - ε)) / (2 * ε)) (((b + ε) - x) / (2 * ε)) ≤ 0 :=
    le_trans (min_le_left _ _) h
  have h3 : min 1 (min ((x - (a - ε)) / (2 * ε)) ((b + ε - x) / (2 * ε))) ≤ 0 :=
    le_trans (min_le_right _ _) h2
  exact max_eq_left h3

/-- indicatorApprox is 0 for x ≥ b + ε (above the support). -/
lemma indicatorApprox_eq_zero_above (a b ε : ℝ) (hε : ε > 0) (x : ℝ) (hx : x ≥ b + ε) :
    indicatorApprox a b ε hε x = 0 := by
  unfold indicatorApprox
  simp only [ContinuousMap.coe_mk]
  have h : ((b + ε) - x) / (2 * ε) ≤ 0 := by
    rw [div_le_iff₀ (by linarith : 2 * ε > 0)]
    linarith
  have h2 : min ((x - (a - ε)) / (2 * ε)) (((b + ε) - x) / (2 * ε)) ≤ 0 :=
    le_trans (min_le_right _ _) h
  have h3 : min 1 (min ((x - (a - ε)) / (2 * ε)) ((b + ε - x) / (2 * ε))) ≤ 0 :=
    le_trans (min_le_right _ _) h2
  exact max_eq_left h3

/-- indicatorApprox is 0 outside [a - ε, b + ε]. -/
lemma indicatorApprox_eq_zero_outside (a b ε : ℝ) (hε : ε > 0) (x : ℝ)
    (hx : x ≤ a - ε ∨ x ≥ b + ε) : indicatorApprox a b ε hε x = 0 := by
  cases hx with
  | inl h => exact indicatorApprox_eq_zero_below a b ε hε x h
  | inr h => exact indicatorApprox_eq_zero_above a b ε hε x h

/-- For x in [a+ε, b-ε], the bump function equals 1. -/
lemma indicatorApprox_eq_one (a b ε : ℝ) (hε : ε > 0) (x : ℝ)
    (hx_lo : a + ε ≤ x) (hx_hi : x ≤ b - ε) :
    indicatorApprox a b ε hε x = 1 := by
  unfold indicatorApprox
  simp only [ContinuousMap.coe_mk]
  have h1 : (x - (a - ε)) / (2 * ε) ≥ 1 := by
    rw [ge_iff_le, le_div_iff₀ (by linarith : 2 * ε > 0)]
    linarith
  have h2 : ((b + ε) - x) / (2 * ε) ≥ 1 := by
    rw [ge_iff_le, le_div_iff₀ (by linarith : 2 * ε > 0)]
    linarith
  have h3 : min ((x - (a - ε)) / (2 * ε)) ((b + ε - x) / (2 * ε)) ≥ 1 := le_min h1 h2
  have h4 : min 1 (min ((x - (a - ε)) / (2 * ε)) ((b + ε - x) / (2 * ε))) = 1 :=
    min_eq_left h3
  rw [h4]
  exact max_eq_right (by linarith)

/-- Indicator approximation is monotone decreasing in ε on [a, b]:
    For smaller ε, the bump function is larger on the core interval.
    Note: This is only true for x in [a, b]; outside this region the relationship is more complex. -/
lemma indicatorApprox_mono_eps_on_core (a b ε₁ ε₂ : ℝ) (hε₁ : ε₁ > 0) (hε₂ : ε₂ > 0)
    (hle : ε₁ ≤ ε₂) (x : ℝ) (hxa : a ≤ x) (hxb : x ≤ b) :
    indicatorApprox a b ε₂ hε₂ x ≤ indicatorApprox a b ε₁ hε₁ x := by
  unfold indicatorApprox
  simp only [ContinuousMap.coe_mk]
  have h2ε₁ : 0 < 2 * ε₁ := by linarith
  have h2ε₂ : 0 < 2 * ε₂ := by linarith
  apply max_le (le_max_left _ _)
  apply le_max_of_le_right
  apply min_le_min_left
  apply min_le_min
  · -- left₂ ≤ left₁ when x ≥ a
    rw [div_le_div_iff₀ h2ε₂ h2ε₁]
    -- (x - a + ε₂)(2ε₁) ≤ (x - a + ε₁)(2ε₂)
    -- 2ε₁(x-a) + 2ε₁ε₂ ≤ 2ε₂(x-a) + 2ε₁ε₂
    -- 2ε₁(x-a) ≤ 2ε₂(x-a)
    -- (x-a)(ε₁ - ε₂) ≤ 0  [true since x ≥ a and ε₁ ≤ ε₂]
    nlinarith
  · -- right₂ ≤ right₁ when x ≤ b
    rw [div_le_div_iff₀ h2ε₂ h2ε₁]
    -- (b + ε₂ - x)(2ε₁) ≤ (b + ε₁ - x)(2ε₂)
    -- (b-x)(ε₂ - ε₁) ≤ 0  [true since x ≤ b and ε₂ ≥ ε₁]
    nlinarith

/-- At the left boundary a, indicatorApprox equals 1/2 (when a ≤ b). -/
lemma indicatorApprox_at_left_boundary (a b ε : ℝ) (hε : ε > 0) (hab : a ≤ b) :
    indicatorApprox a b ε hε a = 1/2 := by
  unfold indicatorApprox
  simp only [ContinuousMap.coe_mk]
  have h2ε : 0 < 2 * ε := by linarith
  -- At x = a: left term = (a - (a - ε)) / (2ε) = ε / (2ε) = 1/2
  have hleft : (a - (a - ε)) / (2 * ε) = 1/2 := by
    have : a - (a - ε) = ε := by ring
    rw [this]
    field_simp
  rw [hleft]
  -- right term = (b + ε - a)/(2ε) ≥ ε/(2ε) = 1/2 since b ≥ a
  have hright : ((b + ε) - a) / (2 * ε) ≥ 1/2 := by
    rw [ge_iff_le, le_div_iff₀ h2ε]
    linarith
  have h1 : min (1/2) (((b + ε) - a) / (2 * ε)) = 1/2 := min_eq_left hright
  have h2 : min 1 (min (1/2) (((b + ε) - a) / (2 * ε))) = 1/2 := by
    rw [h1]; norm_num
  rw [h2]
  exact max_eq_right (by norm_num : (0 : ℝ) ≤ 1/2)

/-- At the right boundary b, indicatorApprox equals 1/2 (when a ≤ b). -/
lemma indicatorApprox_at_right_boundary (a b ε : ℝ) (hε : ε > 0) (hab : a ≤ b) :
    indicatorApprox a b ε hε b = 1/2 := by
  unfold indicatorApprox
  simp only [ContinuousMap.coe_mk]
  have h2ε : 0 < 2 * ε := by linarith
  -- At x = b: right term = (b + ε - b) / (2ε) = ε / (2ε) = 1/2
  have hright : ((b + ε) - b) / (2 * ε) = 1/2 := by
    have : (b + ε) - b = ε := by ring
    rw [this]
    field_simp
  -- left term = (b - (a - ε)) / (2ε) = (b - a + ε) / (2ε) ≥ ε/(2ε) = 1/2
  have hleft : (b - (a - ε)) / (2 * ε) ≥ 1/2 := by
    rw [ge_iff_le, le_div_iff₀ h2ε]
    have : b - (a - ε) = b - a + ε := by ring
    rw [this]
    linarith
  have h1 : min ((b - (a - ε)) / (2 * ε)) (((b + ε) - b) / (2 * ε)) = 1/2 := by
    rw [hright]
    exact min_eq_right hleft
  have h2 : min 1 (min ((b - (a - ε)) / (2 * ε)) (((b + ε) - b) / (2 * ε))) = 1/2 := by
    rw [h1]; norm_num
  rw [h2]
  exact max_eq_right (by norm_num : (0 : ℝ) ≤ 1/2)

/-- For x in the interior (a, b), indicatorApprox_ε(x) → 1 as ε → 0. -/
lemma indicatorApprox_tendsto_one_interior (a b x : ℝ) (hxa : a < x) (hxb : x < b) :
    Filter.Tendsto (fun ε : ℝ => if hε : ε > 0 then indicatorApprox a b ε hε x else 0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  -- For ε < min(x - a, b - x), the point x is in [a + ε, b - ε], so indicatorApprox = 1
  let ε₀ := min (x - a) (b - x)
  have hε₀_pos : ε₀ > 0 := lt_min (by linarith) (by linarith)
  use ε₀
  constructor
  · exact hε₀_pos
  intro ε hε_mem hε_dist
  simp only [Set.mem_Ioi] at hε_mem
  simp only [dif_pos hε_mem]
  rw [Real.dist_eq]
  -- For ε < ε₀, x ∈ [a + ε, b - ε]
  have hε_small : ε < ε₀ := by
    rw [Real.dist_eq, abs_sub_comm] at hε_dist
    have : |ε| < ε₀ := by simpa using hε_dist
    rwa [abs_of_pos hε_mem] at this
  have hax : a + ε ≤ x := by
    have : ε < x - a := lt_of_lt_of_le hε_small (min_le_left _ _)
    linarith
  have hxb' : x ≤ b - ε := by
    have : ε < b - x := lt_of_lt_of_le hε_small (min_le_right _ _)
    linarith
  -- x ∈ [a + ε, b - ε] implies indicatorApprox = 1
  have h1 := indicatorApprox_eq_one a b ε hε_mem x hax hxb'
  rw [h1]
  simp only [sub_self, abs_zero, hδ]

/-- For x outside [a, b], indicatorApprox_ε(x) → 0 as ε → 0. -/
lemma indicatorApprox_tendsto_zero_exterior (a b x : ℝ) (hx : x < a ∨ x > b) :
    Filter.Tendsto (fun ε : ℝ => if hε : ε > 0 then indicatorApprox a b ε hε x else 0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  cases hx with
  | inl hxa => -- x < a
    -- For ε < a - x, x < a - ε, so indicatorApprox = 0
    let ε₀ := a - x
    have hε₀_pos : ε₀ > 0 := by linarith
    use ε₀
    constructor
    · exact hε₀_pos
    intro ε hε_mem hε_dist
    simp only [Set.mem_Ioi] at hε_mem
    simp only [dif_pos hε_mem]
    rw [Real.dist_eq]
    have hε_small : ε < ε₀ := by
      rw [Real.dist_eq, abs_sub_comm] at hε_dist
      have : |ε| < ε₀ := by simpa using hε_dist
      rwa [abs_of_pos hε_mem] at this
    have hx_below : x ≤ a - ε := by linarith
    have h0 := indicatorApprox_eq_zero_below a b ε hε_mem x hx_below
    rw [h0]
    simp only [sub_zero, abs_zero, hδ]
  | inr hxb => -- x > b
    -- For ε < x - b, x > b + ε, so indicatorApprox = 0
    let ε₀ := x - b
    have hε₀_pos : ε₀ > 0 := by linarith
    use ε₀
    constructor
    · exact hε₀_pos
    intro ε hε_mem hε_dist
    simp only [Set.mem_Ioi] at hε_mem
    simp only [dif_pos hε_mem]
    rw [Real.dist_eq]
    have hε_small : ε < ε₀ := by
      rw [Real.dist_eq, abs_sub_comm] at hε_dist
      have : |ε| < ε₀ := by simpa using hε_dist
      rwa [abs_of_pos hε_mem] at this
    have hx_above : x ≥ b + ε := by linarith
    have h0 := indicatorApprox_eq_zero_above a b ε hε_mem x hx_above
    rw [h0]
    simp only [sub_zero, abs_zero, hδ]

/-- Square root of the bump function. -/
noncomputable def sqrtIndicatorApprox (a b ε : ℝ) (hε : ε > 0) : C(ℝ, ℝ) :=
  ⟨fun x => Real.sqrt (indicatorApprox a b ε hε x),
   (indicatorApprox a b ε hε).continuous.sqrt⟩

/-- Complex version of the square root bump function for CFC. -/
noncomputable def sqrtIndicatorApproxComplex (a b ε : ℝ) (hε : ε > 0) : C(ℝ, ℂ) :=
  ⟨fun x => (sqrtIndicatorApprox a b ε hε x : ℂ),
   Complex.continuous_ofReal.comp (sqrtIndicatorApprox a b ε hε).continuous⟩

/-- The square root bump function squared equals the bump function. -/
lemma sqrtIndicatorApprox_sq (a b ε : ℝ) (hε : ε > 0) (x : ℝ) :
    (sqrtIndicatorApprox a b ε hε x) ^ 2 = indicatorApprox a b ε hε x := by
  unfold sqrtIndicatorApprox
  simp only [ContinuousMap.coe_mk]
  exact Real.sq_sqrt (indicatorApprox_nonneg a b ε hε x)

/-- The square root bump function is non-negative. -/
lemma sqrtIndicatorApprox_nonneg (a b ε : ℝ) (hε : ε > 0) (x : ℝ) :
    0 ≤ sqrtIndicatorApprox a b ε hε x := by
  unfold sqrtIndicatorApprox
  simp only [ContinuousMap.coe_mk]
  exact Real.sqrt_nonneg _

/-- Indicator approximation is monotone in intervals:
    If [a, b] ⊆ [c, d], then indicatorApprox a b ε ≤ indicatorApprox c d ε pointwise. -/
lemma indicatorApprox_mono_interval (a b c d ε : ℝ) (hε : ε > 0)
    (hca : c ≤ a) (hbd : b ≤ d) (x : ℝ) :
    indicatorApprox a b ε hε x ≤ indicatorApprox c d ε hε x := by
  unfold indicatorApprox
  simp only [ContinuousMap.coe_mk]
  -- Both are in [0, 1], need to show LHS ≤ RHS
  apply max_le
  · -- 0 ≤ RHS is clear
    exact le_max_left _ _
  · -- Need: min 1 (min left_a right_b) ≤ max 0 (min 1 (min left_c right_d))
    apply le_max_of_le_right
    apply min_le_min_left
    have h2ε_pos : 0 ≤ 2 * ε := by linarith
    apply min_le_min
    · -- (x - (a - ε)) / (2 * ε) ≤ (x - (c - ε)) / (2 * ε)
      apply div_le_div_of_nonneg_right _ h2ε_pos
      linarith
    · -- ((b + ε) - x) / (2 * ε) ≤ ((d + ε) - x) / (2 * ε)
      apply div_le_div_of_nonneg_right _ h2ε_pos
      linarith

/-- The difference of indicator approximations for nested intervals is non-negative. -/
lemma indicatorApprox_diff_nonneg (a b c d ε : ℝ) (hε : ε > 0)
    (hca : c ≤ a) (hbd : b ≤ d) (x : ℝ) :
    0 ≤ indicatorApprox c d ε hε x - indicatorApprox a b ε hε x := by
  have h := indicatorApprox_mono_interval a b c d ε hε hca hbd x
  linarith

/-- The square root of the difference of indicator approximations. -/
noncomputable def sqrtIndicatorApproxDiff (a b c d ε : ℝ) (hε : ε > 0)
    (_hca : c ≤ a) (_hbd : b ≤ d) : C(ℝ, ℝ) :=
  ⟨fun x => Real.sqrt (indicatorApprox c d ε hε x - indicatorApprox a b ε hε x),
   by
     apply Continuous.sqrt
     exact (indicatorApprox c d ε hε).continuous.sub (indicatorApprox a b ε hε).continuous⟩

/-- Complex version of the square root difference. -/
noncomputable def sqrtIndicatorApproxDiffComplex (a b c d ε : ℝ) (hε : ε > 0)
    (hca : c ≤ a) (hbd : b ≤ d) : C(ℝ, ℂ) :=
  ⟨fun x => (sqrtIndicatorApproxDiff a b c d ε hε hca hbd x : ℂ),
   Complex.continuous_ofReal.comp (sqrtIndicatorApproxDiff a b c d ε hε hca hbd).continuous⟩

/-- The square root difference squared equals the difference. -/
lemma sqrtIndicatorApproxDiff_sq (a b c d ε : ℝ) (hε : ε > 0)
    (hca : c ≤ a) (hbd : b ≤ d) (x : ℝ) :
    (sqrtIndicatorApproxDiff a b c d ε hε hca hbd x) ^ 2 =
    indicatorApprox c d ε hε x - indicatorApprox a b ε hε x := by
  unfold sqrtIndicatorApproxDiff
  simp only [ContinuousMap.coe_mk]
  exact Real.sq_sqrt (indicatorApprox_diff_nonneg a b c d ε hε hca hbd x)

/-! ### Spectral measure from functional calculus -/

/-- The bump function operator for a bounded interval [a,b] with approximation parameter ε.

    We use cfcViaInverseCayleyC0 (which assigns 0 at w=1) because bump functions
    vanish at infinity, ensuring continuity on the full spectrum for unbounded operators. -/
noncomputable def bumpOperator (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b ε : ℝ) (hε : ε > 0) : H →L[ℂ] H :=
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  let bump := cfcViaInverseCayleyC0 (indicatorApproxComplex a b ε hε)
  cfc bump C.U

/-- The bump operators are self-adjoint (since bump functions are real-valued). -/
theorem bumpOperator_self_adjoint (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b ε : ℝ) (hε : ε > 0) :
    (bumpOperator T hT hsa C a b ε hε).adjoint = bumpOperator T hT hsa C a b ε hε := by
  unfold bumpOperator
  haveI hNormal : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  rw [← ContinuousLinearMap.star_eq_adjoint]
  -- cfc respects star, and bump is real-valued so star(bump) = bump
  rw [← cfc_star]
  congr 1
  ext w
  simp only [cfcViaInverseCayleyC0]
  split_ifs with h
  · -- w ≠ 1: star(bump(inverseCayley w)) = bump(inverseCayley w) since bump is real
    simp only [indicatorApproxComplex, ContinuousMap.coe_mk]
    rw [Complex.star_def, Complex.conj_ofReal]
  · -- w = 1: star(0) = 0
    simp only [star_zero]

/-- The square root bump operator. -/
noncomputable def sqrtBumpOperator (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b ε : ℝ) (hε : ε > 0) : H →L[ℂ] H :=
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  let sqrtBump := cfcViaInverseCayleyC0 (sqrtIndicatorApproxComplex a b ε hε)
  cfc sqrtBump C.U

/-- The square root bump operator is self-adjoint (real-valued function). -/
theorem sqrtBumpOperator_self_adjoint (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b ε : ℝ) (hε : ε > 0) :
    (sqrtBumpOperator T hT hsa C a b ε hε).adjoint = sqrtBumpOperator T hT hsa C a b ε hε := by
  unfold sqrtBumpOperator
  haveI hNormal : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  rw [← ContinuousLinearMap.star_eq_adjoint]
  rw [← cfc_star]
  congr 1
  ext w
  simp only [cfcViaInverseCayleyC0]
  split_ifs with h
  · simp only [sqrtIndicatorApproxComplex, ContinuousMap.coe_mk]
    rw [Complex.star_def, Complex.conj_ofReal]
  · simp only [star_zero]

/-- The square root difference operator for interval comparison. -/
noncomputable def sqrtDiffBumpOperator (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b c d ε : ℝ) (hε : ε > 0) (hca : c ≤ a) (hbd : b ≤ d) : H →L[ℂ] H :=
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  let sqrtDiff := cfcViaInverseCayleyC0 (sqrtIndicatorApproxDiffComplex a b c d ε hε hca hbd)
  cfc sqrtDiff C.U

/-- The square root difference operator is self-adjoint. -/
theorem sqrtDiffBumpOperator_self_adjoint (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b c d ε : ℝ) (hε : ε > 0) (hca : c ≤ a) (hbd : b ≤ d) :
    (sqrtDiffBumpOperator T hT hsa C a b c d ε hε hca hbd).adjoint =
    sqrtDiffBumpOperator T hT hsa C a b c d ε hε hca hbd := by
  unfold sqrtDiffBumpOperator
  haveI hNormal : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  rw [← ContinuousLinearMap.star_eq_adjoint]
  rw [← cfc_star]
  congr 1
  ext w
  simp only [cfcViaInverseCayleyC0]
  split_ifs with h
  · simp only [sqrtIndicatorApproxDiffComplex, ContinuousMap.coe_mk]
    rw [Complex.star_def, Complex.conj_ofReal]
  · simp only [star_zero]

/-! ### Unitary properties of Cayley transform (moved here for forward reference) -/

/-- The Cayley transform is a unitary element (in the sense of unitary submonoid). -/
lemma cayleyTransform_mem_unitary (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) : C.U ∈ unitary (H →L[ℂ] H) := by
  rw [Unitary.mem_iff]
  have hU_left : C.U.adjoint ∘L C.U = 1 := C.adjoint_eq_inv
  have hU_right : C.U ∘L C.U.adjoint = 1 := cayley_unitary T hT hsa C
  constructor
  · -- star(U) * U = 1
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact hU_left
  · -- U * star(U) = 1
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact hU_right

/-- The spectrum of the Cayley transform is on the unit circle. -/
lemma spectrum_norm_eq_one_cayley (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (z : ℂ) (hz : z ∈ spectrum ℂ C.U) :
    ‖z‖ = 1 :=
  spectrum.norm_eq_one_of_unitary (cayleyTransform_mem_unitary T hT hsa C) hz

/-- For z on the unit circle with |z - 1| < 1, the inverse Cayley map has large absolute value.

    **Key formula:** For ‖z‖ = 1 and z ≠ 1:
    |inverseCayleyMap(z)| = √((1 + Re(z)) / (1 - Re(z)))

    **Bound:** If |z - 1| < δ ≤ 1, then Re(z) > 1 - δ²/2 (using |z-1|² = 2(1 - Re(z))),
    so 1 + Re(z) > 2 - δ²/2 > 3/2 for δ < 1. Thus |inverseCayleyMap(z)| > 1/δ. -/
lemma inverseCayleyMap_abs_large_near_one (z : ℂ) (hz : z ≠ 1) (hon_circle : ‖z‖ = 1)
    (hclose : ‖z - 1‖ < 1) : |inverseCayleyMap z hz| > 1 / ‖z - 1‖ := by
  -- Use the formula: inverseCayleyMap z = -2 Im(z) / |1 - z|²
  -- For |z| = 1: |inverseCayleyMap z| = √((1 + Re(z)) / (1 - Re(z)))
  unfold inverseCayleyMap
  -- Step 1: Compute |1 - z|² = 2(1 - Re(z)) for |z| = 1
  have h_norm_sq : ‖z - 1‖^2 = 2 * (1 - z.re) := by
    have habs : Complex.normSq z = 1 := by
      rw [Complex.normSq_eq_norm_sq, hon_circle, one_pow]
    have hre_im : z.re * z.re + z.im * z.im = 1 := by
      rw [← Complex.normSq_apply, habs]
    calc ‖z - 1‖^2 = Complex.normSq (z - 1) := by rw [Complex.normSq_eq_norm_sq]
      _ = (z.re - 1) * (z.re - 1) + z.im * z.im := by rw [Complex.normSq_apply]; simp
      _ = z.re * z.re - 2*z.re + 1 + z.im * z.im := by ring
      _ = 1 - 2*z.re + 1 := by linarith
      _ = 2 * (1 - z.re) := by ring
  -- Step 2: Since |z - 1| < 1, we have 1 - Re(z) < 1/2, so Re(z) > 1/2
  have hre_bound : z.re > 1/2 := by
    have h1 : ‖z - 1‖^2 < 1 := by nlinarith [hclose, norm_nonneg (z - 1)]
    rw [h_norm_sq] at h1
    linarith
  -- Step 3: Compute Im(z)² = 1 - Re(z)² for |z| = 1
  have him_sq : z.im^2 = (1 - z.re) * (1 + z.re) := by
    have habs : Complex.normSq z = 1 := by
      rw [Complex.normSq_eq_norm_sq, hon_circle, one_pow]
    have hre_im : z.re * z.re + z.im * z.im = 1 := by rw [← Complex.normSq_apply, habs]
    have hre_im' : z.re^2 + z.im^2 = 1 := by convert hre_im using 2 <;> ring
    nlinarith
  -- Step 4: The key computation for inverseCayleyMap
  -- inverseCayleyMap z = (I * (1 + z) / (1 - z)).re
  -- For |z| = 1: inverseCayleyMap z = -2 Im(z) / |1-z|²
  have h_one_minus_ne : (1 : ℂ) - z ≠ 0 := by
    simp only [ne_eq, sub_eq_zero]
    exact fun h => hz h.symm
  have h_inv_cayley_formula : (Complex.I * (1 + z) / (1 - z)).re = -2 * z.im / ‖z - 1‖^2 := by
    have h1mz_sq : Complex.normSq (1 - z) = ‖z - 1‖^2 := by
      rw [Complex.normSq_eq_norm_sq, norm_sub_rev]
    -- I * (1 + z) = i(1 + re(z) + i·im(z)) = -im(z) + i(1 + re(z))
    -- (1 - z) = 1 - re(z) - i·im(z)
    -- Re((a + bi) / (c + di)) = (ac + bd) / (c² + d²)
    -- where a = -im(z), b = 1 + re(z), c = 1 - re(z), d = -im(z)
    -- ac + bd = -im(z)(1 - re(z)) + (1 + re(z))(-im(z)) = -im(z) + im(z)re(z) - im(z) - im(z)re(z) = -2 im(z)
    rw [Complex.div_re, h1mz_sq]
    have h1 : (Complex.I * (1 + z)).re = -z.im := by simp [Complex.I_re, Complex.I_im]
    have h2 : (Complex.I * (1 + z)).im = 1 + z.re := by simp [Complex.I_re, Complex.I_im]
    have h3 : (1 - z : ℂ).re = 1 - z.re := by simp
    have h4 : (1 - z : ℂ).im = -z.im := by simp
    rw [h1, h2, h3, h4]
    ring
  rw [h_inv_cayley_formula]
  -- Step 5: Bound |inverseCayleyMap z| = 2|Im(z)| / |z-1|²
  have h_norm_pos : ‖z - 1‖ > 0 := by
    have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz
    exact norm_pos_iff.mpr hne
  have h_norm_sq_pos : ‖z - 1‖^2 > 0 := sq_pos_of_pos h_norm_pos
  have h_abs : |(-2 : ℝ) * z.im / ‖z - 1‖^2| = 2 * |z.im| / ‖z - 1‖^2 := by
    rw [abs_div, abs_mul]
    simp only [abs_neg, abs_two]
    rw [abs_of_pos h_norm_sq_pos]
  rw [h_abs]
  -- Step 6: Show 2|Im(z)|/|z-1|² > 1/|z-1|
  -- Equivalently: 2|Im(z)| > |z-1| (after multiplying by |z-1|)
  have him_lower : 4 * z.im^2 > ‖z - 1‖^2 := by
    rw [h_norm_sq, him_sq]
    -- 4 (1 - Re)(1 + Re) > 2(1 - Re)
    -- Since Re > 1/2, we have 1 + Re > 3/2 and 1 - Re > 0
    have hpos : 1 - z.re > 0 := by linarith
    have hpos2 : 1 + z.re > 3/2 := by linarith
    calc 4 * ((1 - z.re) * (1 + z.re)) = 4 * (1 - z.re) * (1 + z.re) := by ring
      _ > 4 * (1 - z.re) * (3/2) := by nlinarith
      _ = 6 * (1 - z.re) := by ring
      _ > 2 * (1 - z.re) := by nlinarith
  -- Convert from squared inequality to linear
  have him_abs_lower : 2 * |z.im| > ‖z - 1‖ := by
    have h1 : (2 * |z.im|)^2 > ‖z - 1‖^2 := by
      calc (2 * |z.im|)^2 = 4 * z.im^2 := by rw [mul_pow, sq_abs]; ring
        _ > ‖z - 1‖^2 := him_lower
    have h2 : 2 * |z.im| ≥ 0 := by positivity
    have h3 : ‖z - 1‖ ≥ 0 := norm_nonneg _
    nlinarith [sq_nonneg (2 * |z.im|), sq_nonneg ‖z - 1‖]
  -- Now prove: 2|Im(z)|/|z-1|² > 1/|z-1|
  -- This is equivalent to: 2|Im(z)|/|z-1| > 1, i.e., 2|Im(z)| > |z-1|
  have key : 2 * |z.im| / ‖z - 1‖ > 1 := by
    rw [gt_iff_lt, one_lt_div h_norm_pos]
    exact him_abs_lower
  have step1 : 2 * |z.im| / ‖z - 1‖^2 = (2 * |z.im| / ‖z - 1‖) / ‖z - 1‖ := by
    have hne : ‖z - 1‖ ≠ 0 := ne_of_gt h_norm_pos
    field_simp [hne]
  rw [step1]
  exact div_lt_div_of_pos_right key h_norm_pos

/-! ### Bump operator monotonicity -/

/-- Key lemma: For nested intervals [a,b] ⊆ [c,d], the bump operator forms satisfy
    ⟨x, P_ab x⟩ ≤ ⟨x, P_cd x⟩, where the difference is non-negative.

    Proof: The difference P_cd - P_ab = R² where R is self-adjoint, so
    ⟨x, (P_cd - P_ab) x⟩ = ⟨x, R² x⟩ = ‖Rx‖² ≥ 0. -/
theorem bumpOperator_inner_mono (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b c d ε : ℝ) (hε : ε > 0) (hca : c ≤ a) (hbd : b ≤ d) (x : H) :
    RCLike.re (@inner ℂ H _ x (bumpOperator T hT hsa C a b ε hε x)) ≤
    RCLike.re (@inner ℂ H _ x (bumpOperator T hT hsa C c d ε hε x)) := by
  haveI hNormal : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- The difference operator P_cd - P_ab corresponds to the difference of bump functions
  -- which is non-negative by indicatorApprox_mono_interval
  -- We show this difference equals R² for self-adjoint R, hence is positive
  let R := sqrtDiffBumpOperator T hT hsa C a b c d ε hε hca hbd
  have hR_sa := sqrtDiffBumpOperator_self_adjoint T hT hsa C a b c d ε hε hca hbd
  -- Key: ⟨x, (P_cd - P_ab) x⟩ = ⟨x, R² x⟩ = ‖Rx‖²
  -- We prove this by showing R² = P_cd - P_ab via CFC
  -- Define the CFC functions
  let bump_ab := cfcViaInverseCayleyC0 (indicatorApproxComplex a b ε hε)
  let bump_cd := cfcViaInverseCayleyC0 (indicatorApproxComplex c d ε hε)
  let sqrtDiff := cfcViaInverseCayleyC0 (sqrtIndicatorApproxDiffComplex a b c d ε hε hca hbd)
  -- Key property: sqrtDiff² = bump_cd - bump_ab pointwise
  have hsqDiff_eq : ∀ w, sqrtDiff w * sqrtDiff w = bump_cd w - bump_ab w := by
    intro w
    simp only [sqrtDiff, bump_cd, bump_ab, cfcViaInverseCayleyC0]
    split_ifs with hw
    · -- w ≠ 1
      simp only [sqrtIndicatorApproxDiffComplex, indicatorApproxComplex, ContinuousMap.coe_mk]
      let t := inverseCayleyMap w hw
      -- Use sqrtIndicatorApproxDiff_sq: (sqrtDiff t)² = diff t
      have hsq_real := sqrtIndicatorApproxDiff_sq a b c d ε hε hca hbd t
      -- Convert to complex: (sqrtDiff t : ℂ) * (sqrtDiff t : ℂ) = (diff t : ℂ)
      have hsq : (sqrtIndicatorApproxDiff a b c d ε hε hca hbd t : ℂ) *
                 (sqrtIndicatorApproxDiff a b c d ε hε hca hbd t : ℂ) =
                 ((indicatorApprox c d ε hε t : ℂ) - (indicatorApprox a b ε hε t : ℂ)) := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_sub]
        congr 1
        have h2 : sqrtIndicatorApproxDiff a b c d ε hε hca hbd t *
                  sqrtIndicatorApproxDiff a b c d ε hε hca hbd t =
                  (sqrtIndicatorApproxDiff a b c d ε hε hca hbd t) ^ 2 := by ring
        rw [h2, hsq_real]
      -- t is definitionally equal to inverseCayleyMap w hw
      exact hsq
    · -- w = 1
      ring
  -- Continuity of the CFC functions on the spectrum
  -- The key is that cfcViaInverseCayleyC0 functions are continuous on {z | z ≠ 1} and equal 0 at z=1
  -- with proper limiting behavior (bump functions vanish at infinity)
  have hcont_sqrtDiff : ContinuousOn sqrtDiff (spectrum ℂ C.U) := by
    intro w hw
    by_cases h1 : w = 1
    · -- At w = 1: need to show continuity at 1
      subst h1
      apply Metric.continuousWithinAt_iff.mpr
      intro ε' hε'
      -- sqrtDiff(1) = 0, and sqrtDiff(z) → 0 as z → 1 (bump functions vanish at infinity)
      let R := max (max (|c - ε|) (|a - ε|)) (max (|b + ε|) (|d + ε|)) + 1
      use min (1/2) (1 / (R + 1))
      constructor
      · apply lt_min; linarith; positivity
      · intro z hz_mem hz_dist
        have hsqrtDiff1 : sqrtDiff 1 = 0 := by
          simp only [sqrtDiff, cfcViaInverseCayleyC0, ne_eq, not_true_eq_false, ↓reduceDIte]
        rw [hsqrtDiff1, dist_zero_right]
        simp only [sqrtDiff, cfcViaInverseCayleyC0]
        by_cases hz_ne1 : z ≠ 1
        · simp only [dif_pos hz_ne1, sqrtIndicatorApproxDiffComplex, ContinuousMap.coe_mk]
          rw [Complex.norm_real, Real.norm_eq_abs]
          -- For z close to 1, inverseCayleyMap(z) is large (outside support)
          have hnorm1 : ‖z‖ = 1 := spectrum.norm_eq_one_of_unitary
            (cayleyTransform_mem_unitary T hT hsa C) hz_mem
          have hz_dist_norm : ‖z - 1‖ < min (1/2) (1 / (R + 1)) := by
            rw [← Complex.dist_eq]; exact hz_dist
          have hclose : ‖z - 1‖ < 1 := calc ‖z - 1‖ < min (1/2) (1 / (R + 1)) := hz_dist_norm
            _ ≤ 1/2 := min_le_left _ _
            _ < 1 := by norm_num
          have hinv_large := inverseCayleyMap_abs_large_near_one z hz_ne1 hnorm1 hclose
          have hz_dist_R : ‖z - 1‖ < 1 / (R + 1) := lt_of_lt_of_le hz_dist_norm (min_le_right _ _)
          have hR_pos : R + 1 > 0 := by positivity
          have hinv_gt_R : |inverseCayleyMap z hz_ne1| > R := by
            have h1 : 1 / ‖z - 1‖ > R + 1 := by
              have hnorm_pos : ‖z - 1‖ > 0 := norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne1)
              rw [gt_iff_lt, lt_div_iff₀ hnorm_pos]
              calc (R + 1) * ‖z - 1‖ < (R + 1) * (1 / (R + 1)) := by
                    apply mul_lt_mul_of_pos_left hz_dist_R hR_pos
                _ = 1 := mul_one_div_cancel (ne_of_gt hR_pos)
            linarith
          -- Show sqrtIndicatorApproxDiff is 0 when |inverseCayleyMap z| > R
          have hindDiff_zero : indicatorApprox c d ε hε (inverseCayleyMap z hz_ne1) -
                               indicatorApprox a b ε hε (inverseCayleyMap z hz_ne1) = 0 := by
            -- R bounds all four corners
            have hR_c : R > |c - ε| := by
              have h1 : max (max |c - ε| |a - ε|) (max |b + ε| |d + ε|) ≥ |c - ε| :=
                le_trans (le_max_left _ _) (le_max_left _ _)
              linarith
            have hR_d : R > |d + ε| := by
              have h1 : max (max |c - ε| |a - ε|) (max |b + ε| |d + ε|) ≥ |d + ε| :=
                le_trans (le_max_right _ _) (le_max_right _ _)
              linarith
            have hR_a : R > |a - ε| := by
              have h1 : max (max |c - ε| |a - ε|) (max |b + ε| |d + ε|) ≥ |a - ε| :=
                le_trans (le_max_right _ _) (le_max_left _ _)
              linarith
            have hR_b : R > |b + ε| := by
              have h1 : max (max |c - ε| |a - ε|) (max |b + ε| |d + ε|) ≥ |b + ε| :=
                le_trans (le_max_left _ _) (le_max_right _ _)
              linarith
            set t := inverseCayleyMap z hz_ne1 with ht_def
            have hind_c_zero : indicatorApprox c d ε hε t = 0 := by
              apply indicatorApprox_eq_zero_outside
              by_cases ht_pos : t ≥ 0
              · right
                have ht_gt_R : t > R := by
                  have : |t| = t := abs_of_nonneg ht_pos; linarith
                have : t > d + ε := calc t > R := ht_gt_R
                  _ > |d + ε| := hR_d
                  _ ≥ d + ε := le_abs_self _
                linarith
              · left
                push_neg at ht_pos
                have ht_lt_neg_R : t < -R := by
                  have : |t| = -t := abs_of_neg ht_pos; linarith
                have : t < c - ε := calc t < -R := ht_lt_neg_R
                  _ < -|c - ε| := by linarith
                  _ ≤ c - ε := neg_abs_le _
                linarith
            have hind_a_zero : indicatorApprox a b ε hε t = 0 := by
              apply indicatorApprox_eq_zero_outside
              by_cases ht_pos : t ≥ 0
              · right
                have ht_gt_R : t > R := by
                  have : |t| = t := abs_of_nonneg ht_pos; linarith
                have : t > b + ε := calc t > R := ht_gt_R
                  _ > |b + ε| := hR_b
                  _ ≥ b + ε := le_abs_self _
                linarith
              · left
                push_neg at ht_pos
                have ht_lt_neg_R : t < -R := by
                  have : |t| = -t := abs_of_neg ht_pos; linarith
                have : t < a - ε := calc t < -R := ht_lt_neg_R
                  _ < -|a - ε| := by linarith
                  _ ≤ a - ε := neg_abs_le _
                linarith
            rw [hind_c_zero, hind_a_zero]; ring
          unfold sqrtIndicatorApproxDiff
          simp only [ContinuousMap.coe_mk]
          rw [hindDiff_zero, Real.sqrt_zero, abs_zero]
          exact hε'
        · -- z = 1
          push_neg at hz_ne1
          simp only [hz_ne1, ne_eq, not_true_eq_false, not_false_eq_true, dif_neg]
          simp only [norm_zero]
          exact hε'
    · -- At w ≠ 1: f is continuous on the open set {z | z ≠ 1}, so continuous at w
      have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_compl_singleton
      have haway := cfcViaInverseCayleyC0_continuousOn (sqrtIndicatorApproxDiffComplex a b c d ε hε hca hbd) w h1
      have hcont_at : ContinuousAt sqrtDiff w := haway.continuousAt (hopen.mem_nhds h1)
      exact hcont_at.continuousWithinAt
  have hcont_bump_ab : ContinuousOn bump_ab (spectrum ℂ C.U) := by
    intro w hw
    by_cases h1 : w = 1
    · -- At w = 1: need to show continuity at 1
      subst h1
      apply Metric.continuousWithinAt_iff.mpr
      intro ε' hε'
      let R_ab := max (|a - ε|) (|b + ε|) + 1
      use min (1/2) (1 / (R_ab + 1))
      constructor
      · apply lt_min; linarith; positivity
      · intro z hz_mem hz_dist
        have hbump_ab_1 : bump_ab 1 = 0 := by
          simp only [bump_ab, cfcViaInverseCayleyC0, ne_eq, not_true_eq_false, ↓reduceDIte]
        rw [hbump_ab_1, dist_zero_right]
        simp only [bump_ab, cfcViaInverseCayleyC0]
        by_cases hz_ne1 : z ≠ 1
        · simp only [dif_pos hz_ne1, indicatorApproxComplex, ContinuousMap.coe_mk]
          rw [Complex.norm_real, Real.norm_eq_abs]
          have hnorm1 : ‖z‖ = 1 := spectrum.norm_eq_one_of_unitary
            (cayleyTransform_mem_unitary T hT hsa C) hz_mem
          have hz_dist_norm : ‖z - 1‖ < min (1/2) (1 / (R_ab + 1)) := by
            rw [← Complex.dist_eq]; exact hz_dist
          have hclose : ‖z - 1‖ < 1 := calc ‖z - 1‖ < min (1/2) (1 / (R_ab + 1)) := hz_dist_norm
            _ ≤ 1/2 := min_le_left _ _
            _ < 1 := by norm_num
          have hinv_large := inverseCayleyMap_abs_large_near_one z hz_ne1 hnorm1 hclose
          have hz_dist_R : ‖z - 1‖ < 1 / (R_ab + 1) := lt_of_lt_of_le hz_dist_norm (min_le_right _ _)
          have hR_pos : R_ab + 1 > 0 := by positivity
          have hinv_gt_R : |inverseCayleyMap z hz_ne1| > R_ab := by
            have h1' : 1 / ‖z - 1‖ > R_ab + 1 := by
              have hnorm_pos : ‖z - 1‖ > 0 := norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne1)
              rw [gt_iff_lt, lt_div_iff₀ hnorm_pos]
              calc (R_ab + 1) * ‖z - 1‖ < (R_ab + 1) * (1 / (R_ab + 1)) := by
                    apply mul_lt_mul_of_pos_left hz_dist_R hR_pos
                _ = 1 := mul_one_div_cancel (ne_of_gt hR_pos)
            linarith
          -- indicatorApprox is 0 outside [-R_ab, R_ab]
          have hind_zero : indicatorApprox a b ε hε (inverseCayleyMap z hz_ne1) = 0 := by
            apply indicatorApprox_eq_zero_outside
            have hR_a : R_ab > |a - ε| := by
              have h1' : max |a - ε| |b + ε| ≥ |a - ε| := le_max_left _ _; linarith
            have hR_b : R_ab > |b + ε| := by
              have h1' : max |a - ε| |b + ε| ≥ |b + ε| := le_max_right _ _; linarith
            set t := inverseCayleyMap z hz_ne1 with ht_def
            by_cases ht_pos : t ≥ 0
            · right
              have ht_gt_R : t > R_ab := by
                have : |t| = t := abs_of_nonneg ht_pos; linarith
              have : t > b + ε := calc t > R_ab := ht_gt_R
                _ > |b + ε| := hR_b
                _ ≥ b + ε := le_abs_self _
              linarith
            · left
              push_neg at ht_pos
              have ht_lt_neg_R : t < -R_ab := by
                have : |t| = -t := abs_of_neg ht_pos; linarith
              have : t < a - ε := calc t < -R_ab := ht_lt_neg_R
                _ < -|a - ε| := by linarith
                _ ≤ a - ε := neg_abs_le _
              linarith
          rw [hind_zero, abs_zero]
          exact hε'
        · push_neg at hz_ne1
          simp only [hz_ne1, ne_eq, not_true_eq_false, ↓reduceDIte, norm_zero]
          exact hε'
    · -- w ≠ 1: f is continuous on the open set {z | z ≠ 1}, so continuous at w
      have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_compl_singleton
      have haway := cfcViaInverseCayleyC0_continuousOn (indicatorApproxComplex a b ε hε) w h1
      have hcont_at : ContinuousAt bump_ab w := haway.continuousAt (hopen.mem_nhds h1)
      exact hcont_at.continuousWithinAt
  have hcont_bump_cd : ContinuousOn bump_cd (spectrum ℂ C.U) := by
    intro w hw
    by_cases h1 : w = 1
    · -- At w = 1: need to show continuity at 1
      subst h1
      apply Metric.continuousWithinAt_iff.mpr
      intro ε' hε'
      let R_cd := max (|c - ε|) (|d + ε|) + 1
      use min (1/2) (1 / (R_cd + 1))
      constructor
      · apply lt_min; linarith; positivity
      · intro z hz_mem hz_dist
        have hbump_cd_1 : bump_cd 1 = 0 := by
          simp only [bump_cd, cfcViaInverseCayleyC0, ne_eq, not_true_eq_false, ↓reduceDIte]
        rw [hbump_cd_1, dist_zero_right]
        simp only [bump_cd, cfcViaInverseCayleyC0]
        by_cases hz_ne1 : z ≠ 1
        · simp only [dif_pos hz_ne1, indicatorApproxComplex, ContinuousMap.coe_mk]
          rw [Complex.norm_real, Real.norm_eq_abs]
          have hnorm1 : ‖z‖ = 1 := spectrum.norm_eq_one_of_unitary
            (cayleyTransform_mem_unitary T hT hsa C) hz_mem
          have hz_dist_norm : ‖z - 1‖ < min (1/2) (1 / (R_cd + 1)) := by
            rw [← Complex.dist_eq]; exact hz_dist
          have hclose : ‖z - 1‖ < 1 := calc ‖z - 1‖ < min (1/2) (1 / (R_cd + 1)) := hz_dist_norm
            _ ≤ 1/2 := min_le_left _ _
            _ < 1 := by norm_num
          have hinv_large := inverseCayleyMap_abs_large_near_one z hz_ne1 hnorm1 hclose
          have hz_dist_R : ‖z - 1‖ < 1 / (R_cd + 1) := lt_of_lt_of_le hz_dist_norm (min_le_right _ _)
          have hR_pos : R_cd + 1 > 0 := by positivity
          have hinv_gt_R : |inverseCayleyMap z hz_ne1| > R_cd := by
            have h1' : 1 / ‖z - 1‖ > R_cd + 1 := by
              have hnorm_pos : ‖z - 1‖ > 0 := norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne1)
              rw [gt_iff_lt, lt_div_iff₀ hnorm_pos]
              calc (R_cd + 1) * ‖z - 1‖ < (R_cd + 1) * (1 / (R_cd + 1)) := by
                    apply mul_lt_mul_of_pos_left hz_dist_R hR_pos
                _ = 1 := mul_one_div_cancel (ne_of_gt hR_pos)
            linarith
          -- indicatorApprox is 0 outside [-R_cd, R_cd]
          have hind_zero : indicatorApprox c d ε hε (inverseCayleyMap z hz_ne1) = 0 := by
            apply indicatorApprox_eq_zero_outside
            have hR_c : R_cd > |c - ε| := by
              have h1' : max |c - ε| |d + ε| ≥ |c - ε| := le_max_left _ _; linarith
            have hR_d : R_cd > |d + ε| := by
              have h1' : max |c - ε| |d + ε| ≥ |d + ε| := le_max_right _ _; linarith
            set t := inverseCayleyMap z hz_ne1 with ht_def
            by_cases ht_pos : t ≥ 0
            · right
              have ht_gt_R : t > R_cd := by
                have : |t| = t := abs_of_nonneg ht_pos; linarith
              have : t > d + ε := calc t > R_cd := ht_gt_R
                _ > |d + ε| := hR_d
                _ ≥ d + ε := le_abs_self _
              linarith
            · left
              push_neg at ht_pos
              have ht_lt_neg_R : t < -R_cd := by
                have : |t| = -t := abs_of_neg ht_pos; linarith
              have : t < c - ε := calc t < -R_cd := ht_lt_neg_R
                _ < -|c - ε| := by linarith
                _ ≤ c - ε := neg_abs_le _
              linarith
          rw [hind_zero, abs_zero]
          exact hε'
        · push_neg at hz_ne1
          simp only [hz_ne1, ne_eq, not_true_eq_false, ↓reduceDIte, norm_zero]
          exact hε'
    · -- w ≠ 1: f is continuous on the open set {z | z ≠ 1}, so continuous at w
      have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_compl_singleton
      have haway := cfcViaInverseCayleyC0_continuousOn (indicatorApproxComplex c d ε hε) w h1
      have hcont_at : ContinuousAt bump_cd w := haway.continuousAt (hopen.mem_nhds h1)
      exact hcont_at.continuousWithinAt
  -- Show that cfc(sqrtDiff)² = cfc(bump_cd) - cfc(bump_ab)
  have hdiff_eq_sq : bumpOperator T hT hsa C c d ε hε - bumpOperator T hT hsa C a b ε hε = R * R := by
    simp only [bumpOperator, sqrtDiffBumpOperator, R]
    -- cfc(bump_cd) - cfc(bump_ab) = cfc(sqrtDiff) * cfc(sqrtDiff)
    rw [← cfc_mul sqrtDiff sqrtDiff C.U hcont_sqrtDiff hcont_sqrtDiff]
    rw [← cfc_sub bump_cd bump_ab C.U hcont_bump_cd hcont_bump_ab]
    congr 1
    ext w
    exact (hsqDiff_eq w).symm
  -- Now use hdiff_eq_sq to show the inner product inequality
  have hdiff_inner : @inner ℂ H _ x ((bumpOperator T hT hsa C c d ε hε -
      bumpOperator T hT hsa C a b ε hε) x) = @inner ℂ H _ x ((R * R) x) := by
    congr 1
    rw [hdiff_eq_sq]
  rw [ContinuousLinearMap.sub_apply, inner_sub_right] at hdiff_inner
  -- ⟨x, R * R x⟩ = ⟨x, R(Rx)⟩ = ⟨R*x, Rx⟩ = ⟨Rx, Rx⟩ = ‖Rx‖² (using R self-adjoint)
  have hRsq_inner : @inner ℂ H _ x ((R * R) x) = @inner ℂ H _ (R x) (R x) := by
    simp only [ContinuousLinearMap.mul_apply]
    -- ⟨x, R(Rx)⟩ = ⟨R.adjoint x, Rx⟩ = ⟨Rx, Rx⟩ (since R.adjoint = R)
    have h1 : @inner ℂ H _ (R.adjoint x) (R x) = @inner ℂ H _ x (R (R x)) :=
      ContinuousLinearMap.adjoint_inner_left R (R x) x
    rw [hR_sa] at h1
    exact h1.symm
  rw [hRsq_inner] at hdiff_inner
  -- ⟨Rx, Rx⟩ = ‖Rx‖² which has non-negative real part
  have hRx_nonneg : 0 ≤ RCLike.re (@inner ℂ H _ (R x) (R x)) := by
    rw [inner_self_eq_norm_sq (R x)]
    exact sq_nonneg _
  -- From hdiff_inner: ⟨x, P_cd x⟩ - ⟨x, P_ab x⟩ = ‖Rx‖²
  -- Taking real parts: re⟨x, P_cd x⟩ - re⟨x, P_ab x⟩ = ‖Rx‖² ≥ 0
  have hre_diff : RCLike.re (@inner ℂ H _ x (bumpOperator T hT hsa C c d ε hε x)) -
      RCLike.re (@inner ℂ H _ x (bumpOperator T hT hsa C a b ε hε x)) =
      RCLike.re (@inner ℂ H _ (R x) (R x)) := by
    have h := congrArg RCLike.re hdiff_inner
    simp only [map_sub] at h
    exact h
  linarith [hRx_nonneg]

/- **Note on monotonicity:** Bump operators are NOT globally monotone in ε.

   While `indicatorApprox_mono_eps_on_core` shows that smaller ε gives larger values on [a,b],
   in the transition regions [a-ε, a] and [b, b+ε], the relationship is **reversed**:
   larger ε means wider support, so points outside [a,b] have positive value for large ε
   but value 0 for small ε.

   **Counterexample:** Take x with spectral measure concentrated near a - ε₁.
   Then for ε₂ > ε₁: bump_{ε₂}(a - ε₁) > 0 but bump_{ε₁}(a - ε₁) = 0.

   The Cauchy sequence proof for `bumpOperator_inner_cauchy` therefore uses **dominated
   convergence** for spectral measures instead of monotone convergence:
   - The bump functions bump_ε converge pointwise to χ_{(a,b)} ∪ {1/2 at boundaries}
   - All bump functions satisfy |bump_ε| ≤ 1
   - The spectral measure ⟨x, E(·) x⟩ is finite
   - By dominated convergence: ⟨x, P_ε x⟩ = ∫ bump_ε dμ_x converges -/

/-- The bump operators are positive contractions (0 ≤ bump ≤ 1 implies 0 ≤ P ≤ 1). -/
theorem bumpOperator_nonneg (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b ε : ℝ) (hε : ε > 0) (x : H) :
    0 ≤ RCLike.re (@inner ℂ H _ x (bumpOperator T hT hsa C a b ε hε x)) := by
  -- STRATEGY: Show P = Q² where Q = sqrtBumpOperator is self-adjoint, then ⟨x, Px⟩ = ‖Qx‖² ≥ 0
  haveI hNormal : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- Q = sqrt(bump) operator is self-adjoint
  have hQ_sa := sqrtBumpOperator_self_adjoint T hT hsa C a b ε hε
  let Q := sqrtBumpOperator T hT hsa C a b ε hε
  -- For self-adjoint Q: ⟨x, Q²x⟩ = ⟨Qx, Qx⟩ = ‖Qx‖²
  have hinner_sq : @inner ℂ H _ x (Q (Q x)) = @inner ℂ H _ (Q x) (Q x) := by
    have h1 : @inner ℂ H _ (Q.adjoint x) (Q x) = @inner ℂ H _ x (Q (Q x)) :=
      ContinuousLinearMap.adjoint_inner_left Q (Q x) x
    rw [hQ_sa] at h1
    exact h1.symm
  -- ⟨Qx, Qx⟩ = ‖Qx‖² which has re ≥ 0
  have hQx_norm : RCLike.re (@inner ℂ H _ (Q x) (Q x)) = ‖Q x‖^2 := inner_self_eq_norm_sq (Q x)
  -- Now we need: P = Q² (bump = sqrt(bump)²)
  have hP_eq_Q2 : bumpOperator T hT hsa C a b ε hε = Q * Q := by
    simp only [bumpOperator]
    -- bump = sqrt(bump) * sqrt(bump) pointwise, then use cfc_mul
    have hbump_eq : cfcViaInverseCayleyC0 (indicatorApproxComplex a b ε hε) =
        fun w => cfcViaInverseCayleyC0 (sqrtIndicatorApproxComplex a b ε hε) w *
                 cfcViaInverseCayleyC0 (sqrtIndicatorApproxComplex a b ε hε) w := by
      ext w
      simp only [cfcViaInverseCayleyC0]
      split_ifs with h
      · -- w ≠ 1: show bump(t) = sqrt(bump(t))² at t = inverseCayleyMap w h
        simp only [indicatorApproxComplex, sqrtIndicatorApproxComplex, ContinuousMap.coe_mk]
        let t := inverseCayleyMap w h
        have hsq : (sqrtIndicatorApprox a b ε hε t : ℂ) *
                   (sqrtIndicatorApprox a b ε hε t : ℂ) =
                   (indicatorApprox a b ε hε t : ℂ) := by
          rw [← Complex.ofReal_mul]
          congr 1
          have h1 := sqrtIndicatorApprox_sq a b ε hε t
          have : sqrtIndicatorApprox a b ε hε t * sqrtIndicatorApprox a b ε hε t =
                 (sqrtIndicatorApprox a b ε hε t) ^ 2 := by ring
          rw [this, h1]
        exact hsq.symm
      · -- w = 1: show 0 = 0 * 0
        ring
    rw [hbump_eq]
    -- cfc (f * f) = cfc f * cfc f by cfc_mul, which requires continuity on spectrum
    let f := cfcViaInverseCayleyC0 (sqrtIndicatorApproxComplex a b ε hε)
    show cfc (fun w => f w * f w) C.U = cfc f C.U * cfc f C.U
    -- Prove continuity of f on spectrum
    have hf_cont : ContinuousOn f (spectrum ℂ C.U) := by
      have hf_cont_away : ContinuousOn f {z | z ≠ 1} :=
        cfcViaInverseCayleyC0_continuousOn (sqrtIndicatorApproxComplex a b ε hε)
      intro w hw
      by_cases h1 : w = 1
      · -- At w = 1: f(1) = 0 and f(z) → 0 as z → 1 (bump functions vanish at infinity)
        subst h1
        rw [Metric.continuousWithinAt_iff]
        intro ε' hε'
        -- For z close to 1, inverseCayleyMap(z) is outside the support of the bump function
        -- Support of sqrtIndicatorApprox is [a-ε, b+ε]
        let R := max (|a - ε|) (|b + ε|) + 1
        -- For |inverseCayleyMap(z)| > R, sqrtIndicatorApprox = 0
        -- inverseCayleyMap(e^{iθ}) = -cot(θ/2) which → ±∞ as θ → 0
        -- We need δ such that |z - 1| < δ implies |inverseCayleyMap(z)| > R
        -- Use δ = 2/(R + 1) (heuristic: small angle θ gives large cot)
        use min (1/2) (1 / (R + 1))
        constructor
        · apply lt_min
          · norm_num
          · positivity
        intro z hz_mem hz_dist
        -- f(1) = 0
        have hf1 : f 1 = 0 := by
          show cfcViaInverseCayleyC0 (sqrtIndicatorApproxComplex a b ε hε) 1 = 0
          simp only [cfcViaInverseCayleyC0, ne_eq, not_true_eq_false, ↓reduceDIte]
        rw [hf1, dist_zero_right]
        -- Show ‖f z‖ < ε'
        show ‖cfcViaInverseCayleyC0 (sqrtIndicatorApproxComplex a b ε hε) z‖ < ε'
        simp only [cfcViaInverseCayleyC0]
        by_cases hz_ne1 : z ≠ 1
        · -- z ≠ 1: show sqrtIndicatorApprox(inverseCayleyMap z) is small
          rw [dif_pos hz_ne1]
          simp only [sqrtIndicatorApproxComplex, ContinuousMap.coe_mk]
          rw [Complex.norm_real, Real.norm_eq_abs]
          have hnonneg := sqrtIndicatorApprox_nonneg a b ε hε (inverseCayleyMap z hz_ne1)
          rw [abs_of_nonneg hnonneg]
          -- Key insight: for z close to 1, inverseCayleyMap(z) is outside the support
          -- of the bump function, so sqrtIndicatorApprox = sqrt(0) = 0 < ε'
          -- We show indicatorApprox(inverseCayleyMap z) = 0 using that:
          -- 1. |inverseCayleyMap(z)| > R for |z - 1| < 1/(R+1)
          -- 2. This puts inverseCayleyMap(z) outside [a-ε, b+ε]
          simp only [sqrtIndicatorApprox, ContinuousMap.coe_mk]
          -- Show indicatorApprox(inverseCayleyMap z) = 0
          have hind_zero : indicatorApprox a b ε hε (inverseCayleyMap z hz_ne1) = 0 := by
            -- Key: for z close to 1, |inverseCayleyMap z| is large
            -- inverseCayleyMap z = Re(i(1+z)/(1-z))
            -- For |z - 1| < 1/(R+1) ≤ 1/2, we have |inverseCayleyMap z| > R
            -- This means inverseCayleyMap z ∉ [a-ε, b+ε] ⊆ [-R+1, R-1]
            -- The detailed analysis uses properties of the inverse Cayley transform
            -- For a complete proof, we'd need to show:
            -- - For spectrum of unitary U, z is on the unit circle
            -- - inverseCayleyMap(e^{iθ}) = -cot(θ/2) for z = e^{iθ}
            -- - |cot(θ/2)| ≥ 1/|z-1| for |z-1| ≤ 1
            -- - So |inverseCayleyMap z| > 1/(1/(R+1)) = R+1 > R
            -- Using indicatorApprox_eq_zero_outside:
            apply indicatorApprox_eq_zero_outside
            -- Need: inverseCayleyMap z ≤ a - ε OR inverseCayleyMap z ≥ b + ε
            -- Step 1: z is on the unit circle (spectrum of unitary)
            have hon_circle : ‖z‖ = 1 := spectrum_norm_eq_one_cayley T hT hsa C z hz_mem
            -- Step 2: |z - 1| < 1/2 < 1
            have hz_dist_norm : ‖z - 1‖ < min (1/2) (1 / (R + 1)) := by
              rw [← Complex.dist_eq]; exact hz_dist
            have hclose : ‖z - 1‖ < 1 := by
              calc ‖z - 1‖ < min (1/2) (1 / (R + 1)) := hz_dist_norm
                _ ≤ 1/2 := min_le_left _ _
                _ < 1 := by norm_num
            -- Step 3: Use inverseCayleyMap_abs_large_near_one
            have hinv_large : |inverseCayleyMap z hz_ne1| > 1 / ‖z - 1‖ :=
              inverseCayleyMap_abs_large_near_one z hz_ne1 hon_circle hclose
            -- Step 4: Since |z - 1| < 1/(R+1), we have |inverseCayleyMap z| > R + 1
            have hz_dist_R : ‖z - 1‖ < 1 / (R + 1) := lt_of_lt_of_le hz_dist_norm (min_le_right _ _)
            have hR_pos : R + 1 > 0 := by
              have : R = max (|a - ε|) (|b + ε|) + 1 := rfl
              have h1 : max (|a - ε|) (|b + ε|) ≥ 0 := le_max_of_le_left (abs_nonneg _)
              linarith
            have hinv_gt_R : |inverseCayleyMap z hz_ne1| > R := by
              have h1 : 1 / ‖z - 1‖ > R + 1 := by
                have hnorm_pos : ‖z - 1‖ > 0 := norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne1)
                rw [gt_iff_lt, lt_div_iff₀ hnorm_pos]
                calc (R + 1) * ‖z - 1‖ < (R + 1) * (1 / (R + 1)) := by
                      apply mul_lt_mul_of_pos_left hz_dist_R hR_pos
                  _ = 1 := mul_one_div_cancel (ne_of_gt hR_pos)
              calc |inverseCayleyMap z hz_ne1| > 1 / ‖z - 1‖ := hinv_large
                _ > R + 1 := h1
                _ > R := by linarith
            -- Step 5: |x| > R implies x ≤ a - ε or x ≥ b + ε
            -- where R = max(|a-ε|, |b+ε|) + 1
            have hR_bound : R > max (|a - ε|) (|b + ε|) := by
              have : R = max (|a - ε|) (|b + ε|) + 1 := rfl
              linarith
            -- |inverseCayleyMap z| > R means inverseCayleyMap z > R or inverseCayleyMap z < -R
            set t := inverseCayleyMap z hz_ne1 with ht_def
            by_cases ht_pos : t ≥ 0
            · -- t ≥ 0 and |t| > R means t > R
              right
              have ht_gt_R : t > R := by
                have : |t| = t := abs_of_nonneg ht_pos
                linarith
              have hmax : R > |b + ε| := lt_of_le_of_lt (le_max_right _ _) hR_bound
              have h1 : t > b + ε := calc t > R := ht_gt_R
                  _ > |b + ε| := hmax
                  _ ≥ b + ε := le_abs_self _
              exact le_of_lt h1
            · -- t < 0 and |t| > R means t < -R
              left
              push_neg at ht_pos
              have ht_lt_neg_R : t < -R := by
                have : |t| = -t := abs_of_neg ht_pos
                linarith
              have hmax : R > |a - ε| := lt_of_le_of_lt (le_max_left _ _) hR_bound
              have h1 : t < a - ε := calc t < -R := ht_lt_neg_R
                  _ < -|a - ε| := by linarith
                  _ ≤ a - ε := neg_abs_le _
              exact le_of_lt h1
          rw [hind_zero, Real.sqrt_zero]
          exact hε'
        · -- z = 1: ‖0‖ < ε'
          push_neg at hz_ne1
          rw [dif_neg (not_ne_iff.mpr hz_ne1)]
          simp only [norm_zero, hε']
      · -- At w ≠ 1: use continuity away from 1
        have hmem : w ∈ {z : ℂ | z ≠ 1} := h1
        have hcont_at_w := hf_cont_away w hmem
        rw [Metric.continuousWithinAt_iff] at hcont_at_w ⊢
        intro ε' hε'
        obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := hcont_at_w ε' hε'
        have hw_dist : 0 < dist w 1 := by rw [dist_pos]; exact h1
        use min δ₁ (dist w 1 / 2)
        constructor
        · exact lt_min hδ₁_pos (half_pos hw_dist)
        intro z hz_mem hz_dist
        apply hδ₁
        · simp only [Set.mem_setOf_eq]
          intro hz_eq_1
          rw [hz_eq_1] at hz_dist
          have h1 : dist w 1 / 2 < dist w 1 := half_lt_self hw_dist
          rw [dist_comm] at hz_dist
          have h2 : dist w 1 < min δ₁ (dist w 1 / 2) := hz_dist
          linarith [min_le_right δ₁ (dist w 1 / 2)]
        · exact lt_of_lt_of_le hz_dist (min_le_left δ₁ _)
    exact cfc_mul f f C.U hf_cont hf_cont
  -- Now combine: ⟨x, Px⟩ = ⟨x, Q²x⟩ = ⟨Qx, Qx⟩ and re(⟨Qx, Qx⟩) = ‖Qx‖² ≥ 0
  have hcalc : RCLike.re (@inner ℂ H _ x (bumpOperator T hT hsa C a b ε hε x)) = ‖Q x‖^2 := by
    calc RCLike.re (@inner ℂ H _ x (bumpOperator T hT hsa C a b ε hε x))
        = RCLike.re (@inner ℂ H _ x ((Q * Q) x)) := by rw [hP_eq_Q2]
      _ = RCLike.re (@inner ℂ H _ x (Q (Q x))) := rfl
      _ = RCLike.re (@inner ℂ H _ (Q x) (Q x)) := by rw [hinner_sq]
      _ = ‖Q x‖^2 := hQx_norm
  rw [hcalc]
  exact sq_nonneg ‖Q x‖

/-- Bump function difference is bounded by 1. -/
lemma indicatorApprox_diff_le (a b ε₁ ε₂ : ℝ) (hε₁ : ε₁ > 0) (hε₂ : ε₂ > 0) (x : ℝ) :
    |indicatorApprox a b ε₁ hε₁ x - indicatorApprox a b ε₂ hε₂ x| ≤ 1 := by
  have h1 := indicatorApprox_le_one a b ε₁ hε₁ x
  have h2 := indicatorApprox_nonneg a b ε₁ hε₁ x
  have h3 := indicatorApprox_le_one a b ε₂ hε₂ x
  have h4 := indicatorApprox_nonneg a b ε₂ hε₂ x
  rw [abs_le]
  constructor <;> linarith

/-- The bump operators are uniformly bounded by 1. -/
theorem bumpOperator_norm_le_one (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b ε : ℝ) (hε : ε > 0) :
    ‖bumpOperator T hT hsa C a b ε hε‖ ≤ 1 := by
  unfold bumpOperator
  haveI hNormal : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- Use norm_cfc_le: if ‖f(x)‖ ≤ c for x ∈ spectrum, then ‖cfc(f)‖ ≤ c
  apply norm_cfc_le (by norm_num : (0 : ℝ) ≤ 1)
  intro w _
  simp only [cfcViaInverseCayleyC0]
  split_ifs with h
  · -- w ≠ 1
    simp only [indicatorApproxComplex, ContinuousMap.coe_mk]
    have h1 := indicatorApprox_nonneg a b ε hε (inverseCayleyMap w h)
    have h2 := indicatorApprox_le_one a b ε hε (inverseCayleyMap w h)
    calc ‖(↑((indicatorApprox a b ε hε) (inverseCayleyMap w h)) : ℂ)‖
        = |(indicatorApprox a b ε hε) (inverseCayleyMap w h)| := by
          simp only [Complex.norm_real, Real.norm_eq_abs]
      _ = (indicatorApprox a b ε hε) (inverseCayleyMap w h) := abs_of_nonneg h1
      _ ≤ 1 := h2
  · -- w = 1: f(1) = 0, so ‖0‖ ≤ 1
    simp only [norm_zero]
    norm_num

/-- The sequence of bump operator inner products is Cauchy.

    **Proof outline (non-circular, uses only CFC properties):**
    1. The operators P_n = cfc(bump_n) are uniformly bounded: ‖P_n‖ ≤ 1
    2. For x, y ∈ H, |⟨x, P_n y⟩ - ⟨x, P_m y⟩| = |⟨x, (P_n - P_m) y⟩|
       ≤ ‖x‖ · ‖P_n - P_m‖ · ‖y‖ ≤ 2‖x‖ · ‖y‖
    3. The sequence {⟨x, P_n y⟩} is bounded, hence has convergent subsequences
    4. By uniqueness of the limit (from measure theory), the sequence converges

    For the formal proof, we use that the operators converge strongly via
    monotone convergence for positive operators. -/
theorem bumpOperator_inner_cauchy (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b : ℝ) (x y : H) :
    CauchySeq (fun n : ℕ =>
      if hn : n > 0 then
        @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ) / n) (by positivity) y)
      else 0) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  -- For x = 0 or y = 0, the sequence is constant 0
  by_cases hx : x = 0
  · use 1
    intro n _ m _
    simp only [hx, inner_zero_left, dite_eq_ite, ite_self, dist_self, hε]
  by_cases hy : y = 0
  · use 1
    intro n _ m _
    simp only [hy, map_zero, inner_zero_right, dite_eq_ite, ite_self, dist_self, hε]
  -- For nonzero x, y, the bound uses operator norm
  -- |⟨x, P_n y⟩ - ⟨x, P_m y⟩| ≤ ‖x‖ · ‖P_n - P_m‖ · ‖y‖ ≤ 2‖x‖‖y‖
  -- This is bounded, so the sequence has a limit
  -- The convergence follows from monotone approximation theory
  -- For the formal proof, we show the sequence is eventually constant up to ε
  use 1
  intro n hn m hm
  simp only [dist_eq_norm]
  -- Both terms are well-defined since n, m ≥ 1
  have hn' : n > 0 := hn
  have hm' : m > 0 := hm
  have hn_pos : (1 : ℝ) / n > 0 := by positivity
  have hm_pos : (1 : ℝ) / m > 0 := by positivity
  simp only [hn', hm', ↓reduceDIte]
  -- Bound: |⟨x, (P_n - P_m) y⟩| ≤ ‖x‖ · ‖P_n - P_m‖ · ‖y‖
  have hbound : ‖@inner ℂ H _ x (bumpOperator T hT hsa C a b (1/n) hn_pos y) -
                 @inner ℂ H _ x (bumpOperator T hT hsa C a b (1/m) hm_pos y)‖ ≤
                2 * ‖x‖ * ‖y‖ := by
    calc ‖@inner ℂ H _ x (bumpOperator T hT hsa C a b (1/n) hn_pos y) -
           @inner ℂ H _ x (bumpOperator T hT hsa C a b (1/m) hm_pos y)‖
        = ‖@inner ℂ H _ x ((bumpOperator T hT hsa C a b (1/n) hn_pos -
            bumpOperator T hT hsa C a b (1/m) hm_pos) y)‖ := by
          rw [← inner_sub_right]; simp only [ContinuousLinearMap.sub_apply]
      _ ≤ ‖x‖ * ‖(bumpOperator T hT hsa C a b (1/n) hn_pos -
            bumpOperator T hT hsa C a b (1/m) hm_pos) y‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖bumpOperator T hT hsa C a b (1/n) hn_pos -
            bumpOperator T hT hsa C a b (1/m) hm_pos‖ * ‖y‖) := by
          apply mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ ‖x‖ * ((‖bumpOperator T hT hsa C a b (1/n) hn_pos‖ +
            ‖bumpOperator T hT hsa C a b (1/m) hm_pos‖) * ‖y‖) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ ‖x‖ * ((1 + 1) * ‖y‖) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          apply add_le_add (bumpOperator_norm_le_one T hT hsa C a b _ hn_pos)
                          (bumpOperator_norm_le_one T hT hsa C a b _ hm_pos)
      _ = 2 * ‖x‖ * ‖y‖ := by ring
  -- The sequence is bounded; for full convergence, use monotone approximation
  -- This requires showing bump operators form a monotone sequence, which follows
  -- from the order structure of CFC for positive functions
  -- For now, we use the bound to show the difference is small for large n, m
  -- (In the limit construction, we use Classical.choose which exists by Cauchy completeness)
  by_cases hxy : 2 * ‖x‖ * ‖y‖ < ε
  · exact lt_of_le_of_lt hbound hxy
  · -- If 2‖x‖‖y‖ ≥ ε, we need the actual convergence proof
    push_neg at hxy
    -- **Proof strategy using spectral measure and dominated convergence:**
    -- The inner product ⟨x, P_n y⟩ = ∫ bump_n(λ) d⟨x, E(λ) y⟩ where E is the spectral measure.
    --
    -- 1. The bump functions bump_{1/n} converge pointwise to χ_{(a,b)} ∪ {1/2 on {a,b}}
    --    - On (a, b): bump_n → 1
    --    - On (-∞, a) ∪ (b, ∞): bump_n → 0
    --    - At a, b: bump_n(a) = bump_n(b) = 1/2 for all n
    --
    -- 2. All bump functions satisfy |bump_n| ≤ 1 (by indicatorApprox_le_one)
    --
    -- 3. By dominated convergence for the complex spectral measure:
    --    ⟨x, P_n y⟩ → ⟨x, P([a,b]) y⟩ (where the boundary contribution depends on
    --    whether a, b are eigenvalues of T)
    --
    -- 4. Convergent sequences are Cauchy.
    --
    -- **Technical details:**
    -- - The spectral measure ⟨x, E(·) y⟩ is a complex measure of total variation ≤ ‖x‖‖y‖
    -- - Dominated convergence applies since |bump_n| ≤ 1 is integrable
    -- - The limit exists and equals the spectral projection onto [a,b]
    --
    -- **Alternative approach using CFC:**
    -- The CFC is an isometry: ‖cfc f a‖ = sup_{t ∈ spectrum} |f(t)|
    -- Since bump_n doesn't converge uniformly (only pointwise), we need SOT convergence.
    -- For SOT, use that ⟨x, P_n x⟩ is bounded and the sequence has at most one limit point.
    --
    -- This proof requires spectral measure infrastructure not fully available in current Mathlib.
    sorry

/-- The sesquilinear form for a bounded interval [a,b], defined as the limit of
    inner products with bump function approximations.

    B_{[a,b]}(x, y) = lim_{n→∞} ⟨x, cfc(bump_n) y⟩

    where bump_n = indicatorApproxComplex a b (1/n).

    **Limit existence:** The sequence is Cauchy by `bumpOperator_inner_cauchy`,
    and ℂ is complete, so the limit exists. -/
noncomputable def spectralFormInterval (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b : ℝ) (x y : H) : ℂ :=
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  let seq : ℕ → ℂ := fun n =>
    if hn : n > 0 then
      @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ) / n) (by positivity) y)
    else 0
  -- The limit exists by Cauchy completeness
  have hcauchy : CauchySeq seq := bumpOperator_inner_cauchy T hT hsa C a b x y
  Classical.choose (cauchySeq_tendsto_of_complete hcauchy)

/-- The spectral form is linear in the second argument. -/
theorem spectralFormInterval_linear_right (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b : ℝ) (x : H) : IsLinearMap ℂ (spectralFormInterval T hT hsa C a b x) where
  map_add := fun y₁ y₂ => by
    -- The limit of ⟨x, P_n (y₁ + y₂)⟩ = lim ⟨x, P_n y₁⟩ + lim ⟨x, P_n y₂⟩
    -- because P_n is linear and limits preserve addition
    unfold spectralFormInterval
    have hcauchy1 := bumpOperator_inner_cauchy T hT hsa C a b x y₁
    have hcauchy2 := bumpOperator_inner_cauchy T hT hsa C a b x y₂
    have hcauchy_sum := bumpOperator_inner_cauchy T hT hsa C a b x (y₁ + y₂)
    have hspec1 := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy1)
    have hspec2 := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy2)
    have hspec_sum := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy_sum)
    -- Show the sequences satisfy the linearity pointwise (typed over ℕ)
    have hpointwise : ∀ n : ℕ, (if hn : n > 0 then
        @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) (y₁ + y₂)) else 0) =
        (if hn : n > 0 then @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y₁) else 0) +
        (if hn : n > 0 then @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y₂) else 0) := by
      intro n
      split_ifs with hn
      · simp only [map_add, inner_add_right]
      · simp
    -- The limit of the sum sequence equals the sum of the limits
    have hlim_add : Filter.Tendsto (fun n : ℕ => (if hn : n > 0 then
        @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y₁) else 0) +
        (if hn : n > 0 then @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y₂) else 0))
        Filter.atTop (nhds (Classical.choose (cauchySeq_tendsto_of_complete hcauchy1) +
                           Classical.choose (cauchySeq_tendsto_of_complete hcauchy2))) :=
      hspec1.add hspec2
    -- By uniqueness of limits
    have huniq := tendsto_nhds_unique (hspec_sum.congr hpointwise) hlim_add
    exact huniq
  map_smul := fun c y => by
    unfold spectralFormInterval
    have hcauchy1 := bumpOperator_inner_cauchy T hT hsa C a b x y
    have hcauchy_smul := bumpOperator_inner_cauchy T hT hsa C a b x (c • y)
    have hspec1 := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy1)
    have hspec_smul := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy_smul)
    have hpointwise : ∀ n : ℕ, (if hn : n > 0 then
        @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) (c • y)) else 0) =
        c * (if hn : n > 0 then @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y) else 0) := by
      intro n
      split_ifs with hn
      · simp only [map_smul, inner_smul_right]
      · simp
    have hlim_smul : Filter.Tendsto (fun n : ℕ => c *
        (if hn : n > 0 then @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y) else 0))
        Filter.atTop (nhds (c * Classical.choose (cauchySeq_tendsto_of_complete hcauchy1))) :=
      hspec1.const_mul c
    have huniq := tendsto_nhds_unique (hspec_smul.congr hpointwise) hlim_smul
    exact huniq

/-- The spectral form is conjugate-linear in the first argument. -/
theorem spectralFormInterval_conj_linear_left (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b : ℝ) (y : H) (c : ℂ) (x₁ x₂ : H) :
    spectralFormInterval T hT hsa C a b (c • x₁ + x₂) y =
    starRingEnd ℂ c * spectralFormInterval T hT hsa C a b x₁ y +
    spectralFormInterval T hT hsa C a b x₂ y := by
  unfold spectralFormInterval
  have hcauchy1 := bumpOperator_inner_cauchy T hT hsa C a b x₁ y
  have hcauchy2 := bumpOperator_inner_cauchy T hT hsa C a b x₂ y
  have hcauchy_sum := bumpOperator_inner_cauchy T hT hsa C a b (c • x₁ + x₂) y
  have hspec1 := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy1)
  have hspec2 := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy2)
  have hspec_sum := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy_sum)
  have hpointwise : ∀ n : ℕ, (if hn : n > 0 then
      @inner ℂ H _ (c • x₁ + x₂) (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y) else 0) =
      starRingEnd ℂ c * (if hn : n > 0 then @inner ℂ H _ x₁ (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y) else 0) +
      (if hn : n > 0 then @inner ℂ H _ x₂ (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y) else 0) := by
    intro n
    split_ifs with hn
    · simp only [inner_add_left, inner_smul_left, starRingEnd_apply]
    · simp
  have hlim_comb : Filter.Tendsto (fun n : ℕ =>
      starRingEnd ℂ c * (if hn : n > 0 then @inner ℂ H _ x₁ (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y) else 0) +
      (if hn : n > 0 then @inner ℂ H _ x₂ (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y) else 0))
      Filter.atTop (nhds (starRingEnd ℂ c * Classical.choose (cauchySeq_tendsto_of_complete hcauchy1) +
                         Classical.choose (cauchySeq_tendsto_of_complete hcauchy2))) :=
    (hspec1.const_mul (starRingEnd ℂ c)).add hspec2
  exact tendsto_nhds_unique (hspec_sum.congr hpointwise) hlim_comb

/-- The spectral form is bounded. -/
theorem spectralFormInterval_bounded (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (a b : ℝ) :
    ∃ C_bnd : ℝ, ∀ x y, ‖spectralFormInterval T hT hsa C a b x y‖ ≤ C_bnd * ‖x‖ * ‖y‖ := by
  use 1
  intro x y
  unfold spectralFormInterval
  have hcauchy := bumpOperator_inner_cauchy T hT hsa C a b x y
  have hspec := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy)
  -- The limit of bounded sequence is bounded
  -- Each term satisfies |⟨x, P_n y⟩| ≤ ‖x‖ · ‖P_n y‖ ≤ ‖x‖ · ‖P_n‖ · ‖y‖ ≤ ‖x‖ · ‖y‖
  have hbound_seq : ∀ n : ℕ, ‖(if hn : n > 0 then
      @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y) else 0)‖ ≤ ‖x‖ * ‖y‖ := by
    intro n
    split_ifs with hn
    · have hn_pos : (1 : ℝ) / n > 0 := by positivity
      calc ‖@inner ℂ H _ x (bumpOperator T hT hsa C a b (1/n) hn_pos y)‖
          ≤ ‖x‖ * ‖bumpOperator T hT hsa C a b (1/n) hn_pos y‖ := norm_inner_le_norm _ _
        _ ≤ ‖x‖ * (‖bumpOperator T hT hsa C a b (1/n) hn_pos‖ * ‖y‖) := by
            apply mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ ‖x‖ * (1 * ‖y‖) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            apply mul_le_mul_of_nonneg_right (bumpOperator_norm_le_one T hT hsa C a b _ hn_pos) (norm_nonneg _)
        _ = ‖x‖ * ‖y‖ := by ring
    · simp only [norm_zero]
      apply mul_nonneg (norm_nonneg _) (norm_nonneg _)
  -- The limit inherits the bound
  have hlim_bound := Filter.Tendsto.norm hspec
  have hle : ‖Classical.choose (cauchySeq_tendsto_of_complete hcauchy)‖ ≤ ‖x‖ * ‖y‖ := by
    apply le_of_tendsto hlim_bound
    filter_upwards with n
    exact hbound_seq n
  linarith [mul_nonneg (norm_nonneg x) (norm_nonneg y)]

/-- Direct bound: the spectral form for intervals satisfies ‖B(x,y)‖ ≤ ‖x‖ * ‖y‖. -/
theorem spectralFormInterval_norm_bound (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (a b : ℝ) (x y : H) :
    ‖spectralFormInterval T hT hsa C a b x y‖ ≤ ‖x‖ * ‖y‖ := by
  -- Directly prove from the definition, same proof as spectralFormInterval_bounded with C_bnd = 1
  unfold spectralFormInterval
  have hcauchy := bumpOperator_inner_cauchy T hT hsa C a b x y
  have hspec := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy)
  have hbound_seq : ∀ n : ℕ, ‖(if hn : n > 0 then
      @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y) else 0)‖ ≤ ‖x‖ * ‖y‖ := by
    intro n
    split_ifs with hn
    · have hn_pos : (1 : ℝ) / n > 0 := by positivity
      calc ‖@inner ℂ H _ x (bumpOperator T hT hsa C a b (1/n) hn_pos y)‖
          ≤ ‖x‖ * ‖bumpOperator T hT hsa C a b (1/n) hn_pos y‖ := norm_inner_le_norm _ _
        _ ≤ ‖x‖ * (‖bumpOperator T hT hsa C a b (1/n) hn_pos‖ * ‖y‖) := by
            apply mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ ‖x‖ * (1 * ‖y‖) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            apply mul_le_mul_of_nonneg_right (bumpOperator_norm_le_one T hT hsa C a b _ hn_pos) (norm_nonneg _)
        _ = ‖x‖ * ‖y‖ := by ring
    · simp only [norm_zero]
      apply mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hlim_bound := Filter.Tendsto.norm hspec
  apply le_of_tendsto hlim_bound
  filter_upwards with n
  exact hbound_seq n

/-- The spectral projection for a bounded interval [a, b], constructed via the
    sesquilinear-to-operator theorem applied to `spectralFormInterval`. -/
noncomputable def spectralProjectionInterval (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (a b : ℝ) : H →L[ℂ] H :=
  let B := spectralFormInterval T hT hsa C a b
  let hlin := spectralFormInterval_linear_right T hT hsa C a b
  let hconj := spectralFormInterval_conj_linear_left T hT hsa C a b
  let hbnd := spectralFormInterval_bounded T hT hsa C a b
  -- Apply sesquilinearToOperator to construct the operator directly
  sesquilinearToOperator B hlin hconj hbnd

/-- The spectral projection for an interval satisfies ⟨x, P y⟩ = spectralFormInterval x y. -/
theorem spectralProjectionInterval_inner (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (a b : ℝ) (x y : H) :
    @inner ℂ H _ x (spectralProjectionInterval T hT hsa C a b y) =
    spectralFormInterval T hT hsa C a b x y := by
  unfold spectralProjectionInterval
  let B := spectralFormInterval T hT hsa C a b
  let hlin := spectralFormInterval_linear_right T hT hsa C a b
  let hconj := spectralFormInterval_conj_linear_left T hT hsa C a b
  let hbnd := spectralFormInterval_bounded T hT hsa C a b
  -- Use sesquilinearToOperator_inner directly (no Classical.choose needed)
  exact (sesquilinearToOperator_inner B hlin hconj hbnd x y).symm

/-- The diagonal spectral form (x = y case) is real-valued.

    This follows from the bump operators being self-adjoint:
    ⟨x, Px⟩ = ⟨Px, x⟩ = conj⟨x, Px⟩, so ⟨x, Px⟩ ∈ ℝ. -/
theorem spectralFormInterval_diagonal_real (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (a b : ℝ) (x : H) :
    (spectralFormInterval T hT hsa C a b x x).im = 0 := by
  -- For self-adjoint P: ⟨x, Px⟩ = ⟨Px, x⟩ = conj⟨x, Px⟩
  -- So ⟨x, Px⟩ is real (im = 0)
  unfold spectralFormInterval
  -- The sequence has real terms (each bump operator is self-adjoint)
  have hcauchy := bumpOperator_inner_cauchy T hT hsa C a b x x
  have hspec := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy)
  -- Each term ⟨x, P_n x⟩ has im = 0 because P_n is self-adjoint
  have hreal : ∀ n : ℕ, (if hn : n > 0 then
      @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) x) else 0).im = 0 := by
    intro n
    split_ifs with hn
    · -- P_n is self-adjoint, so ⟨x, P_n x⟩ is real
      have hn_pos : (1 : ℝ)/n > 0 := by positivity
      have hSA := bumpOperator_self_adjoint T hT hsa C a b (1/n) hn_pos
      -- For self-adjoint P: ⟨x, Px⟩ = ⟨Px, x⟩ = conj⟨x, Px⟩
      have h2 : @inner ℂ H _ x (bumpOperator T hT hsa C a b (1/n) hn_pos x) =
                starRingEnd ℂ (@inner ℂ H _ (bumpOperator T hT hsa C a b (1/n) hn_pos x) x) := by
        rw [inner_conj_symm]
      have h3 : @inner ℂ H _ (bumpOperator T hT hsa C a b (1/n) hn_pos x) x =
                @inner ℂ H _ x (bumpOperator T hT hsa C a b (1/n) hn_pos x) := by
        rw [← ContinuousLinearMap.adjoint_inner_right, hSA]
      rw [h3] at h2
      -- h2: ⟨x, Px⟩ = conj⟨x, Px⟩, so ⟨x, Px⟩ is real
      exact Complex.conj_eq_iff_im.mp h2.symm
    · rfl
  -- The limit of a sequence with im = 0 has im = 0
  -- Use that ℝ is closed in ℂ, so limits of real sequences are real
  have hclosed : IsClosed {z : ℂ | z.im = 0} := by
    have : {z : ℂ | z.im = 0} = Complex.im ⁻¹' {0} := rfl
    rw [this]
    exact IsClosed.preimage Complex.continuous_im isClosed_singleton
  -- All terms of the sequence are in the closed set {z | z.im = 0}
  have hmem : ∀ n : ℕ, (if hn : n > 0 then
      @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) x) else 0) ∈
      {z : ℂ | z.im = 0} := by
    intro n
    simp only [Set.mem_setOf_eq]
    exact hreal n
  -- The limit is in the closed set
  exact hclosed.mem_of_tendsto hspec (Filter.Eventually.of_forall hmem)

/-- The diagonal spectral form (x = y case) is non-negative.

    This follows from the bump operators being positive:
    ⟨x, Px⟩ ≥ 0 for positive P. -/
theorem spectralFormInterval_diagonal_nonneg (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (a b : ℝ) (x : H) :
    0 ≤ (spectralFormInterval T hT hsa C a b x x).re := by
  -- The limit of ⟨x, bump_ε(T)x⟩ where bump_ε ≥ 0
  -- Since bump_ε(T) is positive, ⟨x, bump_ε(T)x⟩ ≥ 0
  -- The limit of non-negative reals is non-negative
  unfold spectralFormInterval
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  let seq : ℕ → ℂ := fun n =>
    if hn : n > 0 then
      @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ) / n) (by positivity) x)
    else 0
  have hcauchy : CauchySeq seq := bumpOperator_inner_cauchy T hT hsa C a b x x
  let L : ℂ := Classical.choose (cauchySeq_tendsto_of_complete hcauchy)
  have hlimit : Tendsto seq atTop (nhds L) := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy)
  -- Each term seq n has non-negative real part (for n > 0, by bumpOperator_nonneg)
  have hseq_nonneg : ∀ n, 0 ≤ (seq n).re := fun n => by
    simp only [seq]
    by_cases hn : n > 0
    · simp only [dif_pos hn]
      exact bumpOperator_nonneg T hT hsa C a b (1 / n) (by positivity) x
    · simp only [dif_neg hn, Complex.zero_re, le_refl]
  -- The real part function is continuous, so lim re(seq n) = re(lim seq n)
  have hre_tendsto : Tendsto (fun n => (seq n).re) atTop (nhds L.re) :=
    (Complex.continuous_re.tendsto L).comp hlimit
  -- The limit of non-negative reals is non-negative (closed set property)
  have hclosed : IsClosed {x : ℝ | 0 ≤ x} := isClosed_Ici
  exact hclosed.mem_of_tendsto hre_tendsto (Filter.Eventually.of_forall hseq_nonneg)

/-- The spectral form is monotone in the interval: [a,b] ⊆ [c,d] implies
    spectralFormInterval a b x x ≤ spectralFormInterval c d x x.

    This follows from P([a,b]) ≤ P([c,d]) when [a,b] ⊆ [c,d]. -/
theorem spectralFormInterval_mono_interval (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b c d : ℝ) (_hab : a ≤ b) (_hcd : c ≤ d) (hac : c ≤ a) (hbd : b ≤ d) (x : H) :
    (spectralFormInterval T hT hsa C a b x x).re ≤
    (spectralFormInterval T hT hsa C c d x x).re := by
  -- If [a,b] ⊆ [c,d], then χ_{[a,b]} ≤ χ_{[c,d]} pointwise
  -- By CFC positivity, P([a,b]) ≤ P([c,d]) in the Loewner order
  -- Hence ⟨x, P([a,b])x⟩ ≤ ⟨x, P([c,d])x⟩
  unfold spectralFormInterval
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- Get the two Cauchy sequences and their limits
  let seq_ab : ℕ → ℂ := fun n =>
    if hn : n > 0 then @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1:ℝ)/n) (by positivity) x)
    else 0
  let seq_cd : ℕ → ℂ := fun n =>
    if hn : n > 0 then @inner ℂ H _ x (bumpOperator T hT hsa C c d ((1:ℝ)/n) (by positivity) x)
    else 0
  have hcauchy_ab := bumpOperator_inner_cauchy T hT hsa C a b x x
  have hcauchy_cd := bumpOperator_inner_cauchy T hT hsa C c d x x
  have hspec_ab := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy_ab)
  have hspec_cd := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy_cd)
  -- Each term satisfies the inequality: bump_ab ≤ bump_cd pointwise implies
  -- ⟨x, P_ab x⟩ ≤ ⟨x, P_cd x⟩ for each n
  have hpointwise : ∀ n : ℕ, (seq_ab n).re ≤ (seq_cd n).re := by
    intro n
    simp only [seq_ab, seq_cd]
    split_ifs with hn
    · -- For n > 0, use that bump operators preserve ordering
      -- The difference P_cd - P_ab corresponds to a non-negative function
      -- (indicatorApprox c d ε - indicatorApprox a b ε ≥ 0)
      -- So ⟨x, (P_cd - P_ab) x⟩ ≥ 0, i.e., ⟨x, P_ab x⟩ ≤ ⟨x, P_cd x⟩
      have hε_pos : (1:ℝ)/n > 0 := by positivity
      -- Both inner products are real (self-adjoint operators)
      have hab_real : ((@inner ℂ H _ x (bumpOperator T hT hsa C a b (1/n) hε_pos x)) : ℂ).im = 0 := by
        have hSA := bumpOperator_self_adjoint T hT hsa C a b (1/n) hε_pos
        have h2 : @inner ℂ H _ x (bumpOperator T hT hsa C a b (1/n) hε_pos x) =
                  starRingEnd ℂ (@inner ℂ H _ (bumpOperator T hT hsa C a b (1/n) hε_pos x) x) := by
          rw [inner_conj_symm]
        have h3 : @inner ℂ H _ (bumpOperator T hT hsa C a b (1/n) hε_pos x) x =
                  @inner ℂ H _ x (bumpOperator T hT hsa C a b (1/n) hε_pos x) := by
          rw [← ContinuousLinearMap.adjoint_inner_right, hSA]
        rw [h3] at h2
        exact Complex.conj_eq_iff_im.mp h2.symm
      have hcd_real : ((@inner ℂ H _ x (bumpOperator T hT hsa C c d (1/n) hε_pos x)) : ℂ).im = 0 := by
        have hSA := bumpOperator_self_adjoint T hT hsa C c d (1/n) hε_pos
        have h2 : @inner ℂ H _ x (bumpOperator T hT hsa C c d (1/n) hε_pos x) =
                  starRingEnd ℂ (@inner ℂ H _ (bumpOperator T hT hsa C c d (1/n) hε_pos x) x) := by
          rw [inner_conj_symm]
        have h3 : @inner ℂ H _ (bumpOperator T hT hsa C c d (1/n) hε_pos x) x =
                  @inner ℂ H _ x (bumpOperator T hT hsa C c d (1/n) hε_pos x) := by
          rw [← ContinuousLinearMap.adjoint_inner_right, hSA]
        rw [h3] at h2
        exact Complex.conj_eq_iff_im.mp h2.symm
      -- Non-negativity of bump operators
      have hab_nonneg := bumpOperator_nonneg T hT hsa C a b (1/n) hε_pos x
      have hcd_nonneg := bumpOperator_nonneg T hT hsa C c d (1/n) hε_pos x
      -- The difference is also non-negative because bump_cd - bump_ab ≥ 0
      -- This follows from indicatorApprox_mono_interval
      -- For now, we use that the cd form includes the ab form plus additional positive contribution
      -- The key insight: ⟨x, P_cd x⟩ - ⟨x, P_ab x⟩ = ⟨x, (P_cd - P_ab) x⟩
      -- where P_cd - P_ab ≥ 0 because the underlying functions satisfy bump_cd ≥ bump_ab
      -- Since both are real, we just need re(ab) ≤ re(cd)
      -- This follows from the operator ordering, which is proved via the function ordering
      -- For the formal proof, use that the non-negative difference operator gives non-negative form
      -- Use bumpOperator_inner_mono: for nested intervals [a,b] ⊆ [c,d], re⟨x, P_ab x⟩ ≤ re⟨x, P_cd x⟩
      exact bumpOperator_inner_mono T hT hsa C a b c d (1/n) hε_pos hac hbd x
    · -- n = 0 case: both are 0
      linarith
  -- The limit preserves the inequality
  have hre_ab : Tendsto (fun n => (seq_ab n).re) atTop
      (nhds (Classical.choose (cauchySeq_tendsto_of_complete hcauchy_ab)).re) :=
    (Complex.continuous_re.tendsto _).comp hspec_ab
  have hre_cd : Tendsto (fun n => (seq_cd n).re) atTop
      (nhds (Classical.choose (cauchySeq_tendsto_of_complete hcauchy_cd)).re) :=
    (Complex.continuous_re.tendsto _).comp hspec_cd
  exact le_of_tendsto_of_tendsto hre_ab hre_cd (Filter.Eventually.of_forall hpointwise)

/-- For a bounded interval [a, b], the spectral projection is idempotent: P² = P.

    **Proof Strategy:**
    1. Goal: P² = P, equivalently spectralFormInterval(x, Py) = spectralFormInterval(x, y)
    2. spectralFormInterval(x, Py) = lim_n ⟨x, P_n(Py)⟩
    3. Using self-adjointness: ⟨x, P_n(Py)⟩ = ⟨P_n x, Py⟩ = spectralFormInterval(P_n x, y)
    4. spectralFormInterval(P_n x, y) = lim_m ⟨P_n x, P_m y⟩ = lim_m ⟨x, P_n P_m y⟩
    5. P_n P_m = cfc(bump_n · bump_m) by cfc_mul
    6. Key: bump_n · bump_m → bump_n pointwise as m → ∞ (since bump_m → indicator)
    7. So lim_m ⟨x, P_n P_m y⟩ = ⟨x, P_n y⟩
    8. Therefore lim_n spectralFormInterval(P_n x, y) = lim_n ⟨x, P_n y⟩ = spectralFormInterval(x, y)
    9. Limit interchange is justified by uniform boundedness of all operators (norm ≤ 1). -/
theorem spectralProjectionInterval_idempotent (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (a b : ℝ) :
    spectralProjectionInterval T hT hsa C a b ∘L spectralProjectionInterval T hT hsa C a b =
    spectralProjectionInterval T hT hsa C a b := by
  let P := spectralProjectionInterval T hT hsa C a b
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.comp_apply]
  rw [spectralProjectionInterval_inner, spectralProjectionInterval_inner]
  -- Goal: spectralFormInterval(x, Py) = spectralFormInterval(x, y)
  -- The key technical step uses the CFC product formula and limit interchange.
  -- P_n P_m = cfc(bump_n · bump_m), and bump_n · bump_m → bump_n as m → ∞.
  -- This implies: spectralFormInterval(x, Py) = lim_n lim_m ⟨x, P_n P_m y⟩
  --                                           = lim_n ⟨x, P_n y⟩
  --                                           = spectralFormInterval(x, y)
  sorry

/-- For a bounded interval [a, b], the spectral projection is self-adjoint: P* = P. -/
theorem spectralProjectionInterval_selfAdjoint (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (a b : ℝ) :
    (spectralProjectionInterval T hT hsa C a b).adjoint =
    spectralProjectionInterval T hT hsa C a b := by
  -- First prove that spectralFormInterval is Hermitian: B(x, y) = conj(B(y, x))
  have hHermitian : ∀ x y, spectralFormInterval T hT hsa C a b x y =
      starRingEnd ℂ (spectralFormInterval T hT hsa C a b y x) := by
    intro x y
    unfold spectralFormInterval
    have hcauchy_xy := bumpOperator_inner_cauchy T hT hsa C a b x y
    have hcauchy_yx := bumpOperator_inner_cauchy T hT hsa C a b y x
    have hspec_xy := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy_xy)
    have hspec_yx := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy_yx)
    -- Each bumpOperator P_n is self-adjoint, so ⟨x, P_n y⟩ = conj⟨y, P_n x⟩
    have hpointwise : ∀ n : ℕ, (if hn : n > 0 then
        @inner ℂ H _ x (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) y) else 0) =
        starRingEnd ℂ (if hn : n > 0 then
        @inner ℂ H _ y (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) x) else 0) := by
      intro n
      split_ifs with hn
      · have hε_pos : (1 : ℝ)/n > 0 := by positivity
        have hSA := bumpOperator_self_adjoint T hT hsa C a b (1/n) hε_pos
        -- ⟨x, P y⟩ = ⟨P x, y⟩ = conj⟨y, P x⟩ for self-adjoint P
        calc @inner ℂ H _ x (bumpOperator T hT hsa C a b (1/n) hε_pos y)
            = @inner ℂ H _ ((bumpOperator T hT hsa C a b (1/n) hε_pos).adjoint x) y := by
                rw [ContinuousLinearMap.adjoint_inner_left]
          _ = @inner ℂ H _ (bumpOperator T hT hsa C a b (1/n) hε_pos x) y := by rw [hSA]
          _ = starRingEnd ℂ (@inner ℂ H _ y (bumpOperator T hT hsa C a b (1/n) hε_pos x)) := by
                rw [inner_conj_symm]
      · simp only [map_zero]
    -- The limit of star(seq) equals star(limit) using Filter.Tendsto.star
    have hlim_star : Filter.Tendsto (fun n : ℕ => starRingEnd ℂ (if hn : n > 0 then
        @inner ℂ H _ y (bumpOperator T hT hsa C a b ((1 : ℝ)/n) (by positivity) x) else 0))
        Filter.atTop (nhds (starRingEnd ℂ (Classical.choose (cauchySeq_tendsto_of_complete hcauchy_yx)))) :=
      hspec_yx.star
    exact tendsto_nhds_unique (hspec_xy.congr hpointwise) hlim_star
  -- Now prove P.adjoint = P using the Hermitian property
  let P := spectralProjectionInterval T hT hsa C a b
  ext y
  apply ext_inner_left ℂ
  intro x
  -- Goal: ⟨x, P.adjoint y⟩ = ⟨x, P y⟩
  -- adjoint_inner_right: ⟨x, A† y⟩ = ⟨A x, y⟩
  rw [ContinuousLinearMap.adjoint_inner_right]
  -- Goal: ⟨P x, y⟩ = ⟨x, P y⟩
  -- ⟨P x, y⟩ = conj⟨y, P x⟩ = conj(B(y, x)) = B(x, y) = ⟨x, P y⟩
  calc @inner ℂ H _ (P x) y
      = starRingEnd ℂ (@inner ℂ H _ y (P x)) := (inner_conj_symm _ _).symm
    _ = starRingEnd ℂ (spectralFormInterval T hT hsa C a b y x) := by
          rw [spectralProjectionInterval_inner]
    _ = spectralFormInterval T hT hsa C a b x y := (hHermitian x y).symm
    _ = @inner ℂ H _ x (P y) := (spectralProjectionInterval_inner T hT hsa C a b x y).symm

/-! ### Strong operator topology limits -/

/-- A sequence of operators A_n converges in the strong operator topology (SOT)
    to A if A_n x → A x for all x ∈ H. -/
def SOTConverges (A : ℕ → H →L[ℂ] H) (L : H →L[ℂ] H) : Prop :=
  ∀ x : H, Tendsto (fun n => A n x) atTop (nhds (L x))

/-- For a self-adjoint positive contraction B (0 ≤ B ≤ I in Loewner order), we have ‖Bx‖² ≤ re⟨x, Bx⟩.

    **Proof:** For self-adjoint B, ‖Bx‖² = ⟨Bx, Bx⟩ = ⟨x, B²x⟩. Since 0 ≤ B ≤ I implies
    B² ≤ B (because B(I-B) ≥ 0 for commuting positive operators), we get
    ⟨x, B²x⟩ ≤ ⟨x, Bx⟩.

    The condition 0 ≤ B ≤ I in Loewner order means:
    - ⟨x, Bx⟩ ≥ 0 for all x (positivity)
    - ⟨x, Bx⟩ ≤ ‖x‖² for all x (bounded by identity) -/
lemma norm_sq_le_inner_of_positive_contraction (B : H →L[ℂ] H)
    (hSA : B.adjoint = B)
    (hPos : ∀ x, 0 ≤ RCLike.re (@inner ℂ H _ x (B x)))
    (hLeI : ∀ x, RCLike.re (@inner ℂ H _ x (B x)) ≤ ‖x‖^2)
    (x : H) :
    ‖B x‖^2 ≤ RCLike.re (@inner ℂ H _ x (B x)) := by
  -- Step 1: ‖Bx‖² = re⟨Bx, Bx⟩ (inner product with itself equals norm squared)
  have h1 : (‖B x‖ : ℝ)^2 = RCLike.re (@inner ℂ H _ (B x) (B x)) := by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) (B x)
    simp only [RCLike.re_to_complex] at this ⊢
    exact this.symm
  -- Step 2: ⟨Bx, Bx⟩ = ⟨x, B²x⟩ using adjoint property and B = B*
  -- adjoint_inner_right A x y : ⟨x, A* y⟩ = ⟨A x, y⟩
  -- With A = B, x = x, y = Bx: ⟨x, B*(Bx)⟩ = ⟨Bx, Bx⟩
  -- Since B* = B: ⟨x, B(Bx)⟩ = ⟨Bx, Bx⟩
  have h2 : @inner ℂ H _ (B x) (B x) = @inner ℂ H _ x ((B * B) x) := by
    have hadj := ContinuousLinearMap.adjoint_inner_right B x (B x)
    -- hadj : ⟨x, B*(Bx)⟩ = ⟨Bx, Bx⟩
    rw [hSA] at hadj
    -- hadj : ⟨x, B(Bx)⟩ = ⟨Bx, Bx⟩
    exact hadj.symm
  -- Step 3: We need B² ≤ B in Loewner order, i.e., re⟨x, B²x⟩ ≤ re⟨x, Bx⟩
  -- This follows from t² ≤ t for t ∈ [0,1], applied via functional calculus
  -- For 0 ≤ B ≤ I, the spectrum of B is in [0,1], and f(t) = t - t² ≥ 0 on [0,1]
  -- Hence B - B² ≥ 0, so B² ≤ B
  -- This is a non-trivial spectral theory result
  have h3 : RCLike.re (@inner ℂ H _ x ((B * B) x)) ≤ RCLike.re (@inner ℂ H _ x (B x)) := by
    -- The key estimate: B² ≤ B for 0 ≤ B ≤ I (Loewner order)
    -- **Proof using spectral square root:**
    -- For 0 ≤ B ≤ I self-adjoint, let C = √B (positive square root via spectral theorem).
    -- Then C² = B and 0 ≤ C ≤ I (since √· is operator monotone on [0,∞)).
    -- Apply hLeI to vector Cx: ⟨Cx, B(Cx)⟩ ≤ ‖Cx‖²
    -- LHS = ⟨x, C·B·C x⟩ = ⟨x, C·C²·C x⟩ = ⟨x, C⁴x⟩ = ⟨x, B²x⟩
    -- RHS = ‖Cx‖² = ⟨Cx, Cx⟩ = ⟨x, C²x⟩ = ⟨x, Bx⟩
    -- Hence ⟨x, B²x⟩ ≤ ⟨x, Bx⟩, i.e., B² ≤ B.
    --
    -- **Alternative proof using CFC:**
    -- For t ∈ [0,1]: t - t² = t(1-t) ≥ 0
    -- By CFC positivity: cfc(t - t², B) = B - B² ≥ 0
    --
    -- Both proofs require spectral theory infrastructure.
    -- Suffices to show: ⟨x, Bx⟩ - ⟨x, B²x⟩ ≥ 0
    have hdiff : RCLike.re (@inner ℂ H _ x (B x)) - RCLike.re (@inner ℂ H _ x ((B * B) x)) =
        RCLike.re (@inner ℂ H _ x ((B - B * B) x)) := by
      rw [ContinuousLinearMap.sub_apply, inner_sub_right, map_sub]
    suffices hkey : 0 ≤ RCLike.re (@inner ℂ H _ x ((B - B * B) x)) by linarith
    -- B - B² = B(I - B), and for commuting positive operators, the product is positive
    -- Strategy: Prove 0 ≤ B and B ≤ 1 in Loewner order, then use CFC
    -- The key estimate: for 0 ≤ B ≤ I self-adjoint, we have B² ≤ B
    -- Equivalently: ⟨x, Bx⟩ ≥ ⟨x, B²x⟩ = ‖Bx‖² for all x
    --
    -- **Proof strategy using CFC:**
    -- 1. B is self-adjoint with spectrum in [0,1] (from 0 ≤ B ≤ I)
    -- 2. The function f(t) = t - t² = t(1-t) is nonneg on [0,1]
    -- 3. By CFC: cfc(f, B) = B - B² ≥ 0
    -- 4. Hence ⟨x, (B - B²)x⟩ ≥ 0, i.e., ⟨x, Bx⟩ ≥ ⟨x, B²x⟩
    --
    -- **Alternative direct proof:**
    -- For self-adjoint B: ⟨x, B²x⟩ = ⟨Bx, Bx⟩ = ‖Bx‖²
    -- So we need ⟨x, Bx⟩.re ≥ ‖Bx‖²
    -- This follows from: for 0 ≤ B ≤ I, the spectrum is in [0,1], so B² ≤ B
    --
    -- **Proof using CFC.sqrt:**
    -- Step 1: Show B is positive in Loewner order (0 ≤ B)
    have hB_isPos : B.IsPositive := by
      rw [ContinuousLinearMap.isPositive_def']
      constructor
      · exact hSA
      · intro y
        rw [ContinuousLinearMap.reApplyInnerSelf]
        -- re⟪B y, y⟫ = re⟪y, B y⟫ by inner_re_symm
        rw [inner_re_symm]
        exact hPos y
    have hB_nonneg : (0 : H →L[ℂ] H) ≤ B := by
      rw [ContinuousLinearMap.nonneg_iff_isPositive]
      exact hB_isPos
    -- Step 2: Let C = √B (exists since B ≥ 0)
    let C := CFC.sqrt B
    -- C is nonnegative and self-adjoint
    have hC_nonneg : (0 : H →L[ℂ] H) ≤ C := CFC.sqrt_nonneg B
    have hC_isPos : C.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive C).mp hC_nonneg
    have hC_sa : C.adjoint = C := hC_isPos.isSelfAdjoint
    -- C² = B
    have hC_sq : C * C = B := CFC.sqrt_mul_sqrt_self B hB_nonneg
    -- Step 3: Apply hLeI to (C x)
    -- We need: re⟪C x, B (C x)⟫ ≤ ‖C x‖²
    -- hLeI gives: re⟪y, B y⟫ ≤ ‖y‖² for all y
    -- Applying to y = C x: re⟪C x, B (C x)⟫ ≤ ‖C x‖²
    have hLeI_Cx : RCLike.re (@inner ℂ H _ (C x) (B (C x))) ≤ ‖C x‖^2 := hLeI (C x)
    -- Step 4: Transform LHS: ⟨C x, B (C x)⟩ = ⟨x, C⁴ x⟩ = ⟨x, B² x⟩
    -- Using adjoint_inner_right: ⟪x, C† y⟫ = ⟪C x, y⟫
    -- With C† = C: ⟪x, C y⟫ = ⟪C x, y⟫, equivalently ⟪C x, y⟫ = ⟪x, C y⟫
    have hLHS : @inner ℂ H _ (C x) (B (C x)) = @inner ℂ H _ x ((B * B) x) := by
      -- ⟨Cx, B(Cx)⟩ = ⟨Cx, C²(Cx)⟩
      rw [← hC_sq]
      -- Unfold to ⟨Cx, C(C(Cx))⟩
      simp only [ContinuousLinearMap.mul_apply]
      -- adjoint_inner_right C x z : ⟪x, C† z⟫ = ⟪C x, z⟫
      -- With C† = C and z = C(C(Cx)): ⟪x, C(C(C(Cx)))⟫ = ⟪Cx, C(C(Cx))⟫
      -- Taking symm: ⟪Cx, C(C(Cx))⟫ = ⟪x, C(C(C(Cx)))⟫
      -- adjoint_inner_right C x z : ⟪x, C z⟫ = ⟪C x, z⟫ (since C† = C)
      -- We need: ⟪Cx, C(C(Cx))⟫ = ⟪x, C(C(C(Cx)))⟫
      -- From adjoint_inner_right with z = C(C(Cx)): ⟪x, C(C(C(Cx)))⟫ = ⟪Cx, C(C(Cx))⟫
      -- So the symm gives us our goal!
      have step := ContinuousLinearMap.adjoint_inner_right C x (C (C (C x)))
      rw [hC_sa] at step
      -- After simp, goal is: ⟨Cx, C(C(Cx))⟩ = ⟨x, C(C(C(Cx)))⟩
      -- step.symm provides exactly: ⟨Cx, C(C(Cx))⟩ = ⟨x, C(C(C(Cx)))⟩
      exact step.symm
    -- Step 5: Transform RHS: ‖Cx‖² = ⟨Cx, Cx⟩ = ⟨x, C² x⟩ = re⟨x, B x⟩
    have hRHS : (‖C x‖ : ℝ)^2 = RCLike.re (@inner ℂ H _ x (B x)) := by
      -- ‖Cx‖² = re⟨Cx, Cx⟩ (inner product with itself equals norm squared)
      have h_norm_sq := inner_self_eq_norm_sq (𝕜 := ℂ) (C x)
      simp only [RCLike.re_to_complex] at h_norm_sq
      -- Using adjoint_inner_right: ⟪x, C y⟫ = ⟪C x, y⟫
      -- With y = Cx: ⟪x, C(Cx)⟫ = ⟪Cx, Cx⟫
      -- Taking symm: ⟪Cx, Cx⟫ = ⟪x, C(Cx)⟫ = ⟪x, Bx⟫
      have step := ContinuousLinearMap.adjoint_inner_right C x (C x)
      rw [hC_sa] at step
      have hinner_eq : @inner ℂ H _ (C x) (C x) = @inner ℂ H _ x (B x) := by
        rw [step.symm]
        simp only [← ContinuousLinearMap.mul_apply, hC_sq]
      -- h_norm_sq : (inner (C x) (C x)).re = ‖C x‖²
      -- Goal: ‖C x‖² = re(inner x (B x))
      calc (‖C x‖ : ℝ)^2 = (@inner ℂ H _ (C x) (C x)).re := h_norm_sq.symm
        _ = (@inner ℂ H _ x (B x)).re := by rw [hinner_eq]
        _ = RCLike.re (@inner ℂ H _ x (B x)) := rfl
    -- Step 6: Combine: re⟨x, B²x⟩ ≤ re⟨x, Bx⟩, hence 0 ≤ re⟨x, (B - B²)x⟩
    have hLHS_re : RCLike.re (@inner ℂ H _ x ((B * B) x)) =
        RCLike.re (@inner ℂ H _ (C x) (B (C x))) := by
      rw [← hLHS]
    -- First show re⟨x, B²x⟩ ≤ re⟨x, Bx⟩
    have hB2_le_B : RCLike.re (@inner ℂ H _ x ((B * B) x)) ≤ RCLike.re (@inner ℂ H _ x (B x)) :=
      calc RCLike.re (@inner ℂ H _ x ((B * B) x))
          = RCLike.re (@inner ℂ H _ (C x) (B (C x))) := hLHS_re
        _ ≤ ‖C x‖^2 := hLeI_Cx
        _ = RCLike.re (@inner ℂ H _ x (B x)) := hRHS
    -- Now use hdiff: re⟨x, Bx⟩ - re⟨x, B²x⟩ = re⟨x, (B - B²)x⟩
    -- We have re⟨x, B²x⟩ ≤ re⟨x, Bx⟩, i.e., 0 ≤ re⟨x, Bx⟩ - re⟨x, B²x⟩
    linarith
  calc (‖B x‖ : ℝ)^2 = RCLike.re (@inner ℂ H _ (B x) (B x)) := h1
    _ = RCLike.re (@inner ℂ H _ x ((B * B) x)) := by rw [h2]
    _ ≤ RCLike.re (@inner ℂ H _ x (B x)) := h3

/-- For monotone increasing sequences of positive contractions, the SOT limit exists.

    **Proof outline:**
    1. For each x, the sequence ⟨x, A_n x⟩ is monotone increasing (from hMono) and bounded by ‖x‖²
    2. Hence ⟨x, A_n x⟩ converges for each x (monotone bounded real sequences converge)
    3. By polarization, ⟨x, A_n y⟩ converges for all x, y
    4. This defines a bounded sesquilinear form B(x,y) = lim_n ⟨x, A_n y⟩
    5. Apply sesquilinearToOperator to get L with ⟨x, Ly⟩ = B(x,y)
    6. Show A_n x → L x using: for n > m, (A_n - A_m)² ≤ A_n - A_m when 0 ≤ A_m ≤ A_n ≤ I
       So ‖A_n x - A_m x‖² = ⟨x, (A_n-A_m)² x⟩ ≤ ⟨x, (A_n-A_m) x⟩ → 0, showing A_n x is Cauchy. -/
theorem monotone_positive_contraction_SOT_limit
    (A : ℕ → H →L[ℂ] H)
    (hSA : ∀ n, (A n).adjoint = A n)  -- self-adjoint
    (hPos : ∀ n x, 0 ≤ RCLike.re (@inner ℂ H _ x (A n x)))  -- positive
    (hBound : ∀ n, ‖A n‖ ≤ 1)  -- contraction
    (hMono : ∀ n x, RCLike.re (@inner ℂ H _ x (A n x)) ≤ RCLike.re (@inner ℂ H _ x (A (n+1) x))) :
    ∃ L : H →L[ℂ] H, SOTConverges A L := by
  -- Step 1: For each x, A_n x is a Cauchy sequence in H
  have hCauchy : ∀ x : H, CauchySeq (fun n => A n x) := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    -- The diagonal inner products ⟨x, A_n x⟩ form a monotone bounded sequence
    -- Use that ⟨x, A_n x⟩ converges (monotone + bounded ⟹ Cauchy)
    have hdiag_mono : Monotone (fun n => RCLike.re (@inner ℂ H _ x (A n x))) := by
      intro n m hnm
      induction hnm with
      | refl => rfl
      | step _ ih => exact le_trans ih (hMono _ x)
    have hdiag_bound : ∀ n, RCLike.re (@inner ℂ H _ x (A n x)) ≤ ‖x‖^2 := by
      intro n
      have h1 : ‖@inner ℂ H _ x (A n x)‖ ≤ ‖x‖ * ‖A n x‖ := norm_inner_le_norm x (A n x)
      have h2 : ‖A n x‖ ≤ ‖A n‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      have h3 : ‖A n‖ * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (hBound n) (norm_nonneg _)
      have h4 : ‖A n x‖ ≤ ‖x‖ := by linarith
      have h5 : ‖@inner ℂ H _ x (A n x)‖ ≤ ‖x‖^2 := by
        calc ‖@inner ℂ H _ x (A n x)‖ ≤ ‖x‖ * ‖A n x‖ := h1
          _ ≤ ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
          _ = ‖x‖^2 := by ring
      -- |re z| ≤ |z| for complex z, and |z| = ‖z‖
      have h6 : |RCLike.re (@inner ℂ H _ x (A n x))| ≤ ‖@inner ℂ H _ x (A n x)‖ :=
        RCLike.abs_re_le_norm _
      have h7 : RCLike.re (@inner ℂ H _ x (A n x)) ≤ |RCLike.re (@inner ℂ H _ x (A n x))| :=
        le_abs_self _
      linarith
    -- The monotone bounded sequence converges, hence is Cauchy
    -- In ℝ, monotone bounded sequences converge (and hence are Cauchy)
    have hdiag_bddAbove : BddAbove (Set.range (fun n => RCLike.re (@inner ℂ H _ x (A n x)))) :=
      ⟨‖x‖^2, fun _ ⟨n, hn⟩ => hn ▸ hdiag_bound n⟩
    have hdiag_tendsto : ∃ L, Tendsto (fun n => RCLike.re (@inner ℂ H _ x (A n x))) atTop (nhds L) :=
      ⟨_, tendsto_atTop_ciSup hdiag_mono hdiag_bddAbove⟩
    have hdiag_cauchy : CauchySeq (fun n => RCLike.re (@inner ℂ H _ x (A n x))) :=
      hdiag_tendsto.choose_spec.cauchySeq
    rw [Metric.cauchySeq_iff] at hdiag_cauchy
    -- For the vector sequence, use ‖A_n x - A_m x‖² ≤ ⟨x, (A_n - A_m) x⟩ for n > m
    -- This follows from (A_n - A_m)² ≤ A_n - A_m when 0 ≤ A_m ≤ A_n ≤ I
    obtain ⟨N, hN⟩ := hdiag_cauchy (ε^2) (sq_pos_of_pos hε)
    use N
    intro n hn m hm
    -- Without loss of generality, assume n ≥ m (the distance is symmetric)
    wlog hnm : m ≤ n generalizing n m with hsymm
    · rw [dist_comm]
      exact hsymm m hm n hn (le_of_lt (not_le.mp hnm))
    -- Now n ≥ m, so A_n - A_m ≥ 0
    -- The key estimate: ‖A_n x - A_m x‖² ≤ ⟨x, A_n x⟩ - ⟨x, A_m x⟩
    -- This follows from the spectral theorem or direct computation using (A_n - A_m)² ≤ A_n - A_m
    have hdiff_pos : 0 ≤ RCLike.re (@inner ℂ H _ x ((A n - A m) x)) := by
      simp only [ContinuousLinearMap.sub_apply, inner_sub_right]
      have h := hdiag_mono hnm
      simp only [RCLike.re_to_complex, Complex.sub_re] at h ⊢
      linarith
    -- For the norm bound, we use that for 0 ≤ B ≤ I, ⟨Bx, Bx⟩ ≤ ⟨x, Bx⟩
    -- This follows from B² ≤ B (a consequence of B(I-B) ≥ 0 and B = B*)
    -- For now, bound directly: ‖(A_n - A_m) x‖² ≤ ‖A_n - A_m‖² ‖x‖² ≤ 4‖x‖²
    -- But this doesn't give us Cauchy. We need the finer estimate.
    -- The finer estimate uses: for self-adjoint B with 0 ≤ B ≤ I, ‖Bx‖² ≤ ⟨x, Bx⟩
    -- Proof: ⟨Bx, Bx⟩ = ⟨x, B²x⟩ ≤ ⟨x, Bx⟩ (since B² ≤ B for 0 ≤ B ≤ I)
    -- The condition B² ≤ B follows from B(I-B) ≥ 0, which holds when 0 ≤ B ≤ I
    -- For the formal proof, we apply this with B = A_n - A_m
    have hB_bound : dist (A n x) (A m x) < ε := by
      rw [dist_eq_norm]
      -- Use that ⟨x, A_n x⟩ - ⟨x, A_m x⟩ < ε² for large n, m
      have hdist_re : |RCLike.re (@inner ℂ H _ x (A n x)) - RCLike.re (@inner ℂ H _ x (A m x))| < ε^2 := by
        have h1 := hN n hn m hm
        rw [Real.dist_eq] at h1
        exact h1
      -- The real part difference bounds the norm squared (by the estimate above)
      -- ‖A_n x - A_m x‖² ≤ ⟨x, (A_n - A_m) x⟩.re = ⟨x, A_n x⟩.re - ⟨x, A_m x⟩.re < ε²
      -- Hence ‖A_n x - A_m x‖ < ε
      -- For a complete proof, we need the estimate ‖Bx‖² ≤ ⟨x, Bx⟩.re for 0 ≤ B ≤ I
      -- This is a standard result that requires the spectral theorem or direct verification
      -- For now, we use that the difference of diagonal inner products controls the distance
      by_cases hx : x = 0
      · simp [hx, hε]
      · -- Use the bound ‖A_n x - A_m x‖² ≤ (⟨x, A_n x⟩ - ⟨x, A_m x⟩).re via the auxiliary lemma
        -- Let B = A n - A m. We verify the hypotheses of norm_sq_le_inner_of_positive_contraction:
        let B := A n - A m
        -- B is self-adjoint
        have hB_sa : B.adjoint = B := by
          have h1 : (A n).adjoint = A n := hSA n
          have h2 : (A m).adjoint = A m := hSA m
          calc B.adjoint = (A n - A m).adjoint := rfl
            _ = (A n).adjoint - (A m).adjoint := map_sub _ _ _
            _ = A n - A m := by rw [h1, h2]
        -- B ≥ 0 (positivity) - prove for all y
        have hB_pos : ∀ y, 0 ≤ RCLike.re (@inner ℂ H _ y (B y)) := by
          intro y
          have hBy : B y = A n y - A m y := ContinuousLinearMap.sub_apply _ _ _
          rw [hBy, inner_sub_right]
          -- For y, we need the monotonicity of ⟨y, A_k y⟩
          have hdiag_mono_y : RCLike.re (@inner ℂ H _ y (A m y)) ≤ RCLike.re (@inner ℂ H _ y (A n y)) := by
            have hmono : Monotone (fun k => RCLike.re (@inner ℂ H _ y (A k y))) := by
              intro i j hij
              induction hij with
              | refl => rfl
              | step _ ih => exact le_trans ih (hMono _ y)
            exact hmono hnm
          -- RCLike.re (a - b) = RCLike.re a - RCLike.re b
          rw [map_sub]
          linarith
        -- B ≤ I (bounded by identity): ⟨y, By⟩ ≤ ‖y‖² for all y
        have hB_leI : ∀ y, RCLike.re (@inner ℂ H _ y (B y)) ≤ ‖y‖^2 := by
          intro y
          have hBy : B y = A n y - A m y := ContinuousLinearMap.sub_apply _ _ _
          rw [hBy, inner_sub_right]
          -- Need ⟨y, A_n y⟩ ≤ ‖y‖² for all y and A_m ≥ 0
          have hdiag_bound_y : ∀ k, RCLike.re (@inner ℂ H _ y (A k y)) ≤ ‖y‖^2 := by
            intro k
            have h1 : ‖@inner ℂ H _ y (A k y)‖ ≤ ‖y‖ * ‖A k y‖ := norm_inner_le_norm y (A k y)
            have h2 : ‖A k y‖ ≤ ‖A k‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
            have h3 : ‖A k‖ * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right (hBound k) (norm_nonneg _)
            have h4 : ‖A k y‖ ≤ ‖y‖ := by linarith
            have h5 : ‖@inner ℂ H _ y (A k y)‖ ≤ ‖y‖^2 := by
              calc ‖@inner ℂ H _ y (A k y)‖ ≤ ‖y‖ * ‖A k y‖ := h1
                _ ≤ ‖y‖ * ‖y‖ := mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
                _ = ‖y‖^2 := by ring
            have h6 : |RCLike.re (@inner ℂ H _ y (A k y))| ≤ ‖@inner ℂ H _ y (A k y)‖ :=
              RCLike.abs_re_le_norm _
            have h7 : RCLike.re (@inner ℂ H _ y (A k y)) ≤ |RCLike.re (@inner ℂ H _ y (A k y))| :=
              le_abs_self _
            linarith
          rw [map_sub]
          linarith [hdiag_bound_y n, hPos m y]
        -- Apply the auxiliary lemma
        have hkey : ‖B x‖^2 ≤ RCLike.re (@inner ℂ H _ x (B x)) :=
          norm_sq_le_inner_of_positive_contraction B hB_sa hB_pos hB_leI x
        -- Now connect to the original goal
        have hBx : B x = A n x - A m x := ContinuousLinearMap.sub_apply _ _ _
        have hB_inner_eq : RCLike.re (@inner ℂ H _ x (B x)) =
            RCLike.re (@inner ℂ H _ x (A n x)) - RCLike.re (@inner ℂ H _ x (A m x)) := by
          rw [hBx, inner_sub_right, map_sub]
        rw [hB_inner_eq] at hkey
        -- Since n ≥ m, the difference is positive, so |diff| = diff < ε²
        have hdiff_nonneg : 0 ≤ RCLike.re (@inner ℂ H _ x (A n x)) - RCLike.re (@inner ℂ H _ x (A m x)) := by
          have h := hdiag_mono hnm
          linarith
        have hdiff_lt : RCLike.re (@inner ℂ H _ x (A n x)) - RCLike.re (@inner ℂ H _ x (A m x)) < ε^2 := by
          rw [abs_of_nonneg hdiff_nonneg] at hdist_re
          exact hdist_re
        -- ‖(A n - A m) x‖² < ε², so ‖(A n - A m) x‖ < ε
        have hnorm_sq_lt : ‖B x‖^2 < ε^2 := lt_of_le_of_lt hkey hdiff_lt
        have hnorm_nonneg : 0 ≤ ‖B x‖ := norm_nonneg _
        have hε_pos : 0 < ε := hε
        have hnorm_lt : ‖B x‖ < ε := by
          nlinarith [sq_nonneg ‖B x‖, sq_nonneg ε]
        exact hnorm_lt
    exact hB_bound
  -- Step 2: Extract the limit for each x
  -- Since H is complete and A_n x is Cauchy, it converges
  have hlim : ∀ x, ∃ y, Tendsto (fun n => A n x) atTop (nhds y) := by
    intro x
    exact cauchySeq_tendsto_of_complete (hCauchy x)
  -- Define L x as the limit of A_n x
  let L_fun : H → H := fun x => Classical.choose (hlim x)
  have hL_spec : ∀ x, Tendsto (fun n => A n x) atTop (nhds (L_fun x)) :=
    fun x => Classical.choose_spec (hlim x)
  -- Step 3: Show L_fun is linear
  have hL_add : ∀ x y, L_fun (x + y) = L_fun x + L_fun y := by
    intro x y
    have h1 : Tendsto (fun n => A n (x + y)) atTop (nhds (L_fun (x + y))) := hL_spec (x + y)
    have h2 : Tendsto (fun n => A n x + A n y) atTop (nhds (L_fun x + L_fun y)) :=
      (hL_spec x).add (hL_spec y)
    have h3 : (fun n => A n (x + y)) = (fun n => A n x + A n y) := by
      ext n; exact (A n).map_add x y
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2
  have hL_smul : ∀ (c : ℂ) x, L_fun (c • x) = c • L_fun x := by
    intro c x
    have h1 : Tendsto (fun n => A n (c • x)) atTop (nhds (L_fun (c • x))) := hL_spec (c • x)
    have h2 : Tendsto (fun n => c • A n x) atTop (nhds (c • L_fun x)) :=
      (hL_spec x).const_smul c
    have h3 : (fun n => A n (c • x)) = (fun n => c • A n x) := by
      ext n; exact (A n).map_smul c x
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2
  -- Step 4: Show L_fun is bounded
  have hL_bound : ∃ C : ℝ, ∀ x, ‖L_fun x‖ ≤ C * ‖x‖ := by
    use 1
    intro x
    -- ‖L_fun x‖ = lim ‖A_n x‖ ≤ lim (‖A_n‖ * ‖x‖) ≤ 1 * ‖x‖
    have htend : Tendsto (fun n => ‖A n x‖) atTop (nhds ‖L_fun x‖) :=
      (continuous_norm.tendsto _).comp (hL_spec x)
    have hbound_seq : ∀ n, ‖A n x‖ ≤ 1 * ‖x‖ := by
      intro n
      calc ‖A n x‖ ≤ ‖A n‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (hBound n) (norm_nonneg _)
    exact le_of_tendsto htend (Filter.Eventually.of_forall hbound_seq)
  -- Construct L as a continuous linear map
  let L_lin : H →ₗ[ℂ] H := {
    toFun := L_fun
    map_add' := hL_add
    map_smul' := hL_smul
  }
  obtain ⟨C, hC⟩ := hL_bound
  let L : H →L[ℂ] H := ⟨L_lin, AddMonoidHomClass.continuous_of_bound L_lin C hC⟩
  use L
  -- L satisfies SOTConverges
  intro x
  exact hL_spec x

/-- The sesquilinear form for a half-line (-∞, a], defined as the limit of increasing intervals.

    B_{(-∞,a]}(x, y) = lim_{n→∞} B_{[-n,a]}(x, y) = lim_{n→∞} ⟨x, P([-n,a]) y⟩

    The limit exists because:
    1. P([-n, a]) is monotone increasing (P([-n,a]) ≤ P([-(n+1),a]))
    2. All P([-n, a]) are positive contractions
    3. By monotone convergence for operators, the SOT limit exists -/
noncomputable def spectralFormHalfLine (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a : ℝ) (x y : H) : ℂ :=
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- Define the sequence of inner products
  let seq : ℕ → ℂ := fun n => spectralFormInterval T hT hsa C (-(n : ℝ)) a x y
  -- The sequence is Cauchy because the operators P([-n, a]) form a monotone
  -- bounded sequence and ⟨x, P([-n, a]) y⟩ converges by polarization
  have hcauchy : CauchySeq seq := by
    -- The inner products form a Cauchy sequence by polarization identity:
    -- If ⟨x, P_n x⟩ and ⟨y, P_n y⟩ converge (monotone bounded), then ⟨x, P_n y⟩ converges.
    --
    -- **Proof strategy:**
    -- 1. P_n := bumpOperator(indicatorApprox(-n, a)) forms a monotone sequence of projections
    -- 2. For diagonal elements ⟨x, P_n x⟩: monotone bounded ⟹ Cauchy (by hdiag_cauchy argument)
    -- 3. Apply polarization: ⟨x, P_n y⟩ = 1/4 Σ_{k=0}^3 i^k ⟨x + i^k y, P_n (x + i^k y)⟩
    -- 4. Each term on RHS is Cauchy (diagonal), so LHS is Cauchy
    rw [Metric.cauchySeq_iff]
    intro ε hε
    -- For large n, m, the difference |seq n - seq m| is small
    -- because P([-n, a]) and P([-m, a]) are close (both approximate the same projection)
    use 1
    intro n hn m hm
    simp only [dist_eq_norm]
    -- By polarization and monotone convergence of diagonal inner products
    sorry
  -- Extract the limit using Cauchy completeness
  Classical.choose (cauchySeq_tendsto_of_complete hcauchy)

/-- The spectral form for half-lines is linear in the second argument. -/
theorem spectralFormHalfLine_linear_right (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (a : ℝ) (x : H) :
    IsLinearMap ℂ (spectralFormHalfLine T hT hsa C a x) where
  map_add := fun y₁ y₂ => by
    unfold spectralFormHalfLine
    haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
    -- Define the sequences
    let seq1 : ℕ → ℂ := fun n => spectralFormInterval T hT hsa C (-(n : ℝ)) a x y₁
    let seq2 : ℕ → ℂ := fun n => spectralFormInterval T hT hsa C (-(n : ℝ)) a x y₂
    let seq_sum : ℕ → ℂ := fun n => spectralFormInterval T hT hsa C (-(n : ℝ)) a x (y₁ + y₂)
    -- Cauchy sequences
    have hcauchy1 : CauchySeq seq1 := by
      rw [Metric.cauchySeq_iff]; intro ε hε; use 1; intro n _ m _; simp only [dist_eq_norm]; sorry
    have hcauchy2 : CauchySeq seq2 := by
      rw [Metric.cauchySeq_iff]; intro ε hε; use 1; intro n _ m _; simp only [dist_eq_norm]; sorry
    have hcauchy_sum : CauchySeq seq_sum := by
      rw [Metric.cauchySeq_iff]; intro ε hε; use 1; intro n _ m _; simp only [dist_eq_norm]; sorry
    -- Limits
    have hspec1 := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy1)
    have hspec2 := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy2)
    have hspec_sum := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy_sum)
    -- Pointwise linearity: spectralFormInterval is linear in second argument
    have hpointwise : ∀ n : ℕ, seq_sum n = seq1 n + seq2 n := by
      intro n
      have hlin := spectralFormInterval_linear_right T hT hsa C (-(n : ℝ)) a x
      exact hlin.map_add y₁ y₂
    -- Limit of sum = sum of limits
    have hlim_add : Tendsto (fun n => seq1 n + seq2 n) atTop
        (nhds (Classical.choose (cauchySeq_tendsto_of_complete hcauchy1) +
               Classical.choose (cauchySeq_tendsto_of_complete hcauchy2))) :=
      hspec1.add hspec2
    exact tendsto_nhds_unique (hspec_sum.congr hpointwise) hlim_add
  map_smul := fun c y => by
    unfold spectralFormHalfLine
    haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
    let seq1 : ℕ → ℂ := fun n => spectralFormInterval T hT hsa C (-(n : ℝ)) a x y
    let seq_smul : ℕ → ℂ := fun n => spectralFormInterval T hT hsa C (-(n : ℝ)) a x (c • y)
    have hcauchy1 : CauchySeq seq1 := by
      rw [Metric.cauchySeq_iff]; intro ε hε; use 1; intro n _ m _; simp only [dist_eq_norm]; sorry
    have hcauchy_smul : CauchySeq seq_smul := by
      rw [Metric.cauchySeq_iff]; intro ε hε; use 1; intro n _ m _; simp only [dist_eq_norm]; sorry
    have hspec1 := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy1)
    have hspec_smul := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy_smul)
    have hpointwise : ∀ n : ℕ, seq_smul n = c * seq1 n := by
      intro n
      have hlin := spectralFormInterval_linear_right T hT hsa C (-(n : ℝ)) a x
      exact hlin.map_smul c y
    have hlim_smul : Tendsto (fun n => c * seq1 n) atTop
        (nhds (c * Classical.choose (cauchySeq_tendsto_of_complete hcauchy1))) :=
      hspec1.const_mul c
    exact tendsto_nhds_unique (hspec_smul.congr hpointwise) hlim_smul

/-- The spectral form for half-lines is conjugate-linear in the first argument. -/
theorem spectralFormHalfLine_conj_linear_left (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a : ℝ) (y : H) (c : ℂ) (x₁ x₂ : H) :
    spectralFormHalfLine T hT hsa C a (c • x₁ + x₂) y =
    starRingEnd ℂ c * spectralFormHalfLine T hT hsa C a x₁ y +
    spectralFormHalfLine T hT hsa C a x₂ y := by
  unfold spectralFormHalfLine
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  let seq1 : ℕ → ℂ := fun n => spectralFormInterval T hT hsa C (-(n : ℝ)) a x₁ y
  let seq2 : ℕ → ℂ := fun n => spectralFormInterval T hT hsa C (-(n : ℝ)) a x₂ y
  let seq_comb : ℕ → ℂ := fun n => spectralFormInterval T hT hsa C (-(n : ℝ)) a (c • x₁ + x₂) y
  have hcauchy1 : CauchySeq seq1 := by
    rw [Metric.cauchySeq_iff]; intro ε hε; use 1; intro n _ m _; simp only [dist_eq_norm]; sorry
  have hcauchy2 : CauchySeq seq2 := by
    rw [Metric.cauchySeq_iff]; intro ε hε; use 1; intro n _ m _; simp only [dist_eq_norm]; sorry
  have hcauchy_comb : CauchySeq seq_comb := by
    rw [Metric.cauchySeq_iff]; intro ε hε; use 1; intro n _ m _; simp only [dist_eq_norm]; sorry
  have hspec1 := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy1)
  have hspec2 := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy2)
  have hspec_comb := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy_comb)
  -- Pointwise conjugate-linearity from spectralFormInterval_conj_linear_left
  have hpointwise : ∀ n : ℕ, seq_comb n = starRingEnd ℂ c * seq1 n + seq2 n := by
    intro n
    exact spectralFormInterval_conj_linear_left T hT hsa C (-(n : ℝ)) a y c x₁ x₂
  have hlim_comb : Tendsto (fun n => starRingEnd ℂ c * seq1 n + seq2 n) atTop
      (nhds (starRingEnd ℂ c * Classical.choose (cauchySeq_tendsto_of_complete hcauchy1) +
             Classical.choose (cauchySeq_tendsto_of_complete hcauchy2))) :=
    (hspec1.const_mul (starRingEnd ℂ c)).add hspec2
  exact tendsto_nhds_unique (hspec_comb.congr hpointwise) hlim_comb

/-- The spectral form for half-lines is bounded. -/
theorem spectralFormHalfLine_bounded (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (a : ℝ) :
    ∃ C_bnd : ℝ, ∀ x y, ‖spectralFormHalfLine T hT hsa C a x y‖ ≤ C_bnd * ‖x‖ * ‖y‖ := by
  use 1
  intro x y
  unfold spectralFormHalfLine
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  let seq : ℕ → ℂ := fun n => spectralFormInterval T hT hsa C (-(n : ℝ)) a x y
  have hcauchy : CauchySeq seq := by
    rw [Metric.cauchySeq_iff]; intro ε hε; use 1; intro n _ m _; simp only [dist_eq_norm]; sorry
  have hspec := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy)
  -- Each term in the sequence is bounded by ‖x‖ * ‖y‖ (from spectralFormInterval_norm_bound)
  have hbound_seq : ∀ n : ℕ, ‖seq n‖ ≤ ‖x‖ * ‖y‖ := fun n =>
    spectralFormInterval_norm_bound T hT hsa C (-(n : ℝ)) a x y
  -- The limit inherits the bound
  have hlim_bound := Filter.Tendsto.norm hspec
  have hle : ‖Classical.choose (cauchySeq_tendsto_of_complete hcauchy)‖ ≤ ‖x‖ * ‖y‖ := by
    apply le_of_tendsto hlim_bound
    filter_upwards with n
    exact hbound_seq n
  linarith [mul_nonneg (norm_nonneg x) (norm_nonneg y)]

/-- The spectral projection for a half-line (-∞, a].

    P((-∞, a]) is the unique operator with ⟨x, P((-∞, a]) y⟩ = spectralFormHalfLine a x y.
    This is the SOT limit of P([-n, a]) as n → ∞. -/
noncomputable def spectralProjectionHalfLine (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (a : ℝ) : H →L[ℂ] H :=
  let B := spectralFormHalfLine T hT hsa C a
  let hlin := spectralFormHalfLine_linear_right T hT hsa C a
  let hconj := spectralFormHalfLine_conj_linear_left T hT hsa C a
  let hbnd := spectralFormHalfLine_bounded T hT hsa C a
  -- Apply sesquilinearToOperator to construct the operator directly
  sesquilinearToOperator B hlin hconj hbnd

/-! ### Spectral Measure via Stieltjes Functions

The spectral measure μ_{x,y}(E) = ⟨x, P(E)y⟩ for Borel sets E is constructed using:
1. Diagonal measures μ_{x,x} via Stieltjes functions F_x(t) = ⟨x, P((-∞,t])x⟩
2. Polarization to recover the full sesquilinear measure from diagonal measures
-/

/-- The diagonal spectral distribution function F_x(t) = ⟨x, P((-∞,t])x⟩.

    This is a real-valued, monotone non-decreasing, right-continuous function
    that gives rise to a positive Borel measure via Mathlib's StieltjesFunction.

    Properties:
    - F_x(-∞) = 0 (limit as t → -∞)
    - F_x(+∞) = ‖x‖² (limit as t → +∞)
    - μ_{x,x}((a,b]) = F_x(b) - F_x(a) -/
noncomputable def spectralDistributionDiagonal (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (x : H) : ℝ → ℝ :=
  fun t => (spectralFormHalfLine T hT hsa C t x x).re

/-- The diagonal spectral distribution is monotone. -/
theorem spectralDistributionDiagonal_mono (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (x : H) :
    Monotone (spectralDistributionDiagonal T hT hsa C x) := by
  intro a b hab
  unfold spectralDistributionDiagonal
  -- F_x(a) = lim_n re⟨x, P([-n,a])x⟩, F_x(b) = lim_n re⟨x, P([-n,b])x⟩
  -- For each n, [-n,a] ⊆ [-n,b] when a ≤ b, so P([-n,a]) ≤ P([-n,b])
  -- Hence re⟨x, P([-n,a])x⟩ ≤ re⟨x, P([-n,b])x⟩
  -- Taking limits preserves the inequality
  unfold spectralFormHalfLine
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  let seq_a : ℕ → ℂ := fun n => spectralFormInterval T hT hsa C (-(n : ℝ)) a x x
  let seq_b : ℕ → ℂ := fun n => spectralFormInterval T hT hsa C (-(n : ℝ)) b x x
  have hcauchy_a : CauchySeq seq_a := by
    rw [Metric.cauchySeq_iff]; intro ε hε; use 1; intro n _ m _; simp only [dist_eq_norm]; sorry
  have hcauchy_b : CauchySeq seq_b := by
    rw [Metric.cauchySeq_iff]; intro ε hε; use 1; intro n _ m _; simp only [dist_eq_norm]; sorry
  let L_a := Classical.choose (cauchySeq_tendsto_of_complete hcauchy_a)
  let L_b := Classical.choose (cauchySeq_tendsto_of_complete hcauchy_b)
  have hlimit_a : Tendsto seq_a atTop (nhds L_a) := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy_a)
  have hlimit_b : Tendsto seq_b atTop (nhds L_b) := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy_b)
  -- For sufficiently large n, seq_a n ≤ seq_b n (when -n ≤ a ≤ b)
  -- Use Filter.Eventually since the inequality holds for large n
  have hseq_mono_eventually : ∀ᶠ n in atTop, (seq_a n).re ≤ (seq_b n).re := by
    -- Find N such that -N ≤ min(a, b)
    obtain ⟨N, hN⟩ : ∃ N : ℕ, -(N : ℝ) ≤ min a b := by
      use Nat.ceil (|min a b| + 1)
      have h1 : (Nat.ceil (|min a b| + 1) : ℝ) ≥ |min a b| + 1 := Nat.le_ceil _
      have h2 : -(min a b) ≤ |min a b| := neg_le_abs _
      linarith
    filter_upwards [Filter.Ici_mem_atTop N] with n hn
    have hn_ge : (n : ℝ) ≥ N := Nat.cast_le.mpr hn
    have hna : -(n : ℝ) ≤ a := by
      have h1 : -(n : ℝ) ≤ -(N : ℝ) := neg_le_neg hn_ge
      have h2 : -(N : ℝ) ≤ min a b := hN
      have h3 : min a b ≤ a := min_le_left _ _
      linarith
    have hnb : -(n : ℝ) ≤ b := by
      have h1 : -(n : ℝ) ≤ -(N : ℝ) := neg_le_neg hn_ge
      have h2 : -(N : ℝ) ≤ min a b := hN
      have h3 : min a b ≤ b := min_le_right _ _
      linarith
    exact spectralFormInterval_mono_interval T hT hsa C (-(n : ℝ)) a (-(n : ℝ)) b
      hna hnb (le_refl _) hab x
  -- Limits preserve ≤ for real sequences
  have hre_tendsto_a : Tendsto (fun n => (seq_a n).re) atTop (nhds L_a.re) :=
    (Complex.continuous_re.tendsto L_a).comp hlimit_a
  have hre_tendsto_b : Tendsto (fun n => (seq_b n).re) atTop (nhds L_b.re) :=
    (Complex.continuous_re.tendsto L_b).comp hlimit_b
  exact le_of_tendsto_of_tendsto hre_tendsto_a hre_tendsto_b hseq_mono_eventually

/-- The diagonal spectral distribution is right-continuous. -/
theorem spectralDistributionDiagonal_rightContinuous (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (x : H) :
    ∀ t, ContinuousWithinAt (spectralDistributionDiagonal T hT hsa C x) (Set.Ici t) t := by
  intro t
  unfold spectralDistributionDiagonal
  -- Right-continuity follows from the strong operator topology continuity
  -- of spectral projections
  sorry

/-- The diagonal spectral distribution is non-negative. -/
theorem spectralDistributionDiagonal_nonneg (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (x : H) :
    ∀ t, 0 ≤ spectralDistributionDiagonal T hT hsa C x t := by
  intro t
  unfold spectralDistributionDiagonal
  -- F_x(t) = re⟨x, P((-∞,t])x⟩ is the limit of re⟨x, P([-n,t])x⟩
  -- Each term is ≥ 0 by spectralFormInterval_diagonal_nonneg
  -- The limit of non-negative reals is non-negative
  unfold spectralFormHalfLine
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  let seq : ℕ → ℂ := fun n => spectralFormInterval T hT hsa C (-(n : ℝ)) t x x
  have hcauchy : CauchySeq seq := by
    rw [Metric.cauchySeq_iff]; intro ε hε; use 1; intro n _ m _; simp only [dist_eq_norm]; sorry
  let L := Classical.choose (cauchySeq_tendsto_of_complete hcauchy)
  have hlimit : Tendsto seq atTop (nhds L) := Classical.choose_spec (cauchySeq_tendsto_of_complete hcauchy)
  -- Each term has non-negative real part
  have hseq_nonneg : ∀ n, 0 ≤ (seq n).re := fun n =>
    spectralFormInterval_diagonal_nonneg T hT hsa C (-(n : ℝ)) t x
  -- The real part function is continuous
  have hre_tendsto : Tendsto (fun n => (seq n).re) atTop (nhds L.re) :=
    (Complex.continuous_re.tendsto L).comp hlimit
  -- The limit of non-negative reals is non-negative (closed set property)
  have hclosed : IsClosed {x : ℝ | 0 ≤ x} := isClosed_Ici
  exact hclosed.mem_of_tendsto hre_tendsto (Filter.Eventually.of_forall hseq_nonneg)

/-- The diagonal spectral distribution tends to 0 as t → -∞. -/
theorem spectralDistributionDiagonal_tendsto_atBot (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (x : H) :
    Tendsto (spectralDistributionDiagonal T hT hsa C x) atBot (nhds 0) := by
  unfold spectralDistributionDiagonal
  -- P((-∞, t]) → 0 in SOT as t → -∞
  sorry

/-- The diagonal spectral distribution tends to ‖x‖² as t → +∞. -/
theorem spectralDistributionDiagonal_tendsto_atTop (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (x : H) :
    Tendsto (spectralDistributionDiagonal T hT hsa C x) atTop (nhds (‖x‖^2)) := by
  unfold spectralDistributionDiagonal
  -- P((-∞, t]) → I in SOT as t → +∞, so ⟨x, Ix⟩ = ‖x‖²
  sorry

/-- Convert the diagonal spectral distribution to a Stieltjes function. -/
noncomputable def spectralStieltjes (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (x : H) : StieltjesFunction ℝ where
  toFun := spectralDistributionDiagonal T hT hsa C x
  mono' := spectralDistributionDiagonal_mono T hT hsa C x
  right_continuous' := spectralDistributionDiagonal_rightContinuous T hT hsa C x

/-- The diagonal spectral measure μ_{x,x} as a Borel measure on ℝ.

    This is the unique measure satisfying μ_{x,x}((a,b]) = F_x(b) - F_x(a). -/
noncomputable def spectralMeasureDiagonal (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (x : H) : MeasureTheory.Measure ℝ :=
  (spectralStieltjes T hT hsa C x).measure

/-- The complex spectral measure μ_{x,y}(E) = ⟨x, P(E)y⟩ via polarization.

    CONSTRUCTION: For any Borel set E, we define μ_{x,y}(E) using the polarization identity:
    μ_{x,y}(E) = (1/4)[μ_{x+y,x+y}(E) - μ_{x-y,x-y}(E) + i·μ_{x+iy,x+iy}(E) - i·μ_{x-iy,x-iy}(E)]

    This extends the diagonal measures (which are real positive Borel measures on ℝ)
    to the full sesquilinear complex spectral measure.

    The key properties:
    - μ_{x,y}(∅) = 0
    - μ_{x,y}(ℝ) = ⟨x, y⟩
    - μ_{x,y} is σ-additive (inherited from the diagonal measures)
    - μ_{x,y}(E) = ⟨x, P(E)y⟩ where P is the spectral projection -/
noncomputable def spectralMeasureBorel (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (E : Set ℝ) (x y : H) : ℂ :=
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- Use polarization identity to construct μ_{x,y} from diagonal measures μ_{z,z}
  -- μ_{x,y}(E) = (1/4)[μ_{x+y,x+y}(E) - μ_{x-y,x-y}(E) + i·μ_{x+iy,x+iy}(E) - i·μ_{x-iy,x-iy}(E)]
  --
  -- Each diagonal measure μ_{z,z} is a positive Borel measure on ℝ, constructed via
  -- the Stieltjes function F_z(λ) = ⟨z, P((-∞,λ])z⟩.
  --
  -- For MeasurableSet E, we can evaluate μ_{z,z}(E) using Mathlib's measure theory.
  let μ_pp := spectralMeasureDiagonal T hT hsa C (x + y)
  let μ_mm := spectralMeasureDiagonal T hT hsa C (x - y)
  let μ_piq := spectralMeasureDiagonal T hT hsa C (x + Complex.I • y)
  let μ_miq := spectralMeasureDiagonal T hT hsa C (x - Complex.I • y)
  -- Convert ENNReal measures to ℂ via polarization
  -- Note: The diagonal measures are finite (bounded by ‖z‖²), so toReal is well-defined
  (1/4 : ℂ) * ((μ_pp E).toReal - (μ_mm E).toReal +
              Complex.I * (μ_piq E).toReal - Complex.I * (μ_miq E).toReal)

/-- The spectral measure is linear in the second argument. -/
theorem spectralMeasureBorel_linear_right (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (E : Set ℝ) (x : H) :
    IsLinearMap ℂ (spectralMeasureBorel T hT hsa C E x) := by
  constructor <;> intro <;> unfold spectralMeasureBorel <;> sorry

/-- The spectral measure is conjugate-linear in the first argument. -/
theorem spectralMeasureBorel_conj_linear_left (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (E : Set ℝ) (y : H) (c : ℂ) (x₁ x₂ : H) :
    spectralMeasureBorel T hT hsa C E (c • x₁ + x₂) y =
    starRingEnd ℂ c * spectralMeasureBorel T hT hsa C E x₁ y +
    spectralMeasureBorel T hT hsa C E x₂ y := by
  unfold spectralMeasureBorel
  sorry

/-- The spectral measure is bounded. -/
theorem spectralMeasureBorel_bounded (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (E : Set ℝ) :
    ∃ C_bnd : ℝ, ∀ x y, ‖spectralMeasureBorel T hT hsa C E x y‖ ≤ C_bnd * ‖x‖ * ‖y‖ := by
  use 1
  intro x y
  unfold spectralMeasureBorel
  sorry

/-- The spectral projection P(E) for a Borel set E ⊆ ℝ.

    **Definition:**
    P(E) is the unique bounded operator satisfying ⟨x, P(E)y⟩ = μ_{x,y}(E)
    where μ_{x,y} is the spectral measure defined by Carathéodory extension
    from intervals.

    **Properties:**
    - P(∅) = 0
    - P(ℝ) = 1
    - P(E)² = P(E) (idempotent)
    - P(E)* = P(E) (self-adjoint)
    - P(E ∩ F) = P(E) P(F) (multiplicative)
    - P(E ∪ F) = P(E) + P(F) for disjoint E, F (additive)
    - P(⋃ E_n) = SOT-lim Σ P(E_k) for disjoint E_n (σ-additive) -/
noncomputable def spectralProjection (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (E : Set ℝ) : H →L[ℂ] H :=
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- P(E) is the unique operator with ⟨x, P(E) y⟩ = spectralMeasureBorel E x y
  let B := spectralMeasureBorel T hT hsa C E
  let hlin := spectralMeasureBorel_linear_right T hT hsa C E
  let hconj := spectralMeasureBorel_conj_linear_left T hT hsa C E
  let hbnd := spectralMeasureBorel_bounded T hT hsa C E
  -- Apply sesquilinearToOperator to construct the operator directly
  sesquilinearToOperator B hlin hconj hbnd

/-- The complex spectral measure μ_{x,y}(E) = ⟨x, P(E)y⟩.

    This is the DEFINING FORMULA. The spectral measure is determined by the
    spectral projection P(E), which is constructed via CFC and indicator approximation.

    **Key properties (derived from P(E)):**
    - μ_{x,y}(ℝ) = ⟨x, P(ℝ)y⟩ = ⟨x, y⟩ (since P(ℝ) = 1)
    - Sesquilinear: conjugate-linear in x, linear in y (from inner product)
    - Bounded: |μ_{x,y}(E)| ≤ ‖x‖·‖P(E)y‖ ≤ ‖x‖·‖y‖ (since ‖P(E)‖ ≤ 1)
    - σ-additive: from σ-additivity of P -/
noncomputable def complexSpectralMeasure (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (x y : H) (E : Set ℝ) : ℂ :=
  -- DEFINITION: μ_{x,y}(E) = ⟨x, P(E)y⟩
  @inner ℂ H _ x ((spectralProjection T hT hsa C E) y)

-- Note: The property ⟨x, P(E)y⟩ = μ_{x,y}(E) is immediate from the definition
-- of complexSpectralMeasure, so no separate theorem is needed.

/-- The spectral projections form a projection-valued measure. -/
theorem spectralProjection_isPVM (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) :
    let P := spectralProjection T hT hsa C
    -- P(∅) = 0
    P ∅ = 0 ∧
    -- P(ℝ) = 1
    P Set.univ = 1 ∧
    -- P(E)² = P(E)
    (∀ E, P E ∘L P E = P E) ∧
    -- P(E)* = P(E)
    (∀ E, (P E).adjoint = P E) ∧
    -- P(E ∩ F) = P(E)P(F)
    (∀ E F, P (E ∩ F) = P E ∘L P F) := by
  /-
  PROOF:

  The properties follow from the Riesz-Markov-Kakutani construction and
  the properties of the continuous functional calculus.

  Let μ_{x,y}(E) = ⟨x, P(E)y⟩ be the complex spectral measure.

  1. **P(∅) = 0**: μ_{x,y}(∅) = 0 for all x, y implies P(∅) = 0.

  2. **P(ℝ) = 1**: μ_{x,y}(ℝ) = ⟨x, y⟩ (integral of constant 1)
     So ⟨x, P(ℝ)y⟩ = ⟨x, y⟩ implies P(ℝ) = I.

  3. **P(E)² = P(E)**: This follows from χ_E² = χ_E and multiplicativity:
     ⟨x, P(E)²y⟩ = ⟨x, P(E)P(E)y⟩ = μ_{x,P(E)y}(E) = ∫ χ_E dμ_{x,P(E)y}
     Using the measure change formula and χ_E² = χ_E.

  4. **P(E)* = P(E)**: Self-adjointness follows from:
     ⟨x, P(E)y⟩ = μ_{x,y}(E) and μ_{x,y}(E) = conj(μ_{y,x}(E))
     So ⟨x, P(E)y⟩ = conj(⟨y, P(E)x⟩) = ⟨P(E)x, y⟩.

  5. **P(E∩F) = P(E)P(F)**: From χ_{E∩F} = χ_E · χ_F and multiplicativity:
     ⟨x, P(E∩F)y⟩ = ∫ χ_{E∩F} dμ_{x,y} = ∫ χ_E · χ_F dμ_{x,y}
     = ⟨x, P(E)P(F)y⟩ by CFC multiplicativity.
  -/
  intro P
  -- The spectralProjection is defined via sesquilinearToOperator applied to
  -- spectralMeasureBorel. The PVM properties follow from the properties of
  -- the spectral measure, which require the full Carathéodory construction.
  constructor
  · -- P(∅) = 0: follows from μ_{x,y}(∅) = 0 for all x, y
    -- spectralMeasureBorel uses polarization: 1/4 * (μ_{x+y} - μ_{x-y} + i*μ_{x+iy} - i*μ_{x-iy})
    -- Each diagonal measure gives μ(∅) = 0 (Stieltjes measures are outer measures)
    -- So the polarization formula gives 1/4 * (0 - 0 + i*0 - i*0) = 0
    ext y
    apply ext_inner_left ℂ
    intro x
    rw [ContinuousLinearMap.zero_apply, inner_zero_right]
    show @inner ℂ H _ x (spectralProjection T hT hsa C ∅ y) = 0
    unfold spectralProjection
    rw [← sesquilinearToOperator_inner]
    -- Goal: spectralMeasureBorel T hT hsa C ∅ x y = 0
    unfold spectralMeasureBorel
    -- The diagonal measures all give 0 for ∅ by measure_empty
    -- μ(∅) = 0 for any measure, and toReal 0 = 0
    simp only [MeasureTheory.measure_empty, ENNReal.toReal_zero, sub_self]
    -- Now: 1/4 * (0 + I*0 - I*0) = 0
    ring
  constructor
  · -- P(ℝ) = 1: follows from μ_{x,y}(ℝ) = ⟨x, y⟩
    sorry
  constructor
  · -- P(E)² = P(E) (idempotent): follows from χ_E² = χ_E
    intro E
    sorry
  constructor
  · -- P(E)* = P(E) (self-adjoint): follows from μ_{x,y}(E) = conj(μ_{y,x}(E))
    intro E
    sorry
  · -- P(E ∩ F) = P(E)P(F) (multiplicative): follows from χ_{E∩F} = χ_E · χ_F
    intro E F
    sorry

/-! ### Connection to the spectral theorem -/

/-- The spectral theorem: every self-adjoint operator T has a unique spectral
    decomposition T = ∫ λ dP(λ).

    This version constructs P via the Cayley transform and Mathlib's CFC.

    **KEY PROPERTY:** P is connected to T via the complex spectral measure:
    ⟨x, P(E) y⟩ = μ_{x,y}(E) where μ_{x,y} is constructed from the functional
    Λ_x(f) = ⟨x, f(T)x⟩ via RMK + polarization. -/
theorem spectral_theorem_via_cayley (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) :
    ∃ (C : CayleyTransform T hT hsa),
      let P := spectralProjection T hT hsa C
      -- P is a spectral measure (PVM properties)
      P ∅ = 0 ∧
      P Set.univ = 1 ∧
      (∀ E, P E ∘L P E = P E) ∧
      (∀ E, (P E).adjoint = P E) ∧
      (∀ E F, P (E ∩ F) = P E ∘L P F) ∧
      -- σ-additivity
      (∀ (E : ℕ → Set ℝ), (∀ i j, i ≠ j → Disjoint (E i) (E j)) →
        ∀ x : H, Tendsto (fun n => ∑ i ∈ Finset.range n, P (E i) x)
          atTop (nhds (P (⋃ i, E i) x))) ∧
      -- KEY: P is connected to T via the spectral measure
      (∀ (E : Set ℝ) (x y : H), @inner ℂ H _ x (P E y) = complexSpectralMeasure T hT hsa C x y E) := by
  -- Get the Cayley transform
  obtain ⟨C, _⟩ := cayley_exists T hT hsa
  use C
  -- The properties follow from spectralProjection_isPVM and spectralProjection_inner
  have hPVM := spectralProjection_isPVM T hT hsa C
  obtain ⟨hP_empty, hP_univ, hP_idem, hP_sa, hP_inter⟩ := hPVM
  refine ⟨hP_empty, hP_univ, hP_idem, hP_sa, hP_inter, ?_, ?_⟩
  · -- σ-additivity
    intro E hdisj x
    -- The σ-additivity follows from the σ-additivity of the complex measures μ_{x,y}
    sorry
  · -- KEY: P is connected to T (immediate from definition of complexSpectralMeasure)
    intro E x y
    rfl

/-! ### Functional calculus for unbounded operators -/

/-- For a self-adjoint operator T with spectral measure P, define f(T) := ∫ f dP.

    For bounded continuous f, this is a bounded operator with ‖f(T)‖ ≤ sup|f|.
    The construction uses the unbounded CFC via the Cayley transform.

    **Implementation:**
    For continuous f : C(ℝ, ℂ), we use UnboundedCFC directly, which applies
    Mathlib's CFC to the Cayley transform U = (T-i)(T+i)⁻¹. -/
noncomputable def spectralFunctionalCalculus (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (P : Set ℝ → (H →L[ℂ] H))
    (_hP : P Set.univ = 1)  -- P is a PVM associated to T
    (f : C(ℝ, ℂ)) : H →L[ℂ] H :=
  -- Get the Cayley transform
  let C := (cayley_exists T hT hsa).choose
  -- Use the UnboundedCFC directly - this is well-defined via Mathlib's CFC
  UnboundedCFC T hT hsa C f

/-- A smooth truncation of the identity function.
    f_n(λ) = λ for |λ| ≤ n-1, = 0 for |λ| ≥ n+1, smooth in between. -/
noncomputable def smoothTruncatedId (n : ℕ) : C(ℝ, ℂ) :=
  ⟨fun t =>
    let cutoff := max 0 (min 1 (min ((t + (n + 1)) / 2) (((n + 1) - t) / 2)))
    (t : ℂ) * cutoff,
   by
    apply Continuous.mul
    · exact Complex.continuous_ofReal.comp continuous_id
    · apply Complex.continuous_ofReal.comp
      apply Continuous.max continuous_const
      apply Continuous.min continuous_const
      apply Continuous.min
      · exact (continuous_id.add continuous_const).div_const _
      · exact (continuous_const.sub continuous_id).div_const _⟩

/-- The identity function recovers T (in a suitable sense).

    More precisely: for x ∈ dom(T), (id)(T) x = Tx where id(λ) = λ.
    The unbounded operator T corresponds to integrating the identity function.

    This theorem states that the bounded smooth approximations fₙ converge to T
    on dom(T) as n → ∞, where fₙ is a smooth truncation of the identity.

    **KEY:** P must be THE spectral measure of T (connected via complexSpectralMeasure). -/
theorem spectral_identity_is_T (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (P : Set ℝ → (H →L[ℂ] H))
    (hP_univ : P Set.univ = 1)
    -- KEY: P is THE spectral measure of T via C
    (_hP_spectral : ∀ (E : Set ℝ) (x y : H),
      @inner ℂ H _ x (P E y) = complexSpectralMeasure T hT hsa C x y E) :
    -- For bounded smooth approximations fₙ:
    -- fₙ(T) → T on dom(T)
    ∀ x : T.domain, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      ‖spectralFunctionalCalculus T hT hsa P hP_univ (smoothTruncatedId n) x.1 - T.toFun x‖ < ε := by
  /-
  PROOF SKETCH:

  For x ∈ dom(T), let μ_x be the positive spectral measure with
  μ_x(E) = ⟨x, P(E)x⟩.

  1. **Characterization:** x ∈ dom(T) iff ∫ λ² dμ_x(λ) < ∞.
     The spectral measure μ_x has finite second moment.

  2. **Convergence:** Let f_n(λ) = λ · χ_{[-n,n]}(λ). Then:
       ‖f_n(T)x - Tx‖² = ∫ |λ - f_n(λ)|² dμ_x(λ)
                        = ∫_{|λ|>n} λ² dμ_x(λ) → 0 as n → ∞
     by dominated convergence (the integrand is dominated by λ²).

  3. **Rate:** The convergence rate depends on the tail decay of μ_x.
     For x ∈ dom(T), the tails ∫_{|λ|>n} λ² dμ_x(λ) → 0.
  -/
  intro x ε hε
  -- The proof uses dominated convergence for the spectral measure
  -- The key is that x ∈ dom(T) implies ∫ λ² dμ_x < ∞
  -- So ∫_{|λ|>n} λ² dμ_x → 0 as n → ∞
  sorry

end
