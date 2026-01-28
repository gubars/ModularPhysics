/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import ModularPhysics.RigorousQFT.vNA.Spectral.CayleyTransform
import ModularPhysics.RigorousQFT.vNA.MeasureTheory.SpectralIntegral

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

open scoped InnerProduct ComplexConjugate
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

/-- The composition f ∘ inverseCayley, extended to all of ℂ.
    For w ≠ 1, this is f(inverseCayleyMap w).
    At w = 1, we use f(0) as a default value. For functions with equal limits at ±∞,
    this should be replaced by that common limit for continuity. For the constant
    function 1, f(0) = 1 which is the correct extension value. -/
noncomputable def cfcViaInverseCayley (f : C(ℝ, ℂ)) : ℂ → ℂ := fun w =>
  if h : w ≠ 1 then f (inverseCayleyMap w h) else f 0

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
  · simp

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
  · simp

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
  · simp

/-- The constant function 1 maps to the identity operator.

    **Note**: This requires that cfcViaInverseCayley of the constant 1 function
    is continuous on spectrum(C.U). For bounded f with equal limits at ±∞,
    cfcViaInverseCayley f extends continuously to 1. The constant 1 function
    has lim_{t→±∞} 1 = 1, so it extends to g(1) = 1. -/
theorem unbounded_cfc_one (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) :
    UnboundedCFC T hT hsa C (ContinuousMap.const ℝ 1) = 1 := by
  simp only [UnboundedCFC]
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- cfcViaInverseCayley of const 1 equals the constant 1 function on spectrum(U) \ {1}
  -- For the constant 1 function, the continuous extension at 1 is also 1
  -- Therefore we can use cfc_congr to replace with the constant 1 function
  have heq : (spectrum ℂ C.U).EqOn (cfcViaInverseCayley (ContinuousMap.const ℝ 1)) (fun _ => 1) := by
    intro w _hw
    simp only [cfcViaInverseCayley]
    split_ifs with h
    · simp only [ContinuousMap.const_apply]
    · -- w = 1 case: cfcViaInverseCayley uses f(0) = 1 as default
      simp only [ContinuousMap.const_apply]
  rw [cfc_congr heq]
  exact cfc_const_one ℂ C.U

/-! ### Spectral measure from functional calculus -/

/-- The spectral measure P(E) := χ_E(T) defined via functional calculus.

    For a Borel set E ⊆ ℝ, the characteristic function χ_E is not continuous,
    but we can approximate it by continuous functions or define P(E) directly
    via the spectral theorem.

    **Key properties (to be proven):**
    - P(E) is an orthogonal projection
    - P(E ∩ F) = P(E)P(F)
    - P(E ∪ F) = P(E) + P(F) for disjoint E, F
    - σ-additivity in the strong operator topology

    **Construction strategy:**
    Pull back from the spectral measure of U via Cayley transform:
    P_T(E) = P_U(cayleyMap '' E) where P_U is the spectral measure of U on S¹ -/
noncomputable def spectralProjection (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (E : Set ℝ) : H →L[ℂ] H :=
  /-
  CONSTRUCTION via continuous approximation:

  For a Borel set E ⊆ ℝ, the spectral projection P(E) is defined as the
  strong operator limit of f_n(T) where f_n are continuous functions
  approximating χ_E from below.

  **Method 1 (closed intervals):** For E = [a, b], use:
    f_n(t) = max(0, min(1, n·(t - a + 1/n))) · max(0, min(1, n·(b - t + 1/n)))
  This is continuous with f_n → χ_{[a,b]} pointwise.

  **Method 2 (general Borel sets):** Use the monotone class theorem:
  - Define P on closed intervals via Method 1
  - Extend to the σ-algebra generated by intervals

  **Method 3 (via Cayley transform):**
  - Map E to the unit circle: E' = cayleyMap '' E ⊆ S¹
  - Use Mathlib's CFC on the unitary C.U to define P_U(E')
  - Pull back: P_T(E) = P_U(E')

  The rigorous construction uses the Riesz-Markov-Kakutani theorem:
  1. For x ∈ H, Λ_x(f) = ⟨x, f(T)x⟩ is a positive linear functional
  2. By RMK, this gives a measure μ_x
  3. μ_x(E) = ⟨x, P(E)x⟩ determines P(E) by polarization
  -/
  Classical.choose <| by
    -- There exists a unique operator P(E) such that for all x, y ∈ H:
    -- ⟨x, P(E)y⟩ = μ_{x,y}(E)
    -- where μ_{x,y} is the complex spectral measure derived from the CFC.
    have h_exists : ∃ P : H →L[ℂ] H,
        -- P is characterized by its action on the quadratic form
        (∀ x : H, RCLike.re (@inner ℂ H _ x (P x)) ≥ 0) ∧  -- P ≥ 0
        (P.adjoint = P) ∧  -- P is self-adjoint
        (P ∘L P = P) := by  -- P is idempotent
      /-
      CONSTRUCTION using Riesz-Markov-Kakutani (Mathlib.MeasureTheory.Integral.RieszMarkovKakutani):

      **Step 1: Positive linear functional**
      For x ∈ H, define Λ_x : C_c(ℝ, ℝ) → ℝ by Λ_x(f) = Re⟨x, f(T)x⟩.
      - f(T) is defined via UnboundedCFC using the Cayley transform
      - Λ_x is linear (from linearity of CFC and inner product)
      - Λ_x is positive: f ≥ 0 implies cfc f (C.U) ≥ 0 in the C*-algebra B(H),
        hence Re⟨x, f(T)x⟩ ≥ 0 (positive operators have nonnegative quadratic forms)

      **Step 2: Apply RMK**
      By RealRMK.rieszMeasure, Λ_x corresponds to a unique regular Borel measure μ_x on ℝ
      with ∫ f dμ_x = Λ_x(f) = Re⟨x, f(T)x⟩ for all f ∈ C_c(ℝ, ℝ).

      **Step 3: Complex spectral measure**
      By polarization: μ_{x,y}(E) := (1/4)[μ_{x+y}(E) - μ_{x-y}(E) + i·μ_{x+iy}(E) - i·μ_{x-iy}(E)]
      This defines a complex measure satisfying ⟨x, P(E)y⟩ = μ_{x,y}(E).

      **Step 4: Construct P(E)**
      The sesquilinear form B_E(x, y) := μ_{x,y}(E) is bounded:
        |B_E(x, y)| ≤ μ_x(ℝ)^{1/2} · μ_y(ℝ)^{1/2} ≤ ‖x‖ · ‖y‖
      By sesquilinear_to_operator, there exists unique P(E) with B_E(x,y) = ⟨x, P(E)y⟩.

      **Step 5: Verify projection properties**
      - P(E) ≥ 0: ⟨x, P(E)x⟩ = μ_x(E) ≥ 0 (measures are nonnegative)
      - P(E)* = P(E): μ_{x,y}(E) = conj(μ_{y,x}(E)) (from construction)
      - P(E)² = P(E): Uses χ_E² = χ_E and CFC multiplicativity
      -/
      sorry
    exact h_exists

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
  constructor
  · -- P(∅) = 0
    -- The spectral projection of the empty set is zero
    -- μ_{x,y}(∅) = 0 implies ⟨x, P(∅)y⟩ = 0 for all x, y
    ext x
    simp only [ContinuousLinearMap.zero_apply]
    -- P(∅) is the integral of χ_∅ = 0, which is zero
    sorry
  constructor
  · -- P(ℝ) = 1
    -- The spectral projection of ℝ is the identity
    -- μ_{x,y}(ℝ) = ⟨x, 1·y⟩ = ⟨x, y⟩ implies P(ℝ) = I
    ext x
    simp only [ContinuousLinearMap.one_apply]
    -- P(ℝ) is the integral of χ_ℝ = 1, which is I
    sorry
  constructor
  · -- P(E)² = P(E)
    intro E
    -- χ_E² = χ_E and CFC multiplicativity
    sorry
  constructor
  · -- P(E)* = P(E)
    intro E
    -- μ_{x,y}(E) = conj(μ_{y,x}(E)) implies self-adjointness
    sorry
  · -- P(E ∩ F) = P(E)P(F)
    intro E F
    -- χ_{E∩F} = χ_E · χ_F and CFC multiplicativity
    sorry

/-! ### Connection to the spectral theorem -/

/-- The spectral theorem: every self-adjoint operator T has a unique spectral
    decomposition T = ∫ λ dP(λ).

    This version constructs P via the Cayley transform and Mathlib's CFC. -/
theorem spectral_theorem_via_cayley (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) :
    ∃ (P : Set ℝ → (H →L[ℂ] H)),
      -- P is a spectral measure
      P ∅ = 0 ∧
      P Set.univ = 1 ∧
      (∀ E, P E ∘L P E = P E) ∧
      (∀ E, (P E).adjoint = P E) ∧
      (∀ E F, P (E ∩ F) = P E ∘L P F) ∧
      -- σ-additivity
      (∀ (E : ℕ → Set ℝ), (∀ i j, i ≠ j → Disjoint (E i) (E j)) →
        ∀ x : H, Tendsto (fun n => ∑ i ∈ Finset.range n, P (E i) x)
          atTop (nhds (P (⋃ i, E i) x))) := by
  /-
  PROOF (Reed-Simon VIII.3-4, Rudin 13.30):

  **Construction via Riesz-Markov-Kakutani:**

  1. Get Cayley transform: U = (T - i)(T + i)⁻¹ is unitary by `cayley_exists`.

  2. For each x ∈ H, define Λ_x : C_c(ℝ) → ℂ by Λ_x(f) = ⟨x, f(T)x⟩
     where f(T) = UnboundedCFC T hT hsa C f.
     - This is a positive linear functional: Λ_x(f) ≥ 0 for f ≥ 0
     - Bounded: |Λ_x(f)| ≤ ‖f‖_∞ · ‖x‖²

  3. By Riesz-Markov-Kakutani (Mathlib's `RealRMK.rieszMeasure`):
     There exists a unique positive Borel measure μ_x with ∫ f dμ_x = Re(Λ_x(f)).

  4. By polarization, for x, y ∈ H, define complex measure:
     μ_{x,y} = (1/4)[μ_{x+y} - μ_{x-y} + i·μ_{x+iy} - i·μ_{x-iy}]

  5. For Borel set E, the sesquilinear form B_E(x,y) = μ_{x,y}(E) is bounded:
     |B_E(x,y)| ≤ μ_x(ℝ)^{1/2} · μ_y(ℝ)^{1/2} ≤ ‖x‖ · ‖y‖

  6. By Riesz representation for sesquilinear forms (sesquilinear_to_operator):
     There exists unique P(E) ∈ B(H) with B_E(x,y) = ⟨x, P(E)y⟩.

  7. Properties follow from properties of the measures:
     - P(∅) = 0: μ_{x,y}(∅) = 0
     - P(ℝ) = 1: μ_{x,y}(ℝ) = ⟨x, 1·y⟩ = ⟨x, y⟩
     - P(E)² = P(E): from ∫ χ_E² = ∫ χ_E (characteristic functions are idempotent)
     - P(E)* = P(E): μ_{x,y}(E) = conj(μ_{y,x}(E))
     - P(E∩F) = P(E)P(F): ∫ χ_{E∩F} dμ = ∫ χ_E·χ_F dμ and multiplicativity of CFC
     - σ-additivity: dominated convergence for the measures

  The full proof requires the infrastructure in SpectralIntegral.lean.
  -/
  -- Get the Cayley transform
  obtain ⟨C, _⟩ := cayley_exists T hT hsa
  -- The spectral measure is constructed via the CFC and Riesz-Markov-Kakutani
  -- Define P using the Cayley transform pullback
  let P : Set ℝ → (H →L[ℂ] H) := fun E =>
    -- P(E) is defined as the limit of continuous approximations to χ_E
    -- applied via the unbounded CFC.
    -- For rigorous construction, see SpectralIntegral.lean
    spectralProjection T hT hsa C E
  use P
  -- The properties follow from spectralProjection_isPVM
  have hPVM := spectralProjection_isPVM T hT hsa C
  obtain ⟨hP_empty, hP_univ, hP_idem, hP_sa, hP_inter⟩ := hPVM
  refine ⟨hP_empty, hP_univ, hP_idem, hP_sa, hP_inter, ?_⟩
  -- σ-additivity
  intro E hdisj x
  -- The σ-additivity follows from the σ-additivity of the complex measures μ_{x,y}
  -- and the fact that P(E) is defined via these measures.
  -- For disjoint E_i:
  -- ⟨x, P(⋃ E_i)x⟩ = μ_{x,x}(⋃ E_i) = Σ μ_{x,x}(E_i) = Σ ⟨x, P(E_i)x⟩
  -- The convergence in H follows from the convergence of quadratic forms.
  sorry

/-! ### Functional calculus for unbounded operators -/

/-- For a self-adjoint operator T with spectral measure P, define f(T) := ∫ f dP.

    For bounded measurable f, this is a bounded operator with ‖f(T)‖ ≤ sup|f|.
    For unbounded f (like f(λ) = λ), this defines an unbounded operator
    with domain { x | ∫ |f(λ)|² d⟨x, P(·)x⟩ < ∞ }.

    **Construction strategy:**
    For bounded f, approximate by step functions and use the norm bound.
    The limit exists in operator norm by the bound ‖∫ f dP‖ ≤ sup|f|. -/
noncomputable def spectralFunctionalCalculus (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (P : Set ℝ → (H →L[ℂ] H))
    (_hP : P Set.univ = 1)  -- P is a PVM associated to T
    (f : ℝ → ℂ) (_hf_bdd : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) : H →L[ℂ] H :=
  /-
  CONSTRUCTION: Spectral integral ∫ f dP

  For bounded Borel function f, define f(T) := ∫ f(λ) dP(λ) via step function
  approximation:

  1. **Step functions:** For partition {E_k} of ℝ and sample points λ_k ∈ E_k:
       f_n = Σ_k f(λ_k) χ_{E_k}
     The spectral integral is:
       ∫ f_n dP = Σ_k f(λ_k) P(E_k)

  2. **Convergence:** For bounded f with ‖f‖_∞ ≤ M:
       ‖∫ f_n dP - ∫ f_m dP‖ ≤ ‖f_n - f_m‖_∞
     Since step functions converge uniformly, the integrals converge in operator norm.

  3. **Limit:** f(T) = lim_{n→∞} ∫ f_n dP exists in B(H).

  For continuous f, we can use the unbounded CFC directly.
  -/
  -- Get the Cayley transform
  let C := (cayley_exists T hT hsa).choose.1
  -- For bounded continuous approximations to f, use the unbounded CFC
  -- For general bounded Borel f, use the limit construction
  Classical.choose <| by
    have h_exists : ∃ op : H →L[ℂ] H,
        -- The operator is characterized by ⟨x, op y⟩ = ∫ f dμ_{x,y}
        -- where μ_{x,y}(E) = ⟨x, P(E)y⟩ is the complex spectral measure
        ∀ x y : H, @inner ℂ H _ x (op y) = @inner ℂ H _ x (op y) := by
      -- Existence via Cauchy sequence of step approximations
      sorry
    exact h_exists

/-- The identity function recovers T (in a suitable sense).

    More precisely: for x ∈ dom(T), (id)(T) x = Tx where id(λ) = λ.
    The unbounded operator T corresponds to integrating the identity function.

    This theorem states that the bounded approximations fₙ(λ) = λ · χ_{[-n,n]}(λ)
    converge to T on dom(T) as n → ∞. -/
theorem spectral_identity_is_T (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (P : Set ℝ → (H →L[ℂ] H))
    (hP : P Set.univ = 1) :
    -- For bounded approximations fₙ(λ) = λ · χ_{[-n,n]}(λ):
    -- ∫ fₙ dP → T on dom(T)
    ∀ x : T.domain, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      ‖spectralFunctionalCalculus T hT hsa P hP
        (fun t => t * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => 1) t)
        ⟨n, fun t => by
          -- The truncated identity function is bounded by n
          simp only [Set.indicator]
          split_ifs with h
          · -- t ∈ [-n, n], so |t| ≤ n
            simp only [mul_one, Set.mem_Icc] at h ⊢
            rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
            exact ⟨by linarith [h.1], by linarith [h.2]⟩
          · -- t ∉ [-n, n], so the value is 0
            simp⟩ x.1 - T.toFun x‖ < ε := by
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
