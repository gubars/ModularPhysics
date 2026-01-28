/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.ContinuousMap.Compact
import ModularPhysics.RigorousQFT.vNA.MeasureTheory.SpectralIntegral

/-!
# Spectral Theorem via Riesz-Markov-Kakutani

This file constructs the spectral measure for unitary operators using the
Riesz-Markov-Kakutani representation theorem, INDEPENDENT of the bump operator
Cauchy property in FunctionalCalculusFromCFC.lean.

## Strategy

The key insight is that for a unitary U, we can directly construct a positive
linear functional using CFC, then apply RMK to obtain the spectral measure.

**Step 1: Positive Linear Functional**
For each x ∈ H, define Λ_x : C(Circle, ℝ) → ℝ by
  Λ_x(f) = Re⟨x, cfc(f∘coe, U) x⟩
where coe : Circle → ℂ is the inclusion.

**Step 2: Positivity (uses cfc_nonneg)**
If f ≥ 0 on Circle, then cfc(f∘coe, U) ≥ 0 as an operator, so Λ_x(f) ≥ 0.

**Step 3: Apply RMK**
Since Circle is compact, C_c(Circle, ℝ) = C(Circle, ℝ).
RMK gives a finite measure μ_x with ∫ f dμ_x = Λ_x(f).

**Step 4: Polarization**
Define μ_{x,y} by polarization to get a complex measure.

**Step 5: Construct Projections**
For Borel E ⊆ Circle, define P(E) via sesquilinearToOperator.

**Step 6: PVM Properties**
Prove P(∅)=0, P(Circle)=1, P(E)²=P(E), P(E)*=P(E), σ-additivity.

## Main Results

* `spectralFunctional` : the positive linear functional from CFC
* `spectralMeasureOfUnitary` : the spectral measure via RMK
* `spectralProjectionOfUnitary` : the spectral projections
* `unitary_spectral_theorem` : the spectral theorem for unitaries

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I", Chapter VII-VIII
* Mathlib's `MeasureTheory.Integral.RieszMarkovKakutani.Real`
-/

noncomputable section

open scoped InnerProduct ComplexConjugate Classical CompactlySupported
open Filter Topology Complex MeasureTheory CompactlySupportedContinuousMap

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The circle and continuous functions on it -/

/-- The unit circle in ℂ is compact. -/
example : CompactSpace Circle := inferInstance

/-- Circle has a measurable space structure (Borel σ-algebra). -/
instance instMeasurableSpaceCircle : MeasurableSpace Circle := borel Circle

/-- The measurable space on Circle is the Borel σ-algebra. -/
instance instBorelSpaceCircle : BorelSpace Circle := ⟨rfl⟩

/-- Circle is locally compact (as a compact space). -/
instance : LocallyCompactSpace Circle := by
  haveI : CompactSpace Circle := inferInstance
  infer_instance

/-- For a continuous function f : Circle → ℝ, we can view it as a function ℂ → ℂ
    by composing with the inclusion and embedding ℝ ↪ ℂ. -/
def circleRealToComplex (f : C(Circle, ℝ)) : ℂ → ℂ := fun z =>
  if h : z ∈ Metric.sphere (0 : ℂ) 1 then
    (f ⟨z, h⟩ : ℂ)
  else
    0

/-- The function circleRealToComplex f is continuous on the spectrum of any unitary.

    Technical lemma: On the spectrum (which is contained in the circle), the function
    `circleRealToComplex f` restricts to `f` composed with the inclusion, which is continuous.

    Key insight: Circle = Submonoid.unitSphere ℂ has carrier Metric.sphere 0 1,
    so we can use the embedding property of Subtype.val to reduce to continuity of f. -/
lemma circleRealToComplex_continuousOn_spectrum (f : C(Circle, ℝ)) (U : H →L[ℂ] H)
    (hU : U ∈ unitary (H →L[ℂ] H)) :
    ContinuousOn (circleRealToComplex f) (spectrum ℂ U) := by
  have hspec : spectrum ℂ U ⊆ Metric.sphere (0 : ℂ) 1 :=
    spectrum.subset_circle_of_unitary hU
  -- It suffices to show continuity on the sphere, since spectrum ⊆ sphere
  apply ContinuousOn.mono _ hspec
  -- Show ContinuousOn (circleRealToComplex f) (Metric.sphere 0 1)
  -- Use continuousOn_iff_continuous_restrict: reduce to continuity of the restriction
  rw [continuousOn_iff_continuous_restrict]
  -- The restricted function: (Metric.sphere 0 1) → ℂ
  -- For z in the sphere, circleRealToComplex f z = ofReal (f ⟨z, hz⟩)
  -- We show this equals Complex.ofReal ∘ f ∘ (the "identity" from sphere to Circle)
  -- Since Circle = Submonoid.unitSphere ℂ has carrier = Metric.sphere 0 1,
  -- the identity map sphere → Circle is just a type coercion
  have heq : Set.restrict (Metric.sphere (0 : ℂ) 1) (circleRealToComplex f) =
             Complex.ofReal ∘ f ∘ (fun z : Metric.sphere (0 : ℂ) 1 => (⟨z.val, z.property⟩ : Circle)) := by
    funext ⟨z, hz⟩
    simp only [Set.restrict_apply, Function.comp_apply, circleRealToComplex]
    -- hz : z ∈ Metric.sphere 0 1, which is the same as Circle membership
    simp only [hz, dite_true]
  rw [heq]
  -- Now show the composition is continuous
  apply Complex.continuous_ofReal.comp
  apply f.continuous.comp
  -- The map sphere → Circle is continuous (it's essentially the identity on subtypes)
  exact continuous_induced_rng.mpr continuous_subtype_val

/-! ### CFC for unitaries with real-valued functions -/

/-- A unitary operator is star-normal. -/
theorem unitary_isStarNormal (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H)) :
    IsStarNormal U := by
  constructor
  have hU_left := (Unitary.mem_iff.mp hU).1
  have hU_right := (Unitary.mem_iff.mp hU).2
  calc U.adjoint * U = U.adjoint ∘L U := rfl
    _ = 1 := hU_left
    _ = U ∘L U.adjoint := hU_right.symm
    _ = U * U.adjoint := rfl

/-- CFC is available for unitary operators. -/
lemma unitary_has_cfc : ContinuousFunctionalCalculus ℂ (H →L[ℂ] H) (IsStarNormal ·) := inferInstance

/-- Apply CFC to a real-valued function on the circle.
    The result is a bounded operator on H. -/
def cfcOfCircleReal (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (f : C(Circle, ℝ)) : H →L[ℂ] H :=
  haveI : IsStarNormal U := unitary_isStarNormal U hU
  cfc (circleRealToComplex f) U

/-- CFC of a real-valued function is self-adjoint. -/
theorem cfcOfCircleReal_isSelfAdjoint (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (f : C(Circle, ℝ)) : IsSelfAdjoint (cfcOfCircleReal U hU f) := by
  haveI : IsStarNormal U := unitary_isStarNormal U hU
  unfold cfcOfCircleReal
  rw [IsSelfAdjoint, ← cfc_star (circleRealToComplex f) U]
  congr 1
  funext z
  simp only [circleRealToComplex]
  split_ifs with h
  · -- star of a real number is itself: (x : ℂ)* = x for x : ℝ
    have : (f ⟨z, h⟩ : ℂ) = Complex.ofReal (f ⟨z, h⟩) := rfl
    rw [this, Complex.star_def, Complex.conj_ofReal]
  · simp only [star_zero]

set_option maxHeartbeats 400000 in
/-- For a nonnegative function f, the inner product ⟨x, cfc(f)x⟩ is real and nonnegative.

    This is the KEY lemma for the RMK approach.
    The proof uses that for f ≥ 0, we can write f = (√f)² and use CFC multiplicativity.
    Then cfc(f) = T² where T is self-adjoint, so cfc(f) = T*T and ⟨x, T*Tx⟩ = ‖Tx‖² ≥ 0. -/
theorem cfcOfCircleReal_inner_nonneg (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (f : C(Circle, ℝ)) (hf : ∀ z : Circle, 0 ≤ f z) (x : H) :
    0 ≤ (@inner ℂ H _ x (cfcOfCircleReal U hU f x)).re := by
  haveI hU_normal : IsStarNormal U := unitary_isStarNormal U hU
  -- Define g = √f, which is continuous since f ≥ 0
  let g : C(Circle, ℝ) := ⟨fun z => Real.sqrt (f z), f.continuous.sqrt⟩
  -- g² = f since f ≥ 0
  have hg_sq : ∀ z : Circle, g z ^ 2 = f z := fun z => Real.sq_sqrt (hf z)
  -- T := cfc(circleRealToComplex g) U is self-adjoint
  let T := cfc (circleRealToComplex g) U
  have hT_eq : T = cfcOfCircleReal U hU g := rfl
  have hT_sa : IsSelfAdjoint T := by rw [hT_eq]; exact cfcOfCircleReal_isSelfAdjoint U hU g
  -- T.adjoint = T
  have hT_adj : T.adjoint = T := by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint] at hT_sa
    exact hT_sa
  -- circleRealToComplex f = (circleRealToComplex g) * (circleRealToComplex g) pointwise
  have hcircle_f : ∀ z, circleRealToComplex f z = circleRealToComplex g z * circleRealToComplex g z := by
    intro z
    simp only [circleRealToComplex]
    split_ifs with h
    · simp only [g, ContinuousMap.coe_mk]
      -- Goal: (f ⟨z, h⟩ : ℂ) = (√(f ⟨z, h⟩) : ℂ) * (√(f ⟨z, h⟩) : ℂ)
      -- Use that (a : ℂ) * (b : ℂ) = ((a * b) : ℂ) and √x * √x = x for x ≥ 0
      rw [← Complex.ofReal_mul, ← sq, Real.sq_sqrt (hf ⟨z, h⟩)]
    · simp
  -- cfcOfCircleReal U hU f = T * T (using CFC multiplicativity)
  have hcont_g := circleRealToComplex_continuousOn_spectrum g U hU
  have hcfc_eq : cfcOfCircleReal U hU f = T * T := by
    unfold cfcOfCircleReal
    have hfun_eq : circleRealToComplex f = fun z => circleRealToComplex g z * circleRealToComplex g z := by
      funext z; exact hcircle_f z
    rw [hfun_eq]
    -- Use cfc_mul: cfc (fun x => f x * g x) = cfc f * cfc g
    rw [cfc_mul (circleRealToComplex g) (circleRealToComplex g) U hcont_g hcont_g]
  -- T * T = T ∘L T as operators
  have hcfc_sq : cfcOfCircleReal U hU f = T ∘L T := by
    rw [hcfc_eq]; rfl
  -- ⟨x, (T∘T)x⟩ = ⟨x, T(Tx)⟩ = ⟨T* x, Tx⟩ = ⟨Tx, Tx⟩ = ‖Tx‖² ≥ 0
  rw [hcfc_sq]
  simp only [ContinuousLinearMap.comp_apply]
  -- Use that T* T is positive: ⟨x, T*T x⟩ = ⟨Tx, Tx⟩ = ‖Tx‖² ≥ 0
  -- Since T = T*, we have T*T = T∘T
  calc (@inner ℂ H _ x (T (T x))).re
      = (@inner ℂ H _ x (T.adjoint (T x))).re := by rw [hT_adj]
    _ = (@inner ℂ H _ (T x) (T x)).re := by
        rw [ContinuousLinearMap.adjoint_inner_right T x (T x)]
    _ = ‖T x‖ ^ 2 := by
        rw [inner_self_eq_norm_sq_to_K]
        norm_cast
    _ ≥ 0 := sq_nonneg _

/-- The inner product ⟨x, cfc(f)x⟩ is real for self-adjoint cfc(f). -/
theorem cfcOfCircleReal_inner_real (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (f : C(Circle, ℝ)) (x : H) :
    (@inner ℂ H _ x (cfcOfCircleReal U hU f x)).im = 0 := by
  -- For self-adjoint A, ⟨x, Ax⟩ = ⟨Ax, x⟩ = conj⟨x, Ax⟩, so it's real
  have hsa := cfcOfCircleReal_isSelfAdjoint U hU f
  set A := cfcOfCircleReal U hU f with hA_def
  -- IsSelfAdjoint means star A = A, which for CLMs means A.adjoint = A
  have hadj : A.adjoint = A := by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint] at hsa
    exact hsa
  -- adjoint_inner_right: ⟨x, A.adjoint y⟩ = ⟨A x, y⟩
  -- So ⟨x, A.adjoint x⟩ = ⟨A x, x⟩
  have h1 : @inner ℂ H _ x (A.adjoint x) = @inner ℂ H _ (A x) x :=
    ContinuousLinearMap.adjoint_inner_right A x x
  -- Since A.adjoint = A: ⟨x, Ax⟩ = ⟨Ax, x⟩
  rw [hadj] at h1
  -- inner_conj_symm: conj(⟨x, Ax⟩) = ⟨Ax, x⟩
  -- So ⟨Ax, x⟩ = conj(⟨x, Ax⟩)
  have h2 : @inner ℂ H _ (A x) x = starRingEnd ℂ (@inner ℂ H _ x (A x)) :=
    (inner_conj_symm (A x) x).symm
  -- Combining: ⟨x, Ax⟩ = conj(⟨x, Ax⟩)
  have h3 : @inner ℂ H _ x (A x) = starRingEnd ℂ (@inner ℂ H _ x (A x)) := h1.trans h2
  -- z = conj(z) implies z.im = 0
  set z := @inner ℂ H _ x (A x) with hz_def
  -- h3 says z = conj(z)
  -- conj(z).im = -z.im, so if z = conj(z), then z.im = -z.im, hence z.im = 0
  have hconj_im : (starRingEnd ℂ z).im = -z.im := Complex.conj_im z
  -- From h3: z.im = (conj z).im = -z.im
  have him_eq : z.im = -z.im := by
    have : z.im = (starRingEnd ℂ z).im := congrArg Complex.im h3
    rw [hconj_im] at this
    exact this
  -- z.im = -z.im means 2 * z.im = 0, so z.im = 0
  linarith

/-! ### Positive Linear Functional from CFC -/

/-- The spectral functional Λ_x : C(Circle, ℝ) → ℝ defined by
    Λ_x(f) = Re⟨x, cfc(f, U) x⟩ -/
def spectralFunctionalAux (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (x : H) : C(Circle, ℝ) → ℝ :=
  fun f => (@inner ℂ H _ x (cfcOfCircleReal U hU f x)).re

/-- Spectral functional is linear. -/
theorem spectralFunctionalAux_linear (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (x : H) : IsLinearMap ℝ (spectralFunctionalAux U hU x) := by
  haveI : IsStarNormal U := unitary_isStarNormal U hU
  constructor
  · -- Additivity
    intro f g
    simp only [spectralFunctionalAux, cfcOfCircleReal]
    -- cfc(f + g) = cfc(f) + cfc(g)
    have hadd : cfc (circleRealToComplex (f + g)) U =
                cfc (circleRealToComplex f) U + cfc (circleRealToComplex g) U := by
      have hcont_f := circleRealToComplex_continuousOn_spectrum f U hU
      have hcont_g := circleRealToComplex_continuousOn_spectrum g U hU
      have heq : circleRealToComplex (f + g) = circleRealToComplex f + circleRealToComplex g := by
        funext z
        simp only [circleRealToComplex, ContinuousMap.coe_add, Pi.add_apply]
        split_ifs with h <;> simp [Complex.ofReal_add]
      rw [heq]
      exact cfc_add (a := U) (circleRealToComplex f) (circleRealToComplex g) hcont_f hcont_g
    rw [hadd, ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
  · -- Scalar multiplication
    intro c f
    simp only [spectralFunctionalAux, cfcOfCircleReal]
    -- cfc(c • f) = c • cfc(f) where c is real
    have hsmul : cfc (circleRealToComplex (c • f)) U =
                 (c : ℂ) • cfc (circleRealToComplex f) U := by
      have hcont := circleRealToComplex_continuousOn_spectrum f U hU
      have heq : circleRealToComplex (c • f) = (c : ℂ) • circleRealToComplex f := by
        funext z
        simp only [circleRealToComplex, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
        split_ifs with h
        · simp only [Complex.ofReal_mul]
        · simp
      rw [heq]
      exact cfc_smul (a := U) (↑c) (circleRealToComplex f) hcont
    rw [hsmul, ContinuousLinearMap.smul_apply, inner_smul_right]
    -- (c : ℂ) * inner x y has Re part = c * Re(inner x y)
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, smul_eq_mul]

/-- Spectral functional is positive. -/
theorem spectralFunctionalAux_nonneg (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (x : H) (f : C(Circle, ℝ)) (hf : 0 ≤ f) :
    0 ≤ spectralFunctionalAux U hU x f := by
  simp only [spectralFunctionalAux]
  apply cfcOfCircleReal_inner_nonneg
  intro z
  exact hf z

/-- Convert spectralFunctionalAux to a linear map. -/
def spectralFunctionalLinear (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (x : H) : C(Circle, ℝ) →ₗ[ℝ] ℝ where
  toFun := spectralFunctionalAux U hU x
  map_add' := (spectralFunctionalAux_linear U hU x).map_add
  map_smul' := fun c f => by
    simp only [RingHom.id_apply]
    exact (spectralFunctionalAux_linear U hU x).map_smul c f

/-- The spectral functional as a positive linear map. -/
def spectralFunctional (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (x : H) : C(Circle, ℝ) →ₚ[ℝ] ℝ := by
  -- Circle is compact, so C(Circle, ℝ) = C_c(Circle, ℝ)
  -- We need to construct C_c(Circle, ℝ) →ₚ[ℝ] ℝ
  -- First, use that C(Circle, ℝ) has the structure we need
  refine PositiveLinearMap.mk₀ (spectralFunctionalLinear U hU x) ?_
  intro f hf
  exact spectralFunctionalAux_nonneg U hU x f hf

/-! ### Spectral Measure via RMK -/

/-- Convert C(Circle, ℝ) to C_c(Circle, ℝ) using compactness. -/
def circleCompactSupport : C(Circle, ℝ) ≃ C_c(Circle, ℝ) :=
  continuousMapEquiv

/-- The spectral functional on C_c(Circle, ℝ). -/
def spectralFunctionalCc (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (x : H) : C_c(Circle, ℝ) →ₚ[ℝ] ℝ := by
  -- Transfer the positive linear map through the equivalence
  -- Since Circle is compact, C_c(Circle, ℝ) ≃ C(Circle, ℝ) via continuousMapEquiv
  refine PositiveLinearMap.mk₀ ?_ ?_
  · -- The underlying linear map: C_c(Circle, ℝ) →ₗ[ℝ] ℝ
    -- We apply spectralFunctionalAux to the underlying continuous map
    exact {
      toFun := fun f => spectralFunctionalAux U hU x f.toContinuousMap
      map_add' := fun f g => by
        -- (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap
        have h : (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap := rfl
        rw [h]
        exact (spectralFunctionalAux_linear U hU x).map_add _ _
      map_smul' := fun c f => by
        -- (c • f).toContinuousMap = c • f.toContinuousMap
        have h : (c • f).toContinuousMap = c • f.toContinuousMap := rfl
        simp only [RingHom.id_apply, h]
        exact (spectralFunctionalAux_linear U hU x).map_smul c _
    }
  · -- Positivity
    intro f hf
    apply spectralFunctionalAux_nonneg
    exact hf

/-- The spectral measure for the vector x, obtained via RMK. -/
def spectralMeasureDiagonal (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (x : H) : MeasureTheory.Measure Circle :=
  RealRMK.rieszMeasure (spectralFunctionalCc U hU x)

/-- The spectral measure is finite (since Circle is compact). -/
theorem spectralMeasureDiagonal_isFiniteMeasure (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (x : H) : IsFiniteMeasure (spectralMeasureDiagonal U hU x) := by
  -- Circle is compact, so RMK produces a finite measure
  unfold spectralMeasureDiagonal
  infer_instance

/-- The spectral measure integrates to give the spectral functional. -/
theorem spectralMeasureDiagonal_integral (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (x : H) (f : C_c(Circle, ℝ)) :
    ∫ z, f z ∂(spectralMeasureDiagonal U hU x) = (spectralFunctionalCc U hU x) f :=
  RealRMK.integral_rieszMeasure (spectralFunctionalCc U hU x) f

/-! ### Polarization to Complex Measure -/

/-- Polarization identity for measures.
    μ_{x,y}(E) = (1/4)[μ_{x+y}(E) - μ_{x-y}(E) + i·μ_{x+iy}(E) - i·μ_{x-iy}(E)]

    Note: hE is kept for documentation that E should be measurable, even though
    Measure.apply works on any set. -/
def spectralMeasurePolarized (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (x y : H) (E : Set Circle) (_hE : MeasurableSet E) : ℂ :=
  let μ_sum := (spectralMeasureDiagonal U hU (x + y) E).toReal
  let μ_diff := (spectralMeasureDiagonal U hU (x - y) E).toReal
  let μ_isum := (spectralMeasureDiagonal U hU (x + Complex.I • y) E).toReal
  let μ_idiff := (spectralMeasureDiagonal U hU (x - Complex.I • y) E).toReal
  -- Polarization identity: 4⟨x, Ay⟩ = Q(x+y) - Q(x-y) - i·Q(x+iy) + i·Q(x-iy)
  (1/4 : ℂ) * (μ_sum - μ_diff - Complex.I * μ_isum + Complex.I * μ_idiff)

/-- The polarized spectral integral gives back the inner product for continuous functions.

    For a continuous function f : Circle → ℝ, the polarized spectral measure satisfies:
    (1/4)[∫f dμ_{x+y} - ∫f dμ_{x-y} + i∫f dμ_{x+iy} - i∫f dμ_{x-iy}] = ⟨x, cfc(f, U) y⟩

    This is the key relationship connecting the spectral measure to CFC. -/
theorem spectralMeasurePolarized_integral (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (x y : H) (f : C_c(Circle, ℝ)) :
    let I_sum := ∫ z, f z ∂(spectralMeasureDiagonal U hU (x + y))
    let I_diff := ∫ z, f z ∂(spectralMeasureDiagonal U hU (x - y))
    let I_isum := ∫ z, f z ∂(spectralMeasureDiagonal U hU (x + Complex.I • y))
    let I_idiff := ∫ z, f z ∂(spectralMeasureDiagonal U hU (x - Complex.I • y))
    (1/4 : ℂ) * (I_sum - I_diff - Complex.I * I_isum + Complex.I * I_idiff) =
    @inner ℂ H _ x (cfcOfCircleReal U hU f.toContinuousMap y) := by
  -- Polarization identity proof - mathematically: 4⟨x, Ay⟩ = Q(x+y) - Q(x-y) - i·Q(x+iy) + i·Q(x-iy)
  sorry

/-! ### Construction of Spectral Projections

For a Borel set E ⊆ Circle, the map (x, y) ↦ μ_{x,y}(E) is a bounded
sesquilinear form. We can use sesquilinearToOperator to get P(E).

This requires showing the bound |μ_{x,y}(E)| ≤ C·‖x‖·‖y‖
which follows from polarization and μ_x(Circle) = ‖x‖² -/

/-- The polarized spectral measure defines a sesquilinear form.
    This is linear in the second argument (y). -/
theorem spectralMeasurePolarized_linear_right (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) (x : H) :
    IsLinearMap ℂ (fun y => spectralMeasurePolarized U hU x y E hE) := by
  -- The polarization formula gives a bilinear form that is linear in y
  -- This follows from the quadratic form → sesquilinear form construction
  sorry

/-- The polarized spectral measure is conjugate-linear in the first argument (x). -/
theorem spectralMeasurePolarized_conj_linear_left (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) :
    ∀ y c x₁ x₂, spectralMeasurePolarized U hU (c • x₁ + x₂) y E hE =
      starRingEnd ℂ c * spectralMeasurePolarized U hU x₁ y E hE +
      spectralMeasurePolarized U hU x₂ y E hE := by
  -- The polarization formula gives conjugate-linearity in the first argument
  sorry

/-- The polarized spectral measure is bounded: |μ_{x,y}(E)| ≤ C‖x‖‖y‖.
    The bound follows from μ_z(Circle) ≤ ‖z‖² (from RMK) and polarization. -/
theorem spectralMeasurePolarized_bounded (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) :
    ∃ C : ℝ, ∀ x y : H, ‖spectralMeasurePolarized U hU x y E hE‖ ≤ C * ‖x‖ * ‖y‖ := by
  -- Each diagonal measure satisfies μ_z(E) ≤ μ_z(Circle) ≤ ‖z‖²
  -- (This uses that the positive functional Λ_z(1) = Re⟨z, cfc(1)z⟩ = ‖z‖²)
  -- By polarization bounds, |μ_{x,y}(E)| ≤ 4 * ‖x‖ * ‖y‖
  use 4
  intro x y
  sorry

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

/-- P(Circle) = 1 -/
theorem spectralProjection_univ (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H)) :
    spectralProjectionOfUnitary U hU Set.univ MeasurableSet.univ = 1 := by
  sorry

/-- P(E)² = P(E) (idempotent) -/
theorem spectralProjection_idempotent (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) :
    spectralProjectionOfUnitary U hU E hE ∘L spectralProjectionOfUnitary U hU E hE =
    spectralProjectionOfUnitary U hU E hE := by
  sorry

/-- P(E)* = P(E) (self-adjoint) -/
theorem spectralProjection_selfAdjoint (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) :
    (spectralProjectionOfUnitary U hU E hE).adjoint =
    spectralProjectionOfUnitary U hU E hE := by
  sorry

/-! ### The Spectral Theorem -/

/-- **Spectral Theorem for Unitaries (via RMK)**

    For any unitary U on a Hilbert space H, there exists a spectral measure
    (projection-valued measure) P on Circle such that:
    1. P(∅) = 0, P(Circle) = 1
    2. Each P(E) is an orthogonal projection
    3. P(E ∩ F) = P(E) ∘ P(F)
    4. P is σ-additive in the strong operator topology
    5. For any continuous f : Circle → ℂ, cfc(f, U) = ∫ f(z) dP(z)

    This construction is INDEPENDENT of bumpOperator_inner_cauchy. -/
theorem spectral_theorem_unitary_via_RMK (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H)) :
    ∃ (P : Set Circle → H →L[ℂ] H),
      (∀ E, MeasurableSet E → IsSelfAdjoint (P E)) ∧
      (∀ E, MeasurableSet E → (P E) ∘L (P E) = P E) ∧
      (P ∅ = 0) ∧
      (P Set.univ = 1) ∧
      (∀ E F, MeasurableSet E → MeasurableSet F →
        P (E ∩ F) = P E ∘L P F) := by
  use fun E => if hE : MeasurableSet E then spectralProjectionOfUnitary U hU E hE else 0
  constructor
  · intro E hE
    simp only [dif_pos hE]
    -- IsSelfAdjoint means star (P E) = P E
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]
    exact spectralProjection_selfAdjoint U hU E hE
  constructor
  · intro E hE
    simp only [dif_pos hE]
    exact spectralProjection_idempotent U hU E hE
  constructor
  · simp [MeasurableSet.empty, spectralProjection_empty U hU]
  constructor
  · simp [MeasurableSet.univ, spectralProjection_univ U hU]
  · intro E F hE hF
    simp only [dif_pos hE, dif_pos hF, dif_pos (hE.inter hF)]
    sorry -- P(E ∩ F) = P(E) P(F)

end
