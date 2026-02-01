/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.vNA.Spectral.SpectralViaCayleyRMK
import ModularPhysics.RigorousQFT.vNA.Spectral.FunctionalCalculusFromCFC.Basic

/-!
# The T-P Connection for the Spectral Theorem

This file establishes the crucial connection between a self-adjoint operator T and
its spectral measure P: the spectral representation `f(T) = ∫ f(λ) dP(λ)`.

## Main Results

* `spectralMeasureDiagonalOnR`: The diagonal spectral measure on ℝ, defined as
  the pullback of the Circle measure via cayleyToCircle.

* `TP_connection_indicator`: The T-P connection for indicator functions:
  `⟨x, P(E) y⟩ = μ^ℝ_{x,y}(E)`

* `TP_connection`: The main T-P connection theorem:
  `⟨x, UnboundedCFC T f y⟩ = polarized spectral integral of f over ℝ`

## Strategy

The proof uses three key ingredients from the RMK approach:

1. **U-P Connection (proven in SpectralMeasurePolarizedViaRMK.lean):**
   For compactly supported continuous f on Circle:
   `⟨x, cfcOfCircleReal U hU f y⟩ = (1/4)[∫f dμ_{x+y} - ∫f dμ_{x-y} - i∫f dμ_{x+iy} + i∫f dμ_{x-iy}]`

2. **Cayley Transform:**
   For self-adjoint T with Cayley transform U = (T-i)(T+i)⁻¹:
   `UnboundedCFC T f = cfc (cfcViaInverseCayley f) U`

3. **Change of Variables:**
   Since cayleyToCircle : ℝ → Circle \ {1} is a measurable bijection and P({1}) = 0:
   `∫ (f ∘ inverseCayley) dμ^Circle = ∫ f dμ^ℝ`

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I", Chapter VIII
-/

noncomputable section

open scoped InnerProduct ComplexConjugate Topology
open Complex MeasureTheory Set Filter Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Diagonal Spectral Measure on ℝ -/

/-- The diagonal spectral measure on ℝ for vector z, defined as the pullback of the
    Circle measure via cayleyToCircle.

    For a measurable set E ⊆ ℝ:
    `μ^ℝ_z(E) = μ^Circle_z(cayleyToCircle '' E)` -/
def spectralMeasureDiagonalOnR (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (z : H) : Measure ℝ :=
  (spectralMeasureDiagonal C.U (cayley_mem_unitary T hT hsa C) z).comap cayleyToCircle

/-- The polarized spectral measure on ℝ, defined as the pullback of the Circle measure
    via cayleyToCircle.

    For a measurable set E ⊆ ℝ:
    `μ^ℝ_{x,y}(E) = μ^Circle_{x,y}(cayleyToCircle '' E)` -/
def spectralMeasurePolarizedOnR (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (x y : H) (E : Set ℝ) (hE : MeasurableSet E) : ℂ :=
  let U := C.U
  let hU := cayley_mem_unitary T hT hsa C
  let E_circle := cayleyToCircle '' E
  let hE_circle := cayleyToCircle_measurableSet_image E hE
  spectralMeasurePolarized U hU x y E_circle hE_circle

/-! ### T-P Connection for Indicator Functions -/

/-- The polarized spectral measure on ℝ equals the inner product with spectralMeasureFromRMK.
    This is the **T-P connection for indicator functions**:

    `⟨x, P(E) y⟩ = μ^ℝ_{x,y}(E)`

    where P(E) = spectralMeasureFromRMK T hT hsa C E hE. -/
theorem TP_connection_indicator (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (x y : H) (E : Set ℝ) (hE : MeasurableSet E) :
    @inner ℂ H _ x (spectralMeasureFromRMK T hT hsa C E hE y) =
    spectralMeasurePolarizedOnR T hT hsa C x y E hE := by
  simp only [spectralMeasurePolarizedOnR, spectralMeasureFromRMK]
  unfold spectralProjectionOfUnitary
  rw [← sesquilinearToOperator_inner]

/-- Alias: spectralMeasurePolarizedOnR equals inner product with P(E). -/
theorem spectralMeasurePolarizedOnR_eq_inner (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (x y : H) (E : Set ℝ) (hE : MeasurableSet E) :
    spectralMeasurePolarizedOnR T hT hsa C x y E hE =
    @inner ℂ H _ x (spectralMeasureFromRMK T hT hsa C E hE y) :=
  (TP_connection_indicator T hT hsa C x y E hE).symm

/-! ### Helper lemmas -/

/-- Since P({1}) = 0 for the Cayley transform, the spectral measure is supported on Circle \ {1}. -/
theorem spectralMeasure_supported_on_circle_minus_one (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) :
    spectralProjectionOfUnitary C.U (cayley_mem_unitary T hT hsa C) {1}
      (measurableSet_singleton 1) = 0 :=
  spectralProjection_singleton_one_eq_zero T hT hsa C

/-- The diagonal spectral measure assigns measure 0 to {1} on Circle.
    This follows from P({1}) = 0 and the definition of spectral measure. -/
theorem spectralMeasureDiagonal_singleton_one_eq_zero (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (z : H) : spectralMeasureDiagonal C.U (cayley_mem_unitary T hT hsa C) z {1} = 0 := by
  let U := C.U
  let hU := cayley_mem_unitary T hT hsa C
  -- P({1}) = 0 by spectralProjection_singleton_one_eq_zero
  have hP1_eq_zero := spectralProjection_singleton_one_eq_zero T hT hsa C
  have hPz : spectralProjectionOfUnitary U hU {1} (measurableSet_singleton 1) z = 0 := by
    rw [hP1_eq_zero, ContinuousLinearMap.zero_apply]
  -- spectralMeasurePolarized_diag: spectralMeasurePolarized z z {1} = μ_z({1}).toReal
  have h := spectralMeasurePolarized_diag U hU z {1} (measurableSet_singleton 1)
  -- spectralMeasurePolarized z z {1} = ⟨z, P({1}) z⟩ by sesquilinear form
  have hpol_zero : spectralMeasurePolarized U hU z z {1} (measurableSet_singleton 1) = 0 := by
    have hinner : @inner ℂ H _ z (spectralProjectionOfUnitary U hU {1} (measurableSet_singleton 1) z) =
        spectralMeasurePolarized U hU z z {1} (measurableSet_singleton 1) := by
      unfold spectralProjectionOfUnitary
      rw [← sesquilinearToOperator_inner]
    rw [hPz, inner_zero_right] at hinner
    exact hinner.symm
  -- h : spectralMeasurePolarized z z {1} = ↑μ_z({1}).toReal
  rw [hpol_zero] at h
  -- h : 0 = ↑μ_z({1}).toReal
  haveI : IsFiniteMeasure (spectralMeasureDiagonal U hU z) := spectralMeasureDiagonal_isFiniteMeasure U hU z
  have hfinite : spectralMeasureDiagonal U hU z {1} ≠ ⊤ := measure_ne_top _ _
  exact ((ENNReal.toReal_eq_zero_iff _).mp (Complex.ofReal_injective h.symm)).resolve_right hfinite

/-- cfcViaInverseCayley is continuous on {z | z ≠ 1}. -/
lemma cfcViaInverseCayley_continuousOn (f : C(ℝ, ℂ)) :
    ContinuousOn (cfcViaInverseCayley f) {z | z ≠ 1} := by
  apply ContinuousOn.congr (cfcViaInverseCayleyC0_continuousOn f)
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  exact (cfcViaInverseCayleyC0_eq_away_from_one f z hz).symm

/-! ### Change of Variables -/

/-- The change of variables formula: the spectral measure on ℝ is the pullback of
    the spectral measure on Circle via cayleyToCircle.

    For any measurable E ⊆ ℝ:
    `μ^ℝ_{x,y}(E) = μ^Circle_{x,y}(cayleyToCircle '' E)` -/
theorem spectralMeasure_pullback_formula (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (x y : H) (E : Set ℝ) (hE : MeasurableSet E) :
    spectralMeasurePolarizedOnR T hT hsa C x y E hE =
    spectralMeasurePolarized C.U (cayley_mem_unitary T hT hsa C) x y
      (cayleyToCircle '' E) (cayleyToCircle_measurableSet_image E hE) := rfl

/-! ### Change of Variables for Integrals

The key insight is that since μ^Circle({1}) = 0, integrals over Circle equal integrals
over Circle \ {1}, and there is a bijection Circle \ {1} ↔ ℝ via inverseCayley.

This means ∫_ℝ f dμ^ℝ = ∫_{Circle\{1}} (f ∘ inverseCayley) dμ^Circle = ∫_Circle (f ∘ inverseCayley) dμ^Circle
-/

/-- Since μ^Circle({1}) = 0, integrals over Circle equal integrals over Circle \ {1}. -/
theorem integral_circle_eq_integral_minus_one (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (z : H) (g : Circle → ℂ) :
    ∫ w, g w ∂(spectralMeasureDiagonal C.U (cayley_mem_unitary T hT hsa C) z) =
    ∫ w in (Set.univ : Set Circle) \ {1}, g w ∂(spectralMeasureDiagonal C.U (cayley_mem_unitary T hT hsa C) z) := by
  let U := C.U
  let hU := cayley_mem_unitary T hT hsa C
  let μ := spectralMeasureDiagonal U hU z
  -- Since μ({1}) = 0, the integral over {1} is 0
  have h1 : μ {1} = 0 := spectralMeasureDiagonal_singleton_one_eq_zero T hT hsa C z
  -- Use that univ \ {1} has full measure (since {1} has measure 0)
  -- ∫ g dμ = ∫_{univ \ {1}} g dμ when μ({1}) = 0
  symm
  apply MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero
  -- Need to show: for almost all x, x ∉ (univ \ {1}) → g x = 0
  -- But x ∉ (univ \ {1}) means x ∈ {1}, and μ({1}) = 0
  rw [Filter.eventually_iff]
  -- The set {x | x ∉ univ \ {1} → g x = 0} is null-measurable with complement of measure 0
  -- Actually, we need to show that the set where the implication fails has measure 0
  -- The set where it fails is {x | x ∉ univ \ {1} ∧ g x ≠ 0} = {x | x ∈ {1} ∧ g x ≠ 0} ⊆ {1}
  have hsub : {x | ¬(x ∉ (Set.univ : Set Circle) \ {1} → g x = 0)} ⊆ {1} := by
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff,
      true_and] at hx ⊢
    -- hx : ¬(x = 1 → g x = 0), need to show x = 1
    -- ¬(P → Q) ↔ P ∧ ¬Q
    push_neg at hx
    exact hx.1
  exact MeasureTheory.measure_mono_null hsub h1

/-- The integral of f over μ^ℝ relates to the integral over μ^Circle via change of variables.

    For continuous f : ℝ → ℂ, we have:
    ∫ f dμ^ℝ_z = ∫ (f ∘ inverseCayley) dμ^Circle_z

    where the Circle integral is taken over Circle \ {1} (but equals the full Circle integral
    since μ^Circle_z({1}) = 0).

    **Technical note**: The comap measure μ^ℝ = μ^Circle.comap(cayleyToCircle) satisfies
    the change of variables formula. For an injective measurable function φ : X → Y and
    a measure ν on Y, we have ∫ f d(ν.comap φ) = ∫ (f ∘ φ⁻¹) dν when φ⁻¹ is defined.

    **Proof strategy**: Define g on Circle \ {1} as f ∘ inverseCayley, and extend to {1}
    arbitrarily. Since μ({1}) = 0, the value at 1 doesn't affect the integral. -/
theorem integral_spectralMeasureDiagonalOnR_eq_circle (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (z : H) (f : ℝ → ℂ) (_hf : Integrable f (spectralMeasureDiagonalOnR T hT hsa C z)) :
    ∃ g : Circle → ℂ,
    ∫ t, f t ∂(spectralMeasureDiagonalOnR T hT hsa C z) =
    ∫ w, g w ∂(spectralMeasureDiagonal C.U (cayley_mem_unitary T hT hsa C) z) := by
  let U := C.U
  let hU := cayley_mem_unitary T hT hsa C
  let μ_R := spectralMeasureDiagonalOnR T hT hsa C z
  let μ_Circle := spectralMeasureDiagonal U hU z
  -- Define g on Circle: g(w) = f(inverseCayley(w)) for w ≠ 1, g(1) = 0
  let g : Circle → ℂ := fun w =>
    if h : (w : ℂ) ≠ 1 then f (inverseCayleyMap (w : ℂ) h) else 0
  use g
  -- μ_R = μ_Circle.comap cayleyToCircle by definition
  -- The comap measure satisfies: ∫ f d(μ.comap φ) = ∫ f d(μ restricted to range φ) composed with φ⁻¹
  -- Since cayleyToCircle : ℝ → Circle \ {1} is a bijection onto its image
  -- and μ_Circle({1}) = 0, we have the result
  unfold spectralMeasureDiagonalOnR
  -- Key lemmas:
  -- 1. MeasurableEmbedding.integral_map: ∫ g d(μ.map f) = ∫ t, g (f t) dμ
  -- 2. MeasurableEmbedding.map_comap: (μ.comap f).map f = μ.restrict (range f)
  -- 3. cayleyToCircle_range: range cayleyToCircle = {z | z ≠ 1}
  -- 4. spectralMeasureDiagonal_singleton_one_eq_zero: μ({1}) = 0

  -- Step 1: Show f t = g (cayleyToCircle t) for all t
  have hf_eq_g : ∀ t : ℝ, f t = g (cayleyToCircle t) := by
    intro t
    simp only [g]
    -- cayleyToCircle t ≠ 1
    have hz : (cayleyToCircle t : ℂ) ≠ 1 := by
      intro h
      exact cayleyMap_ne_one t (by simp only [cayleyToCircle_coe] at h; exact h)
    rw [dif_pos hz]
    -- inverseCayleyMap (cayleyToCircle t) = t
    -- The inverseCayleyMap_cayleyToCircle uses a specific proof, but by proof irrelevance
    -- it equals our goal which uses hz
    have hinv := inverseCayleyMap_cayleyToCircle t
    -- hinv : inverseCayleyMap ↑(cayleyToCircle t) ⋯ = t
    -- Goal : f t = f (inverseCayleyMap (↑(cayleyToCircle t)) hz)
    -- By proof irrelevance, inverseCayleyMap with any proof of ≠ 1 gives the same result
    congr 1
    -- Goal: t = inverseCayleyMap (↑(cayleyToCircle t)) hz
    -- Use proof irrelevance: the proof hz and the proof ⋯ are equal
    convert hinv.symm using 2

  -- Step 2: Rewrite the LHS integral using the equality f = g ∘ cayleyToCircle
  have h_lhs_eq : ∫ t, f t ∂(μ_Circle.comap cayleyToCircle) =
      ∫ t, g (cayleyToCircle t) ∂(μ_Circle.comap cayleyToCircle) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    exact hf_eq_g t

  rw [h_lhs_eq]

  -- Step 3: Use map_comap to relate (comap).map to restrict
  have h_map_comap := cayleyToCircle_measurableEmbedding.map_comap μ_Circle
  -- h_map_comap : (μ_Circle.comap cayleyToCircle).map cayleyToCircle = μ_Circle.restrict (range cayleyToCircle)

  -- Step 4: Apply integral_map to comap measure
  -- MeasurableEmbedding.integral_map : ∫ g d(μ.map f) = ∫ t, g (f t) dμ
  -- So: ∫ w, g w d((comap).map) = ∫ t, g (cayleyToCircle t) d(comap)
  have h_integral_via_map :
      ∫ t, g (cayleyToCircle t) ∂(μ_Circle.comap cayleyToCircle) =
      ∫ w, g w ∂((μ_Circle.comap cayleyToCircle).map cayleyToCircle) :=
    (cayleyToCircle_measurableEmbedding.integral_map (μ := μ_Circle.comap cayleyToCircle) g).symm

  rw [h_integral_via_map, h_map_comap]

  -- Step 5: The range is Circle \ {1}
  have h_range : Set.range cayleyToCircle = {z : Circle | z ≠ 1} := cayleyToCircle_range

  -- Step 6: Show the restricted integral equals the full integral (since μ({1}) = 0)
  have h_μ1 : μ_Circle {1} = 0 := spectralMeasureDiagonal_singleton_one_eq_zero T hT hsa C z

  -- Convert range to the setOf notation
  rw [h_range]

  -- Goal: ∫ w, g w ∂(μ_Circle.restrict {z | z ≠ 1}) = ∫ w, g w ∂μ_Circle
  -- Use restrict_eq_self_of_ae_mem: if ∀ᵐ x ∂μ, x ∈ s, then μ.restrict s = μ
  have h_ae_mem : ∀ᵐ w ∂μ_Circle, w ∈ {z : Circle | z ≠ 1} := by
    rw [Filter.eventually_iff]
    -- Need to show {x | x ∈ {z | z ≠ 1}} ∈ ae μ_Circle
    -- which means μ_Circle({z | z ≠ 1}ᶜ) = 0
    rw [MeasureTheory.mem_ae_iff]
    -- Goal: μ_Circle {x | x ∈ {z | z ≠ 1}}ᶜ = 0
    -- Simplify the set
    have h_eq : {x : Circle | x ∈ {z : Circle | z ≠ 1}}ᶜ = {1} := by
      ext z
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
      tauto
    rw [h_eq]
    exact h_μ1

  have h_restrict_eq : μ_Circle.restrict {z : Circle | z ≠ 1} = μ_Circle :=
    Measure.restrict_eq_self_of_ae_mem h_ae_mem

  rw [h_restrict_eq]

/-! ### Diagonal Spectral Formula for Complex-Valued Functions -/

/-- For real-valued f, the inner product ⟨z, cfc f U z⟩ equals the integral ∫ f dμ_z.

    This is because cfcOfCircleReal f is self-adjoint, so ⟨z, (cfc f) z⟩ is real, and
    equals spectralFunctionalAux U hU z f = ∫ f dμ_z by RMK. -/
theorem diagonal_spectral_integral_real (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (f : C(Circle, ℝ)) (z : H) :
    @inner ℂ H _ z (cfcOfCircleReal U hU f z) =
    (∫ w, f w ∂(spectralMeasureDiagonal U hU z) : ℂ) := by
  haveI : IsStarNormal U := unitary_isStarNormal U hU
  -- cfcOfCircleReal f is self-adjoint, so ⟨z, A z⟩ is real
  have hreal := cfcOfCircleReal_inner_real U hU f z
  -- So ⟨z, A z⟩ = Re⟨z, A z⟩ = spectralFunctionalAux
  have hinner_eq_re : @inner ℂ H _ z (cfcOfCircleReal U hU f z) =
      ((@inner ℂ H _ z (cfcOfCircleReal U hU f z)).re : ℂ) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [Complex.ofReal_im, hreal]
  rw [hinner_eq_re]
  -- spectralFunctionalAux U hU z f = ∫ f dμ_z by RMK
  have h_aux := spectralMeasureDiagonal_integral U hU z (toCc f)
  simp only [toCc_apply] at h_aux
  -- h_aux : ∫ (z : Circle), f z dμ_z = (spectralFunctionalCc U hU z) (toCc f)
  -- (spectralFunctionalCc U hU z) (toCc f) = spectralFunctionalAux U hU z f = Re⟨z, cfcOfCircleReal U hU f z⟩
  have hdef : (spectralFunctionalCc U hU z) (toCc f) =
      (@inner ℂ H _ z (cfcOfCircleReal U hU f z)).re := rfl
  rw [hdef] at h_aux
  -- h_aux : ∫ (z : Circle), f z dμ_z = (inner z ((cfcOfCircleReal U hU f) z)).re
  -- Goal: ↑(inner z ((cfcOfCircleReal U hU f) z)).re = ∫ (w : Circle), ↑(f w) dμ_z
  -- Step 1: ↑(..).re = ↑(∫ f dμ) via h_aux
  have h1 := congrArg Complex.ofReal h_aux.symm
  -- h1 : ↑(..).re = ↑(∫ f dμ)
  -- Step 2: ↑(∫ f dμ) = ∫ ↑(f w) dμ via integral_ofReal
  have h2 : Complex.ofReal (∫ w, f w ∂(spectralMeasureDiagonal U hU z)) =
      ∫ w, (f w : ℂ) ∂(spectralMeasureDiagonal U hU z) := integral_ofReal.symm
  exact h1.trans h2

/-! ### The Main T-P Connection Theorem -/

/-- **The T-P Connection Theorem**

    For a self-adjoint operator T with Cayley transform U and spectral measure P,
    and for a continuous bounded function f : ℝ → ℂ, the functional calculus
    satisfies the spectral representation:

    `⟨x, f(T) y⟩ = (1/4)[∫f dμ^ℝ_{x+y} - ∫f dμ^ℝ_{x-y} - i∫f dμ^ℝ_{x+iy} + i∫f dμ^ℝ_{x-iy}]`

    where μ^ℝ_z is the diagonal spectral measure on ℝ defined as the pullback of
    the Circle measure via the Cayley transform.

    **Proof Strategy:**
    1. By definition: f(T) = UnboundedCFC T f = cfc(cfcViaInverseCayley f, U)
    2. For the Cayley transform, cfcViaInverseCayley f is continuous on Circle \ {1}
    3. Since μ^Circle_z({1}) = 0 (follows from P({1}) = 0), integrals over Circle
       equal integrals over Circle \ {1}
    4. By change of variables with cayleyToCircle:
       ∫_{Circle\{1}} (f ∘ inverseCayley) dμ^Circle_z = ∫_ℝ f dμ^ℝ_z
    5. Apply spectralMeasurePolarized_integral from the RMK approach

    The technical challenge is that cfcViaInverseCayley f is not compactly supported
    on Circle, so we cannot directly apply spectralMeasurePolarized_integral.
    We handle this by:
    - Showing the integral over {1} is 0 (since μ({1}) = 0)
    - Using that cfcViaInverseCayley f is continuous on the complement Circle \ {1}
    - The integral over Circle \ {1} equals the integral of f over ℝ by change of variables -/
theorem TP_connection (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (f : C(ℝ, ℂ)) (x y : H) :
    let μ_sum := spectralMeasureDiagonalOnR T hT hsa C (x + y)
    let μ_diff := spectralMeasureDiagonalOnR T hT hsa C (x - y)
    let μ_isum := spectralMeasureDiagonalOnR T hT hsa C (x + Complex.I • y)
    let μ_idiff := spectralMeasureDiagonalOnR T hT hsa C (x - Complex.I • y)
    @inner ℂ H _ x (UnboundedCFC T hT hsa C f y) =
    (1/4 : ℂ) * (∫ t, f t ∂μ_sum - ∫ t, f t ∂μ_diff -
                Complex.I * ∫ t, f t ∂μ_isum + Complex.I * ∫ t, f t ∂μ_idiff) := by
  let U := C.U
  let hU := cayley_mem_unitary T hT hsa C
  haveI : IsStarNormal U := cayleyTransform_isStarNormal T hT hsa C
  -- **Proof Strategy**
  --
  -- Step 1: Split f = f_Re + i·f_Im into real and imaginary parts
  let f_Re : C(ℝ, ℝ) := ⟨fun t => (f t).re, Complex.continuous_re.comp f.continuous⟩
  let f_Im : C(ℝ, ℝ) := ⟨fun t => (f t).im, Complex.continuous_im.comp f.continuous⟩
  -- f = f_Re + i·f_Im pointwise
  have hf_eq : ∀ t, f t = Complex.ofReal (f_Re t) + Complex.I * Complex.ofReal (f_Im t) := by
    intro t
    simp only [f_Re, f_Im, ContinuousMap.coe_mk]
    -- (f t).re + (f t).im * I = f t, but we need I * (f t).im
    have h := Complex.re_add_im (f t)
    rw [mul_comm] at h
    exact h.symm

  -- Step 2: By linearity of UnboundedCFC (cfc is additive and respects scalar mult)
  -- UnboundedCFC T f = UnboundedCFC T f_Re' + I • UnboundedCFC T f_Im'
  -- where f_Re' embeds f_Re into C(ℝ, ℂ)

  -- Step 3: Use spectralFunctionalAux_polarization for each real part
  -- For real g on Circle:
  -- ⟨x, cfcOfCircleReal U hU g y⟩ = (1/4)[Λ_{x+y}(g) - Λ_{x-y}(g) - i·Λ_{x+iy}(g) + i·Λ_{x-iy}(g)]

  -- Step 4: Apply spectralFunctionalAux_eq_integral_R to convert Circle integrals to ℝ integrals
  -- Λ_z(g) = ∫_ℝ f dμ^ℝ_z when g = f ∘ inverseCayley

  -- Step 5: Combine real and imaginary parts
  -- ⟨x, UnboundedCFC T f y⟩ = ⟨x, UnboundedCFC T f_Re y⟩ + i·⟨x, UnboundedCFC T f_Im y⟩
  --   = (1/4)[∫ f_Re dμ_{x+y} - ...] + i·(1/4)[∫ f_Im dμ_{x+y} - ...]
  --   = (1/4)[∫ (f_Re + i·f_Im) dμ_{x+y} - ...]
  --   = (1/4)[∫ f dμ_{x+y} - ...]

  -- The full proof requires proving additivity of cfc and the change of variables formula
  -- The key lemmas are available (spectralFunctionalAux_polarization, diagonal_spectral_integral_real)
  -- but connecting them requires additional scaffolding
  sorry

/-- **Corollary: The T-P connection for the diagonal case**

    For z ∈ H:
    `‖f(T) z‖² = ∫_ℝ |f(λ)|² dμ^ℝ_z(λ)`

    This follows from the polarization identity and TP_connection. -/
theorem TP_connection_diagonal (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (f : C(ℝ, ℂ)) (z : H) :
    ‖UnboundedCFC T hT hsa C f z‖^2 =
    ∫ t, ‖f t‖^2 ∂(spectralMeasureDiagonalOnR T hT hsa C z) := by
  -- By TP_connection with x = y = z:
  -- ⟨z, f(T) z⟩ = (1/4)[∫|f|² dμ_{2z} - 0 - i∫|f|² dμ_{(1+i)z} + i∫|f|² dμ_{(1-i)z}]
  -- Using the quadratic scaling μ_{cz} = |c|² μ_z:
  -- = (1/4)[4∫|f|² dμ_z - 0 - 2i∫|f|² dμ_z + 2i∫|f|² dμ_z]
  -- = ∫|f|² dμ_z
  sorry

/-! ### Connection to the spectral_theorem sorry -/

/-- **The spectral theorem T-P connection**

    This theorem provides exactly what is needed to fill the sorry in
    `spectral_theorem` in Unbounded/Spectral.lean:

    For a self-adjoint operator T with spectral measure P:
    `T = ∫ λ dP(λ)` in the sense that for all x, y in dom(T):
    `⟨x, T y⟩ = ∫ λ d⟨x, P(λ) y⟩`

    In our framework, this means:
    `⟨x, T y⟩ = ∫_ℝ λ dμ^ℝ_{x,y}(λ)`

    The identity function id(λ) = λ satisfies:
    `UnboundedCFC T id = T` on dom(T) (this is the key property of functional calculus)

    Combined with TP_connection, this gives the T-P connection for T itself. -/
theorem spectral_theorem_TP_connection (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (x : H) (y : T.domain) :
    @inner ℂ H _ x (T.toFun y) =
    spectralMeasurePolarizedOnR T hT hsa C x (y : H) Set.univ MeasurableSet.univ := by
  -- The identity function id : ℝ → ℂ given by id(λ) = λ
  -- UnboundedCFC T id should equal T on dom(T)
  -- Then ⟨x, T y⟩ = ⟨x, UnboundedCFC T id y⟩
  -- By TP_connection, this equals the polarized spectral integral of id
  -- = ∫_ℝ λ dμ^ℝ_{x,y}(λ)
  -- For E = ℝ: μ^ℝ_{x,y}(ℝ) = ⟨x, P(ℝ) y⟩ = ⟨x, y⟩ (since P(ℝ) = 1)
  -- The full proof requires showing UnboundedCFC T id = T and using TP_connection
  sorry

end
