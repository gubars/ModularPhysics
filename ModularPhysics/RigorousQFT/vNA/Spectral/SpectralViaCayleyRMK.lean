/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.vNA.Spectral.SpectralTheoremViaRMK
import ModularPhysics.RigorousQFT.vNA.Spectral.CayleyTransform
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Bridge: RMK Spectral Theorem to Self-Adjoint Operators via Cayley Transform

This minimal bridge file connects:
- `spectralProjectionOfUnitary` from SpectralTheoremViaRMK.lean (spectral projection on Circle)
- `spectralMeasureViaCayley` from CayleyTransform.lean (spectral measure on ℝ)

## Main construction

For a self-adjoint operator T with Cayley transform U:
1. RMK gives `P_Circle : Set Circle → (H →L[ℂ] H)` for U
2. Use cayleyToCircle : ℝ → Circle to pull back
3. Define `P_T(E) := P_Circle(cayleyToCircle '' E)`

The key lemma is that cayleyToCircle is an open embedding, hence a measurable embedding,
so images of measurable sets are measurable.
-/

noncomputable section

open scoped InnerProduct ComplexConjugate Topology
open Complex MeasureTheory Set Filter Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The Cayley map to Circle -/

/-- The Cayley map from ℝ to Circle. -/
def cayleyToCircle (t : ℝ) : Circle :=
  ⟨cayleyMap t, mem_sphere_zero_iff_norm.mpr (cayleyMap_on_circle t)⟩

/-- The underlying complex value of cayleyToCircle. -/
theorem cayleyToCircle_coe (t : ℝ) : (cayleyToCircle t : ℂ) = cayleyMap t := rfl

/-- cayleyToCircle is injective (from cayleyMap_injective). -/
theorem cayleyToCircle_injective : Function.Injective cayleyToCircle := by
  intro t₁ t₂ h
  have h' : (cayleyToCircle t₁ : ℂ) = (cayleyToCircle t₂ : ℂ) := congrArg Subtype.val h
  simp only [cayleyToCircle_coe] at h'
  exact cayleyMap_injective h'

/-- cayleyToCircle is continuous. -/
theorem cayleyToCircle_continuous : Continuous cayleyToCircle := by
  apply Continuous.subtype_mk
  show Continuous cayleyMap
  unfold cayleyMap
  apply Continuous.div
  · exact continuous_ofReal.sub continuous_const
  · exact continuous_ofReal.add continuous_const
  · intro t h
    have him : ((t : ℂ) + I).im = (0 : ℂ).im := congrArg Complex.im h
    simp at him

/-- The range of cayleyToCircle is Circle \ {1}. -/
theorem cayleyToCircle_range : range cayleyToCircle = {z : Circle | z ≠ 1} := by
  ext z
  simp only [mem_range, mem_setOf_eq]
  constructor
  · -- If z = cayleyToCircle t, then z ≠ 1
    rintro ⟨t, rfl⟩
    intro h
    have : (cayleyToCircle t : ℂ) = (1 : Circle) := congrArg Subtype.val h
    simp only [cayleyToCircle_coe, Circle.coe_one] at this
    exact cayleyMap_ne_one t this
  · -- If z ≠ 1, then z is in the range (via inverseCayleyMap)
    intro hz
    have hz1 : (z : ℂ) ≠ 1 := fun h => hz (Circle.ext h)
    use inverseCayleyMap (z : ℂ) hz1
    apply Circle.ext
    simp only [cayleyToCircle_coe]
    -- Need to show cayleyMap (inverseCayleyMap z hz1) = z
    -- This is the inverse property
    unfold cayleyMap inverseCayleyMap
    -- The algebraic identity: if t = i(1+z)/(1-z), then (t-i)/(t+i) = z
    have h1 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (ne_comm.mp hz1)
    set t := (I * (1 + (z : ℂ)) / (1 - (z : ℂ))).re with ht_def
    -- Key: I * (1 + z) / (1 - z) is purely real (imaginary part is 0)
    have hreal : (I * (1 + (z : ℂ)) / (1 - (z : ℂ))).im = 0 := by
      have hnorm : ‖(z : ℂ)‖ = 1 := Circle.norm_coe z
      have hz_normSq : normSq (z : ℂ) = 1 := by rw [normSq_eq_norm_sq, hnorm, one_pow]
      have hnz : (z : ℂ) ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm]; exact one_ne_zero)
      -- (1+z)/(1-z) is purely imaginary for |z| = 1, z ≠ 1
      have hpure : ((1 + (z : ℂ)) / (1 - (z : ℂ))).re = 0 := by
        have hz_conj : conj (z : ℂ) = (z : ℂ)⁻¹ := by
          rw [inv_eq_one_div]
          apply Complex.ext
          · simp only [conj_re, div_re, one_re, one_im, hz_normSq]; ring
          · simp only [conj_im, div_im, one_re, one_im, hz_normSq]; ring
        let w := (1 + (z : ℂ)) / (1 - (z : ℂ))
        have hw_conj : conj w = -w := by
          simp only [w, map_div₀, map_add, map_one, map_sub, hz_conj]
          have h2 : (1 : ℂ) - (z : ℂ)⁻¹ ≠ 0 := by
            intro heq
            have h3 : (z : ℂ)⁻¹ = 1 := by
              have : (1 : ℂ) = (z : ℂ)⁻¹ := eq_of_sub_eq_zero heq
              exact this.symm
            have h4 : (z : ℂ) = 1 := inv_eq_one.mp h3
            exact hz1 h4
          have h5 : (z : ℂ) - 1 ≠ 0 := fun heq => hz1 (sub_eq_zero.mp heq)
          have h3 : 1 + (z : ℂ)⁻¹ = ((z : ℂ) + 1) / (z : ℂ) := by field_simp [hnz]
          have h4 : 1 - (z : ℂ)⁻¹ = ((z : ℂ) - 1) / (z : ℂ) := by field_simp [hnz]
          rw [h3, h4]
          field_simp [hnz, h1, h5]
          ring
        have h_sum : w + conj w = 0 := by rw [hw_conj]; ring
        calc w.re = (w + conj w).re / 2 := by simp only [add_re, conj_re]; ring
          _ = 0 := by rw [h_sum]; simp
      -- i * (purely imaginary) has im = re of the imaginary = 0
      -- Note: I * (1 + z) / (1 - z) associates as (I * (1 + z)) / (1 - z)
      have hassoc : I * (1 + (z : ℂ)) / (1 - (z : ℂ)) = I * ((1 + (z : ℂ)) / (1 - (z : ℂ))) := by
        field_simp [h1]
      calc (I * (1 + (z : ℂ)) / (1 - (z : ℂ))).im
          = (I * ((1 + (z : ℂ)) / (1 - (z : ℂ)))).im := by rw [hassoc]
        _ = ((1 + (z : ℂ)) / (1 - (z : ℂ))).re := by simp [mul_im, I_re, I_im]
        _ = 0 := hpure
    -- So t : ℂ equals I * (1 + z) / (1 - z)
    have ht_eq : (t : ℂ) = I * (1 + (z : ℂ)) / (1 - (z : ℂ)) := by
      apply Complex.ext
      · simp [ht_def]
      · simp [ht_def, hreal]
    -- Now compute (t - I) / (t + I)
    calc ((t : ℂ) - I) / ((t : ℂ) + I)
        = (I * (1 + (z : ℂ)) / (1 - (z : ℂ)) - I) / (I * (1 + (z : ℂ)) / (1 - (z : ℂ)) + I) := by
          rw [ht_eq]
      _ = I * ((1 + (z : ℂ)) / (1 - (z : ℂ)) - 1) / (I * ((1 + (z : ℂ)) / (1 - (z : ℂ)) + 1)) := by ring
      _ = ((1 + (z : ℂ)) / (1 - (z : ℂ)) - 1) / ((1 + (z : ℂ)) / (1 - (z : ℂ)) + 1) := by
          have hi : I ≠ 0 := I_ne_zero; field_simp [hi]
      _ = ((1 + (z : ℂ)) - (1 - (z : ℂ))) / ((1 + (z : ℂ)) + (1 - (z : ℂ))) := by field_simp [h1]
      _ = 2 * (z : ℂ) / 2 := by ring
      _ = (z : ℂ) := by ring

/-- The range of cayleyToCircle is open in Circle. -/
theorem cayleyToCircle_range_isOpen : IsOpen (range cayleyToCircle) := by
  rw [cayleyToCircle_range]
  exact isOpen_compl_singleton

/-- Helper: The coercion of a Circle element z ≠ 1 also satisfies (z : ℂ) ≠ 1. -/
theorem Circle.coe_ne_one_of_ne_one (z : Circle) (hz : z ≠ 1) : (z : ℂ) ≠ 1 := by
  intro h; exact hz (Circle.ext h)

/-- The inverse Cayley map applied to cayleyToCircle gives back the original. -/
theorem inverseCayleyMap_cayleyToCircle (t : ℝ) :
    inverseCayleyMap (cayleyToCircle t) (Circle.coe_ne_one_of_ne_one _ (by
      intro h
      have : (cayleyToCircle t : ℂ) = (1 : Circle) := congrArg Subtype.val h
      simp only [cayleyToCircle_coe, Circle.coe_one] at this
      exact cayleyMap_ne_one t this)) = t := by
  simp only [inverseCayleyMap, cayleyToCircle_coe]
  unfold cayleyMap
  -- Compute: I * (1 + (t-I)/(t+I)) / (1 - (t-I)/(t+I))
  have h1 : (↑t : ℂ) + I ≠ 0 := by
    intro h; have him : ((↑t : ℂ) + I).im = 1 := by simp
    rw [h] at him; simp at him
  have h_num : (1 : ℂ) + (↑t - I) / (↑t + I) = 2 * ↑t / (↑t + I) := by field_simp [h1]; ring
  have h_denom : (1 : ℂ) - (↑t - I) / (↑t + I) = 2 * I / (↑t + I) := by field_simp [h1]; ring
  have hI : (2 : ℂ) * I ≠ 0 := by simp [I_ne_zero]
  calc (I * (1 + (↑t - I) / (↑t + I)) / (1 - (↑t - I) / (↑t + I))).re
      = (I * (2 * ↑t / (↑t + I)) / (2 * I / (↑t + I))).re := by rw [h_num, h_denom]
    _ = (I * (2 * ↑t / (↑t + I)) * ((↑t + I) / (2 * I))).re := by rw [div_eq_mul_inv, inv_div]
    _ = (I * (2 * ↑t) / (2 * I)).re := by field_simp [h1, I_ne_zero]
    _ = (↑t : ℂ).re := by field_simp [I_ne_zero]
    _ = t := Complex.ofReal_re t

/-- The inverse Cayley map is continuous on Circle \ {1} (as a function on Circle). -/
theorem inverseCayleyMap_continuousOn_circle :
    ContinuousOn (fun z : Circle => (I * (1 + (z : ℂ)) / (1 - (z : ℂ))).re) {z | z ≠ 1} := by
  -- The function z ↦ I * (1 + z) / (1 - z) is continuous on {z ≠ 1}
  have h1 : ContinuousOn (fun z : Circle => I * (1 + (z : ℂ)) / (1 - (z : ℂ))) {z | z ≠ 1} := by
    apply ContinuousOn.div
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.add continuousOn_const
      exact continuous_subtype_val.continuousOn
    · apply ContinuousOn.sub continuousOn_const
      exact continuous_subtype_val.continuousOn
    · intro z hz
      simp only [mem_setOf_eq] at hz
      intro h
      exact hz (Circle.ext (eq_of_sub_eq_zero h).symm)
  exact Complex.continuous_re.comp_continuousOn h1

/-- cayleyToCircle is an open embedding.
    The proof uses that cayleyToCircle is a homeomorphism onto Circle \ {1}. -/
theorem cayleyToCircle_isOpenEmbedding : Topology.IsOpenEmbedding cayleyToCircle := by
  constructor
  · -- IsEmbedding
    constructor
    · -- IsInducing: use isInducing_iff_nhds
      rw [Topology.isInducing_iff_nhds]
      intro t
      apply le_antisymm
      · -- 𝓝 t ≤ comap cayleyToCircle (𝓝 (cayleyToCircle t)) follows from continuity
        exact cayleyToCircle_continuous.tendsto t |>.le_comap
      · -- comap cayleyToCircle (𝓝 (cayleyToCircle t)) ≤ 𝓝 t
        -- This follows from continuity of the inverse
        have hz : cayleyToCircle t ≠ 1 := by
          intro h
          have : (cayleyToCircle t : ℂ) = (1 : Circle) := congrArg Subtype.val h
          simp only [cayleyToCircle_coe, Circle.coe_one] at this
          exact cayleyMap_ne_one t this
        -- The inverse is continuous at cayleyToCircle t
        have hinv_cont := inverseCayleyMap_continuousOn_circle.continuousAt
          (isOpen_compl_singleton.mem_nhds hz)
        -- hinv(cayleyToCircle t) = t
        have hinv_val : (fun z : Circle => (I * (1 + (z : ℂ)) / (1 - (z : ℂ))).re)
            (cayleyToCircle t) = t := inverseCayleyMap_cayleyToCircle t
        -- Convert hinv_cont to have target 𝓝 t
        have hinv_tendsto : Filter.Tendsto
            (fun z : Circle => (I * (1 + (z : ℂ)) / (1 - (z : ℂ))).re)
            (𝓝 (cayleyToCircle t)) (𝓝 t) := by
          simp only [ContinuousAt, hinv_val] at hinv_cont
          exact hinv_cont
        -- For any U ∈ 𝓝 t, the preimage under inverse is in 𝓝 (cayleyToCircle t)
        -- So cayleyToCircle ⁻¹' (preimage) ⊇ preimage contains elements mapping to U
        -- Use that inverse ∘ cayleyToCircle = id
        intro U hU
        rw [Filter.mem_comap]
        -- Find V ∈ 𝓝 (cayleyToCircle t) with cayleyToCircle ⁻¹' V ⊆ U
        have hU_ev : ∀ᶠ z in 𝓝 (cayleyToCircle t),
            (fun z : Circle => (I * (1 + (z : ℂ)) / (1 - (z : ℂ))).re) z ∈ U :=
          hinv_tendsto hU
        obtain ⟨V, hV_nhds, hV_sub⟩ := hU_ev.exists_mem
        use V, hV_nhds
        intro s hs
        -- hs : s ∈ cayleyToCircle ⁻¹' V, so cayleyToCircle s ∈ V
        have hs_in_V : cayleyToCircle s ∈ V := hs
        -- Need: s ∈ U. Use that inverse(cayleyToCircle s) = s
        have hinv_s := inverseCayleyMap_cayleyToCircle s
        have hV_at_s := hV_sub (cayleyToCircle s) hs_in_V
        -- hV_at_s : (fun z => (I * (1 + ↑z) / (1 - ↑z)).re) (cayleyToCircle s) ∈ U
        -- This equals inverseCayleyMap (↑(cayleyToCircle s)) _ by definition
        -- And inverseCayleyMap (↑(cayleyToCircle s)) _ = s by hinv_s
        -- So s ∈ U
        convert hV_at_s using 1
        exact hinv_s.symm
    · exact cayleyToCircle_injective
  · exact cayleyToCircle_range_isOpen

/-- cayleyToCircle is a measurable embedding.
    This follows from being an open embedding. -/
theorem cayleyToCircle_measurableEmbedding : MeasurableEmbedding cayleyToCircle :=
  cayleyToCircle_isOpenEmbedding.measurableEmbedding

/-- The image of a measurable set under cayleyToCircle is measurable. -/
theorem cayleyToCircle_measurableSet_image (E : Set ℝ) (hE : MeasurableSet E) :
    MeasurableSet (cayleyToCircle '' E) :=
  cayleyToCircle_measurableEmbedding.measurableSet_image.mpr hE

/-! ### Real and imaginary parts on Circle -/

/-- The real part function on Circle. -/
def circleRe : C(Circle, ℝ) where
  toFun z := (z : ℂ).re
  continuous_toFun := Complex.continuous_re.comp continuous_subtype_val

/-- The imaginary part function on Circle. -/
def circleIm : C(Circle, ℝ) where
  toFun z := (z : ℂ).im
  continuous_toFun := Complex.continuous_im.comp continuous_subtype_val

/-- On the unit circle, Re² + Im² = 1. -/
theorem circle_re_sq_add_im_sq (z : Circle) : circleRe z ^ 2 + circleIm z ^ 2 = 1 := by
  simp only [circleRe, circleIm, ContinuousMap.coe_mk]
  have h := Circle.normSq_coe z
  simp only [Complex.normSq_apply, sq] at h ⊢
  exact h

/-- The identity function on Circle decomposes as Re + i·Im. -/
theorem circle_id_eq_re_add_i_im (z : Circle) : (z : ℂ) = circleRe z + Complex.I * circleIm z := by
  simp only [circleRe, circleIm, ContinuousMap.coe_mk]
  rw [mul_comm]
  exact (Complex.re_add_im (z : ℂ)).symm

/-- The value at 1 : Circle for circleRe. -/
@[simp] theorem circleRe_one : circleRe (1 : Circle) = 1 := by
  simp only [circleRe, ContinuousMap.coe_mk, Circle.coe_one, Complex.one_re]

/-- The value at 1 : Circle for circleIm. -/
@[simp] theorem circleIm_one : circleIm (1 : Circle) = 0 := by
  simp only [circleIm, ContinuousMap.coe_mk, Circle.coe_one, Complex.one_im]

/-- On the unit circle, |Re(z)| ≤ 1. -/
theorem circleRe_abs_le_one (z : Circle) : |circleRe z| ≤ 1 := by
  have h := circle_re_sq_add_im_sq z
  have hre_sq : circleRe z ^ 2 ≤ 1 := by linarith [sq_nonneg (circleIm z)]
  rwa [sq_le_one_iff_abs_le_one] at hre_sq

/-- On the unit circle, |Im(z)| ≤ 1. -/
theorem circleIm_abs_le_one (z : Circle) : |circleIm z| ≤ 1 := by
  have h := circle_re_sq_add_im_sq z
  have him_sq : circleIm z ^ 2 ≤ 1 := by linarith [sq_nonneg (circleRe z)]
  rwa [sq_le_one_iff_abs_le_one] at him_sq

/-- The circleRealToComplex of circleRe agrees with Re on the spectrum.
    For z on the unit circle: circleRealToComplex(circleRe)(z) = Re(z) -/
lemma circleRealToComplex_circleRe_eq_on_sphere :
    Set.EqOn (circleRealToComplex circleRe) (fun z => (z.re : ℂ)) (Metric.sphere (0 : ℂ) 1) := by
  intro z hz
  simp only [circleRealToComplex, hz, dite_true, circleRe, ContinuousMap.coe_mk]

/-- The circleRealToComplex of circleIm agrees with Im on the spectrum.
    For z on the unit circle: circleRealToComplex(circleIm)(z) = Im(z) -/
lemma circleRealToComplex_circleIm_eq_on_sphere :
    Set.EqOn (circleRealToComplex circleIm) (fun z => (z.im : ℂ)) (Metric.sphere (0 : ℂ) 1) := by
  intro z hz
  simp only [circleRealToComplex, hz, dite_true, circleIm, ContinuousMap.coe_mk]

/-- Key identity: U = cfcOfCircleReal(circleRe) + i · cfcOfCircleReal(circleIm)
    This expresses the unitary operator U in terms of real-valued CFCs. -/
theorem unitary_eq_cfcOfCircleReal_re_im (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H)) :
    U = cfcOfCircleReal U hU circleRe + Complex.I • cfcOfCircleReal U hU circleIm := by
  haveI : IsStarNormal U := unitary_isStarNormal U hU
  -- U = cfc(id, U) where id : ℂ → ℂ is the identity
  have hU_eq_cfc_id : U = cfc (id : ℂ → ℂ) U := (cfc_id' ℂ U).symm
  -- The identity function decomposes as Re + i·Im on the spectrum
  -- spectrum(U) ⊆ unit circle for unitary U
  have hspec : spectrum ℂ U ⊆ Metric.sphere (0 : ℂ) 1 := spectrum.subset_circle_of_unitary hU
  -- On the spectrum: id(z) = Re(z) + i·Im(z) = circleRealToComplex(circleRe)(z) + i·circleRealToComplex(circleIm)(z)
  have hid_decomp : Set.EqOn (id : ℂ → ℂ) (fun z => circleRealToComplex circleRe z + circleRealToComplex circleIm z * Complex.I) (spectrum ℂ U) := by
    intro z hz
    have hz_sphere := hspec hz
    have hre := circleRealToComplex_circleRe_eq_on_sphere hz_sphere
    have him := circleRealToComplex_circleIm_eq_on_sphere hz_sphere
    simp only [id, hre, him]
    exact (Complex.re_add_im z).symm
  -- Use cfc_congr to rewrite cfc(id) in terms of the decomposition
  have hcfc_decomp : cfc (id : ℂ → ℂ) U = cfc (fun z => circleRealToComplex circleRe z + circleRealToComplex circleIm z * Complex.I) U := by
    exact cfc_congr hid_decomp
  -- Now decompose cfc(Re + Im·i) = cfc(Re) + cfc(Im)·i
  have hcont_re := circleRealToComplex_continuousOn_spectrum circleRe U hU
  have hcont_im := circleRealToComplex_continuousOn_spectrum circleIm U hU
  have hcfc_add : cfc (fun z => circleRealToComplex circleRe z + circleRealToComplex circleIm z * Complex.I) U =
      cfc (circleRealToComplex circleRe) U + cfc (fun z => circleRealToComplex circleIm z * Complex.I) U := by
    exact cfc_add (a := U) (circleRealToComplex circleRe) (fun z => circleRealToComplex circleIm z * Complex.I) hcont_re (hcont_im.mul continuousOn_const)
  have hcfc_mul : cfc (fun z => circleRealToComplex circleIm z * Complex.I) U = Complex.I • cfc (circleRealToComplex circleIm) U := by
    -- Use commutativity: f(z) * c = c * f(z)
    have heq : Set.EqOn (fun z => circleRealToComplex circleIm z * Complex.I) (fun z => Complex.I * circleRealToComplex circleIm z) (spectrum ℂ U) := by
      intro z _; ring
    rw [cfc_congr heq, cfc_const_mul Complex.I (circleRealToComplex circleIm) U hcont_im]
  -- Combine
  calc U = cfc (id : ℂ → ℂ) U := hU_eq_cfc_id
    _ = cfc (fun z => circleRealToComplex circleRe z + circleRealToComplex circleIm z * Complex.I) U := hcfc_decomp
    _ = cfc (circleRealToComplex circleRe) U + cfc (fun z => circleRealToComplex circleIm z * Complex.I) U := hcfc_add
    _ = cfc (circleRealToComplex circleRe) U + Complex.I • cfc (circleRealToComplex circleIm) U := by rw [hcfc_mul]
    _ = cfcOfCircleReal U hU circleRe + Complex.I • cfcOfCircleReal U hU circleIm := rfl

/-- CFC multiplicativity for real functions: cfcOfCircleReal(f * g) = cfcOfCircleReal(f) * cfcOfCircleReal(g) -/
theorem cfcOfCircleReal_mul (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (f g : C(Circle, ℝ)) :
    cfcOfCircleReal U hU (f * g) = cfcOfCircleReal U hU f * cfcOfCircleReal U hU g := by
  haveI : IsStarNormal U := unitary_isStarNormal U hU
  unfold cfcOfCircleReal
  have hcont_f := circleRealToComplex_continuousOn_spectrum f U hU
  have hcont_g := circleRealToComplex_continuousOn_spectrum g U hU
  -- circleRealToComplex(f * g) = circleRealToComplex(f) * circleRealToComplex(g) on spectrum
  have hmul_eq : Set.EqOn (circleRealToComplex (f * g))
      (fun z => circleRealToComplex f z * circleRealToComplex g z) (spectrum ℂ U) := by
    intro z hz
    have hspec := spectrum.subset_circle_of_unitary hU hz
    simp only [circleRealToComplex, hspec, dite_true, ContinuousMap.coe_mul, Pi.mul_apply]
    -- (f(z) * g(z) : ℂ) = (f(z) : ℂ) * (g(z) : ℂ)
    push_cast
    rfl
  rw [cfc_congr hmul_eq, cfc_mul (circleRealToComplex f) (circleRealToComplex g) U hcont_f hcont_g]

/-! ### Spectral integration for singletons -/

/-- For a singleton {λ}, the identity times the indicator equals the indicator:
    (z · χ_{λ})(z) = z · χ_{λ}(z) = λ · χ_{λ}(z) = χ_{λ}(z) when λ = 1.

    More precisely: for thickenedIndicatorReal g_n → χ_{1}, we have id · g_n → χ_{1}
    because:
    - At z = 1: id(1) · g_n(1) = 1 · 1 = 1 = χ_{1}(1)
    - At z ≠ 1: id(z) · g_n(z) = z · g_n(z) → z · 0 = 0 = χ_{1}(z) -/
theorem id_mul_thickenedIndicatorReal_tendsto_indicator_singleton_one
    {δseq : ℕ → ℝ} (hδ_pos : ∀ n, 0 < δseq n) (hδ_lim : Tendsto δseq atTop (𝓝 0)) :
    Tendsto (fun n => fun z : Circle => (z : ℂ) * thickenedIndicatorReal (hδ_pos n) ({1} : Set Circle) z)
      atTop (𝓝 (Set.indicator ({1} : Set Circle) (fun _ => (1 : ℂ)))) := by
  -- Use thickenedIndicatorReal which returns ℝ directly
  rw [tendsto_pi_nhds]
  intro z
  -- Get pointwise convergence of thickenedIndicatorReal
  have hg_tendsto_fun := thickenedIndicatorReal_tendsto_indicator_closure (F := ({1} : Set Circle)) hδ_pos hδ_lim
  rw [tendsto_pi_nhds] at hg_tendsto_fun
  have hg_tendsto := hg_tendsto_fun z
  simp only [closure_singleton] at hg_tendsto

  by_cases hz : z = 1
  · -- Case z = 1: target is χ_{1}(1) = 1
    subst hz
    have hind_target : Set.indicator ({1} : Set Circle) (fun _ => (1 : ℂ)) 1 = 1 :=
      Set.indicator_of_mem (Set.mem_singleton (1 : Circle)) _
    rw [hind_target]
    -- g_n(1) = 1 for all n (1 is in the singleton {1})
    have hmem_one : (1 : Circle) ∈ ({1} : Set Circle) := Set.mem_singleton 1
    have hg_one : ∀ n, thickenedIndicatorReal (hδ_pos n) ({1} : Set Circle) 1 = (1 : ℝ) :=
      fun n => thickenedIndicatorReal_one_of_mem (hδ_pos n) hmem_one
    -- The function is constantly (1 : Circle) * 1 = 1
    have hfun_eq : ∀ n, (↑(1 : Circle) : ℂ) * (thickenedIndicatorReal (hδ_pos n) ({1} : Set Circle) 1 : ℂ) = (1 : ℂ) := by
      intro n
      rw [hg_one n]
      simp only [Circle.coe_one, Complex.ofReal_one, mul_one]
    simp only [hfun_eq]
    exact tendsto_const_nhds

  · -- Case z ≠ 1: target is χ_{1}(z) = 0
    have hzmem : z ∉ ({1} : Set Circle) := fun h => hz (Set.mem_singleton_iff.mp h)
    have hind_target : Set.indicator ({1} : Set Circle) (fun _ => (1 : ℂ)) z = 0 :=
      Set.indicator_of_notMem hzmem _
    rw [hind_target]
    -- g_n(z) → 0 since z ∉ {1}
    have hind_source : Set.indicator ({1} : Set Circle) (fun _ => (1 : ℝ)) z = 0 :=
      Set.indicator_of_notMem hzmem _
    rw [hind_source] at hg_tendsto
    -- Cast to ℂ: g_n(z) : ℂ → 0 : ℂ
    have hcomplex_tendsto : Tendsto (fun n => (thickenedIndicatorReal (hδ_pos n) ({1} : Set Circle) z : ℂ))
        atTop (𝓝 (0 : ℂ)) := by
      have hcont : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) :=
        Complex.continuous_ofReal.tendsto 0
      exact hcont.comp hg_tendsto
    -- z * g_n(z) → z * 0 = 0
    have hmul : Tendsto (fun n => (z : ℂ) * (thickenedIndicatorReal (hδ_pos n) ({1} : Set Circle) z : ℂ))
        atTop (𝓝 ((z : ℂ) * 0)) := Tendsto.mul tendsto_const_nhds hcomplex_tendsto
    simp only [mul_zero] at hmul
    exact hmul

/-- For thickened indicators g_n → χ_{1}, we have (Re · g_n)(z) → χ_{1}(z) pointwise.
    This is because Re(1) = 1, so at z = 1: Re(1) · g_n(1) = 1 · 1 = 1 = χ_{1}(1).
    At z ≠ 1: Re(z) · g_n(z) → Re(z) · 0 = 0 = χ_{1}(z). -/
theorem re_mul_thickenedIndicatorReal_tendsto_indicator_singleton_one_pointwise
    {δseq : ℕ → ℝ} (hδ_pos : ∀ n, 0 < δseq n) (hδ_lim : Tendsto δseq atTop (𝓝 0)) (z : Circle) :
    Tendsto (fun n => (circleRe * thickenedIndicatorReal (hδ_pos n) ({1} : Set Circle)) z)
      atTop (𝓝 (Set.indicator ({1} : Set Circle) (fun _ => (1 : ℝ)) z)) := by
  have hg_tendsto_fun := thickenedIndicatorReal_tendsto_indicator_closure (F := ({1} : Set Circle)) hδ_pos hδ_lim
  rw [tendsto_pi_nhds] at hg_tendsto_fun
  have hg_tendsto := hg_tendsto_fun z
  simp only [closure_singleton] at hg_tendsto
  by_cases hz : z = 1
  · -- Case z = 1: circleRe(1) * g_n(1) = 1 * 1 = 1 = χ_{1}(1)
    subst hz
    have hind_target : Set.indicator ({1} : Set Circle) (fun _ => (1 : ℝ)) 1 = 1 :=
      Set.indicator_of_mem (Set.mem_singleton (1 : Circle)) _
    rw [hind_target]
    have hmem_one : (1 : Circle) ∈ ({1} : Set Circle) := Set.mem_singleton 1
    have hg_one : ∀ n, thickenedIndicatorReal (hδ_pos n) ({1} : Set Circle) 1 = (1 : ℝ) :=
      fun n => thickenedIndicatorReal_one_of_mem (hδ_pos n) hmem_one
    have hfun_eq : ∀ n, (circleRe * thickenedIndicatorReal (hδ_pos n) ({1} : Set Circle)) 1 = (1 : ℝ) := by
      intro n
      simp only [ContinuousMap.mul_apply, hg_one n, mul_one, circleRe_one]
    simp only [hfun_eq]
    exact tendsto_const_nhds
  · -- Case z ≠ 1: circleRe(z) * g_n(z) → Re(z) * 0 = 0 = χ_{1}(z)
    have hzmem : z ∉ ({1} : Set Circle) := fun h => hz (Set.mem_singleton_iff.mp h)
    have hind_target : Set.indicator ({1} : Set Circle) (fun _ => (1 : ℝ)) z = 0 :=
      Set.indicator_of_notMem hzmem _
    rw [hind_target]
    have hind_source : Set.indicator ({1} : Set Circle) (fun _ => (1 : ℝ)) z = 0 :=
      Set.indicator_of_notMem hzmem _
    rw [hind_source] at hg_tendsto
    -- Re(z) * g_n(z) → Re(z) * 0 = 0
    have hmul : Tendsto (fun n => circleRe z * thickenedIndicatorReal (hδ_pos n) ({1} : Set Circle) z)
        atTop (𝓝 (circleRe z * 0)) := Tendsto.mul tendsto_const_nhds hg_tendsto
    simp only [mul_zero] at hmul
    simp only [ContinuousMap.mul_apply]
    exact hmul

/-- For thickened indicators g_n → χ_{1}, we have (Im · g_n)(z) → 0 pointwise.
    This is because Im(1) = 0, so at z = 1: Im(1) · g_n(1) = 0 · 1 = 0.
    At z ≠ 1: Im(z) · g_n(z) → Im(z) · 0 = 0. -/
theorem im_mul_thickenedIndicatorReal_tendsto_zero_pointwise
    {δseq : ℕ → ℝ} (hδ_pos : ∀ n, 0 < δseq n) (hδ_lim : Tendsto δseq atTop (𝓝 0)) (z : Circle) :
    Tendsto (fun n => (circleIm * thickenedIndicatorReal (hδ_pos n) ({1} : Set Circle)) z)
      atTop (𝓝 (0 : ℝ)) := by
  have hg_tendsto_fun := thickenedIndicatorReal_tendsto_indicator_closure (F := ({1} : Set Circle)) hδ_pos hδ_lim
  rw [tendsto_pi_nhds] at hg_tendsto_fun
  have hg_tendsto := hg_tendsto_fun z
  simp only [closure_singleton] at hg_tendsto
  by_cases hz : z = 1
  · -- Case z = 1: circleIm(1) * g_n(1) = 0 * 1 = 0
    subst hz
    have hmem_one : (1 : Circle) ∈ ({1} : Set Circle) := Set.mem_singleton 1
    have hg_one : ∀ n, thickenedIndicatorReal (hδ_pos n) ({1} : Set Circle) 1 = (1 : ℝ) :=
      fun n => thickenedIndicatorReal_one_of_mem (hδ_pos n) hmem_one
    have hfun_eq : ∀ n, (circleIm * thickenedIndicatorReal (hδ_pos n) ({1} : Set Circle)) 1 = (0 : ℝ) := by
      intro n
      simp only [ContinuousMap.mul_apply, hg_one n, mul_one, circleIm_one]
    simp only [hfun_eq]
    exact tendsto_const_nhds
  · -- Case z ≠ 1: circleIm(z) * g_n(z) → Im(z) * 0 = 0
    have hzmem : z ∉ ({1} : Set Circle) := fun h => hz (Set.mem_singleton_iff.mp h)
    have hind_source : Set.indicator ({1} : Set Circle) (fun _ => (1 : ℝ)) z = 0 :=
      Set.indicator_of_notMem hzmem _
    rw [hind_source] at hg_tendsto
    -- Im(z) * g_n(z) → Im(z) * 0 = 0
    have hmul : Tendsto (fun n => circleIm z * thickenedIndicatorReal (hδ_pos n) ({1} : Set Circle) z)
        atTop (𝓝 (circleIm z * 0)) := Tendsto.mul tendsto_const_nhds hg_tendsto
    simp only [mul_zero] at hmul
    simp only [ContinuousMap.mul_apply]
    exact hmul

/-- General dominated convergence for spectral functionals.
    If f_n → f pointwise with |f_n| ≤ 1, then spectralFunctionalAux(f_n) → ∫ f dμ. -/
theorem spectralFunctionalAux_tendsto_of_pointwise (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (f : ℕ → C(Circle, ℝ)) (f_lim : Circle → ℝ) (w : H)
    (hf_le_one : ∀ n z, |f n z| ≤ 1)
    (hf_nonneg : ∀ n z, 0 ≤ f n z)
    (hf_tendsto : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (f_lim z))) :
    Tendsto (fun n => spectralFunctionalAux U hU w (f n))
      atTop (𝓝 (∫ z, f_lim z ∂(spectralMeasureDiagonal U hU w))) := by
  let μ_w := spectralMeasureDiagonal U hU w
  -- spectralFunctionalAux w (f n) = ∫ (f n) dμ_w
  have hfunc_eq : ∀ n, spectralFunctionalAux U hU w (f n) = ∫ z, f n z ∂μ_w := by
    intro n
    unfold spectralFunctionalAux
    have h := spectralMeasureDiagonal_integral U hU w (toCc (f n))
    simp only [toCc_apply] at h
    have hdef : (spectralFunctionalCc U hU w) (toCc (f n)) = spectralFunctionalAux U hU w (f n) := rfl
    rw [hdef] at h
    exact h.symm
  -- Apply dominated convergence
  have hconv : Tendsto (fun n => ∫ z, f n z ∂μ_w) atTop (𝓝 (∫ z, f_lim z ∂μ_w)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro n; exact (f n).continuous.aestronglyMeasurable
    · have hfinite : IsFiniteMeasure μ_w := spectralMeasureDiagonal_isFiniteMeasure U hU w
      exact integrable_const (1 : ℝ)
    · intro n
      apply Filter.Eventually.of_forall
      intro z
      rw [Real.norm_of_nonneg (hf_nonneg n z)]
      exact le_of_abs_le (hf_le_one n z)
    · apply Filter.Eventually.of_forall
      intro z
      exact hf_tendsto z
  convert hconv using 1
  funext n
  exact hfunc_eq n

/-- Generalized dominated convergence for spectral functionals (no non-negativity needed).
    If f_n → f pointwise with |f_n| ≤ M, then spectralFunctionalAux(f_n) → ∫ f dμ. -/
theorem spectralFunctionalAux_tendsto_of_pointwise_general (U : H →L[ℂ] H)
    (hU : U ∈ unitary (H →L[ℂ] H)) (f : ℕ → C(Circle, ℝ)) (f_lim : Circle → ℝ) (w : H)
    (M : ℝ) (hf_bound : ∀ n z, |f n z| ≤ M)
    (hf_tendsto : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (f_lim z)))
    (_ : 0 < M) :
    Tendsto (fun n => spectralFunctionalAux U hU w (f n))
      atTop (𝓝 (∫ z, f_lim z ∂(spectralMeasureDiagonal U hU w))) := by
  let μ_w := spectralMeasureDiagonal U hU w
  -- spectralFunctionalAux w (f n) = ∫ (f n) dμ_w
  have hfunc_eq : ∀ n, spectralFunctionalAux U hU w (f n) = ∫ z, f n z ∂μ_w := by
    intro n
    unfold spectralFunctionalAux
    have h := spectralMeasureDiagonal_integral U hU w (toCc (f n))
    simp only [toCc_apply] at h
    have hdef : (spectralFunctionalCc U hU w) (toCc (f n)) = spectralFunctionalAux U hU w (f n) := rfl
    rw [hdef] at h
    exact h.symm
  -- Apply dominated convergence
  have hconv : Tendsto (fun n => ∫ z, f n z ∂μ_w) atTop (𝓝 (∫ z, f_lim z ∂μ_w)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => M)
    · intro n; exact (f n).continuous.aestronglyMeasurable
    · have hfinite : IsFiniteMeasure μ_w := spectralMeasureDiagonal_isFiniteMeasure U hU w
      exact integrable_const M
    · intro n
      apply Filter.Eventually.of_forall
      intro z
      -- ‖f n z‖ = |f n z| for real numbers
      rw [Real.norm_eq_abs]
      exact hf_bound n z
    · apply Filter.Eventually.of_forall
      intro z
      exact hf_tendsto z
  convert hconv using 1
  funext n
  exact hfunc_eq n

set_option maxHeartbeats 400000 in
/-- The spectral integration property for singleton {1}: U P({1}) = P({1}).

    **Proof:** Use CFC multiplicativity and dominated convergence.
    For thickened indicators g_n → χ_{1}:
    1. cfc(g_n, U) → P({1}) weakly: ⟨x, cfc(g_n, U) y⟩ → μ_{x,y}({1}) = ⟨x, P({1}) y⟩
    2. U · cfc(g_n, U) = cfc(id · g_n, U) by CFC multiplicativity
    3. id · g_n → χ_{1} (proven above)
    4. cfc(id · g_n, U) → P({1}) weakly (same limit)
    5. Therefore U P({1}) = P({1}) -/
theorem unitary_comp_spectralProjection_singleton_one (U : H →L[ℂ] H)
    (hU : U ∈ unitary (H →L[ℂ] H)) :
    U ∘L spectralProjectionOfUnitary U hU {1} (measurableSet_singleton 1) =
    spectralProjectionOfUnitary U hU {1} (measurableSet_singleton 1) := by
  haveI : IsStarNormal U := unitary_isStarNormal U hU
  set P := spectralProjectionOfUnitary U hU {1} (measurableSet_singleton 1) with hP_def
  -- Use ext to reduce to inner products
  ext y
  apply ext_inner_left ℂ
  intro x
  -- Goal: ⟨x, U (P y)⟩ = ⟨x, P y⟩
  -- LHS = ⟨U* x, P y⟩ = μ_{U* x, y}({1})
  -- RHS = μ_{x, y}({1})
  --
  -- Strategy: Show both equal the weak limit of cfc(g_n, U)
  -- where g_n are thickened indicators converging to χ_{1}.

  -- Define the approximating sequence
  let δ : ℕ → ℝ := fun n => 1 / (n + 1)
  have hδ_pos : ∀ n, 0 < δ n := fun n => Nat.one_div_pos_of_nat
  have hδ_lim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let g : ℕ → C(Circle, ℝ) := fun n => thickenedIndicatorReal (hδ_pos n) ({1} : Set Circle)

  -- The key fact: Both sides equal the limit of ⟨x, cfc(h_n, U) y⟩ for h_n → χ_{1}
  -- This follows from dominated convergence on the spectral measure.

  -- Step 1: ⟨x, P y⟩ = μ_{x,y}({1}) = lim ⟨x, cfc(g_n, U) y⟩
  have hRHS : @inner ℂ H _ x (P y) = spectralMeasurePolarized U hU x y {1} (measurableSet_singleton 1) := by
    rw [hP_def]
    unfold spectralProjectionOfUnitary
    rw [← sesquilinearToOperator_inner]

  -- Step 2: ⟨x, U (P y)⟩ = ⟨U† x, P y⟩
  have hLHS_adj : @inner ℂ H _ x (U (P y)) = @inner ℂ H _ (U.adjoint x) (P y) := by
    exact (ContinuousLinearMap.adjoint_inner_left U (P y) x).symm

  -- Step 3: For unitary U, U* = U⁻¹, but we use the adjoint relationship
  -- The key is that both ⟨x, U (P y)⟩ and ⟨x, P y⟩ can be computed via limits
  -- of CFC approximations, and these limits are the same.

  -- Key properties from the spectral theory infrastructure:
  have hP_supp := spectralProjection_polarized_product_closed U hU {1} isClosed_singleton x y
  -- hP_supp : ⟨P x, P y⟩ = spectralMeasurePolarized x y {1}

  have hP_idem := spectralProjection_idempotent_closed U hU {1} isClosed_singleton
  have hP_sa := spectralProjection_selfAdjoint U hU {1} (measurableSet_singleton 1)

  -- From the support property: ⟨P x, P y⟩ = spectralMeasurePolarized x y {1} = ⟨x, P y⟩
  have hPxPy_inner : @inner ℂ H _ (P x) (P y) = spectralMeasurePolarized U hU (P x) (P y) Set.univ MeasurableSet.univ :=
    (spectralMeasurePolarized_univ U hU (P x) (P y)).symm

  have hPxy_eq : @inner ℂ H _ (P x) (P y) = @inner ℂ H _ x (P y) := by
    rw [hPxPy_inner, hP_supp, ← hRHS]

  -- Goal: ⟨x, U (P y)⟩ = ⟨x, P y⟩
  -- Strategy: Show ⟨x, U (P y)⟩ = ⟨P x, P y⟩ = ⟨x, P y⟩

  -- The key spectral integration formula (to be proven with dominated convergence):
  -- For z in Range(P({1})), the spectral measure μ_z is supported on {1}.
  -- Therefore U z = ∫ w dP(w) z = 1 · P({1}) z = z (eigenvalue = 1).

  -- Since P y ∈ Range(P({1})) by idempotence, we have U (P y) = P y.

  -- Use the decomposition U = cfcOfCircleReal(Re) + I·cfcOfCircleReal(Im):
  have hU_decomp := unitary_eq_cfcOfCircleReal_re_im U hU

  -- For P y in Range(P({1})), the spectral integration gives:
  -- ⟨x, cfcOfCircleReal(Re) (P y)⟩ = ∫ Re dμ_{x, P y} = Re(1) · μ_{x, P y}({1}) = μ_{x, P y}({1})
  -- ⟨x, cfcOfCircleReal(Im) (P y)⟩ = ∫ Im dμ_{x, P y} = Im(1) · μ_{x, P y}({1}) = 0

  -- Therefore:
  -- ⟨x, U (P y)⟩ = ⟨x, cfcOfCircleReal(Re) (P y)⟩ + I·⟨x, cfcOfCircleReal(Im) (P y)⟩
  --              = μ_{x, P y}({1}) + I·0 = μ_{x, P y}({1})
  --              = μ_{x, y}({1})   (by support property)
  --              = ⟨x, P y⟩

  -- The formal proof requires showing μ_{x, P y} is supported on {1}.
  -- This follows from the spectral support property: P y has support in {1}.

  -- For now, we state this as the key lemma (to be proven with full dominated convergence):
  -- ⟨x, U (P y)⟩ = ⟨x, P y⟩

  -- The calculation: since P y = P (P y) (idempotence), and P is the projection onto
  -- the eigenspace of U with eigenvalue 1, we have U (P y) = 1 · (P y) = P y.

  -- Equivalently: hPxy_eq gives ⟨P x, P y⟩ = ⟨x, P y⟩, and we need ⟨x, U P y⟩ = ⟨P x, P y⟩.

  -- The spectral projection property implies U P = P:
  -- For any y, U (P y) = P y because P projects onto eigenspace for eigenvalue 1.

  -- This is the content of spectral integration for projections onto singletons.
  -- The proof uses CFC multiplicativity and weak convergence.

  -- **Key Proof Strategy:**
  -- 1. For thickened indicators g_n → χ_{1}, cfc(g_n, U) → P({1}) weakly.
  -- 2. U · cfc(g_n, U) = cfc(id · g_n, U) by CFC multiplicativity.
  -- 3. We decompose id · g_n = Re · g_n + I · Im · g_n (on unit circle).
  -- 4. Re · g_n → 1 · χ_{1} = χ_{1} (since Re(1) = 1)
  --    Im · g_n → 0 · χ_{1} = 0 (since Im(1) = 0)
  -- 5. So cfcOfCircleReal(Re · g_n) → P({1}) and cfcOfCircleReal(Im · g_n) → 0 weakly.
  -- 6. Therefore cfc(id · g_n, U) → P({1}) weakly.
  -- 7. Taking limits: ⟨x, U P y⟩ = ⟨x, P y⟩.

  -- The technical details:
  -- ⟨x, U · cfc(g_n, U) y⟩ = ⟨x, cfc(id · g_n, U) y⟩ → ⟨x, P y⟩ (by step 6)
  -- ⟨x, U · cfc(g_n, U) y⟩ = ⟨U† x, cfc(g_n, U) y⟩ → ⟨U† x, P y⟩ = ⟨x, U P y⟩ (by weak conv)
  -- Therefore ⟨x, U P y⟩ = ⟨x, P y⟩.

  -- **Implementation:** Use the multiplicativity property of spectral projections.
  -- For z = P y (in range of P({1})), the spectral measure μ_z is supported on {1}.
  -- This means: spectralMeasurePolarized x z E = spectralMeasurePolarized x y (E ∩ {1}).

  -- From hP_supp: ⟨P x, P y⟩ = spectralMeasurePolarized x y {1}
  -- From hPxy_eq: ⟨P x, P y⟩ = ⟨x, P y⟩
  -- Need: ⟨x, U P y⟩ = ⟨x, P y⟩

  -- Use: U P = P ∘L U for spectral projections onto singletons
  -- This follows from spectral integration: U = ∫ z dP(z) commutes with P(E) for all E.

  -- For the singleton {1}, the spectral integral localizes:
  -- For z in range(P({1})), the spectral measure μ_z is supported on {1}.
  -- So U z = ∫ w dP(w) z = 1 · z = z (eigenvalue 1).

  -- **Key Lemma:** U ∘L P = P (spectral integration formula).
  -- Once we have this, the proof is simple:
  -- ⟨x, U (P y)⟩ = ⟨x, P y⟩ (directly from U P = P).

  -- The spectral integration formula U P({1}) = P({1}) follows from the spectral theorem.
  -- For any z in range(P({1})), U z = 1 · z = z (eigenvalue property).
  -- This is proven via dominated convergence and CFC multiplicativity.

  have hU_P_eq_P : U ∘L P = P := by
    -- **Proof strategy:**
    -- 1. For thickened indicators g_n → χ_{1}, both cfc(g_n, U) and cfc(id · g_n, U) converge weakly to P
    -- 2. U · cfc(g_n, U) = cfc(id · g_n, U) by CFC multiplicativity
    -- 3. Therefore ⟨U† v, P w⟩ = lim ⟨U† v, cfc(g_n, U) w⟩ = lim ⟨v, cfc(id · g_n, U) w⟩ = ⟨v, P w⟩
    ext w
    apply ext_inner_left ℂ
    intro v
    simp only [ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left U (P w) v]
    -- Goal: ⟨U† v, P w⟩ = ⟨v, P w⟩

    -- Define the approximating sequence
    let δ' : ℕ → ℝ := fun n => 1 / (n + 1)
    have hδ'_pos : ∀ n, 0 < δ' n := fun n => Nat.one_div_pos_of_nat
    have hδ'_lim : Tendsto δ' atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    let g' : ℕ → C(Circle, ℝ) := fun n => thickenedIndicatorReal (hδ'_pos n) ({1} : Set Circle)

    -- Key fact 1: ⟨v, cfc(g'_n, U) w⟩ → ⟨v, P w⟩ (weak convergence to P)
    -- This uses the polarization identity and spectralFunctionalAux_tendsto_closed
    have hweak_v : Tendsto (fun n => @inner ℂ H _ v (cfcOfCircleReal U hU (g' n) w))
        atTop (𝓝 (@inner ℂ H _ v (P w))) := by
      -- Use polarization: ⟨v, cfc(g_n, U) w⟩ = (1/4)[Λ_{v+w} - Λ_{v-w} - i·Λ_{v+iw} + i·Λ_{v-iw}]
      have hinner_eq : ∀ n, @inner ℂ H _ v (cfcOfCircleReal U hU (g' n) w) =
          (1/4 : ℂ) * (spectralFunctionalAux U hU (v + w) (g' n) -
                       spectralFunctionalAux U hU (v - w) (g' n) -
                       Complex.I * spectralFunctionalAux U hU (v + Complex.I • w) (g' n) +
                       Complex.I * spectralFunctionalAux U hU (v - Complex.I • w) (g' n)) := by
        intro n
        exact (spectralFunctionalAux_polarization U hU (g' n) v w).symm
      -- Each Λ_z(g'_n) → μ_z({1}).toReal by spectralFunctionalAux_tendsto_closed
      have hΛ1 := spectralFunctionalAux_tendsto_closed U hU {1} isClosed_singleton (v + w) hδ'_pos hδ'_lim
      have hΛ2 := spectralFunctionalAux_tendsto_closed U hU {1} isClosed_singleton (v - w) hδ'_pos hδ'_lim
      have hΛ3 := spectralFunctionalAux_tendsto_closed U hU {1} isClosed_singleton (v + Complex.I • w) hδ'_pos hδ'_lim
      have hΛ4 := spectralFunctionalAux_tendsto_closed U hU {1} isClosed_singleton (v - Complex.I • w) hδ'_pos hδ'_lim
      -- Convert to complex
      have hΛ1' : Tendsto (fun n => (spectralFunctionalAux U hU (v + w) (g' n) : ℂ)) atTop
          (𝓝 ((spectralMeasureDiagonal U hU (v + w) {1}).toReal : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ1
      have hΛ2' : Tendsto (fun n => (spectralFunctionalAux U hU (v - w) (g' n) : ℂ)) atTop
          (𝓝 ((spectralMeasureDiagonal U hU (v - w) {1}).toReal : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ2
      have hΛ3' : Tendsto (fun n => (spectralFunctionalAux U hU (v + Complex.I • w) (g' n) : ℂ)) atTop
          (𝓝 ((spectralMeasureDiagonal U hU (v + Complex.I • w) {1}).toReal : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ3
      have hΛ4' : Tendsto (fun n => (spectralFunctionalAux U hU (v - Complex.I • w) (g' n) : ℂ)) atTop
          (𝓝 ((spectralMeasureDiagonal U hU (v - Complex.I • w) {1}).toReal : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ4
      -- Combine limits
      have hcomb : Tendsto (fun n =>
          (1/4 : ℂ) * (spectralFunctionalAux U hU (v + w) (g' n) -
                       spectralFunctionalAux U hU (v - w) (g' n) -
                       Complex.I * spectralFunctionalAux U hU (v + Complex.I • w) (g' n) +
                       Complex.I * spectralFunctionalAux U hU (v - Complex.I • w) (g' n)))
          atTop (𝓝 ((1/4 : ℂ) * (
            (spectralMeasureDiagonal U hU (v + w) {1}).toReal -
            (spectralMeasureDiagonal U hU (v - w) {1}).toReal -
            Complex.I * (spectralMeasureDiagonal U hU (v + Complex.I • w) {1}).toReal +
            Complex.I * (spectralMeasureDiagonal U hU (v - Complex.I • w) {1}).toReal))) := by
        apply Tendsto.const_mul
        apply Tendsto.add
        · apply Tendsto.sub
          · apply Tendsto.sub hΛ1' hΛ2'
          · exact Tendsto.const_mul Complex.I hΛ3'
        · exact Tendsto.const_mul Complex.I hΛ4'
      -- The limit equals spectralMeasurePolarized v w {1} = ⟨v, P w⟩
      have hlim_eq : (1/4 : ℂ) * (
            (spectralMeasureDiagonal U hU (v + w) {1}).toReal -
            (spectralMeasureDiagonal U hU (v - w) {1}).toReal -
            Complex.I * (spectralMeasureDiagonal U hU (v + Complex.I • w) {1}).toReal +
            Complex.I * (spectralMeasureDiagonal U hU (v - Complex.I • w) {1}).toReal) =
          spectralMeasurePolarized U hU v w {1} (measurableSet_singleton 1) := by
        unfold spectralMeasurePolarized; ring
      have hPinner : @inner ℂ H _ v (P w) =
          spectralMeasurePolarized U hU v w {1} (measurableSet_singleton 1) := by
        rw [hP_def]; unfold spectralProjectionOfUnitary
        rw [← sesquilinearToOperator_inner]
      simp only [hinner_eq]; rw [hPinner, ← hlim_eq]; exact hcomb

    -- Key fact 2: ⟨U† v, cfc(g'_n, U) w⟩ = ⟨v, U cfc(g'_n, U) w⟩ = ⟨v, cfc(id · g'_n, U) w⟩
    have hadj_eq : ∀ n, @inner ℂ H _ (U.adjoint v) (cfcOfCircleReal U hU (g' n) w) =
        @inner ℂ H _ v (U (cfcOfCircleReal U hU (g' n) w)) := by
      intro n
      exact ContinuousLinearMap.adjoint_inner_left U (cfcOfCircleReal U hU (g' n) w) v

    -- U · cfc(g', U) = cfc(id · g', U) by CFC multiplicativity
    have hU_eq_cfc_id : U = cfc (id : ℂ → ℂ) U := (cfc_id' ℂ U).symm
    have hU_mul_cfc_eq : ∀ n, U (cfcOfCircleReal U hU (g' n) w) =
        cfc (fun z => z * circleRealToComplex (g' n) z) U w := by
      intro n
      have hcont_g := circleRealToComplex_continuousOn_spectrum (g' n) U hU
      -- U · cfc(g, U) = cfc(id, U) · cfc(g, U) = cfc(id · g, U)
      unfold cfcOfCircleReal
      have hmul := cfc_mul (id : ℂ → ℂ) (circleRealToComplex (g' n)) U continuousOn_id hcont_g
      -- hmul : cfc id U * cfc g U = cfc (id * g) U
      -- For CLMs, A * B = A ∘L B
      calc U (cfc (circleRealToComplex (g' n)) U w)
          = (U ∘L cfc (circleRealToComplex (g' n)) U) w := rfl
        _ = (cfc (id : ℂ → ℂ) U ∘L cfc (circleRealToComplex (g' n)) U) w := by rw [← hU_eq_cfc_id]
        _ = (cfc (id : ℂ → ℂ) U * cfc (circleRealToComplex (g' n)) U) w := rfl
        _ = (cfc (fun z => id z * circleRealToComplex (g' n) z) U) w := by rw [hmul]
        _ = cfc (fun z => z * circleRealToComplex (g' n) z) U w := by simp only [id]

    -- Key fact 3: ⟨v, cfc(id · g'_n, U) w⟩ also converges to ⟨v, P w⟩
    -- This is because id · g'_n → χ_{1} pointwise (proven in id_mul_thickenedIndicatorReal_tendsto)
    -- We decompose id = Re + i·Im on Circle, so id · g'_n = Re·g'_n + i·Im·g'_n
    -- Re·g'_n → χ_{1} (since Re(1) = 1) and Im·g'_n → 0 (since Im(1) = 0)
    have hweak_id : Tendsto (fun n => @inner ℂ H _ v (cfc (fun z => z * circleRealToComplex (g' n) z) U w))
        atTop (𝓝 (@inner ℂ H _ v (P w))) := by
      -- The function id · g_n = Re · g_n + i · Im · g_n on the unit circle
      -- We decompose: cfc(id · g_n, U) = cfcOfCircleReal(Re · g_n) + i · cfcOfCircleReal(Im · g_n)
      -- And Re · g_n → χ_{1}, Im · g_n → 0

      -- Step 1: Decompose z * g_n(z) = Re(z) * g_n(z) + i * Im(z) * g_n(z) on spectrum
      have hcfc_decomp : ∀ n, cfc (fun z => z * circleRealToComplex (g' n) z) U =
          cfcOfCircleReal U hU (circleRe * g' n) +
          Complex.I • cfcOfCircleReal U hU (circleIm * g' n) := by
        intro n
        haveI : IsStarNormal U := unitary_isStarNormal U hU
        have hcont_g := circleRealToComplex_continuousOn_spectrum (g' n) U hU
        have hcont_re := circleRealToComplex_continuousOn_spectrum circleRe U hU
        have hcont_im := circleRealToComplex_continuousOn_spectrum circleIm U hU
        have hcont_re_g := circleRealToComplex_continuousOn_spectrum (circleRe * g' n) U hU
        have hcont_im_g := circleRealToComplex_continuousOn_spectrum (circleIm * g' n) U hU
        -- On spectrum: z * g(z) = (Re(z) + i*Im(z)) * g(z) = Re(z)*g(z) + i*Im(z)*g(z)
        have heq_on_spec : Set.EqOn (fun z => z * circleRealToComplex (g' n) z)
            (fun z => circleRealToComplex (circleRe * g' n) z +
                      Complex.I * circleRealToComplex (circleIm * g' n) z) (spectrum ℂ U) := by
          intro z hz
          have hz_sphere := spectrum.subset_circle_of_unitary hU hz
          simp only [circleRealToComplex, hz_sphere, dite_true, ContinuousMap.coe_mul,
            Pi.mul_apply, circleRe, circleIm, ContinuousMap.coe_mk]
          -- The goal: z * g(w) = Re(z) * g(w) + I * Im(z) * g(w)
          -- where w = ⟨z, hz_sphere⟩ and (w : ℂ) = z
          -- Set r := g(w) as a real number, then z * r = Re(z) * r + I * Im(z) * r
          set r : ℝ := (g' n) ⟨z, hz_sphere⟩ with hr_def
          simp only [Complex.ofReal_mul]
          -- Now the goal is: z * r = z.re * r + I * (z.im * r)
          -- This follows from z = z.re + z.im * I
          -- First simplify the RHS which has (z.re + z.im * I).re etc
          have hre_simp : ((z.re : ℂ) + (z.im : ℂ) * Complex.I).re = z.re := by
            rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
                Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
            ring
          have him_simp : ((z.re : ℂ) + (z.im : ℂ) * Complex.I).im = z.im := by
            rw [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
                Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
            ring
          -- z = z.re + z.im * I
          have hz_eq : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
          -- Rewrite LHS using hz_eq, RHS simplifies via hre_simp/him_simp
          rw [hz_eq, hre_simp, him_simp]
          ring
        rw [cfc_congr heq_on_spec]
        -- Split cfc of sum
        have hadd : cfc (fun z => circleRealToComplex (circleRe * g' n) z +
            Complex.I * circleRealToComplex (circleIm * g' n) z) U =
            cfc (circleRealToComplex (circleRe * g' n)) U +
            cfc (fun z => Complex.I * circleRealToComplex (circleIm * g' n) z) U := by
          apply cfc_add
          · exact hcont_re_g
          · -- continuousOn for z ↦ I * f(z)
            exact continuousOn_const.mul hcont_im_g
        -- For i * f, use cfc_const_mul
        have hI_mul : cfc (fun z => Complex.I * circleRealToComplex (circleIm * g' n) z) U =
            Complex.I • cfc (circleRealToComplex (circleIm * g' n)) U := by
          rw [cfc_const_mul Complex.I (circleRealToComplex (circleIm * g' n)) U hcont_im_g]
        rw [hadd, hI_mul]
        simp only [cfcOfCircleReal]

      -- Step 2: Decompose the inner product
      have hinner_decomp : ∀ n, @inner ℂ H _ v (cfc (fun z => z * circleRealToComplex (g' n) z) U w) =
          @inner ℂ H _ v (cfcOfCircleReal U hU (circleRe * g' n) w) +
          Complex.I * @inner ℂ H _ v (cfcOfCircleReal U hU (circleIm * g' n) w) := by
        intro n
        rw [hcfc_decomp n]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
        rw [inner_add_right, inner_smul_right]

      -- Step 3: Show cfcOfCircleReal(Re * g_n) converges weakly to P
      -- This uses the same polarization argument as hweak_v, with Re * g_n instead of g_n
      let f_Re : ℕ → C(Circle, ℝ) := fun n => circleRe * g' n

      have hf_Re_bound : ∀ n z, |f_Re n z| ≤ 1 := by
        intro n z
        simp only [f_Re, ContinuousMap.mul_apply]
        have hg_nonneg : 0 ≤ g' n z := thickenedIndicatorReal_nonneg (hδ'_pos n) ({1} : Set Circle) z
        have hg_le_one : g' n z ≤ 1 := thickenedIndicatorReal_le_one (hδ'_pos n) ({1} : Set Circle) z
        have hg_abs : |g' n z| ≤ 1 := abs_le.mpr ⟨by linarith, hg_le_one⟩
        calc |circleRe z * g' n z|
            = |circleRe z| * |g' n z| := abs_mul _ _
          _ ≤ 1 * 1 := by
              apply mul_le_mul (circleRe_abs_le_one z) hg_abs (abs_nonneg _)
              linarith [circleRe_abs_le_one z]
          _ = 1 := mul_one 1

      have hf_Re_tendsto : ∀ z, Tendsto (fun n => f_Re n z)
          atTop (𝓝 (Set.indicator ({1} : Set Circle) (fun _ => (1 : ℝ)) z)) := by
        intro z
        exact re_mul_thickenedIndicatorReal_tendsto_indicator_singleton_one_pointwise hδ'_pos hδ'_lim z

      -- By polarization: ⟨v, cfcOfCircleReal(f_Re n, U) w⟩ converges
      have hweak_Re : Tendsto (fun n => @inner ℂ H _ v (cfcOfCircleReal U hU (f_Re n) w))
          atTop (𝓝 (@inner ℂ H _ v (P w))) := by
        -- Same structure as hweak_v
        have hinner_eq : ∀ n, @inner ℂ H _ v (cfcOfCircleReal U hU (f_Re n) w) =
            (1/4 : ℂ) * (spectralFunctionalAux U hU (v + w) (f_Re n) -
                         spectralFunctionalAux U hU (v - w) (f_Re n) -
                         Complex.I * spectralFunctionalAux U hU (v + Complex.I • w) (f_Re n) +
                         Complex.I * spectralFunctionalAux U hU (v - Complex.I • w) (f_Re n)) := by
          intro n
          exact (spectralFunctionalAux_polarization U hU (f_Re n) v w).symm
        -- Each spectralFunctionalAux converges by dominated convergence
        let f_Re_lim : Circle → ℝ := fun z => Set.indicator ({1} : Set Circle) (fun _ => (1 : ℝ)) z
        have hΛ1 : Tendsto (fun n => spectralFunctionalAux U hU (v + w) (f_Re n))
            atTop (𝓝 (∫ z, f_Re_lim z ∂(spectralMeasureDiagonal U hU (v + w)))) :=
          spectralFunctionalAux_tendsto_of_pointwise_general U hU f_Re f_Re_lim (v + w) 1
            hf_Re_bound hf_Re_tendsto one_pos
        have hΛ2 : Tendsto (fun n => spectralFunctionalAux U hU (v - w) (f_Re n))
            atTop (𝓝 (∫ z, f_Re_lim z ∂(spectralMeasureDiagonal U hU (v - w)))) :=
          spectralFunctionalAux_tendsto_of_pointwise_general U hU f_Re f_Re_lim (v - w) 1
            hf_Re_bound hf_Re_tendsto one_pos
        have hΛ3 : Tendsto (fun n => spectralFunctionalAux U hU (v + Complex.I • w) (f_Re n))
            atTop (𝓝 (∫ z, f_Re_lim z ∂(spectralMeasureDiagonal U hU (v + Complex.I • w)))) :=
          spectralFunctionalAux_tendsto_of_pointwise_general U hU f_Re f_Re_lim (v + Complex.I • w) 1
            hf_Re_bound hf_Re_tendsto one_pos
        have hΛ4 : Tendsto (fun n => spectralFunctionalAux U hU (v - Complex.I • w) (f_Re n))
            atTop (𝓝 (∫ z, f_Re_lim z ∂(spectralMeasureDiagonal U hU (v - Complex.I • w)))) :=
          spectralFunctionalAux_tendsto_of_pointwise_general U hU f_Re f_Re_lim (v - Complex.I • w) 1
            hf_Re_bound hf_Re_tendsto one_pos
        -- The integral of the indicator equals the measure of {1}
        have hintegral_eq : ∀ y : H, ∫ z, f_Re_lim z ∂(spectralMeasureDiagonal U hU y) =
            (spectralMeasureDiagonal U hU y {1}).toReal := by
          intro y
          simp only [f_Re_lim]
          -- ∫ indicator {1} (fun _ => 1) dμ = μ({1})
          have hfinite : IsFiniteMeasure (spectralMeasureDiagonal U hU y) :=
            spectralMeasureDiagonal_isFiniteMeasure U hU y
          -- Convert (fun x => 1) to 1
          have heq : ({1} : Set Circle).indicator (fun _ : Circle => (1 : ℝ)) =
              ({1} : Set Circle).indicator (1 : Circle → ℝ) := by rfl
          rw [heq, integral_indicator_one (measurableSet_singleton 1)]
          -- Now: μ.real {1} = (μ {1}).toReal
          rfl
        -- Convert to complex and combine
        have hΛ1' := Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ1
        have hΛ2' := Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ2
        have hΛ3' := Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ3
        have hΛ4' := Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ4
        simp only [hintegral_eq] at hΛ1' hΛ2' hΛ3' hΛ4'
        have hcomb : Tendsto (fun n =>
            (1/4 : ℂ) * (spectralFunctionalAux U hU (v + w) (f_Re n) -
                         spectralFunctionalAux U hU (v - w) (f_Re n) -
                         Complex.I * spectralFunctionalAux U hU (v + Complex.I • w) (f_Re n) +
                         Complex.I * spectralFunctionalAux U hU (v - Complex.I • w) (f_Re n)))
            atTop (𝓝 ((1/4 : ℂ) * (
              (spectralMeasureDiagonal U hU (v + w) {1}).toReal -
              (spectralMeasureDiagonal U hU (v - w) {1}).toReal -
              Complex.I * (spectralMeasureDiagonal U hU (v + Complex.I • w) {1}).toReal +
              Complex.I * (spectralMeasureDiagonal U hU (v - Complex.I • w) {1}).toReal))) := by
          apply Tendsto.const_mul
          apply Tendsto.add
          · apply Tendsto.sub
            · apply Tendsto.sub hΛ1' hΛ2'
            · exact Tendsto.const_mul Complex.I hΛ3'
          · exact Tendsto.const_mul Complex.I hΛ4'
        have hlim_eq : (1/4 : ℂ) * (
              (spectralMeasureDiagonal U hU (v + w) {1}).toReal -
              (spectralMeasureDiagonal U hU (v - w) {1}).toReal -
              Complex.I * (spectralMeasureDiagonal U hU (v + Complex.I • w) {1}).toReal +
              Complex.I * (spectralMeasureDiagonal U hU (v - Complex.I • w) {1}).toReal) =
            spectralMeasurePolarized U hU v w {1} (measurableSet_singleton 1) := by
          unfold spectralMeasurePolarized; ring
        have hPinner : @inner ℂ H _ v (P w) =
            spectralMeasurePolarized U hU v w {1} (measurableSet_singleton 1) := by
          rw [hP_def]; unfold spectralProjectionOfUnitary; rw [← sesquilinearToOperator_inner]
        simp only [hinner_eq]; rw [hPinner, ← hlim_eq]; exact hcomb

      -- Step 4: Show cfcOfCircleReal(Im * g_n) converges weakly to 0
      let f_Im : ℕ → C(Circle, ℝ) := fun n => circleIm * g' n

      have hf_Im_bound : ∀ n z, |f_Im n z| ≤ 1 := by
        intro n z
        simp only [f_Im, ContinuousMap.mul_apply]
        have hg_nonneg : 0 ≤ g' n z := thickenedIndicatorReal_nonneg (hδ'_pos n) ({1} : Set Circle) z
        have hg_le_one : g' n z ≤ 1 := thickenedIndicatorReal_le_one (hδ'_pos n) ({1} : Set Circle) z
        have hg_abs : |g' n z| ≤ 1 := abs_le.mpr ⟨by linarith, hg_le_one⟩
        calc |circleIm z * g' n z|
            = |circleIm z| * |g' n z| := abs_mul _ _
          _ ≤ 1 * 1 := by
              apply mul_le_mul (circleIm_abs_le_one z) hg_abs (abs_nonneg _)
              linarith [circleIm_abs_le_one z]
          _ = 1 := mul_one 1

      have hf_Im_tendsto : ∀ z, Tendsto (fun n => f_Im n z) atTop (𝓝 (0 : ℝ)) := by
        intro z
        exact im_mul_thickenedIndicatorReal_tendsto_zero_pointwise hδ'_pos hδ'_lim z

      have hweak_Im : Tendsto (fun n => @inner ℂ H _ v (cfcOfCircleReal U hU (f_Im n) w))
          atTop (𝓝 (0 : ℂ)) := by
        have hinner_eq : ∀ n, @inner ℂ H _ v (cfcOfCircleReal U hU (f_Im n) w) =
            (1/4 : ℂ) * (spectralFunctionalAux U hU (v + w) (f_Im n) -
                         spectralFunctionalAux U hU (v - w) (f_Im n) -
                         Complex.I * spectralFunctionalAux U hU (v + Complex.I • w) (f_Im n) +
                         Complex.I * spectralFunctionalAux U hU (v - Complex.I • w) (f_Im n)) := by
          intro n
          exact (spectralFunctionalAux_polarization U hU (f_Im n) v w).symm
        -- Each spectralFunctionalAux converges to 0
        have hΛ1 : Tendsto (fun n => spectralFunctionalAux U hU (v + w) (f_Im n))
            atTop (𝓝 (∫ _, (0 : ℝ) ∂(spectralMeasureDiagonal U hU (v + w)))) :=
          spectralFunctionalAux_tendsto_of_pointwise_general U hU f_Im (fun _ => 0) (v + w) 1
            hf_Im_bound hf_Im_tendsto one_pos
        have hΛ2 : Tendsto (fun n => spectralFunctionalAux U hU (v - w) (f_Im n))
            atTop (𝓝 (∫ _, (0 : ℝ) ∂(spectralMeasureDiagonal U hU (v - w)))) :=
          spectralFunctionalAux_tendsto_of_pointwise_general U hU f_Im (fun _ => 0) (v - w) 1
            hf_Im_bound hf_Im_tendsto one_pos
        have hΛ3 : Tendsto (fun n => spectralFunctionalAux U hU (v + Complex.I • w) (f_Im n))
            atTop (𝓝 (∫ _, (0 : ℝ) ∂(spectralMeasureDiagonal U hU (v + Complex.I • w)))) :=
          spectralFunctionalAux_tendsto_of_pointwise_general U hU f_Im (fun _ => 0) (v + Complex.I • w) 1
            hf_Im_bound hf_Im_tendsto one_pos
        have hΛ4 : Tendsto (fun n => spectralFunctionalAux U hU (v - Complex.I • w) (f_Im n))
            atTop (𝓝 (∫ _, (0 : ℝ) ∂(spectralMeasureDiagonal U hU (v - Complex.I • w)))) :=
          spectralFunctionalAux_tendsto_of_pointwise_general U hU f_Im (fun _ => 0) (v - Complex.I • w) 1
            hf_Im_bound hf_Im_tendsto one_pos
        -- Integrals of 0 are 0
        simp only [integral_zero] at hΛ1 hΛ2 hΛ3 hΛ4
        have hΛ1' := Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ1
        have hΛ2' := Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ2
        have hΛ3' := Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ3
        have hΛ4' := Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ4
        simp only [Complex.ofReal_zero] at hΛ1' hΛ2' hΛ3' hΛ4'
        have hcomb : Tendsto (fun n =>
            (1/4 : ℂ) * (spectralFunctionalAux U hU (v + w) (f_Im n) -
                         spectralFunctionalAux U hU (v - w) (f_Im n) -
                         Complex.I * spectralFunctionalAux U hU (v + Complex.I • w) (f_Im n) +
                         Complex.I * spectralFunctionalAux U hU (v - Complex.I • w) (f_Im n)))
            atTop (𝓝 ((1/4 : ℂ) * (0 - 0 - Complex.I * 0 + Complex.I * 0))) := by
          apply Tendsto.const_mul
          apply Tendsto.add
          · apply Tendsto.sub
            · apply Tendsto.sub hΛ1' hΛ2'
            · exact Tendsto.const_mul Complex.I hΛ3'
          · exact Tendsto.const_mul Complex.I hΛ4'
        simp only [sub_zero, mul_zero, add_zero, MulZeroClass.mul_zero] at hcomb
        simp only [hinner_eq]
        exact hcomb

      -- Step 5: Combine the limits
      simp only [hinner_decomp]
      have hlim : Tendsto (fun n =>
          @inner ℂ H _ v (cfcOfCircleReal U hU (f_Re n) w) +
          Complex.I * @inner ℂ H _ v (cfcOfCircleReal U hU (f_Im n) w))
          atTop (𝓝 (@inner ℂ H _ v (P w) + Complex.I * 0)) := by
        apply Tendsto.add hweak_Re (Tendsto.const_mul Complex.I hweak_Im)
      simp only [mul_zero, add_zero] at hlim
      -- The goal matches hlim after unfolding f_Re and f_Im
      exact hlim

    -- Final step: combine the limits
    -- ⟨U† v, P w⟩ = lim ⟨U† v, cfc(g'_n, U) w⟩  (weak convergence, same as hweak_v with U† v)
    --             = lim ⟨v, U cfc(g'_n, U) w⟩    (by hadj_eq)
    --             = lim ⟨v, cfc(id · g'_n, U) w⟩ (by hU_mul_cfc_eq)
    --             = ⟨v, P w⟩                      (by hweak_id)
    have hweak_Uv : Tendsto (fun n => @inner ℂ H _ (U.adjoint v) (cfcOfCircleReal U hU (g' n) w))
        atTop (𝓝 (@inner ℂ H _ (U.adjoint v) (P w))) := by
      -- Same proof as hweak_v but with U† v instead of v
      have hinner_eq : ∀ n, @inner ℂ H _ (U.adjoint v) (cfcOfCircleReal U hU (g' n) w) =
          (1/4 : ℂ) * (spectralFunctionalAux U hU (U.adjoint v + w) (g' n) -
                       spectralFunctionalAux U hU (U.adjoint v - w) (g' n) -
                       Complex.I * spectralFunctionalAux U hU (U.adjoint v + Complex.I • w) (g' n) +
                       Complex.I * spectralFunctionalAux U hU (U.adjoint v - Complex.I • w) (g' n)) := by
        intro n
        exact (spectralFunctionalAux_polarization U hU (g' n) (U.adjoint v) w).symm
      have hΛ1 := spectralFunctionalAux_tendsto_closed U hU {1} isClosed_singleton (U.adjoint v + w) hδ'_pos hδ'_lim
      have hΛ2 := spectralFunctionalAux_tendsto_closed U hU {1} isClosed_singleton (U.adjoint v - w) hδ'_pos hδ'_lim
      have hΛ3 := spectralFunctionalAux_tendsto_closed U hU {1} isClosed_singleton (U.adjoint v + Complex.I • w) hδ'_pos hδ'_lim
      have hΛ4 := spectralFunctionalAux_tendsto_closed U hU {1} isClosed_singleton (U.adjoint v - Complex.I • w) hδ'_pos hδ'_lim
      have hΛ1' := Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ1
      have hΛ2' := Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ2
      have hΛ3' := Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ3
      have hΛ4' := Complex.continuous_ofReal.continuousAt.tendsto.comp hΛ4
      have hcomb : Tendsto (fun n =>
          (1/4 : ℂ) * (spectralFunctionalAux U hU (U.adjoint v + w) (g' n) -
                       spectralFunctionalAux U hU (U.adjoint v - w) (g' n) -
                       Complex.I * spectralFunctionalAux U hU (U.adjoint v + Complex.I • w) (g' n) +
                       Complex.I * spectralFunctionalAux U hU (U.adjoint v - Complex.I • w) (g' n)))
          atTop (𝓝 ((1/4 : ℂ) * (
            (spectralMeasureDiagonal U hU (U.adjoint v + w) {1}).toReal -
            (spectralMeasureDiagonal U hU (U.adjoint v - w) {1}).toReal -
            Complex.I * (spectralMeasureDiagonal U hU (U.adjoint v + Complex.I • w) {1}).toReal +
            Complex.I * (spectralMeasureDiagonal U hU (U.adjoint v - Complex.I • w) {1}).toReal))) := by
        apply Tendsto.const_mul
        apply Tendsto.add
        · apply Tendsto.sub; apply Tendsto.sub hΛ1' hΛ2'; exact Tendsto.const_mul Complex.I hΛ3'
        · exact Tendsto.const_mul Complex.I hΛ4'
      have hlim_eq : (1/4 : ℂ) * (
            (spectralMeasureDiagonal U hU (U.adjoint v + w) {1}).toReal -
            (spectralMeasureDiagonal U hU (U.adjoint v - w) {1}).toReal -
            Complex.I * (spectralMeasureDiagonal U hU (U.adjoint v + Complex.I • w) {1}).toReal +
            Complex.I * (spectralMeasureDiagonal U hU (U.adjoint v - Complex.I • w) {1}).toReal) =
          spectralMeasurePolarized U hU (U.adjoint v) w {1} (measurableSet_singleton 1) := by
        unfold spectralMeasurePolarized; ring
      have hPinner : @inner ℂ H _ (U.adjoint v) (P w) =
          spectralMeasurePolarized U hU (U.adjoint v) w {1} (measurableSet_singleton 1) := by
        rw [hP_def]; unfold spectralProjectionOfUnitary; rw [← sesquilinearToOperator_inner]
      simp only [hinner_eq]; rw [hPinner, ← hlim_eq]; exact hcomb

    -- The two limits are equal via hadj_eq and hU_mul_cfc_eq
    have hlim_via_U : Tendsto (fun n => @inner ℂ H _ v (cfc (fun z => z * circleRealToComplex (g' n) z) U w))
        atTop (𝓝 (@inner ℂ H _ (U.adjoint v) (P w))) := by
      have heq : ∀ n, @inner ℂ H _ v (cfc (fun z => z * circleRealToComplex (g' n) z) U w) =
          @inner ℂ H _ (U.adjoint v) (cfcOfCircleReal U hU (g' n) w) := by
        intro n
        rw [← hU_mul_cfc_eq n, ← hadj_eq n]
      simp only [heq]
      exact hweak_Uv

    -- By uniqueness of limits: ⟨U† v, P w⟩ = ⟨v, P w⟩
    exact tendsto_nhds_unique hlim_via_U hweak_id

  -- Convert (U.comp P) y to U (P y) and use hU_P_eq_P
  simp only [ContinuousLinearMap.comp_apply]
  -- Goal: ⟨x, U (P y)⟩ = ⟨x, P y⟩
  -- From hU_P_eq_P: (U ∘L P) y = P y, i.e., U (P y) = P y
  have hUPy_eq_Py : U (P y) = P y := by
    calc U (P y) = (U ∘L P) y := rfl
      _ = P y := by rw [hU_P_eq_P]
  rw [hUPy_eq_Py]

/-! ### Main construction: Spectral measure for self-adjoint operators -/

/-- The complete spectral measure for a self-adjoint operator T, constructed via:
    1. Cayley transform U of T (unitary)
    2. RMK spectral projection P_Circle for U on Circle
    3. Pullback via cayleyToCircle

    This inherits all PVM properties from the RMK theorem. -/
def spectralMeasureFromRMK (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (E : Set ℝ) (hE : MeasurableSet E) : H →L[ℂ] H :=
  let U := C.U
  let hU := cayley_mem_unitary T hT hsa C
  let E_circle := cayleyToCircle '' E
  let hE_circle := cayleyToCircle_measurableSet_image E hE
  spectralProjectionOfUnitary U hU E_circle hE_circle

/-- The spectral measure from RMK satisfies P(∅) = 0. -/
theorem spectralMeasureFromRMK_empty (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) :
    spectralMeasureFromRMK T hT hsa C ∅ MeasurableSet.empty = 0 := by
  simp only [spectralMeasureFromRMK, image_empty]
  exact spectralProjection_empty C.U (cayley_mem_unitary T hT hsa C)

/-- The spectral measure from RMK is idempotent. -/
theorem spectralMeasureFromRMK_idempotent (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (E : Set ℝ) (hE : MeasurableSet E) :
    spectralMeasureFromRMK T hT hsa C E hE ∘L spectralMeasureFromRMK T hT hsa C E hE =
    spectralMeasureFromRMK T hT hsa C E hE := by
  simp only [spectralMeasureFromRMK]
  exact spectralProjection_idempotent C.U (cayley_mem_unitary T hT hsa C) _ _

/-- The spectral measure from RMK is self-adjoint. -/
theorem spectralMeasureFromRMK_selfAdjoint (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (E : Set ℝ) (hE : MeasurableSet E) :
    (spectralMeasureFromRMK T hT hsa C E hE).adjoint =
    spectralMeasureFromRMK T hT hsa C E hE := by
  simp only [spectralMeasureFromRMK]
  exact spectralProjection_selfAdjoint C.U (cayley_mem_unitary T hT hsa C) _ _

/-- The spectral measure from RMK is multiplicative on intersections. -/
theorem spectralMeasureFromRMK_multiplicative (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (E F : Set ℝ) (hE : MeasurableSet E) (hF : MeasurableSet F) :
    spectralMeasureFromRMK T hT hsa C (E ∩ F) (hE.inter hF) =
    spectralMeasureFromRMK T hT hsa C E hE ∘L spectralMeasureFromRMK T hT hsa C F hF := by
  simp only [spectralMeasureFromRMK]
  -- Key: cayleyToCircle '' (E ∩ F) = (cayleyToCircle '' E) ∩ (cayleyToCircle '' F) by injectivity
  have h_inter : cayleyToCircle '' (E ∩ F) = cayleyToCircle '' E ∩ cayleyToCircle '' F :=
    image_inter cayleyToCircle_injective
  simp only [h_inter]
  exact spectralProjection_multiplicative C.U (cayley_mem_unitary T hT hsa C) _ _ _ _

/-- For the Cayley transform, 1 is not an eigenvalue, hence P({1}) = 0.

    **Proof Strategy:**
    The key is to show U P({1}) = P({1}) using CFC multiplicativity, then use
    `one_not_eigenvalue` to conclude P({1}) = 0.

    1. For thickened indicators g_n → χ_{1}:
       - cfc(g_n, U) converges to P({1}) weakly
       - U · cfc(g_n, U) = cfc(id · g_n, U) by CFC multiplicativity

    2. At z = 1: (id · g_n)(1) = 1 · g_n(1) = 1 · 1 = 1 = χ_{1}(1)
       At z ≠ 1: (id · g_n)(z) = z · g_n(z) → z · 0 = 0 = χ_{1}(z)
       So id · g_n → χ_{1} pointwise, same limit as g_n.

    3. Both cfc(g_n, U) → P({1}) and cfc(id · g_n, U) = U · cfc(g_n, U) → P({1})
       Taking limits: U P({1}) = P({1})

    4. For any y, let z = P({1}) y. Then U z = z.
       By C.one_not_eigenvalue: z = 0. So P({1}) = 0. -/
theorem spectralProjection_singleton_one_eq_zero (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) :
    spectralProjectionOfUnitary C.U (cayley_mem_unitary T hT hsa C) {1}
      (measurableSet_singleton 1) = 0 := by
  set U := C.U with hU_def
  set hU := cayley_mem_unitary T hT hsa C
  set P := spectralProjectionOfUnitary U hU {1} (measurableSet_singleton 1) with hP_def

  -- Step 1: Show that ‖P z‖² = μ_z({1}).toReal for all z (since {1} is closed)
  have hnorm_sq : ∀ z : H, ‖P z‖^2 = (spectralMeasureDiagonal U hU z {1}).toReal := by
    intro z
    exact spectralProjection_norm_sq_closed U hU {1} isClosed_singleton z

  -- Step 2: Show that range(P) ⊆ eigenspace of U at eigenvalue 1
  -- This uses U P({1}) = P({1}), which follows from spectral integration
  --
  -- The spectral integration formula: U = ∫ z dP(z) implies
  -- U P(E) = ∫_E z dP(z), and for singleton E = {λ}: U P({λ}) = λ P({λ})
  -- For λ = 1: U P({1}) = P({1})

  -- Step 3: Use one_not_eigenvalue to conclude P = 0
  -- For any y, if U(Py) = Py, then by one_not_eigenvalue, Py = 0.

  ext y
  rw [ContinuousLinearMap.zero_apply]

  -- Strategy: Show ‖P y‖ = 0 using hnorm_sq and μ_y({1}) = 0
  -- The key is that μ_z({1}) = 0 when 1 is not an eigenvalue.
  --
  -- To prove μ_z({1}) = 0, we use the spectral integration property:
  -- U P({1}) z = 1 · P({1}) z = P({1}) z
  -- So P({1}) z is in the eigenspace of U at eigenvalue 1.
  -- By one_not_eigenvalue, P({1}) z = 0.

  -- The spectral projection P({1}) satisfies: for any w in range(P({1})),
  -- U w = w (since P({1}) projects onto the eigenspace of eigenvalue 1).
  -- This follows from the spectral integration: U P({1}) = 1 · P({1}) = P({1})

  -- Claim: P y is an eigenvector of U with eigenvalue 1
  -- Proof of claim: Use U ∘L P = P (spectral integration for singletons)

  have hP_eigenvector : U (P y) = P y := by
    -- This follows from U ∘L P = P (proven in unitary_comp_spectralProjection_singleton_one)
    have hUP := unitary_comp_spectralProjection_singleton_one U hU
    calc U (P y) = (U ∘L P) y := rfl
      _ = P y := by rw [hUP]

  -- Now use one_not_eigenvalue
  exact C.one_not_eigenvalue (P y) hP_eigenvector

/-- The spectral measure from RMK satisfies P(ℝ) = 1.
    Key observation: cayleyToCircle '' ℝ = Circle \ {1} by cayleyToCircle_range.
    The spectral projection for Circle \ {1} equals 1 because:
    1. P({1}) = 0 (since 1 is not an eigenvalue of the Cayley transform)
    2. ‖P(Circle \ {1})z‖² = μ_z(Circle \ {1}) = μ_z(Circle) - μ_z({1}) = ‖z‖² - 0 = ‖z‖²
    3. A self-adjoint idempotent with ‖Pz‖ = ‖z‖ for all z must be the identity -/
theorem spectralMeasureFromRMK_univ (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) :
    spectralMeasureFromRMK T hT hsa C Set.univ MeasurableSet.univ = 1 := by
  -- spectralMeasureFromRMK ... Set.univ ... = spectralProjectionOfUnitary U hU (cayleyToCircle '' univ) _
  -- = spectralProjectionOfUnitary U hU (Circle \ {1}) _ (by cayleyToCircle_range)
  let U := C.U
  let hU := cayley_mem_unitary T hT hsa C
  simp only [spectralMeasureFromRMK]
  -- cayleyToCircle '' univ = range cayleyToCircle = Circle \ {1}
  have himg_eq_range : cayleyToCircle '' Set.univ = range cayleyToCircle := image_univ
  have hrange : range cayleyToCircle = {z : Circle | z ≠ 1} := cayleyToCircle_range
  -- Now show P(Circle \ {1}) = 1
  -- Strategy: Show ‖P(Circle \ {1})z‖² = ‖z‖² for all z, which implies P = 1
  -- Using: ‖P(E)z‖² = μ_z(E) and μ_z(Circle \ {1}) = μ_z(Circle) - μ_z({1}) = ‖z‖² - 0
  ext y
  rw [ContinuousLinearMap.one_apply]
  apply ext_inner_left ℂ
  intro x
  -- Goal: ⟨x, P(cayleyToCircle '' univ) y⟩ = ⟨x, y⟩
  have hinner_P : @inner ℂ H _ x
      (spectralProjectionOfUnitary U hU (cayleyToCircle '' Set.univ)
        (cayleyToCircle_measurableSet_image Set.univ MeasurableSet.univ) y) =
      spectralMeasurePolarized U hU x y (cayleyToCircle '' Set.univ)
        (cayleyToCircle_measurableSet_image Set.univ MeasurableSet.univ) := by
    unfold spectralProjectionOfUnitary
    rw [← sesquilinearToOperator_inner]
  rw [hinner_P]
  -- Need: spectralMeasurePolarized x y (Circle \ {1}) = ⟨x, y⟩
  -- = spectralMeasurePolarized x y Circle (total measure)
  -- This holds because μ_{x,y}({1}) = 0 (from spectralProjection_singleton_one_eq_zero)
  have htotal : spectralMeasurePolarized U hU x y Set.univ MeasurableSet.univ = @inner ℂ H _ x y :=
    spectralMeasurePolarized_univ U hU x y
  -- The key is that Circle = (Circle \ {1}) ∪ {1} and {1} has zero measure
  -- From spectralProjection_singleton_one_eq_zero: P({1}) = 0
  -- So μ_{x,y}({1}) = ⟨x, P({1}) y⟩ = ⟨x, 0⟩ = 0
  -- Then μ_{x,y}(Circle \ {1}) = μ_{x,y}(Circle) = ⟨x, y⟩

  -- Step 1: Show P({1}) = 0
  have hP1_eq_zero : spectralProjectionOfUnitary U hU {1} (measurableSet_singleton 1) = 0 :=
    spectralProjection_singleton_one_eq_zero T hT hsa C

  -- Step 2: μ_{x,y}({1}) = 0
  -- This follows from P({1}) = 0, so ⟨x, P({1}) y⟩ = ⟨x, 0⟩ = 0
  have hμ1_eq_zero : spectralMeasurePolarized U hU x y {1} (measurableSet_singleton 1) = 0 := by
    -- spectralMeasurePolarized x y E = ⟨x, P(E) y⟩ by sesquilinear form
    unfold spectralMeasurePolarized
    -- Since P({1}) = 0, P({1}) y = 0
    have hPy : spectralProjectionOfUnitary U hU {1} (measurableSet_singleton 1) y = 0 := by
      rw [hP1_eq_zero, ContinuousLinearMap.zero_apply]
    -- So ⟨x, P({1}) y⟩ = ⟨x, 0⟩ = 0
    -- But we need to relate this to the polarization formula
    -- spectralMeasurePolarized = (1/4)[μ_{x+y} - μ_{x-y} - i·μ_{x+iy} + i·μ_{x-iy}]
    -- Since P({1}) = 0, all diagonal measures μ_z({1}) = 0
    have hdiag_zero : ∀ z : H, (spectralMeasureDiagonal U hU z {1}).toReal = 0 := by
      intro z
      -- spectralMeasureDiagonal z {1} = spectralMeasurePolarized z z {1} by spectralMeasurePolarized_diag
      -- And spectralMeasurePolarized z z {1} = ⟨z, P({1}) z⟩ = ⟨z, 0⟩ = 0
      have hPz : spectralProjectionOfUnitary U hU {1} (measurableSet_singleton 1) z = 0 := by
        rw [hP1_eq_zero, ContinuousLinearMap.zero_apply]
      -- The polarized measure at (z, z) equals the diagonal measure
      have h := spectralMeasurePolarized_diag U hU z {1} (measurableSet_singleton 1)
      -- spectralMeasurePolarized z z {1} = ⟨z, P({1}) z⟩ by sesquilinear form
      have hpol_zero : spectralMeasurePolarized U hU z z {1} (measurableSet_singleton 1) = 0 := by
        -- Use sesquilinearToOperator_inner: ⟨z, P({1}) z⟩ = spectralMeasurePolarized z z {1}
        have hinner : @inner ℂ H _ z (spectralProjectionOfUnitary U hU {1} (measurableSet_singleton 1) z) =
            spectralMeasurePolarized U hU z z {1} (measurableSet_singleton 1) := by
          unfold spectralProjectionOfUnitary
          rw [← sesquilinearToOperator_inner]
        rw [hPz, inner_zero_right] at hinner
        exact hinner.symm
      -- h : spectralMeasurePolarized z z {1} = ↑μ_z({1}).toReal
      -- hpol_zero : spectralMeasurePolarized z z {1} = 0
      -- Need: μ_z({1}).toReal = 0
      rw [h] at hpol_zero
      -- hpol_zero : ↑μ_z({1}).toReal = 0
      exact Complex.ofReal_eq_zero.mp hpol_zero
    simp only [hdiag_zero, Complex.ofReal_zero, mul_zero, sub_zero, add_zero,
      MulZeroClass.mul_zero]

  -- Step 3: cayleyToCircle '' univ = Circle \ {1}
  have himg : cayleyToCircle '' Set.univ = {z : Circle | z ≠ 1} := by
    rw [image_univ, cayleyToCircle_range]

  -- Step 4: μ_{x,y}(Circle \ {1}) = μ_{x,y}(Circle) because μ_{x,y}({1}) = 0
  -- Circle = (Circle \ {1}) ∪ {1} (disjoint)
  have hunion : (Set.univ : Set Circle) = ({z : Circle | z ≠ 1}) ∪ ({1} : Set Circle) := by
    ext z
    simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff, true_iff]
    by_cases hz : z = 1
    · right; exact hz
    · left; exact hz

  have hdisjoint : Disjoint ({z : Circle | z ≠ 1}) ({1} : Set Circle) := by
    rw [Set.disjoint_iff]
    intro z ⟨hz_ne, hz_eq⟩
    simp only [Set.mem_setOf_eq] at hz_ne
    simp only [Set.mem_singleton_iff] at hz_eq
    exact hz_ne hz_eq

  -- The image of univ equals {z | z ≠ 1}
  have hmeas_compl : MeasurableSet ({z : Circle | z ≠ 1}) := by
    -- {z | z ≠ 1} = {1}ᶜ
    have heq : ({z : Circle | z ≠ 1}) = ({1} : Set Circle)ᶜ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [heq]
    exact (measurableSet_singleton 1).compl

  -- Use the fact that spectralMeasurePolarized is additive on disjoint sets
  -- μ(Circle) = μ(Circle \ {1}) + μ({1}) = μ(Circle \ {1}) + 0
  -- Since spectralMeasurePolarized is a linear combination of diagonal measures (which are actual measures),
  -- it inherits additivity.
  have hadd : spectralMeasurePolarized U hU x y Set.univ MeasurableSet.univ =
      spectralMeasurePolarized U hU x y {z : Circle | z ≠ 1} hmeas_compl +
      spectralMeasurePolarized U hU x y {1} (measurableSet_singleton 1) := by
    -- Unfold the definition of spectralMeasurePolarized
    unfold spectralMeasurePolarized
    -- For each diagonal measure μ_w, we have μ_w(univ) = μ_w({z ≠ 1}) + μ_w({1}) by measure additivity
    have hadd_diag : ∀ w : H, (spectralMeasureDiagonal U hU w Set.univ).toReal =
        (spectralMeasureDiagonal U hU w {z : Circle | z ≠ 1}).toReal +
        (spectralMeasureDiagonal U hU w {1}).toReal := by
      intro w
      -- spectralMeasureDiagonal is a measure, so it's additive on disjoint sets
      have hm := @MeasureTheory.measure_union Circle _ (spectralMeasureDiagonal U hU w)
        {z : Circle | z ≠ 1} {1} hdisjoint (measurableSet_singleton 1)
      -- hm : μ_w({z ≠ 1} ∪ {1}) = μ_w({z ≠ 1}) + μ_w({1})
      -- hunion : univ = {z ≠ 1} ∪ {1}
      conv_lhs => rw [hunion]
      rw [hm]
      -- Convert ENNReal addition to Real addition
      have hfinite : IsFiniteMeasure (spectralMeasureDiagonal U hU w) :=
        spectralMeasureDiagonal_isFiniteMeasure U hU w
      have hne1 : (spectralMeasureDiagonal U hU w {z : Circle | z ≠ 1}) ≠ ⊤ :=
        MeasureTheory.measure_ne_top _ _
      have hne2 : (spectralMeasureDiagonal U hU w {1}) ≠ ⊤ :=
        MeasureTheory.measure_ne_top _ _
      exact ENNReal.toReal_add hne1 hne2
    -- Apply hadd_diag to each term
    simp only [hadd_diag, Complex.ofReal_add]
    ring

  rw [hadd, hμ1_eq_zero, add_zero] at htotal
  -- Now htotal : μ_{x,y}({z | z ≠ 1}) = ⟨x, y⟩
  -- And himg : cayleyToCircle '' univ = {z | z ≠ 1}
  -- So μ_{x,y}(cayleyToCircle '' univ) = ⟨x, y⟩
  have himg_meas : cayleyToCircle '' Set.univ = {z : Circle | z ≠ 1} := himg
  -- Convert the goal
  have hmeas_img := cayleyToCircle_measurableSet_image Set.univ MeasurableSet.univ
  -- The measures are equal because the sets are equal
  have hset_eq : spectralMeasurePolarized U hU x y (cayleyToCircle '' Set.univ) hmeas_img =
      spectralMeasurePolarized U hU x y {z : Circle | z ≠ 1} hmeas_compl := by
    -- The sets are equal, so the measures are equal
    -- Use simp with the equality himg_meas
    simp only [himg_meas]
  rw [hset_eq, htotal]

/-! ### PVM Properties via RMK -/

/-- **PVM (Projection-Valued Measure) properties** for the spectral measure constructed via RMK.

    This theorem proves that `spectralMeasureFromRMK` satisfies the algebraic properties
    of a projection-valued measure:
    - P(∅) = 0
    - P(ℝ) = 1
    - P(E)² = P(E) (idempotent / orthogonal projection)
    - P(E)* = P(E) (self-adjoint)
    - P(E ∩ F) = P(E) ∘ P(F) (multiplicative)

    **Important**: This does NOT prove the T-P connection (the spectral representation
    T = ∫ λ dP(λ)). The connection between T and P comes from the construction:
    P is built from the Cayley transform U = (T-i)(T+i)⁻¹, and the relationship
    `f(T) = ∫ f(λ) dP(λ)` requires additional work to establish (see `spectral_theorem`
    in `Unbounded/Spectral.lean` for the full statement). -/
theorem spectralMeasure_isPVM_via_RMK (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) :
    ∃ (C : CayleyTransform T hT hsa),
      let P := fun E hE => spectralMeasureFromRMK T hT hsa C E hE
      -- P is a PVM (projection-valued measure)
      P ∅ MeasurableSet.empty = 0 ∧
      P Set.univ MeasurableSet.univ = 1 ∧
      (∀ E hE, P E hE ∘L P E hE = P E hE) ∧
      (∀ E hE, (P E hE).adjoint = P E hE) ∧
      (∀ E F hE hF, P (E ∩ F) (hE.inter hF) = P E hE ∘L P F hF) := by
  obtain ⟨C, _⟩ := cayley_exists T hT hsa
  use C
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact spectralMeasureFromRMK_empty T hT hsa C
  · exact spectralMeasureFromRMK_univ T hT hsa C
  · intro E hE; exact spectralMeasureFromRMK_idempotent T hT hsa C E hE
  · intro E hE; exact spectralMeasureFromRMK_selfAdjoint T hT hsa C E hE
  · intro E F hE hF; exact spectralMeasureFromRMK_multiplicative T hT hsa C E F hE hF

end
