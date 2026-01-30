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
  -- The proof requires the dominated convergence argument outlined above.

  sorry

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
    -- This follows from U P({1}) = P({1})
    -- The proof uses the spectral integration formula.
    --
    -- For the RMK spectral projection, U P(E) = ∫_E z P(dz)
    -- For E = {1}, this gives U P({1}) = 1 · P({1}) = P({1})
    --
    -- This can be proven via CFC multiplicativity and limits:
    -- Let g_n be thickened indicators converging to χ_{1}.
    -- Then cfc(g_n, U) → P({1}) weakly.
    -- Also U · cfc(g_n, U) = cfc(id · g_n, U) by CFC multiplicativity.
    -- Since id · g_n → χ_{1} (as shown in the docstring), cfc(id · g_n, U) → P({1}).
    -- Taking limits: U P({1}) = P({1}).
    sorry

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
  -- So μ_{x,y}(Circle \ {1}) = μ_{x,y}(Circle) - μ_{x,y}({1}) = ⟨x, y⟩ - 0 = ⟨x, y⟩
  --
  -- To prove this, we need measure additivity or the fact that P({1}) = 0.
  -- From spectralProjection_singleton_one_eq_zero: P({1}) = 0
  -- So μ_{x,y}({1}) = ⟨x, P({1}) y⟩ = ⟨x, 0⟩ = 0
  --
  -- Then μ_{x,y}(Circle \ {1}) = μ_{x,y}(Circle) = ⟨x, y⟩
  -- (since {1} has zero measure and Circle \ {1} ∪ {1} = Circle)
  --
  -- TECHNICAL: Need to establish this equality via the measure structure.
  -- For now, use the fact that range cayleyToCircle is dense in Circle (topologically)
  -- but actually equals Circle \ {1} which has full measure.
  sorry

/-! ### Spectral Theorem via RMK -/

/-- The spectral theorem for self-adjoint operators via RMK.
    This version bypasses CFC and uses the Riesz-Markov-Kakutani theorem directly. -/
theorem spectral_theorem_via_RMK (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
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
