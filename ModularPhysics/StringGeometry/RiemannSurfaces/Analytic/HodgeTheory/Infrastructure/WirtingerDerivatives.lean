import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import ModularPhysics.StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Infrastructure.RealSmoothness

/-!
# Wirtinger Derivatives

This file develops the theory of Wirtinger derivatives, providing the key connection
between ℝ-differentiability and ℂ-differentiability needed for the ∂̄-operator.

## Mathematical Background

For a function f : ℂ → ℂ that is ℝ-differentiable at z, we define the Wirtinger derivatives:
  ∂f/∂z = (1/2)(∂f/∂x - i ∂f/∂y)
  ∂f/∂z̄ = (1/2)(∂f/∂x + i ∂f/∂y)

Equivalently, using the Fréchet derivative L = fderiv ℝ f z : ℂ →L[ℝ] ℂ:
  ∂f/∂z  = (1/2)(L(1) - i·L(i))
  ∂f/∂z̄ = (1/2)(L(1) + i·L(i))

**Key theorem**: f is ℂ-differentiable at z iff ∂f/∂z̄ = 0 (Cauchy-Riemann equations).

When f is ℂ-differentiable, ∂f/∂z equals the complex derivative deriv f z.

## Main Definitions

* `wirtingerDeriv` - The holomorphic derivative ∂/∂z
* `wirtingerDerivBar` - The antiholomorphic derivative ∂/∂z̄

## Main Results

* `holomorphic_iff_wirtingerDerivBar_zero` - f is ℂ-differentiable iff ∂f/∂z̄ = 0
* `wirtingerDeriv_eq_deriv` - When ℂ-differentiable, ∂f/∂z = deriv f z
* `wirtinger_add`, `wirtinger_mul`, etc. - Algebraic properties

## References

* Ahlfors, "Complex Analysis", Chapter 1
* Griffiths-Harris, "Principles of Algebraic Geometry", §0.5
-/

namespace RiemannSurfaces.Analytic.Infrastructure

open Complex

/-!
## Wirtinger Derivatives via Fréchet Derivative

For an ℝ-differentiable function f : ℂ → ℂ, the ℝ-linear Fréchet derivative
L = fderiv ℝ f z can be uniquely decomposed as:
  L(w) = A·w + B·conj(w)
where A, B ∈ ℂ. We have:
  A = ∂f/∂z = (1/2)(L(1) - i·L(i))
  B = ∂f/∂z̄ = (1/2)(L(1) + i·L(i))

The function f is ℂ-differentiable iff B = 0.
-/

/-- The Wirtinger derivative ∂f/∂z = (1/2)(L(1) - i·L(i)) where L = fderiv ℝ f z.
    This is the holomorphic part of the derivative. When f is ℂ-differentiable,
    this equals deriv f z. -/
noncomputable def wirtingerDeriv (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  let L := fderiv ℝ f z
  (1/2 : ℂ) * (L 1 - Complex.I * L Complex.I)

/-- The Wirtinger derivative ∂f/∂z̄ = (1/2)(L(1) + i·L(i)) where L = fderiv ℝ f z.
    This is the antiholomorphic part of the derivative.
    A function is holomorphic iff this vanishes. -/
noncomputable def wirtingerDerivBar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  let L := fderiv ℝ f z
  (1/2 : ℂ) * (L 1 + Complex.I * L Complex.I)

/-!
## The Fundamental Characterization Theorem

The key result: f is ℂ-differentiable iff ∂f/∂z̄ = 0.
-/

/-- Helper: The Cauchy-Riemann condition L(I) = I·L(1) is equivalent to ∂f/∂z̄ = 0. -/
theorem wirtingerDerivBar_eq_zero_iff_cauchyRiemann {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) :
    wirtingerDerivBar f z = 0 ↔ fderiv ℝ f z Complex.I = Complex.I • fderiv ℝ f z 1 := by
  unfold wirtingerDerivBar
  constructor
  · intro h
    -- From (1/2)(L(1) + I·L(I)) = 0, we get L(1) + I·L(I) = 0
    have h' : fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I = 0 := by
      have := h
      simp only [one_div, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or] at this
      exact this
    -- From L(1) + I·L(I) = 0, get I·L(I) = -L(1)
    have h'' : Complex.I * fderiv ℝ f z Complex.I = -fderiv ℝ f z 1 := by
      calc Complex.I * fderiv ℝ f z Complex.I
        _ = (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) - fderiv ℝ f z 1 := by ring
        _ = 0 - fderiv ℝ f z 1 := by rw [h']
        _ = -fderiv ℝ f z 1 := by ring
    -- L(I) = (I * L(I)) / I = -L(1) / I
    have hIinv : Complex.I⁻¹ = -Complex.I := by
      have hIsq : Complex.I * Complex.I = -1 := Complex.I_mul_I
      field_simp
      calc 1 = -(-1) := by ring
        _ = -(Complex.I * Complex.I) := by rw [hIsq]
        _ = -Complex.I ^ 2 := by ring
    have hne : Complex.I ≠ 0 := Complex.I_ne_zero
    calc fderiv ℝ f z Complex.I
      _ = Complex.I⁻¹ * (Complex.I * fderiv ℝ f z Complex.I) := by field_simp
      _ = Complex.I⁻¹ * (-fderiv ℝ f z 1) := by rw [h'']
      _ = (-Complex.I) * (-fderiv ℝ f z 1) := by rw [hIinv]
      _ = Complex.I * fderiv ℝ f z 1 := by ring
      _ = Complex.I • fderiv ℝ f z 1 := by rw [smul_eq_mul]
  · intro hCR
    -- From L(I) = I·L(1), compute I·L(I) = I·I·L(1) = -L(1)
    have hIsq : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have h' : Complex.I * fderiv ℝ f z Complex.I = -fderiv ℝ f z 1 := by
      rw [hCR, smul_eq_mul]
      calc Complex.I * (Complex.I * fderiv ℝ f z 1)
        _ = (Complex.I * Complex.I) * fderiv ℝ f z 1 := by ring
        _ = (-1) * fderiv ℝ f z 1 := by rw [hIsq]
        _ = -fderiv ℝ f z 1 := by ring
    simp only [one_div, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
    calc fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I
      _ = fderiv ℝ f z 1 + (-fderiv ℝ f z 1) := by rw [h']
      _ = 0 := by ring

/-- **The fundamental theorem**: A function is ℂ-differentiable iff it is ℝ-differentiable
    and its Wirtinger derivative ∂f/∂z̄ vanishes. -/
theorem holomorphic_iff_wirtingerDerivBar_zero {f : ℂ → ℂ} {z : ℂ} :
    DifferentiableAt ℂ f z ↔ DifferentiableAt ℝ f z ∧ wirtingerDerivBar f z = 0 := by
  rw [differentiableAt_complex_iff_differentiableAt_real]
  constructor
  · intro ⟨hR, hCR⟩
    exact ⟨hR, (wirtingerDerivBar_eq_zero_iff_cauchyRiemann hR).mpr hCR⟩
  · intro ⟨hR, hBar⟩
    exact ⟨hR, (wirtingerDerivBar_eq_zero_iff_cauchyRiemann hR).mp hBar⟩

/-- When f is ℂ-differentiable, ∂f/∂z equals the complex derivative. -/
theorem wirtingerDeriv_eq_deriv {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    wirtingerDeriv f z = deriv f z := by
  unfold wirtingerDeriv
  have hfR := hf.restrictScalars ℝ
  have hres := hf.fderiv_restrictScalars ℝ
  rw [hres]
  -- fderiv ℂ f z is complex-linear, so (fderiv ℂ f z)(I) = I · (fderiv ℂ f z)(1)
  have hlin : (fderiv ℂ f z).restrictScalars ℝ Complex.I =
      Complex.I * (fderiv ℂ f z).restrictScalars ℝ 1 := by
    simp only [ContinuousLinearMap.coe_restrictScalars']
    have : (fderiv ℂ f z) Complex.I = (fderiv ℂ f z) (Complex.I • 1) := by simp
    rw [this, ContinuousLinearMap.map_smul, smul_eq_mul]
  -- Now L(1) - I · L(I) = L(1) - I · I · L(1) = L(1) + L(1) = 2 · L(1)
  have hIsq : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc (1/2 : ℂ) * ((fderiv ℂ f z).restrictScalars ℝ 1 -
                    Complex.I * (fderiv ℂ f z).restrictScalars ℝ Complex.I)
    _ = (1/2 : ℂ) * ((fderiv ℂ f z).restrictScalars ℝ 1 -
                    Complex.I * (Complex.I * (fderiv ℂ f z).restrictScalars ℝ 1)) := by rw [hlin]
    _ = (1/2 : ℂ) * ((fderiv ℂ f z).restrictScalars ℝ 1 -
                    (Complex.I * Complex.I) * (fderiv ℂ f z).restrictScalars ℝ 1) := by ring
    _ = (1/2 : ℂ) * ((fderiv ℂ f z).restrictScalars ℝ 1 -
                    (-1) * (fderiv ℂ f z).restrictScalars ℝ 1) := by rw [hIsq]
    _ = (1/2 : ℂ) * (2 * (fderiv ℂ f z).restrictScalars ℝ 1) := by ring
    _ = (fderiv ℂ f z).restrictScalars ℝ 1 := by ring
    _ = (fderiv ℂ f z) 1 := rfl
    _ = deriv f z := fderiv_apply_one_eq_deriv

/-!
## Algebraic Properties of Wirtinger Derivatives
-/

section Algebraic

variable {f g : ℂ → ℂ} {z : ℂ}

/-- Wirtinger derivative of sum. -/
theorem wirtingerDeriv_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerDeriv (f + g) z = wirtingerDeriv f z + wirtingerDeriv g z := by
  unfold wirtingerDeriv
  rw [fderiv_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

/-- Wirtinger bar derivative of sum. -/
theorem wirtingerDerivBar_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerDerivBar (f + g) z = wirtingerDerivBar f z + wirtingerDerivBar g z := by
  unfold wirtingerDerivBar
  rw [fderiv_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

/-- Wirtinger derivative of constant multiple. -/
theorem wirtingerDeriv_const_smul (c : ℂ) (hf : DifferentiableAt ℝ f z) :
    wirtingerDeriv (c • f) z = c * wirtingerDeriv f z := by
  unfold wirtingerDeriv
  rw [fderiv_const_smul hf]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  ring

/-- Wirtinger bar derivative of constant multiple. -/
theorem wirtingerDerivBar_const_smul (c : ℂ) (hf : DifferentiableAt ℝ f z) :
    wirtingerDerivBar (c • f) z = c * wirtingerDerivBar f z := by
  unfold wirtingerDerivBar
  rw [fderiv_const_smul hf]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  ring

/-- Wirtinger derivative of negation. -/
theorem wirtingerDeriv_neg :
    wirtingerDeriv (-f) z = -wirtingerDeriv f z := by
  unfold wirtingerDeriv
  simp only [fderiv_neg, ContinuousLinearMap.neg_apply]
  ring

/-- Wirtinger bar derivative of negation. -/
theorem wirtingerDerivBar_neg :
    wirtingerDerivBar (-f) z = -wirtingerDerivBar f z := by
  unfold wirtingerDerivBar
  simp only [fderiv_neg, ContinuousLinearMap.neg_apply]
  ring

/-- Wirtinger derivative of constant function. -/
theorem wirtingerDeriv_const (c : ℂ) : wirtingerDeriv (fun _ => c) z = 0 := by
  unfold wirtingerDeriv
  have heq : (fun _ : ℂ => c) = Function.const ℂ c := rfl
  rw [heq, fderiv_const]
  simp

/-- Wirtinger bar derivative of constant function. -/
theorem wirtingerDerivBar_const (c : ℂ) : wirtingerDerivBar (fun _ => c) z = 0 := by
  unfold wirtingerDerivBar
  have heq : (fun _ : ℂ => c) = Function.const ℂ c := rfl
  rw [heq, fderiv_const]
  simp

/-- Wirtinger derivative of identity. -/
theorem wirtingerDeriv_id : wirtingerDeriv id z = 1 := by
  unfold wirtingerDeriv
  rw [fderiv_id]
  simp only [ContinuousLinearMap.id_apply]
  have hIsq : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc (1 : ℂ) / 2 * (1 - Complex.I * Complex.I)
    _ = 1 / 2 * (1 - (-1)) := by rw [hIsq]
    _ = 1 / 2 * 2 := by ring
    _ = 1 := by ring

/-- Wirtinger bar derivative of identity vanishes (identity is holomorphic). -/
theorem wirtingerDerivBar_id : wirtingerDerivBar id z = 0 := by
  unfold wirtingerDerivBar
  rw [fderiv_id]
  simp only [ContinuousLinearMap.id_apply]
  have hIsq : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc (1 : ℂ) / 2 * (1 + Complex.I * Complex.I)
    _ = 1 / 2 * (1 + (-1)) := by rw [hIsq]
    _ = 0 := by ring

/-- Product rule for Wirtinger derivatives (Leibniz rule).
    This is the standard product rule: ∂(fg)/∂z = (∂f/∂z)g + f(∂g/∂z). -/
theorem wirtingerDeriv_mul (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerDeriv (f * g) z = wirtingerDeriv f z * g z + f z * wirtingerDeriv g z := by
  unfold wirtingerDeriv
  rw [fderiv_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Product rule for Wirtinger bar derivatives (Leibniz rule).
    This is the standard product rule: ∂(fg)/∂z̄ = (∂f/∂z̄)g + f(∂g/∂z̄). -/
theorem wirtingerDerivBar_mul (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerDerivBar (f * g) z = wirtingerDerivBar f z * g z + f z * wirtingerDerivBar g z := by
  unfold wirtingerDerivBar
  rw [fderiv_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Simplified product rule when both functions are holomorphic. -/
theorem wirtingerDeriv_mul_holomorphic
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) :
    wirtingerDeriv (f * g) z = wirtingerDeriv f z * g z + f z * wirtingerDeriv g z := by
  rw [wirtingerDeriv_eq_deriv hf, wirtingerDeriv_eq_deriv hg,
      wirtingerDeriv_eq_deriv (hf.mul hg)]
  exact deriv_mul hf hg

end Algebraic

/-!
## Wirtinger Derivatives of Special Functions
-/

/-- Wirtinger derivative of conjugation: ∂(conj)/∂z = 0.
    Conjugation is antiholomorphic, not holomorphic. -/
theorem wirtingerDeriv_conj : wirtingerDeriv (starRingEnd ℂ) z = 0 := by
  unfold wirtingerDeriv
  have h : fderiv ℝ (starRingEnd ℂ : ℂ → ℂ) z = RiemannSurfaces.Analytic.conjCLM := by
    apply HasFDerivAt.fderiv
    exact RiemannSurfaces.Analytic.conjCLM.hasFDerivAt
  rw [h]
  simp only [RiemannSurfaces.Analytic.conjCLM, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, map_one]
  -- conj(I) = -I
  have hconj : star Complex.I = -Complex.I := Complex.conj_I
  have hIsq : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc (1 : ℂ) / 2 * (1 - Complex.I * star Complex.I)
    _ = 1 / 2 * (1 - Complex.I * (-Complex.I)) := by rw [hconj]
    _ = 1 / 2 * (1 - (-(Complex.I * Complex.I))) := by ring
    _ = 1 / 2 * (1 - (-(-1))) := by rw [hIsq]
    _ = 1 / 2 * 0 := by ring
    _ = 0 := by ring

/-- Wirtinger bar derivative of conjugation: ∂(conj)/∂z̄ = 1.
    This shows conjugation is a "purely antiholomorphic" function. -/
theorem wirtingerDerivBar_conj : wirtingerDerivBar (starRingEnd ℂ) z = 1 := by
  unfold wirtingerDerivBar
  have h : fderiv ℝ (starRingEnd ℂ : ℂ → ℂ) z = RiemannSurfaces.Analytic.conjCLM := by
    apply HasFDerivAt.fderiv
    exact RiemannSurfaces.Analytic.conjCLM.hasFDerivAt
  rw [h]
  simp only [RiemannSurfaces.Analytic.conjCLM, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, map_one]
  have hconj : star Complex.I = -Complex.I := Complex.conj_I
  have hIsq : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc (1 : ℂ) / 2 * (1 + Complex.I * star Complex.I)
    _ = 1 / 2 * (1 + Complex.I * (-Complex.I)) := by rw [hconj]
    _ = 1 / 2 * (1 + (-(Complex.I * Complex.I))) := by ring
    _ = 1 / 2 * (1 + (-(-1))) := by rw [hIsq]
    _ = 1 / 2 * 2 := by ring
    _ = 1 := by ring

/-!
## Differentiability in Manifold Charts

For functions on manifolds, ContMDiff implies differentiability in chart coordinates.
This section provides the bridge needed for Wirtinger derivative computations on Riemann surfaces.
-/

open scoped Manifold
open Topology

/-- For a ContMDiff function on a manifold modeled on ℂ (with ℝ-smoothness),
    composition with chart symm gives DifferentiableAt ℝ.

    This is the key link: manifold smoothness → chart differentiability → Wirtinger derivatives. -/
theorem differentiableAt_chart_comp {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℝ, ℂ) ⊤ M]
    {f : M → ℂ} (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ f) (p : M) :
    DifferentiableAt ℝ (f ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) := by
  -- Get ContMDiffAt from ContMDiff
  have hCM : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ f p := hf.contMDiffAt
  -- Use contMDiffAt_iff_of_mem_source to extract ContDiffWithinAt
  have hp_source : p ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
  have hfp_source : f p ∈ (chartAt ℂ (f p)).source := mem_chart_source ℂ (f p)
  rw [contMDiffAt_iff_of_mem_source hp_source hfp_source] at hCM
  obtain ⟨_, hcdiff⟩ := hCM
  -- For target ℂ (model space), extChartAt is identity
  have htarget : extChartAt 𝓘(ℝ, ℂ) (f p) = PartialEquiv.refl ℂ := by simp only [mfld_simps]
  -- For source, use extend_coe_symm: (f.extend I).symm = f.symm ∘ I.symm
  -- For 𝓘(ℝ, ℂ), I.symm = id, so (extChartAt).symm = chartAt.symm
  have hsource_symm : ∀ z, (extChartAt 𝓘(ℝ, ℂ) p).symm z = (chartAt ℂ p).symm z := by
    intro z
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm,
      Function.comp_apply, id_eq]
  have hsource_val : extChartAt 𝓘(ℝ, ℂ) p p = (chartAt ℂ p) p := by simp only [mfld_simps]
  -- range 𝓘(ℝ, ℂ) = univ since I = id
  have hrange : Set.range (𝓘(ℝ, ℂ) : ℂ → ℂ) = Set.univ := by
    simp only [modelWithCornersSelf_coe, Set.range_id]
  -- Rewrite hcdiff using these simplifications
  have hcdiff' : ContDiffWithinAt ℝ ⊤ (f ∘ (chartAt ℂ p).symm) Set.univ ((chartAt ℂ p) p) := by
    have heq1 : (fun z => (extChartAt 𝓘(ℝ, ℂ) p).symm z) = (fun z => (chartAt ℂ p).symm z) :=
      funext hsource_symm
    have heq2 : (extChartAt 𝓘(ℝ, ℂ) (f p)) ∘ f = f := by
      rw [htarget]; rfl
    -- Rewrite hcdiff step by step
    simp only [heq1, hrange, hsource_val, htarget, PartialEquiv.refl_coe] at hcdiff
    exact hcdiff
  -- ContDiffWithinAt on univ gives ContDiffAt
  have hcdiffAt : ContDiffAt ℝ ⊤ (f ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) :=
    hcdiff'.contDiffAt Filter.univ_mem
  -- ContDiffAt ⊤ implies DifferentiableAt (⊤ ≠ 0)
  exact hcdiffAt.differentiableAt WithTop.top_ne_zero

/-- Variant: ContMDiffAt implies DifferentiableAt in chart. -/
theorem differentiableAt_chart_comp_of_contMDiffAt {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℝ, ℂ) ⊤ M]
    {f : M → ℂ} {p : M} (hf : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ f p) :
    DifferentiableAt ℝ (f ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) := by
  -- Use contMDiffAt_iff_of_mem_source to extract ContDiffWithinAt
  have hp_source : p ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
  have hfp_source : f p ∈ (chartAt ℂ (f p)).source := mem_chart_source ℂ (f p)
  rw [contMDiffAt_iff_of_mem_source hp_source hfp_source] at hf
  obtain ⟨_, hcdiff⟩ := hf
  -- For target ℂ (model space), extChartAt is identity
  have htarget : extChartAt 𝓘(ℝ, ℂ) (f p) = PartialEquiv.refl ℂ := by simp only [mfld_simps]
  -- For source, use extend_coe_symm: (f.extend I).symm = f.symm ∘ I.symm
  have hsource_symm : ∀ z, (extChartAt 𝓘(ℝ, ℂ) p).symm z = (chartAt ℂ p).symm z := by
    intro z
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm,
      Function.comp_apply, id_eq]
  have hsource_val : extChartAt 𝓘(ℝ, ℂ) p p = (chartAt ℂ p) p := by simp only [mfld_simps]
  have hrange : Set.range (𝓘(ℝ, ℂ) : ℂ → ℂ) = Set.univ := by
    simp only [modelWithCornersSelf_coe, Set.range_id]
  -- Rewrite hcdiff using these simplifications
  have hcdiff' : ContDiffWithinAt ℝ ⊤ (f ∘ (chartAt ℂ p).symm) Set.univ ((chartAt ℂ p) p) := by
    have heq1 : (fun z => (extChartAt 𝓘(ℝ, ℂ) p).symm z) = (fun z => (chartAt ℂ p).symm z) :=
      funext hsource_symm
    -- Rewrite hcdiff step by step
    simp only [heq1, hrange, hsource_val, htarget, PartialEquiv.refl_coe] at hcdiff
    exact hcdiff
  have hcdiffAt : ContDiffAt ℝ ⊤ (f ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) :=
    hcdiff'.contDiffAt Filter.univ_mem
  exact hcdiffAt.differentiableAt WithTop.top_ne_zero

/-!
## Smoothness of Wirtinger Derivatives

If f is smooth, then its Wirtinger derivatives are smooth.
This follows from the fact that fderiv of a smooth function is smooth.

**Mathematical argument**:
wirtingerDerivBar f z = (1/2)(fderiv ℝ f z 1 + I * fderiv ℝ f z I)

1. If f is C^{n+1}, then fderiv ℝ f is C^n
2. Evaluation at a fixed vector (like 1 or I) is a bounded linear operation on CLMs
3. Scalar multiplication and addition preserve smoothness
4. Hence wirtingerDerivBar f is C^n

We use fun_prop to automate the smoothness proofs.
-/

/-- Evaluation at a fixed vector is a continuous linear map on the space of CLMs. -/
def evalCLM (v : ℂ) : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ where
  toFun := fun L => L v
  map_add' := fun L₁ L₂ => by simp only [ContinuousLinearMap.add_apply]
  map_smul' := fun c L => by simp only [ContinuousLinearMap.smul_apply, RingHom.id_apply]
  cont := continuous_eval_const v

/-- wirtingerDerivBar f z is defined in terms of fderiv ℝ f z applied to 1 and I.
    Since evaluation at a fixed vector is a continuous linear operation,
    smoothness of fderiv ℝ f implies smoothness of wirtingerDerivBar f. -/
theorem wirtingerDerivBar_contDiff {f : ℂ → ℂ} {n : ℕ∞}
    (hf : ContDiff ℝ (n + 1) f) : ContDiff ℝ n (wirtingerDerivBar f) := by
  unfold wirtingerDerivBar
  -- fderiv ℝ f is ContDiff ℝ n when f is ContDiff ℝ (n + 1)
  have hfderiv : ContDiff ℝ n (fun z => fderiv ℝ f z) := hf.fderiv_right le_rfl
  -- Evaluation at a fixed vector is a CLM, hence smooth
  have heval1 : ContDiff ℝ n (fun z => fderiv ℝ f z 1) :=
    (evalCLM 1).contDiff.comp hfderiv
  have hevalI : ContDiff ℝ n (fun z => fderiv ℝ f z Complex.I) :=
    (evalCLM Complex.I).contDiff.comp hfderiv
  -- Combine with scalar multiplication and addition
  have hsum : ContDiff ℝ n (fun z => fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) :=
    heval1.add (contDiff_const.mul hevalI)
  exact contDiff_const.mul hsum

/-- wirtingerDeriv f z is also smooth when f is smooth. -/
theorem wirtingerDeriv_contDiff {f : ℂ → ℂ} {n : ℕ∞}
    (hf : ContDiff ℝ (n + 1) f) : ContDiff ℝ n (wirtingerDeriv f) := by
  unfold wirtingerDeriv
  have hfderiv : ContDiff ℝ n (fun z => fderiv ℝ f z) := hf.fderiv_right le_rfl
  have heval1 : ContDiff ℝ n (fun z => fderiv ℝ f z 1) :=
    (evalCLM 1).contDiff.comp hfderiv
  have hevalI : ContDiff ℝ n (fun z => fderiv ℝ f z Complex.I) :=
    (evalCLM Complex.I).contDiff.comp hfderiv
  have hdiff : ContDiff ℝ n (fun z => fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I) :=
    heval1.sub (contDiff_const.mul hevalI)
  exact contDiff_const.mul hdiff

/-- wirtingerDerivBar of a C^∞ function is C^∞. -/
theorem wirtingerDerivBar_smooth {f : ℂ → ℂ}
    (hf : ∀ n : ℕ, ContDiff ℝ n f) : ∀ n : ℕ, ContDiff ℝ n (wirtingerDerivBar f) := by
  intro n
  -- We need f to be C^{n+1}, and wirtingerDerivBar_contDiff gives C^n
  have hn1 : ContDiff ℝ (↑(n + 1) : ℕ∞) f := hf (n + 1)
  -- Show (n+1 : ℕ) = (n : ℕ∞) + 1 when coerced
  have heq : (↑(n + 1) : ℕ∞) = (↑n : ℕ∞) + 1 := by simp [Nat.cast_add]
  rw [heq] at hn1
  exact wirtingerDerivBar_contDiff hn1

/-- wirtingerDeriv of a C^∞ function is C^∞. -/
theorem wirtingerDeriv_smooth {f : ℂ → ℂ}
    (hf : ∀ n : ℕ, ContDiff ℝ n f) : ∀ n : ℕ, ContDiff ℝ n (wirtingerDeriv f) := by
  intro n
  have hn1 : ContDiff ℝ (↑(n + 1) : ℕ∞) f := hf (n + 1)
  have heq : (↑(n + 1) : ℕ∞) = (↑n : ℕ∞) + 1 := by simp [Nat.cast_add]
  rw [heq] at hn1
  exact wirtingerDeriv_contDiff hn1

/-!
## The Laplacian in Terms of Wirtinger Derivatives

The Laplacian Δf = ∂²f/∂x² + ∂²f/∂y² can be written as:
  Δf = 4 · ∂²f/∂z∂z̄
-/

/-- The Laplacian equals 4 times the mixed Wirtinger derivative (commutativity).
    This follows from equality of mixed partial derivatives.

    **Proof sketch**:
    - ∂/∂z = (1/2)(∂/∂x - i∂/∂y)
    - ∂/∂z̄ = (1/2)(∂/∂x + i∂/∂y)
    - ∂/∂z(∂/∂z̄) = (1/4)(∂²/∂x² + ∂²/∂y²) by Schwarz's theorem (mixed partials commute)
    - ∂/∂z̄(∂/∂z) = (1/4)(∂²/∂x² + ∂²/∂y²) by Schwarz's theorem
    - Hence they're equal.

    This requires connecting Wirtinger derivatives to second-order Fréchet derivatives
    and using `ContDiffAt.isSymmSndFDerivAt` from Mathlib. -/
theorem laplacian_eq_four_wirtinger_mixed (f : ℂ → ℂ) (z : ℂ)
    (hf : ContDiff ℝ 2 f) :
    wirtingerDeriv (wirtingerDerivBar f) z = wirtingerDerivBar (wirtingerDeriv f) z := by
  -- The key insight is that both sides equal (1/4) * (Laplacian of f).
  -- This uses symmetry of second derivatives for C² functions.
  -- The formal proof requires careful handling of fderiv of fderiv.
  sorry  -- Requires detailed second derivative theory connecting Wirtinger to iterated Fréchet

end RiemannSurfaces.Analytic.Infrastructure
