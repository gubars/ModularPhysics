import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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

/-- Chain rule for wirtingerDerivBar with conjugation: ∂(conj ∘ g)/∂z̄ = conj(∂g/∂z).
    When g is ℂ-differentiable, composing with conjugation swaps the roles of
    wirtingerDeriv and wirtingerDerivBar. -/
theorem wirtingerDerivBar_comp_conj {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℂ g z) :
    wirtingerDerivBar (starRingEnd ℂ ∘ g) z = starRingEnd ℂ (wirtingerDeriv g z) := by
  -- Rewrite RHS using wirtingerDeriv = deriv for holomorphic functions
  rw [wirtingerDeriv_eq_deriv hg]
  -- Expand wirtingerDerivBar to work with fderiv directly
  show (1/2 : ℂ) * (fderiv ℝ (starRingEnd ℂ ∘ g) z 1 +
    Complex.I * fderiv ℝ (starRingEnd ℂ ∘ g) z Complex.I) = starRingEnd ℂ (deriv g z)
  -- Step 1: Chain rule for fderiv (use HasFDerivAt to handle coercion matching)
  have hgR : DifferentiableAt ℝ g z := hg.restrictScalars ℝ
  have hfderiv_chain : fderiv ℝ (starRingEnd ℂ ∘ g) z =
      (RiemannSurfaces.Analytic.conjCLM).comp (fderiv ℝ g z) := by
    apply HasFDerivAt.fderiv
    exact RiemannSurfaces.Analytic.conjCLM.hasFDerivAt.comp z hgR.hasFDerivAt
  -- Step 2: Express fderiv ℝ g z using ℂ-linear structure
  have hres : fderiv ℝ g z = (fderiv ℂ g z).restrictScalars ℝ := hg.fderiv_restrictScalars ℝ
  -- Step 3: Evaluate the composed fderiv at 1 and I
  have heval_1 : fderiv ℝ (starRingEnd ℂ ∘ g) z 1 = starRingEnd ℂ (deriv g z) := by
    rw [hfderiv_chain]
    simp only [ContinuousLinearMap.comp_apply, hres, ContinuousLinearMap.coe_restrictScalars']
    change starRingEnd ℂ ((fderiv ℂ g z) 1) = _
    rw [fderiv_apply_one_eq_deriv]
  have heval_I : fderiv ℝ (starRingEnd ℂ ∘ g) z Complex.I =
      -Complex.I * starRingEnd ℂ (deriv g z) := by
    rw [hfderiv_chain]
    simp only [ContinuousLinearMap.comp_apply, hres, ContinuousLinearMap.coe_restrictScalars']
    change starRingEnd ℂ ((fderiv ℂ g z) Complex.I) = _
    -- ℂ-linearity: (fderiv ℂ g z) I = I • (fderiv ℂ g z) 1 = I * deriv g z
    have hlin : (fderiv ℂ g z) Complex.I = Complex.I * deriv g z := by
      calc (fderiv ℂ g z) Complex.I
        _ = (fderiv ℂ g z) (Complex.I • 1) := by simp
        _ = Complex.I • (fderiv ℂ g z) 1 := ContinuousLinearMap.map_smul _ _ _
        _ = Complex.I * deriv g z := by rw [smul_eq_mul, fderiv_apply_one_eq_deriv]
    rw [hlin, map_mul (starRingEnd ℂ), Complex.conj_I]
  -- Step 4: Substitute and simplify
  rw [heval_1, heval_I]
  -- Goal: (1/2) * (conj(g') + I * (-I * conj(g'))) = conj(g')
  have : Complex.I * (-Complex.I * starRingEnd ℂ (deriv g z)) = starRingEnd ℂ (deriv g z) := by
    rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  rw [this]; ring

/-- Chain rule for wirtingerDeriv with conjugation: ∂(conj ∘ g)/∂z = 0 when g is holomorphic.
    This shows conj ∘ holomorphic is purely antiholomorphic. -/
theorem wirtingerDeriv_comp_conj {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℂ g z) :
    wirtingerDeriv (starRingEnd ℂ ∘ g) z = 0 := by
  show (1/2 : ℂ) * (fderiv ℝ (starRingEnd ℂ ∘ g) z 1 -
    Complex.I * fderiv ℝ (starRingEnd ℂ ∘ g) z Complex.I) = 0
  -- Reuse chain rule computation from wirtingerDerivBar_comp_conj
  have hgR : DifferentiableAt ℝ g z := hg.restrictScalars ℝ
  have hfderiv_chain : fderiv ℝ (starRingEnd ℂ ∘ g) z =
      (RiemannSurfaces.Analytic.conjCLM).comp (fderiv ℝ g z) := by
    apply HasFDerivAt.fderiv
    exact RiemannSurfaces.Analytic.conjCLM.hasFDerivAt.comp z hgR.hasFDerivAt
  have hres : fderiv ℝ g z = (fderiv ℂ g z).restrictScalars ℝ := hg.fderiv_restrictScalars ℝ
  have heval_1 : fderiv ℝ (starRingEnd ℂ ∘ g) z 1 = starRingEnd ℂ (deriv g z) := by
    rw [hfderiv_chain]
    simp only [ContinuousLinearMap.comp_apply, hres, ContinuousLinearMap.coe_restrictScalars']
    change starRingEnd ℂ ((fderiv ℂ g z) 1) = _
    rw [fderiv_apply_one_eq_deriv]
  have heval_I : fderiv ℝ (starRingEnd ℂ ∘ g) z Complex.I =
      -Complex.I * starRingEnd ℂ (deriv g z) := by
    rw [hfderiv_chain]
    simp only [ContinuousLinearMap.comp_apply, hres, ContinuousLinearMap.coe_restrictScalars']
    change starRingEnd ℂ ((fderiv ℂ g z) Complex.I) = _
    have hlin : (fderiv ℂ g z) Complex.I = Complex.I * deriv g z := by
      calc (fderiv ℂ g z) Complex.I
        _ = (fderiv ℂ g z) (Complex.I • 1) := by simp
        _ = Complex.I • (fderiv ℂ g z) 1 := ContinuousLinearMap.map_smul _ _ _
        _ = Complex.I * deriv g z := by rw [smul_eq_mul, fderiv_apply_one_eq_deriv]
    rw [hlin, map_mul (starRingEnd ℂ), Complex.conj_I]
  rw [heval_1, heval_I]
  -- Goal: (1/2) * (conj(g') - I * (-I * conj(g'))) = 0
  have : Complex.I * (-Complex.I * starRingEnd ℂ (deriv g z)) = starRingEnd ℂ (deriv g z) := by
    rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  rw [this]; ring

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
  -- Use the symmetry of second derivatives from Mathlib
  -- For C² functions over ℝ: fderiv ℝ (fderiv ℝ f) z v w = fderiv ℝ (fderiv ℝ f) z w v
  have hsymm : IsSymmSndFDerivAt ℝ f z := by
    apply ContDiffAt.isSymmSndFDerivAt hf.contDiffAt
    simp only [minSmoothness_of_isRCLikeNormedField, le_refl]

  -- Define: D²(v)(w) = fderiv ℝ (fderiv ℝ f) z v w (the second derivative)
  set D2 := fderiv ℝ (fderiv ℝ f) z with hD2

  -- By symmetry: D²(1)(I) = D²(I)(1)
  have hsymm_1_I : D2 1 Complex.I = D2 Complex.I 1 := hsymm 1 Complex.I

  -- Get differentiability
  have hdiff_fderiv : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.contDiffAt.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero

  -- Define helper functions for evaluation at 1 and I
  let eval1 : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ 1
  let evalI : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ Complex.I

  -- Differentiability of the component functions at z
  have hdiff1 : DifferentiableAt ℝ (fun w => fderiv ℝ f w 1) z := by
    have h : DifferentiableAt ℝ (eval1 ∘ fderiv ℝ f) z :=
      eval1.differentiableAt.comp z hdiff_fderiv
    exact h
  have hdiffI : DifferentiableAt ℝ (fun w => fderiv ℝ f w Complex.I) z := by
    have h : DifferentiableAt ℝ (evalI ∘ fderiv ℝ f) z :=
      evalI.differentiableAt.comp z hdiff_fderiv
    exact h

  -- The key lemma: fderiv ℝ (fun w => fderiv ℝ f w v) z u = D2 u v
  have hD2_apply : ∀ u v, fderiv ℝ (fun w => fderiv ℝ f w v) z u = D2 u v := by
    intro u v
    let evalV : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ v
    have hcomp : fderiv ℝ (evalV ∘ fderiv ℝ f) z = evalV.comp (fderiv ℝ (fderiv ℝ f) z) := by
      rw [fderiv_comp z evalV.differentiableAt hdiff_fderiv]
      simp [ContinuousLinearMap.fderiv]
    calc fderiv ℝ (fun w => fderiv ℝ f w v) z u
      _ = (fderiv ℝ (evalV ∘ fderiv ℝ f) z) u := rfl
      _ = (evalV.comp D2) u := by rw [hcomp]
      _ = evalV (D2 u) := rfl
      _ = D2 u v := rfl

  -- Define the inner functions without let bindings for wirtingerDerivBar/wirtingerDeriv
  -- wirtingerDerivBar f z' = (1/2)(fderiv ℝ f z' 1 + I * fderiv ℝ f z' I)
  -- wirtingerDeriv f z' = (1/2)(fderiv ℝ f z' 1 - I * fderiv ℝ f z' I)

  -- Since wirtingerDerivBar and wirtingerDeriv use `let L := fderiv ℝ f z'`,
  -- we need to show they're equal to our simplified forms
  have heq_bar : ∀ z', wirtingerDerivBar f z' =
      (1/2 : ℂ) * (fderiv ℝ f z' 1 + Complex.I * fderiv ℝ f z' Complex.I) := by
    intro z'; unfold wirtingerDerivBar; ring
  have heq_hol : ∀ z', wirtingerDeriv f z' =
      (1/2 : ℂ) * (fderiv ℝ f z' 1 - Complex.I * fderiv ℝ f z' Complex.I) := by
    intro z'; unfold wirtingerDeriv; ring

  -- Now we can compute fderiv of wirtingerDerivBar f at z
  -- We compute directly using the CLM linearity
  have hfderiv_bar_apply : ∀ u, fderiv ℝ (wirtingerDerivBar f) z u =
      (1/2 : ℂ) * (D2 u 1 + Complex.I * D2 u Complex.I) := by
    intro u
    -- wirtingerDerivBar f equals our simpler form
    have heq : wirtingerDerivBar f = fun z' =>
        (1/2 : ℂ) * (fderiv ℝ f z' 1 + Complex.I * fderiv ℝ f z' Complex.I) := by
      ext z'; exact heq_bar z'
    -- Define component functions using smul (•) to match fderiv_const_smul
    let g1 : ℂ → ℂ := fun w => fderiv ℝ f w 1
    let gI : ℂ → ℂ := fun w => fderiv ℝ f w Complex.I
    let g2 : ℂ → ℂ := Complex.I • gI  -- This is fun w => I • gI w = fun w => I * fderiv ℝ f w I
    -- g2 equals the original form
    have hg2_eq : g2 = fun w => Complex.I * fderiv ℝ f w Complex.I := by
      ext w; simp [g2, gI, smul_eq_mul]
    -- Differentiability
    have hdiffI_smul : DifferentiableAt ℝ g2 z := hdiffI.const_smul Complex.I
    have hdiff_sum : DifferentiableAt ℝ (g1 + g2) z := hdiff1.add hdiffI_smul
    -- fderiv of sum
    have hfderiv_sum : fderiv ℝ (g1 + g2) z = fderiv ℝ g1 z + fderiv ℝ g2 z :=
      fderiv_add hdiff1 hdiffI_smul
    -- fderiv of const • g
    have hfderiv_g2 : fderiv ℝ g2 z = Complex.I • fderiv ℝ gI z :=
      fderiv_const_smul hdiffI Complex.I
    -- Now compute
    calc fderiv ℝ (wirtingerDerivBar f) z u
      _ = fderiv ℝ (fun z' => (1/2 : ℂ) * (fderiv ℝ f z' 1 + Complex.I * fderiv ℝ f z' Complex.I)) z u := by
          rw [heq]
      _ = fderiv ℝ ((1/2 : ℂ) • (g1 + g2)) z u := by
          apply congrArg (fun h => fderiv ℝ h z u)
          ext w; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, g1, g2, gI]
      _ = ((1/2 : ℂ) • fderiv ℝ (g1 + g2) z) u := by rw [fderiv_const_smul hdiff_sum]
      _ = (1/2 : ℂ) • (fderiv ℝ (g1 + g2) z u) := rfl
      _ = (1/2 : ℂ) • ((fderiv ℝ g1 z + fderiv ℝ g2 z) u) := by rw [hfderiv_sum]
      _ = (1/2 : ℂ) • (fderiv ℝ g1 z u + fderiv ℝ g2 z u) := rfl
      _ = (1/2 : ℂ) • (D2 u 1 + (Complex.I • fderiv ℝ gI z) u) := by rw [hD2_apply u 1, hfderiv_g2]
      _ = (1/2 : ℂ) • (D2 u 1 + Complex.I • D2 u Complex.I) := by
          -- fderiv ℝ gI z = fderiv ℝ (fun w => fderiv ℝ f w Complex.I) z
          -- and hD2_apply says fderiv ℝ (fun w => fderiv ℝ f w Complex.I) z u = D2 u Complex.I
          have : fderiv ℝ gI z u = D2 u Complex.I := hD2_apply u Complex.I
          simp only [ContinuousLinearMap.smul_apply, this]
      _ = (1/2 : ℂ) * (D2 u 1 + Complex.I * D2 u Complex.I) := by simp only [smul_eq_mul]

  have hfderiv_hol_apply : ∀ u, fderiv ℝ (wirtingerDeriv f) z u =
      (1/2 : ℂ) * (D2 u 1 - Complex.I * D2 u Complex.I) := by
    intro u
    have heq : wirtingerDeriv f = fun z' =>
        (1/2 : ℂ) * (fderiv ℝ f z' 1 - Complex.I * fderiv ℝ f z' Complex.I) := by
      ext z'; exact heq_hol z'
    let g1 : ℂ → ℂ := fun w => fderiv ℝ f w 1
    let gI : ℂ → ℂ := fun w => fderiv ℝ f w Complex.I
    let g2 : ℂ → ℂ := Complex.I • gI
    have hg2_eq : g2 = fun w => Complex.I * fderiv ℝ f w Complex.I := by
      ext w; simp [g2, gI, smul_eq_mul]
    have hdiffI_smul : DifferentiableAt ℝ g2 z := hdiffI.const_smul Complex.I
    have hdiff_sub : DifferentiableAt ℝ (g1 - g2) z := hdiff1.sub hdiffI_smul
    have hfderiv_sub : fderiv ℝ (g1 - g2) z = fderiv ℝ g1 z - fderiv ℝ g2 z :=
      fderiv_sub hdiff1 hdiffI_smul
    have hfderiv_g2 : fderiv ℝ g2 z = Complex.I • fderiv ℝ gI z :=
      fderiv_const_smul hdiffI Complex.I
    calc fderiv ℝ (wirtingerDeriv f) z u
      _ = fderiv ℝ (fun z' => (1/2 : ℂ) * (fderiv ℝ f z' 1 - Complex.I * fderiv ℝ f z' Complex.I)) z u := by
          rw [heq]
      _ = fderiv ℝ ((1/2 : ℂ) • (g1 - g2)) z u := by
          apply congrArg (fun h => fderiv ℝ h z u)
          ext w; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, g1, g2, gI]
      _ = ((1/2 : ℂ) • fderiv ℝ (g1 - g2) z) u := by rw [fderiv_const_smul hdiff_sub]
      _ = (1/2 : ℂ) • (fderiv ℝ (g1 - g2) z u) := rfl
      _ = (1/2 : ℂ) • ((fderiv ℝ g1 z - fderiv ℝ g2 z) u) := by rw [hfderiv_sub]
      _ = (1/2 : ℂ) • (fderiv ℝ g1 z u - fderiv ℝ g2 z u) := rfl
      _ = (1/2 : ℂ) • (D2 u 1 - (Complex.I • fderiv ℝ gI z) u) := by rw [hD2_apply u 1, hfderiv_g2]
      _ = (1/2 : ℂ) • (D2 u 1 - Complex.I • D2 u Complex.I) := by
          have : fderiv ℝ gI z u = D2 u Complex.I := hD2_apply u Complex.I
          simp only [ContinuousLinearMap.smul_apply, this]
      _ = (1/2 : ℂ) * (D2 u 1 - Complex.I * D2 u Complex.I) := by simp only [smul_eq_mul]

  -- Now compute both sides
  -- LHS = wirtingerDeriv (wirtingerDerivBar f) z
  --     = (1/2)(fderiv ℝ (wirtingerDerivBar f) z 1 - I * fderiv ℝ (wirtingerDerivBar f) z I)
  -- RHS = wirtingerDerivBar (wirtingerDeriv f) z
  --     = (1/2)(fderiv ℝ (wirtingerDeriv f) z 1 + I * fderiv ℝ (wirtingerDeriv f) z I)

  -- Expand wirtingerDeriv (wirtingerDerivBar f) z
  have hLHS : wirtingerDeriv (wirtingerDerivBar f) z =
      (1/2 : ℂ) * (fderiv ℝ (wirtingerDerivBar f) z 1 -
                   Complex.I * fderiv ℝ (wirtingerDerivBar f) z Complex.I) := by
    unfold wirtingerDeriv; ring

  -- Expand wirtingerDerivBar (wirtingerDeriv f) z
  have hRHS : wirtingerDerivBar (wirtingerDeriv f) z =
      (1/2 : ℂ) * (fderiv ℝ (wirtingerDeriv f) z 1 +
                   Complex.I * fderiv ℝ (wirtingerDeriv f) z Complex.I) := by
    unfold wirtingerDerivBar; ring

  rw [hLHS, hRHS, hfderiv_bar_apply 1, hfderiv_bar_apply Complex.I,
      hfderiv_hol_apply 1, hfderiv_hol_apply Complex.I]
  -- Now both sides are expressions in D2
  rw [hsymm_1_I]
  ring

end RiemannSurfaces.Analytic.Infrastructure
