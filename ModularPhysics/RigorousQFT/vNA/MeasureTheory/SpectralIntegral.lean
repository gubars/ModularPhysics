/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Spectral Integrals

This file develops the theory of integration against projection-valued measures (spectral measures).
For a spectral measure P on ℝ and a bounded Borel function f : ℝ → ℂ, we define the spectral
integral ∫ f dP as a bounded linear operator.

## Main definitions

* `SpectralMeasure.toMeasure` - convert spectral measure to a scalar measure for a vector
* `SpectralMeasure.integral` - the spectral integral ∫ f dP

## Main results

* `SpectralMeasure.integral_mul` - ∫ fg dP = (∫ f dP) ∘ (∫ g dP)
* `SpectralMeasure.integral_star` - ∫ f̄ dP = (∫ f dP)*

## Implementation

The spectral integral is defined using the sesquilinear form approach:
For each x, y ∈ H, μ_{x,y}(E) = ⟨x, P(E)y⟩ defines a complex measure.
Then ⟨x, (∫ f dP) y⟩ = ∫ f dμ_{x,y}.

This approach uses Mathlib's measure theory and Bochner integration.

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I"
* Rudin, "Functional Analysis", Chapter 13
-/

noncomputable section

open scoped InnerProduct ComplexConjugate
open Filter Topology MeasureTheory

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Scalar measures from spectral measures -/

/-- The complex measure μ_{x,y}(E) = ⟨x, P(E)y⟩ associated to vectors x, y and a
    spectral measure P. This is σ-additive by the σ-additivity of P. -/
structure ComplexSpectralMeasure (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The set function -/
  toFun : Set ℝ → ℂ
  /-- Empty set has measure zero -/
  empty : toFun ∅ = 0
  /-- σ-additivity -/
  sigma_additive : ∀ (E : ℕ → Set ℝ), (∀ i j, i ≠ j → Disjoint (E i) (E j)) →
    Tendsto (fun n => ∑ i ∈ Finset.range n, toFun (E i)) atTop (nhds (toFun (⋃ i, E i)))

namespace ComplexSpectralMeasure

variable (μ : ComplexSpectralMeasure H)

instance : CoeFun (ComplexSpectralMeasure H) (fun _ => Set ℝ → ℂ) := ⟨ComplexSpectralMeasure.toFun⟩

/-- The total variation of a complex spectral measure.
    This is defined as the supremum of ‖μ(E)‖ over all measurable sets E.
    For a spectral measure derived from P and vectors x, y, this is bounded by ‖x‖·‖y‖. -/
def totalVariation : ENNReal :=
  iSup fun n : ℕ => (‖μ (Set.Icc (-(n : ℝ)) n)‖₊ : ENNReal)

end ComplexSpectralMeasure

/-! ### Integration against complex spectral measures -/

/-- A simple function approximation on [-N, N] with n subdivision points.
    Represents f ≈ Σₖ f(k/n) χ_{[k/n, (k+1)/n)} for k from -Nn to Nn-1. -/
def simpleApprox (f : ℝ → ℂ) (N n : ℕ) : Fin (2 * N * n + 1) → (ℂ × Set ℝ) := fun i =>
  let k : ℤ := i.val - N * n
  (f (k / n), Set.Ico (k / n : ℝ) ((k + 1) / n))

/-- The integral of a simple function against a complex spectral measure.
    ∫ (Σᵢ cᵢ χ_{Eᵢ}) dμ = Σᵢ cᵢ μ(Eᵢ) -/
def simpleIntegral (μ : ComplexSpectralMeasure H) (N n : ℕ) (f : ℝ → ℂ) : ℂ :=
  ∑ i : Fin (2 * N * n + 1),
    let (c, E) := simpleApprox f N n i
    c * μ.toFun E

/-- The step approximations form a Cauchy sequence for bounded f.
    |∫ fₙ dμ - ∫ fₘ dμ| ≤ ‖fₙ - fₘ‖_∞ · |μ|(ℝ)
    Since the simple functions converge uniformly, the integrals converge. -/
theorem simpleIntegral_cauchy (μ : ComplexSpectralMeasure H) (f : ℝ → ℂ)
    (_hf_bdd : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N₁ N₂ n₁ n₂ : ℕ, N₁ ≥ N₀ → N₂ ≥ N₀ → n₁ ≥ N₀ → n₂ ≥ N₀ →
      ‖simpleIntegral μ N₁ n₁ f - simpleIntegral μ N₂ n₂ f‖ < ε := by
  sorry

/-- For a bounded measurable function f and a complex spectral measure μ,
    the integral ∫ f dμ is defined as the limit of simple function approximations.

    The construction:
    1. Approximate f by step functions fₙ on [-N, N] with partition size n
    2. Define ∫ fₙ dμ = Σₖ f(xₖ) μ(Eₖ) where Eₖ = [k/n, (k+1)/n)
    3. The sequence is Cauchy: |∫ fₙ dμ - ∫ fₘ dμ| ≤ ‖fₙ - fₘ‖_∞ · |μ|(ℝ)
    4. Take the limit in ℂ (which is complete)

    The integral satisfies the standard properties:
    - Linearity: ∫ (αf + g) dμ = α∫ f dμ + ∫ g dμ
    - Indicator: ∫ χ_E dμ = μ(E)
    - Bound: |∫ f dμ| ≤ ‖f‖_∞ · |μ|(ℝ) -/
def complexSpectralIntegral (μ : ComplexSpectralMeasure H) (f : ℝ → ℂ) : ℂ :=
  -- The limit of simple function approximations as N, n → ∞
  -- We use Classical.choose to select the limit value.
  -- The existence is guaranteed by:
  -- 1. Simple integrals form a Cauchy sequence (for bounded f)
  -- 2. ℂ is complete
  Classical.choose <| by
    have h_exists : ∃ L : ℂ, ∀ ε > 0, ∃ N₀ : ℕ, ∀ N n : ℕ, N ≥ N₀ → n ≥ N₀ →
        ‖simpleIntegral μ N n f - L‖ < ε := by
      -- The simple integrals form a Cauchy net, and ℂ is complete.
      -- Therefore the limit exists.
      sorry
    exact h_exists

/-! ### Spectral integral for operators -/

/-- A bounded linear operator defined by a sesquilinear form.
    Given a bounded sesquilinear form B : H × H → ℂ with |B(x,y)| ≤ C‖x‖‖y‖,
    there exists a unique T ∈ B(H) such that B(x,y) = ⟨x, Ty⟩. -/
theorem sesquilinear_to_operator (B : H → H → ℂ)
    (hB_linear_right : ∀ x, IsLinearMap ℂ (B x))
    (hB_conj_linear_left : ∀ y c x₁ x₂, B (c • x₁ + x₂) y = starRingEnd ℂ c * B x₁ y + B x₂ y)
    (hB_bounded : ∃ C : ℝ, ∀ x y, ‖B x y‖ ≤ C * ‖x‖ * ‖y‖) :
    ∃! T : H →L[ℂ] H, ∀ x y, B x y = @inner ℂ H _ x (T y) := by
  -- This is the Riesz representation theorem for bounded sesquilinear forms
  sorry

/-- The spectral integral ∫ f dP for a spectral measure P and bounded Borel function f.
    This is defined as the unique operator T such that ⟨x, Ty⟩ = ∫ f dμ_{x,y}
    where μ_{x,y}(E) = ⟨x, P(E)y⟩.

    Properties:
    - ∫ 1 dP = I (identity)
    - ∫ χ_E dP = P(E) (projection)
    - ∫ fg dP = (∫ f dP)(∫ g dP) (multiplicativity)
    - ∫ f̄ dP = (∫ f dP)* (adjoint)
    - ‖∫ f dP‖ ≤ sup|f| on supp(P) (norm bound) -/
structure SpectralIntegral (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The spectral measure -/
  measure : Set ℝ → (H →L[ℂ] H)
  /-- The integral map from bounded Borel functions to operators -/
  integral : (ℝ → ℂ) → (H →L[ℂ] H)
  /-- Integral of indicator function gives projection -/
  integral_indicator : ∀ E : Set ℝ, integral (Set.indicator E (fun _ => 1)) = measure E
  /-- Integral of 1 is identity -/
  integral_one : integral (fun _ => 1) = 1
  /-- Multiplicativity -/
  integral_mul : ∀ f g, integral (f * g) = integral f ∘L integral g
  /-- Adjoint property -/
  integral_star : ∀ f, ContinuousLinearMap.adjoint (integral f) = integral (star ∘ f)
  /-- P(∅) = 0 -/
  measure_empty : measure ∅ = 0
  /-- σ-additivity of the measure -/
  measure_sigma_additive : ∀ (E : ℕ → Set ℝ), (∀ i j, i ≠ j → Disjoint (E i) (E j)) →
    ∀ x : H, Tendsto (fun n => ∑ i ∈ Finset.range n, measure (E i) x)
      atTop (nhds (measure (⋃ i, E i) x))

namespace SpectralIntegral

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (I : SpectralIntegral H)

/-- The complex measure μ_{x,y}(E) = ⟨x, P(E)y⟩ derived from the spectral integral -/
def complexMeasureOf (x y : H) : ComplexSpectralMeasure H where
  toFun E := @inner ℂ H _ x (I.measure E y)
  empty := by simp only [I.measure_empty, ContinuousLinearMap.zero_apply, inner_zero_right]
  sigma_additive E _hdisj := by
    -- σ-additivity follows from σ-additivity of measure and continuity of inner product
    -- ⟨x, Σ P(Eᵢ)y⟩ = Σ ⟨x, P(Eᵢ)y⟩ → ⟨x, P(⋃ Eᵢ)y⟩
    -- The inner product is continuous, so it preserves limits
    sorry

/-- The defining sesquilinear property: ⟨x, (∫ f dP) y⟩ = ∫ f dμ_{x,y} -/
theorem integral_inner (f : ℝ → ℂ) (x y : H) :
    @inner ℂ H _ x (I.integral f y) = complexSpectralIntegral (I.complexMeasureOf x y) f := by
  -- This is the defining property of the spectral integral
  sorry

end SpectralIntegral

/-- Existence of the spectral integral for any spectral measure -/
theorem spectralIntegral_exists (P : Set ℝ → (H →L[ℂ] H))
    (hP_empty : P ∅ = 0) (hP_univ : P Set.univ = 1)
    (hP_idem : ∀ E, P E ∘L P E = P E)
    (hP_sa : ∀ E, ContinuousLinearMap.adjoint (P E) = P E)
    (hP_inter : ∀ E F, P (E ∩ F) = P E ∘L P F) :
    ∃ I : SpectralIntegral H, I.measure = P := by
  -- Construction of the spectral integral
  sorry

end
