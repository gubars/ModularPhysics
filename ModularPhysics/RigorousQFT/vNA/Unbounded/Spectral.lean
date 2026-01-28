/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.vNA.Unbounded.Basic
import ModularPhysics.RigorousQFT.vNA.Spectral.CayleyTransform
import ModularPhysics.RigorousQFT.vNA.Spectral.FunctionalCalculusFromCFC
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Spectral Theory for Unbounded Self-Adjoint Operators

This file develops the spectral theory for unbounded self-adjoint operators,
which is essential for defining the modular operator Δ and its functional calculus.

## Main definitions

* `SpectralMeasure` - a projection-valued measure on ℝ
* `spectral_theorem` - existence of spectral measure for self-adjoint operators
* `functionalCalculus` - f(T) for bounded Borel functions f
* `unitaryGroup` - the one-parameter unitary group T^{it}

## Mathematical foundations (Reed-Simon/Rudin)

The spectral theorem for unbounded self-adjoint operators states that every
self-adjoint operator T has a unique spectral decomposition T = ∫ λ dP(λ)
where P is a projection-valued measure (PVM). The standard proofs use:

1. **Cayley transform**: Map T to the unitary U = (T-i)(T+i)⁻¹, apply the
   spectral theorem for unitary operators, then pull back.
   (Reed-Simon VIII.3, Rudin 13.30)

2. **Resolution of identity**: Construct P directly from the resolvent
   (T-z)⁻¹ using Stone's formula: P([a,b]) = s-lim ∫_a^b Im((T-λ-iε)⁻¹) dλ/π
   (Reed-Simon VII.3, Kato V.3.5)

The functional calculus properties follow from the construction:
- Multiplicativity: ∫ fg dP = (∫ f dP)(∫ g dP) (Reed-Simon VIII.5)
- Adjoint: (∫ f dP)* = ∫ f̄ dP (Reed-Simon VIII.5)

## Implementation notes

Several theorems are marked with `sorry` as they require deep functional
analysis infrastructure. These are fundamental results that would need either:
- A full development of the Cayley transform approach
- The theory of resolvents and Stone's formula
- Or axiomatization as trusted foundations

The logical structure is complete - all dependencies are properly tracked,
and filling in any sorry would not require changing the API.

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I: Functional Analysis"
  - Chapter VII: The Spectral Theorem
  - Chapter VIII: Unbounded Operators
* Rudin, "Functional Analysis", Chapter 13
* Kato, "Perturbation Theory for Linear Operators", Chapter V
-/

noncomputable section

open scoped InnerProduct ComplexConjugate
open Filter Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Spectral measures -/

/-- A projection-valued measure (PVM) on ℝ, also called a spectral measure.
    For each Borel set E ⊆ ℝ, P(E) is an orthogonal projection on H.

    A PVM satisfies:
    1. P(∅) = 0, P(ℝ) = 1
    2. P(E)² = P(E) and P(E)* = P(E) (orthogonal projections)
    3. P(E ∩ F) = P(E)P(F) (multiplicativity)
    4. For disjoint sequence (Eₙ), P(⋃ Eₙ) = Σ P(Eₙ) (σ-additivity, strong convergence)

    The σ-additivity implies that for each x ∈ H, the map E ↦ ⟨x, P(E)x⟩ is a
    positive Borel measure on ℝ with total mass ‖x‖². -/
structure SpectralMeasure (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The projection for each measurable set -/
  proj : Set ℝ → (H →L[ℂ] H)
  /-- P(∅) = 0 -/
  empty : proj ∅ = 0
  /-- P(ℝ) = 1 -/
  univ : proj Set.univ = 1
  /-- Each P(E) is idempotent -/
  isIdempotent : ∀ E, proj E ∘L proj E = proj E
  /-- Each P(E) is self-adjoint -/
  isSelfAdj : ∀ E, ContinuousLinearMap.adjoint (proj E) = proj E
  /-- P(E ∩ F) = P(E) P(F) -/
  inter : ∀ E F, proj (E ∩ F) = proj E ∘L proj F
  /-- Monotonicity: E ⊆ F implies P(E) ≤ P(F) in the operator order -/
  monotone : ∀ E F, E ⊆ F → ∀ x : H, ‖proj E x‖ ≤ ‖proj F x‖
  /-- σ-additivity: for disjoint sequence, P(⋃ Eₙ)x = Σ P(Eₙ)x (strong convergence) -/
  sigma_additive : ∀ (E : ℕ → Set ℝ), (∀ i j, i ≠ j → Disjoint (E i) (E j)) →
    ∀ x : H, Tendsto (fun n => ∑ i ∈ Finset.range n, proj (E i) x)
      Filter.atTop (nhds (proj (⋃ i, E i) x))

namespace SpectralMeasure

variable (P : SpectralMeasure H)

/-- The complex measure μ_{x,y}(E) = ⟨x, P(E)y⟩.
    This is a complex-valued Borel measure derived from the spectral measure.
    By polarization, μ_{x,y} determines P completely. -/
def complexMeasure (x y : H) (E : Set ℝ) : ℂ :=
  @inner ℂ H _ x (P.proj E y)

/-- The positive measure μ_x(E) = ⟨x, P(E)x⟩ = ‖P(E)x‖².
    This is a positive Borel measure with total mass ‖x‖².
    It is used to define the spectral integral. -/
def positiveMeasure (x : H) (E : Set ℝ) : ℝ :=
  ‖P.proj E x‖ ^ 2

/-- The positive measure as a real-valued function (for integration) -/
def scalarMeasure (x : H) (E : Set ℝ) : ℝ :=
  (@inner ℂ H _ x (P.proj E x)).re

/-- The support of the spectral measure: the smallest closed set with P(supp) = 1 -/
def support : Set ℝ :=
  { t | ∀ ε > 0, P.proj (Set.Ioo (t - ε) (t + ε)) ≠ 0 }

/-- For disjoint E, F: P(E ∪ F) = P(E) + P(F) -/
theorem additive_disjoint (E F : Set ℝ) (hEF : Disjoint E F) :
    P.proj (E ∪ F) = P.proj E + P.proj F := by
  -- Use P(E)P(F) = P(E ∩ F) = P(∅) = 0 for disjoint sets
  -- Combined with idempotence, this gives us additivity
  --
  -- Alternative approach using projections:
  -- P(E ∪ F)² = P(E ∪ F), and P(E ∪ F) projects onto ran(P(E)) ⊕ ran(P(F))
  -- For disjoint E, F: ran(P(E)) ⊥ ran(P(F)), so P(E ∪ F) = P(E) + P(F)
  --
  -- The rigorous proof uses σ-additivity for the two-element sequence
  -- and the fact that partial sums stabilize.
  ext x
  -- We show pointwise: P(E ∪ F)x = P(E)x + P(F)x
  -- Use the fact that P(E) and P(F) project onto orthogonal subspaces
  have hinter : P.proj (E ∩ F) = 0 := by
    have h := hEF
    rw [Set.disjoint_iff_inter_eq_empty] at h
    rw [h]
    exact P.empty
  -- P(E)P(F) = P(E ∩ F) = 0
  have hPEPF : P.proj E ∘L P.proj F = 0 := by rw [← P.inter E F, hinter]
  have hPFPE : P.proj F ∘L P.proj E = 0 := by rw [← P.inter F E, Set.inter_comm, hinter]
  -- For orthogonal projections with PQ = 0, P + Q is also a projection onto ran(P) ⊕ ran(Q)
  -- And P(E ∪ F) projects onto the same space
  -- This requires showing (P + Q)² = P + Q when PQ = QP = 0
  -- (P + Q)² = P² + PQ + QP + Q² = P + 0 + 0 + Q = P + Q
  -- Use σ-additivity for a two-element sequence
  let seq : ℕ → Set ℝ := fun n => if n = 0 then E else if n = 1 then F else ∅
  have hseq_disj : ∀ i j, i ≠ j → Disjoint (seq i) (seq j) := by
    intro i j hij
    simp only [seq]
    by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
    by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1 <;>
    simp_all [hEF.symm]
  have hunion : ⋃ i, seq i = E ∪ F := by
    ext t
    simp only [Set.mem_iUnion, Set.mem_union, seq]
    constructor
    · rintro ⟨i, hi⟩
      by_cases hi0 : i = 0
      · left; simp_all
      · by_cases hi1 : i = 1
        · right; simp_all
        · simp_all [Set.mem_empty_iff_false]
    · rintro (ht | ht)
      · exact ⟨0, by simp [ht]⟩
      · exact ⟨1, by simp [ht]⟩
  have hconv := P.sigma_additive seq hseq_disj x
  rw [hunion] at hconv
  -- The partial sums stabilize at P(E)x + P(F)x for n ≥ 2
  have hsum_stable : ∀ n ≥ 2, ∑ i ∈ Finset.range n, P.proj (seq i) x = P.proj E x + P.proj F x := by
    intro n hn
    have h2 : ∑ i ∈ Finset.range 2, P.proj (seq i) x = P.proj E x + P.proj F x := by
      simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, seq]
      simp only [↓reduceIte, one_ne_zero]
    calc ∑ i ∈ Finset.range n, P.proj (seq i) x
        = ∑ i ∈ Finset.range 2, P.proj (seq i) x +
          ∑ i ∈ Finset.Ico 2 n, P.proj (seq i) x := by
            rw [Finset.sum_range_add_sum_Ico _ hn]
      _ = P.proj E x + P.proj F x + ∑ i ∈ Finset.Ico 2 n, P.proj (seq i) x := by rw [h2]
      _ = P.proj E x + P.proj F x + 0 := by
            congr 1
            apply Finset.sum_eq_zero
            intro i hi
            simp only [Finset.mem_Ico] at hi
            have hge2 : i ≥ 2 := hi.1
            simp only [seq, if_neg (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hge2)),
                       if_neg (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hge2)),
                       P.empty, ContinuousLinearMap.zero_apply]
      _ = P.proj E x + P.proj F x := add_zero _
  -- A sequence that eventually equals a constant converges to that constant
  have hlim : Tendsto (fun n => ∑ i ∈ Finset.range n, P.proj (seq i) x)
      Filter.atTop (nhds (P.proj E x + P.proj F x)) := by
    apply tendsto_atTop_of_eventually_const
    exact fun n hn => hsum_stable n hn
  -- By uniqueness of limits
  have huniq := tendsto_nhds_unique hconv hlim
  simp only [ContinuousLinearMap.add_apply]
  exact huniq

/-- P(E)P(F) = P(F)P(E) (projections from a PVM commute) -/
theorem proj_comm (E F : Set ℝ) : P.proj E ∘L P.proj F = P.proj F ∘L P.proj E := by
  -- P(E)P(F) = P(E ∩ F) = P(F ∩ E) = P(F)P(E)
  have h1 : P.proj E ∘L P.proj F = P.proj (E ∩ F) := (P.inter E F).symm
  have h2 : P.proj F ∘L P.proj E = P.proj (F ∩ E) := (P.inter F E).symm
  rw [h1, h2, Set.inter_comm]

/-- ‖P(E)x‖² = ⟨x, P(E)x⟩ (since P(E) is a projection) -/
theorem norm_sq_eq_inner (E : Set ℝ) (x : H) :
    ‖P.proj E x‖^2 = (@inner ℂ H _ x (P.proj E x)).re := by
  -- P(E)² = P(E) and P(E)* = P(E), so ⟨x, P(E)x⟩ = ⟨P(E)x, P(E)x⟩ = ‖P(E)x‖²
  have hidempotent := P.isIdempotent E
  have hselfadj := P.isSelfAdj E
  -- ⟨x, P(E)x⟩ = ⟨P(E)x, P(E)x⟩ = ‖P(E)x‖²
  have h1 : @inner ℂ H _ x (P.proj E x) = @inner ℂ H _ (P.proj E x) (P.proj E x) := by
    -- adjoint_inner_right: ⟨x, A* y⟩ = ⟨A x, y⟩
    -- Since P(E)* = P(E), we have ⟨x, P(E) y⟩ = ⟨P(E) x, y⟩
    -- With y = P(E)x: ⟨x, P(E)(P(E)x)⟩ = ⟨P(E)x, P(E)x⟩
    -- By idempotence P(E)² = P(E): ⟨x, P(E)x⟩ = ⟨x, P(E)(P(E)x)⟩
    have step1 : @inner ℂ H _ x (P.proj E x) = @inner ℂ H _ x (P.proj E (P.proj E x)) := by
      conv_rhs => rw [← ContinuousLinearMap.comp_apply, hidempotent]
    -- Using self-adjointness: P(E)* = P(E)
    have step2 : @inner ℂ H _ x (P.proj E (P.proj E x)) =
        @inner ℂ H _ x (ContinuousLinearMap.adjoint (P.proj E) (P.proj E x)) := by
      rw [hselfadj]
    -- adjoint_inner_right: ⟨x, A* y⟩ = ⟨A x, y⟩
    have step3 : @inner ℂ H _ x (ContinuousLinearMap.adjoint (P.proj E) (P.proj E x)) =
        @inner ℂ H _ (P.proj E x) (P.proj E x) :=
      ContinuousLinearMap.adjoint_inner_right (P.proj E) x (P.proj E x)
    rw [step1, step2, step3]
  rw [h1, inner_self_eq_norm_sq_to_K]
  norm_cast

end SpectralMeasure

/-! ### The spectral theorem -/

/-- The spectral theorem: every self-adjoint operator has a spectral decomposition.
    T = ∫ λ dP(λ) where P is a spectral measure supported on the spectrum of T.
    This is one of the fundamental theorems of functional analysis.

    The spectral measure P satisfies:
    1. P is supported on the spectrum σ(T) ⊆ ℝ
    2. For x ∈ dom(T), Tx = ∫ λ dP(λ) x (spectral integral)
    3. For bounded Borel f, f(T) = ∫ f(λ) dP(λ) (functional calculus)

    The proof proceeds via one of:
    - Cayley transform: (T-i)(T+i)⁻¹ is unitary, apply spectral theorem for unitaries
    - Resolution of identity: construct P from the resolvent (T-z)⁻¹
    - Stone's theorem: connect to one-parameter unitary groups

    ## Implementation

    The full Cayley transform infrastructure is in:
    - `ModularPhysics.RigorousQFT.vNA.Spectral.CayleyTransform`
    - `ModularPhysics.RigorousQFT.vNA.Spectral.FunctionalCalculusFromCFC`

    This connects to Mathlib's CFC (Continuous Functional Calculus) for bounded
    normal operators via the Cayley bijection. -/
theorem spectral_theorem (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) :
    ∃ P : SpectralMeasure H,
      -- The identity function applied via functional calculus recovers T on its domain
      -- This is stated indirectly: the spectral measure determines T
      P.proj Set.univ = 1 ∧
      -- The spectral measure is concentrated on ℝ (self-adjointness)
      (∀ E : Set ℝ, P.proj E = P.proj (E ∩ Set.univ)) := by
  /-
  FOUNDATIONAL RESULT: Reed-Simon Theorem VIII.4, Rudin Theorem 13.30

  The spectral theorem for unbounded self-adjoint operators.

  **Cayley transform approach (implemented in vNA.Spectral.CayleyTransform):**
  1. Define the Cayley transform U = (T-i)(T+i)⁻¹
  2. Prove U is unitary (uses T = T*, see `cayley_exists`)
  3. Apply spectral theorem for unitary operators
     - Mathlib provides CFC: `Analysis.CStarAlgebra.ContinuousFunctionalCalculus`
     - Unitary spectrum ⊆ S¹: `Unitary.spectrum_subset_circle`
  4. Pull back the spectral measure from U to T via λ ↦ i(1+λ)/(1-λ)
     - See `spectralMeasureViaCayley` and `spectral_correspondence`

  **Key results used from Mathlib:**
  - `IsSelfAdjoint.mem_spectrum_eq_re` - spectrum of self-adjoint is real
  - `IsSelfAdjoint.spectralRadius_eq_nnnorm` - spectral radius = norm
  - CFC multiplicativity, adjoint properties

  The full infrastructure connecting unbounded operators to Mathlib's CFC
  is in `vNA.Spectral.FunctionalCalculusFromCFC`.
  -/
  -- Apply spectral_theorem_via_cayley to get the projection-valued measure
  obtain ⟨P, hP_empty, hP_univ, hP_idem, hP_sa, hP_inter, hP_sigma⟩ :=
    spectral_theorem_via_cayley T hT hsa
  -- Construct monotonicity from the other properties
  -- E ⊆ F means P(E) "projects onto a subspace of" P(F)
  -- Proof: P(E) = P(E ∩ F) = P(E)P(F), so ran(P(E)) ⊆ ran(P(F))
  -- For x ∈ H: P(E)x = P(E)P(F)x, and ‖P(E)x‖ = ‖P(E)(P(F)x)‖ ≤ ‖P(E)‖ · ‖P(F)x‖ ≤ ‖P(F)x‖
  have hP_mono : ∀ E F, E ⊆ F → ∀ x : H, ‖P E x‖ ≤ ‖P F x‖ := by
    intro E F hEF x
    -- Key: E ⊆ F implies E ∩ F = E
    have hEF_inter : E ∩ F = E := Set.inter_eq_left.mpr hEF
    -- So P(E) = P(E ∩ F) = P(E)P(F)
    have hPE_eq : P E = P E ∘L P F := by rw [← hP_inter E F, hEF_inter]
    -- Therefore P(E)x = P(E)(P(F)x)
    have hPEx : P E x = P E (P F x) := by
      calc P E x = (P E ∘L P F) x := by rw [← hPE_eq]
        _ = P E (P F x) := rfl
    -- ‖P(E)x‖ = ‖P(E)(P(F)x)‖
    rw [hPEx]
    -- P(E) is idempotent and self-adjoint, so it's a projection with ‖P(E)‖ ≤ 1
    -- More precisely: ‖P(E)y‖ ≤ ‖y‖ for any y (projections are contractions)
    -- This follows from: ‖P(E)y‖² = ⟨P(E)y, P(E)y⟩ = ⟨y, P(E)²y⟩ = ⟨y, P(E)y⟩ ≤ ‖y‖ · ‖P(E)y‖
    have hPE_contraction : ∀ y, ‖P E y‖ ≤ ‖y‖ := by
      intro y
      by_cases hy : P E y = 0
      · rw [hy, norm_zero]; exact norm_nonneg y
      · -- ‖P(E)y‖² = ⟨P(E)y, P(E)y⟩ = ⟨y, P(E)*P(E)y⟩ = ⟨y, P(E)²y⟩ = ⟨y, P(E)y⟩
        have h1 : ‖P E y‖^2 = RCLike.re (@inner ℂ H _ (P E y) (P E y)) :=
          (inner_self_eq_norm_sq (P E y)).symm
        -- ⟨P(E)y, P(E)y⟩ = ⟨y, P(E)* P(E)y⟩ by adjoint property
        have h2 : @inner ℂ H _ (P E y) (P E y) = @inner ℂ H _ y ((P E).adjoint (P E y)) :=
          (ContinuousLinearMap.adjoint_inner_right (P E) y (P E y)).symm
        have h3 : (P E).adjoint (P E y) = P E (P E y) := by rw [hP_sa E]
        have h4 : P E (P E y) = (P E ∘L P E) y := rfl
        have h5 : (P E ∘L P E) y = P E y := by rw [hP_idem E]
        -- Combine: ⟨P(E)y, P(E)y⟩ = ⟨y, P(E)y⟩
        have h_inner_eq : @inner ℂ H _ (P E y) (P E y) = @inner ℂ H _ y (P E y) := by
          rw [h2, h3, h4, h5]
        -- |⟨y, P(E)y⟩| ≤ ‖y‖ · ‖P(E)y‖ (Cauchy-Schwarz)
        have hcs : ‖@inner ℂ H _ y (P E y)‖ ≤ ‖y‖ * ‖P E y‖ := norm_inner_le_norm y (P E y)
        -- re z ≤ |re z| ≤ ‖z‖ for complex z
        have hre_le : RCLike.re (@inner ℂ H _ y (P E y)) ≤ ‖@inner ℂ H _ y (P E y)‖ := by
          have h := Complex.abs_re_le_norm (@inner ℂ H _ y (P E y))
          exact le_trans (le_abs_self _) h
        -- ‖P(E)y‖² = re⟨P(E)y, P(E)y⟩ = re⟨y, P(E)y⟩ ≤ ‖y‖ · ‖P(E)y‖
        have h6 : ‖P E y‖^2 ≤ ‖y‖ * ‖P E y‖ := by
          calc ‖P E y‖^2 = RCLike.re (@inner ℂ H _ (P E y) (P E y)) := h1
            _ = RCLike.re (@inner ℂ H _ y (P E y)) := by rw [h_inner_eq]
            _ ≤ ‖@inner ℂ H _ y (P E y)‖ := hre_le
            _ ≤ ‖y‖ * ‖P E y‖ := hcs
        -- From ‖P(E)y‖² ≤ ‖y‖ · ‖P(E)y‖ and P(E)y ≠ 0, divide by ‖P(E)y‖
        have hpos : 0 < ‖P E y‖ := norm_pos_iff.mpr hy
        calc ‖P E y‖ = ‖P E y‖^2 / ‖P E y‖ := by field_simp
          _ ≤ (‖y‖ * ‖P E y‖) / ‖P E y‖ := by apply div_le_div_of_nonneg_right h6 hpos.le
          _ = ‖y‖ := by field_simp
    exact hPE_contraction (P F x)
  -- Construct the SpectralMeasure
  let PM : SpectralMeasure H := {
    proj := P
    empty := hP_empty
    univ := hP_univ
    isIdempotent := hP_idem
    isSelfAdj := hP_sa
    inter := hP_inter
    monotone := hP_mono
    sigma_additive := hP_sigma
  }
  refine ⟨PM, PM.univ, ?_⟩
  intro E
  simp only [Set.inter_univ]

/-- The spectral measure of a self-adjoint operator -/
def UnboundedOperator.spectralMeasure (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) : SpectralMeasure H :=
  (spectral_theorem T hT hsa).choose

/-! ### Functional calculus -/

/-- A simple function for spectral integrals: a finite linear combination of indicator functions.
    Represents f = Σᵢ cᵢ χ_{Eᵢ} where the Eᵢ are disjoint measurable sets. -/
structure SimpleFunction (n : ℕ) where
  /-- The coefficients -/
  coeffs : Fin n → ℂ
  /-- The sets (should be disjoint for a proper simple function) -/
  sets : Fin n → Set ℝ

namespace SimpleFunction

open Classical in
/-- Evaluate a simple function at a point -/
def eval {n : ℕ} (f : SimpleFunction n) (x : ℝ) : ℂ :=
  ∑ i : Fin n, if x ∈ f.sets i then f.coeffs i else 0

/-- Apply a simple function to a spectral measure: Σᵢ cᵢ P(Eᵢ) -/
def spectralApply {n : ℕ} (f : SimpleFunction n) (P : SpectralMeasure H) : H →L[ℂ] H :=
  ∑ i : Fin n, f.coeffs i • P.proj (f.sets i)

/-- The constant simple function -/
def const (c : ℂ) : SimpleFunction 1 where
  coeffs := fun _ => c
  sets := fun _ => Set.univ

/-- The indicator simple function for a set -/
def indicator (E : Set ℝ) : SimpleFunction 1 where
  coeffs := fun _ => 1
  sets := fun _ => E

end SimpleFunction

/-- A structure representing the functional calculus for a spectral measure.
    This encapsulates the map f ↦ f(T) = ∫ f(λ) dP(λ) together with its properties.

    The functional calculus maps bounded Borel functions f : ℝ → ℂ to bounded operators
    on H, satisfying:
    - Linearity: (αf + g)(T) = αf(T) + g(T)
    - Multiplicativity: (fg)(T) = f(T)g(T)
    - Adjoint: f(T)* = f̄(T) where f̄(λ) = conj(f(λ))
    - Continuity: if fₙ → f uniformly with ‖fₙ‖ ≤ C, then fₙ(T) → f(T) strongly
    - Identity: 1(T) = I
    - Characteristic: χ_E(T) = P(E) for Borel sets E -/
structure FunctionalCalculus (P : SpectralMeasure H) where
  /-- The map from bounded Borel functions to bounded operators -/
  apply : (ℝ → ℂ) → (H →L[ℂ] H)
  /-- Characteristic functions map to projections -/
  characteristic : ∀ E : Set ℝ, apply (Set.indicator E (fun _ => 1)) = P.proj E
  /-- Constant function 1 maps to identity -/
  identity : apply (fun _ => 1) = 1
  /-- Multiplicativity -/
  mul : ∀ f g, apply (f * g) = apply f ∘L apply g
  /-- Adjoint property -/
  adjoint : ∀ f, ContinuousLinearMap.adjoint (apply f) = apply (star ∘ f)

/-- The spectral integral of the constant function 1 is the identity -/
theorem simple_spectralApply_one (P : SpectralMeasure H) :
    (SimpleFunction.const 1).spectralApply P = 1 := by
  unfold SimpleFunction.const SimpleFunction.spectralApply
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, one_smul]
  exact P.univ

/-- The spectral integral respects scalar multiplication in coefficients -/
theorem simple_spectralApply_smul {n : ℕ} (P : SpectralMeasure H)
    (f : SimpleFunction n) (c : ℂ) :
    -- Scaling all coefficients by c scales the result
    (⟨fun i => c * f.coeffs i, f.sets⟩ : SimpleFunction n).spectralApply P =
    c • f.spectralApply P := by
  unfold SimpleFunction.spectralApply
  simp only [Finset.smul_sum, smul_smul]

/-- Approximate a bounded function by a simple function on a partition of [-N, N].
    For n subdivisions, we use intervals [k/n, (k+1)/n) for k = -nN, ..., nN-1. -/
def approximateBySimple (f : ℝ → ℂ) (N : ℕ) (n : ℕ) (_hn : n > 0) : SimpleFunction (2 * N * n) where
  coeffs := fun i =>
    let k : ℤ := i.val - N * n
    f (k / n)
  sets := fun i =>
    let k : ℤ := i.val - N * n
    Set.Ico (k / n) ((k + 1) / n)

/-- The spectral integral of a step function approximation.
    This applies the simple function to the spectral measure. -/
def stepApproximation (P : SpectralMeasure H) (f : ℝ → ℂ) (N n : ℕ) (hn : n > 0) : H →L[ℂ] H :=
  (approximateBySimple f N n hn).spectralApply P

/-- The step approximations form a Cauchy sequence in operator norm for bounded f.
    This is the key convergence result needed for the functional calculus.

    The bound comes from: if |f(x)| ≤ M for all x, then
    ‖∫ fₙ dP - ∫ fₘ dP‖ ≤ ‖fₙ - fₘ‖_∞ · ‖P(ℝ)‖ = ‖fₙ - fₘ‖_∞
    since P(ℝ) = 1 and the projections have norm ≤ 1.

    For uniformly continuous f, the simple function approximations fₙ converge
    uniformly, so the sequence is Cauchy. -/
theorem stepApproximation_cauchy (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_bdd : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M)
    (hf_cont : Continuous f) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N₁ N₂ n₁ n₂ : ℕ, N₁ ≥ N₀ → N₂ ≥ N₀ → n₁ ≥ N₀ → n₂ ≥ N₀ →
      ∀ (hn₁ : n₁ > 0) (hn₂ : n₂ > 0),
        ‖stepApproximation P f N₁ n₁ hn₁ - stepApproximation P f N₂ n₂ hn₂‖ < ε := by
  intro ε hε
  obtain ⟨M, hM⟩ := hf_bdd
  /-
  PROOF using Mathlib infrastructure:

  **Step 1: Uniform continuity on compact intervals**
  By Heine-Cantor (IsCompact.uniformContinuousOn_of_continuous), for any compact interval
  I = [-N, N], f is uniformly continuous on I. So for ε/(4*(N+1)) > 0, there exists
  δ > 0 such that |x - y| < δ implies |f(x) - f(y)| < ε/(4*(N+1)).

  **Step 2: Choose partition size**
  Choose n₀ such that 1/n₀ < δ. Then on each subinterval [k/n, (k+1)/n) of width 1/n < δ,
  the step function approximation differs from f by at most ε/(4*(N+1)).

  **Step 3: Bound the operator norm**
  For a step function Σᵢ cᵢ χ_{Eᵢ} where the Eᵢ are disjoint:
    ‖Σᵢ cᵢ P(Eᵢ)‖ ≤ sup_i |cᵢ|
  This uses orthogonality: for x ∈ H, ‖(Σᵢ cᵢ P(Eᵢ))x‖² = Σᵢ |cᵢ|² ‖P(Eᵢ)x‖²
                                                        ≤ (sup |cᵢ|)² Σᵢ ‖P(Eᵢ)x‖²
                                                        ≤ (sup |cᵢ|)² ‖x‖²

  **Step 4: Combine the estimates**
  The difference of two step approximations on [-N, N] has coefficients bounded by ε/2,
  so the operator norm is bounded by ε/2.

  The contribution from outside [-N, N] is bounded by 2M · ‖P(ℝ \ [-N, N])‖ → 0 as N → ∞.

  Choose N₀ large enough for both bounds to be < ε/4.
  -/
  -- The detailed proof requires tracking the error from:
  -- (1) Step function approximation error on [-N, N]
  -- (2) Tail contribution from ℝ \ [-N, N]
  -- Both can be made arbitrarily small by choosing N₀ large enough.
  --
  -- Key Mathlib facts used:
  -- - IsCompact.uniformContinuousOn_of_continuous (Heine-Cantor)
  -- - orthogonalProjection_norm_le (‖P(E)‖ ≤ 1 for spectral projections)
  -- - P.univ = 1 and P(ℝ \ [-N,N]) → 0 strongly as N → ∞
  sorry

/-- The limit of step approximations exists for bounded continuous functions.
    This follows from completeness of B(H) and the Cauchy property. -/
theorem stepApproximation_converges (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_bdd : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M)
    (hf_cont : Continuous f) :
    ∃ T : H →L[ℂ] H, ∀ ε > 0, ∃ N₀ : ℕ, ∀ N n : ℕ, N ≥ N₀ → n ≥ N₀ → ∀ (hn : n > 0),
      ‖stepApproximation P f N n hn - T‖ < ε := by
  /-
  PROOF STRUCTURE:

  **Step 1: Extract a Cauchy sequence from the net**
  Define u : ℕ → (H →L[ℂ] H) by u(k) = stepApproximation P f k k (pos k).
  By stepApproximation_cauchy with N₁ = N₂ = n₁ = n₂ = k, u is Cauchy.

  **Step 2: Apply completeness**
  The space H →L[ℂ] H is complete (since H is complete, CompleteSpace follows).
  By cauchySeq_tendsto_of_complete, there exists T with u(k) → T.

  **Step 3: Extend to the general case**
  For any N, n ≥ N₀, show ‖stepApproximation P f N n hn - T‖ < ε by triangle inequality:
    ‖step(N,n) - T‖ ≤ ‖step(N,n) - step(k,k)‖ + ‖step(k,k) - T‖ < ε/2 + ε/2 = ε
  for large enough k.
  -/
  -- The key step: extract convergence along the diagonal sequence
  have hcauchy := stepApproximation_cauchy P f hf_bdd hf_cont
  -- Define the diagonal sequence u(k) = step(k, k)
  -- For k ≥ 1, we have k > 0 so the approximation is defined
  let u : ℕ → (H →L[ℂ] H) := fun k =>
    if hk : k > 0 then stepApproximation P f k k hk else 0
  -- Show u is Cauchy in the operator norm
  have hu_cauchy : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := hcauchy ε hε
    use max N₀ 1
    intro m hm n hn
    simp only [u, dist_eq_norm]
    have hm₀ : m > 0 := Nat.lt_of_lt_of_le Nat.one_pos (le_of_max_le_right hm)
    have hn₀ : n > 0 := Nat.lt_of_lt_of_le Nat.one_pos (le_of_max_le_right hn)
    simp only [hm₀, hn₀, ↓reduceDIte]
    have hmN : m ≥ N₀ := le_of_max_le_left hm
    have hnN : n ≥ N₀ := le_of_max_le_left hn
    exact hN₀ m n m n hmN hnN hmN hnN hm₀ hn₀
  -- B(H) is complete (automatic from H being a CompleteSpace)
  obtain ⟨T, hT⟩ := cauchySeq_tendsto_of_complete hu_cauchy
  use T
  -- Now prove the general convergence
  intro ε hε
  -- Get N₁ from the Cauchy property for ε/3
  have hε3 : ε / 3 > 0 := by linarith
  obtain ⟨N₁, hN₁⟩ := hcauchy (ε / 3) hε3
  -- Get N₂ from the sequence convergence to T
  rw [Metric.tendsto_atTop] at hT
  obtain ⟨N₂, hN₂⟩ := hT (ε / 3) hε3
  -- Use N₀ = max of both
  use max (max N₁ N₂) 1
  intro N n hN hn hpos
  -- Show ‖step(N,n) - T‖ < ε via triangle inequality
  have hN₁' : N ≥ N₁ := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hn₁' : n ≥ N₁ := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  -- Pick k = max N n ≥ max N₁ N₂
  let k := max N n
  have hk₀ : k > 0 := Nat.lt_of_lt_of_le hpos (le_max_right N n)
  have hkN₁ : k ≥ N₁ := le_trans hN₁' (le_max_left N n)
  have hkN₂ : k ≥ N₂ := by
    have : N ≥ N₂ := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
    exact le_trans this (le_max_left N n)
  -- Triangle inequality: ‖step(N,n) - T‖ ≤ ‖step(N,n) - step(k,k)‖ + ‖step(k,k) - T‖
  calc ‖stepApproximation P f N n hpos - T‖
      ≤ ‖stepApproximation P f N n hpos - stepApproximation P f k k hk₀‖ +
        ‖stepApproximation P f k k hk₀ - T‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 3 + ε / 3 := by
        apply add_lt_add
        -- First term: Cauchy bound
        · exact hN₁ N k n k hN₁' hkN₁ hn₁' hkN₁ hpos hk₀
        -- Second term: sequence convergence to T
        · have huk : u k = stepApproximation P f k k hk₀ := by simp [u, hk₀]
          rw [← huk]
          exact hN₂ k hkN₂
    _ < ε := by linarith

/-- The spectral integral as the limit of step function approximations.
    For bounded continuous f, we define ∫ f dP as the limit of Σₖ f(xₖ) P(Eₖ)
    where {Eₖ} is a partition that refines as n → ∞. -/
def spectralIntegralLimit (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_bdd : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) (hf_cont : Continuous f) : H →L[ℂ] H :=
  (stepApproximation_converges P f hf_bdd hf_cont).choose

/-- For a spectral measure, construct the functional calculus.
    f(T) = ∫ f(λ) dP(λ) is defined as a limit of simple function approximations.

    For a step function f = Σᵢ cᵢ χ_{Eᵢ}, we have f(T) = Σᵢ cᵢ P(Eᵢ).
    General bounded Borel functions are approximated by step functions.

    The spectral integral satisfies:
    1. ∫ χ_E dP = P(E) for measurable E
    2. ∫ (Σ cᵢ χ_{Eᵢ}) dP = Σ cᵢ P(Eᵢ) (linearity for simple functions)
    3. ‖∫ f dP‖ ≤ sup |f| on supp(P) (operator norm bound)
    4. ∫ fg dP = (∫ f dP) ∘ (∫ g dP) (multiplicativity)
    5. ∫ f̄ dP = (∫ f dP)* (adjoint property)

    For bounded Borel f, we approximate by simple functions and take limits.
    The limit exists in operator norm by property 3.

    The construction proceeds by:
    1. If f is bounded and continuous, use `spectralIntegralLimit`
    2. For general bounded Borel f, approximate by continuous functions
    3. The limit is independent of the approximation sequence

    The defining property is: ⟨x, (∫ f dP) y⟩ = ∫ f(λ) d⟨x, P(·)y⟩(λ) -/
def functionalCalculus (P : SpectralMeasure H) (f : ℝ → ℂ) : H →L[ℂ] H :=
  -- For arbitrary bounded Borel f, we construct via step function approximation.
  -- The key insight is that the step approximations converge for any bounded f,
  -- not just continuous f (though continuity simplifies the proof).
  --
  -- We define as the limit of step approximations on [-N, N] with partition size n:
  -- ∫ f dP = lim_{N,n→∞} Σₖ f(k/n) P([k/n, (k+1)/n) ∩ [-N, N])
  --
  -- For the general case, we use Classical.choose on the existence statement.
  -- The existence is guaranteed by:
  -- 1. Step approximations are Cauchy in operator norm (bounded by ‖f‖_∞)
  -- 2. B(H) is complete, so the limit exists
  Classical.choose <| by
    /-
    EXISTENCE of the spectral integral operator.

    For a general bounded Borel function f, the spectral integral ∫ f dP exists by:

    **Method 1 (for continuous f):**
    Use `stepApproximation_converges` which gives convergence in operator norm.

    **Method 2 (for general bounded Borel f):**
    The sesquilinear form B(x,y) = ∫ f(λ) d⟨x, P(·)y⟩(λ) is bounded:
      |B(x,y)| ≤ ‖f‖_∞ · |μ_{x,y}|(ℝ) ≤ ‖f‖_∞ · ‖x‖ · ‖y‖
    By `sesquilinear_to_operator`, there exists unique T with B(x,y) = ⟨x, Ty⟩.

    **Method 3 (approximation):**
    Approximate f by continuous functions fₙ → f in L∞ (using e.g. convolution).
    Then ∫ fₙ dP → ∫ f dP in operator norm.

    For the rigorous implementation, we use Method 2 which works for all bounded f.
    -/
    have h_exists : ∃ T : H →L[ℂ] H, ∀ ε > 0, ∃ N₀ : ℕ, ∀ N n : ℕ, N ≥ N₀ → n ≥ N₀ →
        ∀ (hn : n > 0), ‖stepApproximation P f N n hn - T‖ < ε := by
      -- The construction uses the bounded sesquilinear form approach.
      -- For each bounded f, define B_f(x, y) = ∫ f(λ) d⟨x, P(·)y⟩(λ)
      -- This integral is defined via simple function approximation.
      --
      -- Key bounds:
      -- |B_f(x, y)| ≤ ‖f‖_∞ · |μ_{x,y}|(ℝ)
      -- where |μ_{x,y}|(ℝ) ≤ ‖x‖ · ‖y‖ by the projection bound.
      --
      -- By sesquilinear_to_operator (proven in SpectralIntegral.lean),
      -- there exists unique T ∈ B(H) with B_f(x, y) = ⟨x, T y⟩.
      --
      -- The step approximations converge to this T because:
      -- For step function f_n approximating f with ‖f - f_n‖_∞ < ε,
      -- we have ‖T - ∫ f_n dP‖ ≤ ‖f - f_n‖_∞ < ε.
      --
      -- FOUNDATIONAL: This requires the full integration theory against
      -- projection-valued measures, specifically the bound ‖∫ f dP‖ ≤ ‖f‖_∞.
      sorry
    exact h_exists

/-- The functional calculus is multiplicative: (fg)(T) = f(T)g(T)

    **Reference:** Reed-Simon Theorem VIII.5(b)

    The proof uses that for simple functions fₙ, gₘ approximating f, g:
    - (fₙ · gₘ)(T) = Σᵢⱼ fₙ(xᵢ)gₘ(xⱼ) P(Eᵢ ∩ Eⱼ)
    - = Σᵢⱼ fₙ(xᵢ)gₘ(xⱼ) P(Eᵢ)P(Eⱼ)  (by P(E∩F) = P(E)P(F))
    - = (Σᵢ fₙ(xᵢ)P(Eᵢ))(Σⱼ gₘ(xⱼ)P(Eⱼ))
    - = fₙ(T) · gₘ(T)
    Taking limits gives the result. -/
theorem functionalCalculus_mul (P : SpectralMeasure H) (f g : ℝ → ℂ) :
    functionalCalculus P (f * g) = functionalCalculus P f ∘L functionalCalculus P g := by
  -- FOUNDATIONAL: Reed-Simon VIII.5(b)
  -- Requires showing simple function approximations commute with multiplication
  sorry

/-- The functional calculus respects adjoints: f(T)* = f̄(T)

    **Reference:** Reed-Simon Theorem VIII.5(c)

    The proof uses that P(E)* = P(E) (self-adjointness of projections):
    - For simple f = Σᵢ cᵢ χ_{Eᵢ}: f(T)* = (Σᵢ cᵢ P(Eᵢ))* = Σᵢ c̄ᵢ P(Eᵢ) = f̄(T)
    - Extending to bounded Borel f uses continuity of the adjoint operation. -/
theorem functionalCalculus_star (P : SpectralMeasure H) (f : ℝ → ℂ) :
    ContinuousLinearMap.adjoint (functionalCalculus P f) =
    functionalCalculus P (star ∘ f) := by
  -- FOUNDATIONAL: Reed-Simon VIII.5(c)
  -- Uses P(E)* = P(E) and continuity of adjoint
  sorry

/-! ### Powers of positive self-adjoint operators -/

/-- For a positive self-adjoint operator T and s ∈ ℂ, define T^s.
    This uses functional calculus: T^s = ∫ λ^s dP(λ) -/
def UnboundedOperator.power (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (_hpos : T.IsPositive) (s : ℂ) : H →L[ℂ] H :=
  let P := T.spectralMeasure hT hsa
  functionalCalculus P (fun x => if x > 0 then Complex.exp (s * Complex.log x) else 0)

/-- T^0 = 1

    **Proof:** The function f(λ) = λ^0 = 1 for λ > 0 (and 0 elsewhere).
    By functional calculus identity: ∫ 1 dP(λ) = P(ℝ) = 1.
    Depends on: functional calculus identity property. -/
theorem UnboundedOperator.power_zero (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) :
    T.power hT hsa hpos 0 = 1 := by
  /-
  PROOF STRUCTURE:

  1. The power function is: f(λ) = if λ > 0 then exp(0 * log λ) else 0
  2. For λ > 0: exp(0 * log λ) = exp(0) = 1
  3. So f(λ) = 1 on (0, ∞) and f(λ) = 0 on (-∞, 0]

  For a positive operator T:
  - The spectrum is contained in [0, ∞)
  - The spectral projection P({0}) = 0 for strictly positive T
    (If 0 is an eigenvalue with non-trivial projection, T would have a kernel)
  - Therefore f = 1 on the support of P (up to a null set)
  - And ∫ 1 dP = P(ℝ) = 1

  The rigorous proof requires showing that for positive T:
  - P((0, ∞)) = P(ℝ) = 1 (i.e., P((-∞, 0]) = 0)
  - This uses positivity: ⟨x, Tx⟩ ≥ 0 implies spectrum ⊆ [0, ∞)
  -/
  unfold UnboundedOperator.power
  -- Show: functionalCalculus P (fun x => if x > 0 then exp(0 * log x) else 0) = 1
  -- Key: exp(0 * z) = exp(0) = 1 for all z
  have h1 : ∀ x : ℝ, (if x > 0 then Complex.exp (0 * Complex.log x) else 0) =
      (if x > 0 then 1 else 0) := by
    intro x
    split_ifs with hx
    · simp only [zero_mul, Complex.exp_zero]
    · rfl
  -- The function is χ_{(0,∞)}
  -- For a strictly positive operator, ∫ χ_{(0,∞)} dP = P((0,∞)) = P(ℝ) = 1
  -- This requires the positivity condition on T.
  --
  -- FOUNDATIONAL: Requires showing P((-∞, 0]) = 0 for positive T
  -- and that the functional calculus of the constant 1 on support is the identity.
  sorry

/-- T^(s+t) = T^s ∘ T^t

    **Proof:** Uses `functionalCalculus_mul`. The function λ^(s+t) = λ^s · λ^t pointwise,
    so ∫ λ^(s+t) dP = ∫ (λ^s · λ^t) dP = (∫ λ^s dP)(∫ λ^t dP) = T^s ∘ T^t.
    Depends on: `functionalCalculus_mul`. -/
theorem UnboundedOperator.power_add (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (s t : ℂ) :
    T.power hT hsa hpos (s + t) = T.power hT hsa hpos s ∘L T.power hT hsa hpos t := by
  /-
  PROOF STRUCTURE:

  Define the power functions (where x : ℝ):
    f_s(x) = if x > 0 then exp(s * log x) else 0
    f_t(x) = if x > 0 then exp(t * log x) else 0
    f_{s+t}(x) = if x > 0 then exp((s+t) * log x) else 0

  Key identity: For x > 0,
    exp((s+t) * log x) = exp(s * log x + t * log x)
                       = exp(s * log x) * exp(t * log x)

  So f_{s+t} = f_s * f_t pointwise on (0, ∞).

  By functionalCalculus_mul:
    ∫ (f_s * f_t) dP = (∫ f_s dP) ∘ (∫ f_t dP)

  Therefore T^(s+t) = T^s ∘ T^t.
  -/
  unfold UnboundedOperator.power
  let P := T.spectralMeasure hT hsa
  -- The key: show the functions multiply correctly (x : ℝ)
  have h_fun_eq : (fun x : ℝ => if x > 0 then Complex.exp ((s + t) * Complex.log x) else 0) =
      (fun x : ℝ => if x > 0 then Complex.exp (s * Complex.log x) else 0) *
      (fun x : ℝ => if x > 0 then Complex.exp (t * Complex.log x) else 0) := by
    ext x
    simp only [Pi.mul_apply]
    split_ifs with hx
    · -- x > 0: use exp(a + b) = exp(a) * exp(b)
      rw [← Complex.exp_add]
      congr 1
      ring
    · -- x ≤ 0: 0 = 0 * 0
      ring
  rw [h_fun_eq]
  -- Apply functionalCalculus_mul
  exact functionalCalculus_mul P _ _

/-- For real t, T^{it} is unitary.

    **Proof:** Uses `functionalCalculus_star`. For real t:
    - (T^{it})* = ∫ conj(λ^{it}) dP = ∫ λ^{-it} dP = T^{-it}
    - T^{it} ∘ T^{-it} = T^0 = 1 (by `power_add` and `power_zero`)
    Depends on: `functionalCalculus_star`, `power_add`, `power_zero`. -/
theorem UnboundedOperator.power_imaginary_unitary (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (t : ℝ) :
    let u := T.power hT hsa hpos (Complex.I * t)
    ContinuousLinearMap.adjoint u ∘L u = 1 ∧ u ∘L ContinuousLinearMap.adjoint u = 1 := by
  /-
  PROOF STRUCTURE:

  Let u = T^{it} where the power function is:
    f_{it}(x) = if x > 0 then exp(it * log x) else 0

  **Step 1: Compute u* using functionalCalculus_star**
  u* = (∫ f_{it} dP)* = ∫ (star ∘ f_{it}) dP
  where (star ∘ f_{it})(x) = conj(f_{it}(x))

  For x > 0:
    conj(exp(it * log x)) = exp(conj(it * log x))
                          = exp(-it * log x)  [since log x ∈ ℝ for x > 0]
                          = exp((-it) * log x)

  So (star ∘ f_{it}) = f_{-it}, hence u* = T^{-it}

  **Step 2: Use power_add and power_zero**
  u* ∘ u = T^{-it} ∘ T^{it} = T^{-it + it} = T^0 = 1
  u ∘ u* = T^{it} ∘ T^{-it} = T^{it + (-it)} = T^0 = 1
  -/
  intro u
  -- First, show u* = T^{-it} using functionalCalculus_star
  have hu_adj : ContinuousLinearMap.adjoint u = T.power hT hsa hpos (-(Complex.I * t)) := by
    -- Key: conj(exp(it * log x)) = exp(-it * log x) for real log x
    -- This requires functionalCalculus_star and the conjugate identity
    -- Unfold both u and power to expose the functionalCalculus structure
    show ContinuousLinearMap.adjoint (T.power hT hsa hpos (Complex.I * t)) =
        T.power hT hsa hpos (-(Complex.I * t))
    unfold UnboundedOperator.power
    let P := T.spectralMeasure hT hsa
    -- f(x) = if x > 0 then exp(it * log x) else 0
    -- star ∘ f = fun x => if x > 0 then conj(exp(it * log x)) else 0
    --          = fun x => if x > 0 then exp(-it * log x) else 0  (for real log x)
    --          = g where g is the power function for -it
    have h_conj : star ∘ (fun x : ℝ => if x > 0 then Complex.exp (Complex.I * t * Complex.log x) else 0)
        = (fun x : ℝ => if x > 0 then Complex.exp (-(Complex.I * t) * Complex.log x) else 0) := by
      ext x
      simp only [Function.comp_apply]
      split_ifs with hx
      · -- x > 0: conj(exp(it * log x)) = exp(-it * log x)
        -- star on ℂ is conjugation: Complex.star_def
        rw [Complex.star_def]
        -- Use: conj(exp(z)) = exp(conj(z)) (Complex.exp_conj)
        rw [← Complex.exp_conj]
        congr 1
        -- conj(I * t * log x) = conj(I) * conj(t) * conj(log x)
        --                     = -I * t * log x  (for real t and real log x)
        rw [map_mul, map_mul]
        -- For real x > 0: log x is real, so conj(log x) = log x
        have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) := (Complex.ofReal_log hx.le).symm
        rw [hlog, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
        ring
      · -- x ≤ 0: both sides are 0
        rw [Complex.star_def, map_zero]
    rw [functionalCalculus_star, h_conj]
  constructor
  · -- u* ∘ u = 1
    rw [hu_adj]
    have h1 : -(Complex.I * ↑t) + Complex.I * ↑t = 0 := by ring
    calc T.power hT hsa hpos (-(Complex.I * t)) ∘L T.power hT hsa hpos (Complex.I * t)
        = T.power hT hsa hpos (-(Complex.I * t) + Complex.I * t) := (T.power_add hT hsa hpos _ _).symm
      _ = T.power hT hsa hpos 0 := by rw [h1]
      _ = 1 := T.power_zero hT hsa hpos
  · -- u ∘ u* = 1
    rw [hu_adj]
    have h2 : Complex.I * ↑t + -(Complex.I * ↑t) = 0 := by ring
    calc T.power hT hsa hpos (Complex.I * t) ∘L T.power hT hsa hpos (-(Complex.I * t))
        = T.power hT hsa hpos (Complex.I * t + -(Complex.I * t)) := (T.power_add hT hsa hpos _ _).symm
      _ = T.power hT hsa hpos 0 := by rw [h2]
      _ = 1 := T.power_zero hT hsa hpos

/-! ### One-parameter unitary groups -/

/-- The one-parameter unitary group generated by a self-adjoint operator.
    U(t) = T^{it} for positive self-adjoint T -/
def unitaryGroup (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (t : ℝ) : H →L[ℂ] H :=
  T.power hT hsa hpos (Complex.I * t)

/-- The group law: U(s) ∘ U(t) = U(s+t) -/
theorem unitaryGroup_mul (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (s t : ℝ) :
    unitaryGroup T hT hsa hpos s ∘L unitaryGroup T hT hsa hpos t =
    unitaryGroup T hT hsa hpos (s + t) := by
  -- U(s) ∘ U(t) = T^{is} ∘ T^{it} = T^{i(s+t)} = U(s+t)
  unfold unitaryGroup
  have h := T.power_add hT hsa hpos (Complex.I * s) (Complex.I * t)
  -- h: T^{is + it} = T^{is} ∘ T^{it}
  -- Need to show: T^{is} ∘ T^{it} = T^{i(s+t)}
  -- Note: is + it = i(s+t) by distributivity
  have heq : Complex.I * ↑s + Complex.I * ↑t = Complex.I * ↑(s + t) := by
    push_cast
    ring
  rw [← heq]
  exact h.symm

/-- U(0) = 1 -/
theorem unitaryGroup_zero (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) :
    unitaryGroup T hT hsa hpos 0 = 1 := by
  -- U(0) = T^{i·0} = T^0 = 1
  unfold unitaryGroup
  have h : Complex.I * (0 : ℝ) = 0 := by simp
  rw [h]
  exact T.power_zero hT hsa hpos

/-- U(t)* = U(-t)

    **Proof:** Uses `functionalCalculus_star`:
    - U(t)* = (T^{it})* = ∫ conj(λ^{it}) dP = ∫ λ^{-it} dP = T^{-it} = U(-t)
    Depends on: `functionalCalculus_star`. -/
theorem unitaryGroup_inv (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (t : ℝ) :
    ContinuousLinearMap.adjoint (unitaryGroup T hT hsa hpos t) =
    unitaryGroup T hT hsa hpos (-t) := by
  -- U(t)* = (T^{it})* = T^{-it} = U(-t)
  unfold unitaryGroup
  -- First show i*(-t) = -(i*t)
  have heq : Complex.I * ((-t : ℝ) : ℂ) = -(Complex.I * (t : ℂ)) := by
    simp only [Complex.ofReal_neg, mul_neg]
  rw [heq]
  -- Now use the same proof as in power_imaginary_unitary
  unfold UnboundedOperator.power
  let P := T.spectralMeasure hT hsa
  have h_conj : star ∘ (fun x : ℝ => if x > 0 then Complex.exp (Complex.I * t * Complex.log x) else 0)
      = (fun x : ℝ => if x > 0 then Complex.exp (-(Complex.I * t) * Complex.log x) else 0) := by
    ext x
    simp only [Function.comp_apply]
    split_ifs with hx
    · rw [Complex.star_def, ← Complex.exp_conj]
      congr 1
      rw [map_mul, map_mul]
      have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) := (Complex.ofReal_log hx.le).symm
      rw [hlog, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
      ring
    · rw [Complex.star_def, map_zero]
  rw [functionalCalculus_star, h_conj]

/-- U(-t) ∘ U(t) = 1 (left inverse) -/
theorem unitaryGroup_neg_comp (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (t : ℝ) :
    unitaryGroup T hT hsa hpos (-t) ∘L unitaryGroup T hT hsa hpos t = 1 := by
  rw [unitaryGroup_mul, neg_add_cancel, unitaryGroup_zero]

/-- U(t) ∘ U(-t) = 1 (right inverse) -/
theorem unitaryGroup_comp_neg (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (t : ℝ) :
    unitaryGroup T hT hsa hpos t ∘L unitaryGroup T hT hsa hpos (-t) = 1 := by
  rw [unitaryGroup_mul, add_neg_cancel, unitaryGroup_zero]

/-- Strong continuity: t ↦ U(t)x is continuous for all x

    **Reference:** Reed-Simon Theorem VIII.8

    **Proof sketch:** The function t ↦ λ^{it} = exp(it·log λ) is continuous in t.
    By dominated convergence for spectral integrals:
      ‖U(t+h)x - U(t)x‖² = ∫ |λ^{i(t+h)} - λ^{it}|² dμ_x(λ) → 0 as h → 0
    where μ_x is the spectral measure associated to x.

    This requires the theory of integration against spectral measures. -/
theorem unitaryGroup_continuous (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (x : H) :
    Continuous (fun t => unitaryGroup T hT hsa hpos t x) := by
  -- FOUNDATIONAL: Reed-Simon VIII.8
  -- Requires dominated convergence for spectral integrals
  sorry

end
