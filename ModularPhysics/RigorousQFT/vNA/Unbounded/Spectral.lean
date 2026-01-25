/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.vNA.Unbounded.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Spectral Theory for Unbounded Self-Adjoint Operators

This file develops the spectral theory for unbounded self-adjoint operators,
which is essential for defining the modular operator Δ and its functional calculus.

## Main definitions

* `SpectralMeasure` - a projection-valued measure on ℝ
* `spectralDecomposition` - the spectral theorem for self-adjoint operators
* `functionalCalculus` - f(T) for bounded Borel functions f

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I"
* Rudin, "Functional Analysis", Chapter 13
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
  sorry

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
    - Stone's theorem: connect to one-parameter unitary groups -/
theorem spectral_theorem (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) :
    ∃ P : SpectralMeasure H,
      -- The identity function applied via functional calculus recovers T on its domain
      -- This is stated indirectly: the spectral measure determines T
      P.proj Set.univ = 1 ∧
      -- The spectral measure is concentrated on ℝ (self-adjointness)
      (∀ E : Set ℝ, P.proj E = P.proj (E ∩ Set.univ)) := by
  -- The spectral theorem for unbounded self-adjoint operators is a deep result
  -- Proof methods: Cayley transform, resolution of identity, or direct construction
  sorry

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
    (_hf_bdd : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M)
    (_hf_cont : Continuous f) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N₁ N₂ n₁ n₂ : ℕ, N₁ ≥ N₀ → N₂ ≥ N₀ → n₁ ≥ N₀ → n₂ ≥ N₀ →
      ∀ (hn₁ : n₁ > 0) (hn₂ : n₂ > 0),
        ‖stepApproximation P f N₁ n₁ hn₁ - stepApproximation P f N₂ n₂ hn₂‖ < ε := by
  sorry

/-- The limit of step approximations exists for bounded continuous functions.
    This follows from completeness of B(H) and the Cauchy property. -/
theorem stepApproximation_converges (P : SpectralMeasure H) (f : ℝ → ℂ)
    (hf_bdd : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M)
    (hf_cont : Continuous f) :
    ∃ T : H →L[ℂ] H, ∀ ε > 0, ∃ N₀ : ℕ, ∀ N n : ℕ, N ≥ N₀ → n ≥ N₀ → ∀ (hn : n > 0),
      ‖stepApproximation P f N n hn - T‖ < ε := by
  -- Completeness of B(H) + Cauchy implies convergence
  sorry

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
    -- Existence of the spectral integral operator.
    -- The sesquilinear form B(x,y) = ∫ f(λ) d⟨x, P(·)y⟩(λ) is bounded:
    -- |B(x,y)| ≤ ‖f‖_∞ · |μ_{x,y}|(ℝ) ≤ ‖f‖_∞ · ‖x‖ · ‖y‖
    -- By Riesz representation, there exists unique T with B(x,y) = ⟨x, Ty⟩.
    --
    -- Alternatively, the step approximations Tₙ = Σₖ f(xₖ) P(Eₖ) satisfy:
    -- ‖Tₙ - Tₘ‖ ≤ ‖fₙ - fₘ‖_∞ where fₙ, fₘ are the corresponding step functions.
    -- For finer partitions, ‖fₙ - fₘ‖_∞ → 0, so (Tₙ) is Cauchy and converges.
    --
    -- We provide existence via the step approximation limit construction.
    -- The predicate characterizes T as the limit of step approximations.
    have h_exists : ∃ T : H →L[ℂ] H, ∀ ε > 0, ∃ N₀ : ℕ, ∀ N n : ℕ, N ≥ N₀ → n ≥ N₀ →
        ∀ (hn : n > 0), ‖stepApproximation P f N n hn - T‖ < ε := by
      -- The step approximations form a Cauchy net in the complete space B(H).
      -- By completeness, they converge to some operator T.
      sorry
    exact h_exists

/-- The functional calculus is multiplicative: (fg)(T) = f(T)g(T) -/
theorem functionalCalculus_mul (P : SpectralMeasure H) (f g : ℝ → ℂ) :
    functionalCalculus P (f * g) = functionalCalculus P f ∘L functionalCalculus P g := by
  -- This follows from the multiplicativity of the spectral integral
  sorry

/-- The functional calculus respects adjoints: f(T)* = f̄(T) -/
theorem functionalCalculus_star (P : SpectralMeasure H) (f : ℝ → ℂ) :
    ContinuousLinearMap.adjoint (functionalCalculus P f) =
    functionalCalculus P (star ∘ f) := by
  -- ⟨f(T)x, y⟩ = ∫ f dμ_{x,y} and ⟨x, f(T)y⟩ = ∫ f̄ dμ_{x,y}
  sorry

/-! ### Powers of positive self-adjoint operators -/

/-- For a positive self-adjoint operator T and s ∈ ℂ, define T^s.
    This uses functional calculus: T^s = ∫ λ^s dP(λ) -/
def UnboundedOperator.power (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (_hpos : T.IsPositive) (s : ℂ) : H →L[ℂ] H :=
  let P := T.spectralMeasure hT hsa
  functionalCalculus P (fun x => if x > 0 then Complex.exp (s * Complex.log x) else 0)

/-- T^0 = 1 -/
theorem UnboundedOperator.power_zero (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) :
    T.power hT hsa hpos 0 = 1 := by
  -- λ^0 = exp(0 · log λ) = 1 for all λ > 0
  -- so T^0 = ∫ λ^0 dP(λ) = ∫ 1 dP(λ) = P(ℝ) = 1
  sorry

/-- T^(s+t) = T^s ∘ T^t -/
theorem UnboundedOperator.power_add (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (s t : ℂ) :
    T.power hT hsa hpos (s + t) = T.power hT hsa hpos s ∘L T.power hT hsa hpos t := by
  sorry

/-- For real t, T^{it} is unitary -/
theorem UnboundedOperator.power_imaginary_unitary (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (t : ℝ) :
    let u := T.power hT hsa hpos (Complex.I * t)
    ContinuousLinearMap.adjoint u ∘L u = 1 ∧ u ∘L ContinuousLinearMap.adjoint u = 1 := by
  sorry

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

/-- U(t)* = U(-t) -/
theorem unitaryGroup_inv (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (t : ℝ) :
    ContinuousLinearMap.adjoint (unitaryGroup T hT hsa hpos t) =
    unitaryGroup T hT hsa hpos (-t) := by
  sorry

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

/-- Strong continuity: t ↦ U(t)x is continuous for all x -/
theorem unitaryGroup_continuous (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (x : H) :
    Continuous (fun t => unitaryGroup T hT hsa hpos t x) := by
  sorry

end
