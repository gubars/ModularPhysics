/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Real.Basic

/-!
# Basic Definitions for Stochastic PDEs

This file provides foundational definitions for stochastic analysis
needed for SPDEs and regularity structures.

## Main Definitions

* `Filtration` - A filtration on a measurable space
* `AdaptedProcess` - Processes adapted to a filtration
* `Martingale` - Martingale processes
* `StoppingTime` - Stopping times

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus"
* Da Prato, Zabczyk, "Stochastic Equations in Infinite Dimensions"
-/

namespace SPDE

open MeasureTheory
open scoped MeasureTheory

/-! ## Filtrations -/

/-- A filtration is an increasing family of σ-algebras indexed by time. -/
structure Filtration (Ω : Type*) [MeasurableSpace Ω] (ι : Type*) [Preorder ι] where
  /-- The σ-algebra at time t -/
  σ_algebra : ι → MeasurableSpace Ω
  /-- The filtration is increasing -/
  mono : ∀ s t : ι, s ≤ t → σ_algebra s ≤ σ_algebra t
  /-- Each σ-algebra is a sub-σ-algebra of the ambient one -/
  le_ambient : ∀ t : ι, σ_algebra t ≤ ‹MeasurableSpace Ω›

namespace Filtration

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ι : Type*} [Preorder ι]

/-- Right-continuous filtration -/
def rightContinuous [TopologicalSpace ι] [OrderTopology ι]
    (F : Filtration Ω ι) : Prop :=
  ∀ t : ι, F.σ_algebra t = ⨅ s > t, F.σ_algebra s

/-- Usual conditions: right-continuous and complete -/
def usualConditions [TopologicalSpace ι] [OrderTopology ι]
    (F : Filtration Ω ι) (μ : Measure Ω) : Prop :=
  F.rightContinuous ∧ ∀ t, ∀ s : Set Ω, μ s = 0 → MeasurableSet[F.σ_algebra t] s

end Filtration

/-! ## Adapted Processes -/

/-- A process X is adapted to a filtration F if X_t is F_t-measurable for all t. -/
structure AdaptedProcess {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Preorder ι]
    (F : Filtration Ω ι)
    (E : Type*) [MeasurableSpace E] where
  /-- The process X : ι → Ω → E -/
  process : ι → Ω → E
  /-- X_t is F_t-measurable -/
  adapted : ∀ t : ι, @Measurable Ω E (F.σ_algebra t) _ (process t)

namespace AdaptedProcess

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ι : Type*} [Preorder ι]
variable {E : Type*} [MeasurableSpace E]
variable {F : Filtration Ω ι}

/-- The process at time t -/
def apply (X : AdaptedProcess F E) (t : ι) : Ω → E := X.process t

/-- Constant process -/
def const (F : Filtration Ω ι) (x : E) : AdaptedProcess F E where
  process := fun _ _ => x
  adapted := fun _ => measurable_const

end AdaptedProcess

/-! ## Stopping Times -/

/-- A stopping time with respect to a filtration F. -/
structure StoppingTime {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Preorder ι]
    (F : Filtration Ω ι) where
  /-- The random time τ : Ω → ι -/
  time : Ω → ι
  /-- {τ ≤ t} is F_t-measurable for all t -/
  measurable : ∀ t : ι, @MeasurableSet Ω (F.σ_algebra t) {ω | time ω ≤ t}

namespace StoppingTime

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ι : Type*} [Preorder ι]
variable {F : Filtration Ω ι}

/-- Constant stopping time -/
def const (F : Filtration Ω ι) (t₀ : ι) : StoppingTime F where
  time := fun _ => t₀
  measurable := fun t => by
    by_cases h : t₀ ≤ t
    · convert MeasurableSet.univ
      ext ω
      simp [h]
    · convert MeasurableSet.empty
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h'
      exact h h'

/-- The minimum of two stopping times.
    Note: We require LinearOrder instead of just SemilatticeInf to use min_le_iff. -/
def min {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [LinearOrder ι]
    {F : Filtration Ω ι} (τ₁ τ₂ : StoppingTime F) : StoppingTime F where
  time := fun ω => Min.min (τ₁.time ω) (τ₂.time ω)
  measurable := fun t => by
    have h1 := τ₁.measurable t
    have h2 := τ₂.measurable t
    -- min a b ≤ c iff a ≤ c or b ≤ c
    have : {ω | Min.min (τ₁.time ω) (τ₂.time ω) ≤ t} =
           {ω | τ₁.time ω ≤ t} ∪ {ω | τ₂.time ω ≤ t} := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_union, min_le_iff]
    rw [this]
    exact MeasurableSet.union h1 h2

end StoppingTime

/-! ## Martingales -/

/-- A martingale with respect to filtration F and measure μ. -/
structure Martingale {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Preorder ι]
    (F : Filtration Ω ι) (μ : Measure Ω)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] where
  /-- The underlying adapted process -/
  toAdapted : AdaptedProcess F E
  /-- Integrability: E[|X_t|] < ∞ for all t -/
  integrable : ∀ t : ι, Integrable (toAdapted.process t) μ
  /-- Martingale property: E[X_t | F_s] = X_s for s ≤ t.
      Expressed as: for all F_s-measurable A, ∫_A X_t dμ = ∫_A X_s dμ -/
  martingale_property : ∀ s t : ι, s ≤ t →
    ∀ A : Set Ω, @MeasurableSet Ω (F.σ_algebra s) A →
    ∫ ω, toAdapted.process t ω ∂(μ.restrict A) =
    ∫ ω, toAdapted.process s ω ∂(μ.restrict A)

namespace Martingale

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ι : Type*} [Preorder ι]
variable {F : Filtration Ω ι}
variable {μ : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

/-- The process underlying a martingale -/
def process (M : Martingale F μ E) : ι → Ω → E := M.toAdapted.process

/-- A constant is a martingale -/
def const (F : Filtration Ω ι) (μ : Measure Ω) [IsProbabilityMeasure μ] (x : E) :
    Martingale F μ E where
  toAdapted := AdaptedProcess.const F x
  integrable := fun _ => ⟨aestronglyMeasurable_const, hasFiniteIntegral_const x⟩
  martingale_property := fun _ _ _ _ _ => rfl

end Martingale

/-! ## Submartingales and Supermartingales -/

/-- A submartingale: E[X_t | F_s] ≥ X_s for s ≤ t.
    Expressed via the integral characterization: for all F_s-measurable A,
    ∫_A X_s dμ ≤ ∫_A X_t dμ. -/
structure Submartingale {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Preorder ι]
    (F : Filtration Ω ι) (μ : Measure Ω)
    [MeasurableSpace ℝ] where
  toAdapted : AdaptedProcess F ℝ
  integrable : ∀ t : ι, Integrable (toAdapted.process t) μ
  /-- The submartingale property via conditional expectation:
      for all F_s-measurable sets A, ∫_A X_s dμ ≤ ∫_A X_t dμ -/
  submartingale_property : ∀ s t : ι, s ≤ t →
    ∀ A : Set Ω, @MeasurableSet Ω (F.σ_algebra s) A →
    ∫ ω, toAdapted.process s ω ∂(μ.restrict A) ≤
    ∫ ω, toAdapted.process t ω ∂(μ.restrict A)

/-- A supermartingale: E[X_t | F_s] ≤ X_s for s ≤ t.
    Expressed via the integral characterization: for all F_s-measurable A,
    ∫_A X_s dμ ≥ ∫_A X_t dμ. -/
structure Supermartingale {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Preorder ι]
    (F : Filtration Ω ι) (μ : Measure Ω)
    [MeasurableSpace ℝ] where
  toAdapted : AdaptedProcess F ℝ
  integrable : ∀ t : ι, Integrable (toAdapted.process t) μ
  /-- The supermartingale property via conditional expectation:
      for all F_s-measurable sets A, ∫_A X_s dμ ≥ ∫_A X_t dμ -/
  supermartingale_property : ∀ s t : ι, s ≤ t →
    ∀ A : Set Ω, @MeasurableSet Ω (F.σ_algebra s) A →
    ∫ ω, toAdapted.process s ω ∂(μ.restrict A) ≥
    ∫ ω, toAdapted.process t ω ∂(μ.restrict A)

/-! ## Quadratic Variation -/

/-- The quadratic variation of a process -/
structure QuadraticVariation {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration Ω ℝ) where
  /-- The original process -/
  process : ℝ → Ω → ℝ
  /-- The quadratic variation process ⟨X⟩_t -/
  variation : ℝ → Ω → ℝ
  /-- The quadratic variation is adapted -/
  adapted : ∀ t : ℝ, @Measurable Ω ℝ (F.σ_algebra t) _ (variation t)
  /-- Non-decreasing in t -/
  mono : ∀ ω : Ω, Monotone (fun t => variation t ω)
  /-- Initial condition -/
  initial : ∀ ω : Ω, variation 0 ω = 0

/-- The covariation of two processes -/
noncomputable def covariation {Ω : Type*} (X Y : ℝ → Ω → ℝ) : ℝ → Ω → ℝ :=
  fun t ω => (1/4) * ((fun t => (X t ω + Y t ω)^2) t -
                       (fun t => (X t ω - Y t ω)^2) t)

/-! ## Predictable Processes -/

/-- A predictable process (left-continuous adapted process) -/
structure PredictableProcess {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration Ω ℝ) (E : Type*) [MeasurableSpace E] [TopologicalSpace E] where
  /-- The process -/
  process : ℝ → Ω → E
  /-- Adapted to F -/
  adapted : ∀ t : ℝ, @Measurable Ω E (F.σ_algebra t) _ (process t)
  /-- Left-continuous (pointwise) -/
  left_continuous : ∀ ω : Ω, ∀ t : ℝ, Filter.Tendsto
    (fun s => process s ω) (nhdsWithin t (Set.Iio t)) (nhds (process t ω))

/-! ## Local Martingales -/

/-- A local martingale: a process that is a martingale when stopped -/
structure LocalMartingale {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration Ω ℝ) (μ : Measure Ω)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] where
  /-- The underlying process -/
  process : ℝ → Ω → E
  /-- Adapted to F -/
  adapted : ∀ t : ℝ, @Measurable Ω E (F.σ_algebra t) _ (process t)
  /-- There exists a localizing sequence of stopping times -/
  localizing_sequence : ∃ (τ : ℕ → StoppingTime F),
    (∀ n : ℕ, ∀ ω : Ω, (τ n).time ω ≤ (τ (n + 1)).time ω) ∧
    (∀ ω : Ω, Filter.Tendsto (fun n => (τ n).time ω) Filter.atTop Filter.atTop)

end SPDE
