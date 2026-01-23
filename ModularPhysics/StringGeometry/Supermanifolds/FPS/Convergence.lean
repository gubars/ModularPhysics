/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Convergence of Sequences of Formal Power Series

This file develops the theory of convergence for sequences of formal power series,
following Definition 7.10 from the Waterloo C&O 430 notes.

## Key Concept

**IMPORTANT**: Convergence of formal power series is NOT the same as convergence
of real numbers! A sequence (f₁, f₂, f₃, ...) of formal power series converges
if and only if for each coefficient position n, the sequence of n-th coefficients
is *eventually constant*.

## Definition 7.10 (Waterloo Notes)

A sequence (fₖ)_{k∈ℕ} of formal power series in R[[x]] is convergent provided:
1. There is a uniform lower bound J for the indices I(fₖ)
2. For every n ∈ ℕ, there exists Kₙ ∈ ℕ and Aₙ ∈ R such that
   if k ≥ Kₙ then [xⁿ]fₖ(x) = Aₙ

The second condition says the n-th coefficient sequence is eventually constant.

## Examples (from Waterloo notes)

* lim_{k→∞} xᵏ = 0 ✓ (converges)
* lim_{k→∞} x⁻ᵏ does not exist (for Laurent series)
* lim_{k→∞} (1 + x + ⋯ + xᵏ) = 1/(1-x) ✓
* lim_{k→∞} 1/(1 - x/k) does not exist! (coefficient of x is 1/k, not eventually constant)

## References

* Waterloo C&O 430 notes, Section 7, Definition 7.10
-/

namespace FPSConvergence

open PowerSeries Finset

variable {R : Type*} [CommRing R]

/-! ### Eventually Constant Sequences -/

/-- A sequence of ring elements is eventually constant at value `a` starting from `K`. -/
def EventuallyConstantAt (s : ℕ → R) (a : R) (K : ℕ) : Prop :=
  ∀ k, K ≤ k → s k = a

/-- A sequence is eventually constant if it equals some value from some point onward. -/
def EventuallyConstant (s : ℕ → R) : Prop :=
  ∃ a K, EventuallyConstantAt s a K

/-- If a sequence is eventually constant, extract the limiting value. -/
noncomputable def eventualValue (s : ℕ → R) (h : EventuallyConstant s) : R :=
  h.choose

omit [CommRing R] in
theorem eventualValue_spec (s : ℕ → R) (h : EventuallyConstant s) :
    ∃ K, EventuallyConstantAt s (eventualValue s h) K := by
  unfold eventualValue
  exact ⟨h.choose_spec.choose, h.choose_spec.choose_spec⟩

/-! ### Convergence of FPS Sequences -/

/-- A sequence of formal power series converges if each coefficient sequence
    is eventually constant. This is Definition 7.10 from the Waterloo notes. -/
def Converges (f : ℕ → R⟦X⟧) : Prop :=
  ∀ n : ℕ, EventuallyConstant (fun k => coeff n (f k))

/-- The limit of a convergent sequence of formal power series.
    The n-th coefficient of the limit is the eventual value of the n-th coefficient sequence. -/
noncomputable def limit (f : ℕ → R⟦X⟧) (hf : Converges f) : R⟦X⟧ :=
  mk fun n => eventualValue (fun k => coeff n (f k)) (hf n)

/-- The coefficient of xⁿ in the limit equals the eventual value of the
    coefficient sequence. -/
theorem coeff_limit (f : ℕ → R⟦X⟧) (hf : Converges f) (n : ℕ) :
    coeff n (limit f hf) = eventualValue (fun k => coeff n (f k)) (hf n) := by
  unfold limit
  simp only [coeff_mk]

/-! ### Examples of Convergence -/

/-- Example 7.11(a): The sequence xᵏ converges to 0 in R[[x]].
    For any n, [xⁿ]xᵏ = 0 for all k > n. -/
theorem converges_X_pow : Converges (fun k => (X : R⟦X⟧)^k) := by
  intro n
  use 0, n + 1
  intro k hk
  simp only [coeff_X_pow]
  split_ifs with h
  · omega
  · rfl

/-! ### Properties of Convergent Sequences -/

/-- The constant sequence converges to its constant value. -/
theorem converges_const (f : R⟦X⟧) : Converges (fun _ => f) := by
  intro n
  use coeff n f, 0
  intro k _
  rfl

end FPSConvergence
