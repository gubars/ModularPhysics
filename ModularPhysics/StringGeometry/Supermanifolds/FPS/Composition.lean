/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import ModularPhysics.StringGeometry.Supermanifolds.FPS.Basic

/-!
# Composition of Formal Power Series

This file develops the theory of composition for formal power series,
following Propositions 7.15 and 7.16 from the Waterloo C&O 430 notes.

## When is Composition Well-Defined?

Given f(x) = Σ aₙxⁿ and g(x) = Σ bⱼxʲ, the composition f(g(x)) is defined as
  f(g(x)) := Σₙ aₙ g(x)ⁿ = lim_{K→∞} Σₙ₌ᵢ₍ₖ₎^K aₙ g(x)ⁿ

**Proposition 7.15**: f(g(x)) is well-defined iff one of:
  (i)   g(x) = 0 and I(f) ≥ 0
  (ii)  g(x) ≠ 0 and f(x) has finitely many nonzero coefficients (i.e., f is polynomial)
  (iii) g(x) ≠ 0 and I(g) > 0 (g has no constant term)

The key insight: when I(g) > 0, each coefficient of the composition receives
contributions from only finitely many terms, making the limit well-defined.

## References

* Waterloo C&O 430 notes, Section 7, Propositions 7.15 and 7.16
-/

namespace FPSComposition

open PowerSeries Finset

variable {R : Type*} [CommRing R]

/-! ### Condition for Composition -/

/-- Condition for composition to be well-defined: g has positive index (no constant term).
    This is condition (iii) of Proposition 7.15. -/
def CompositionWellDefined (g : R⟦X⟧) : Prop :=
  constantCoeff g = 0

theorem X_composition_well_defined : CompositionWellDefined (X : R⟦X⟧) :=
  constantCoeff_X

/-- When g has no constant term, the n-th coefficient of g^k is zero for k > n.
    This is why composition is well-defined when I(g) > 0. -/
theorem coeff_pow_eq_zero_of_gt (g : R⟦X⟧) (hg : CompositionWellDefined g)
    (n k : ℕ) (hkn : n < k) : coeff n (g ^ k) = 0 := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    rw [pow_succ, coeff_mul]
    apply sum_eq_zero
    intro ⟨i, j⟩ hij
    simp only [mem_antidiagonal] at hij
    by_cases hik : i < k
    · simp only [ih i hik, zero_mul]
    · push_neg at hik
      have hj : j = 0 := by omega
      subst hj
      rw [coeff_zero_eq_constantCoeff, hg, mul_zero]

/-! ### Powers of series with positive index -/

/-- g^k has index at least k when g has positive index. -/
theorem order_pow_ge (g : R⟦X⟧) (hg : CompositionWellDefined g) (k : ℕ) :
    ∀ n < k, coeff n (g ^ k) = 0 := fun n hn => coeff_pow_eq_zero_of_gt g hg n k hn

/-- The coefficient [x^n] in the finite sum Σ_{k=0}^N a_k g^k stabilizes for N > n
    when g has positive index. This is the key lemma for composition. -/
theorem coeff_sum_pow_stabilizes (f : R⟦X⟧) (g : R⟦X⟧) (hg : CompositionWellDefined g)
    (n N : ℕ) (hN : n < N) :
    coeff n (∑ k ∈ range (N + 1), coeff k f • g ^ k) =
    coeff n (∑ k ∈ range (n + 1), coeff k f • g ^ k) := by
  have h_split : range (N + 1) = range (n + 1) ∪ Ico (n + 1) (N + 1) := by
    ext m; simp only [mem_union, mem_range, mem_Ico]; omega
  have h_disj : Disjoint (range (n + 1)) (Ico (n + 1) (N + 1)) := by
    simp only [disjoint_left, mem_range, mem_Ico, not_and]
    intro m hm hn_le _
    omega
  rw [h_split, sum_union h_disj]
  simp only [map_add]
  suffices h : coeff n (∑ k ∈ Ico (n + 1) (N + 1), coeff k f • g ^ k) = 0 by
    rw [h, add_zero]
  rw [map_sum]
  apply sum_eq_zero
  intro k hk
  simp only [mem_Ico] at hk
  rw [coeff_smul, coeff_pow_eq_zero_of_gt g hg n k hk.1, smul_zero]

end FPSComposition
