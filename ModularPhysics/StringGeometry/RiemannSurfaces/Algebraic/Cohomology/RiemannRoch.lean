import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.Cohomology.AlgebraicCech
import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.Cohomology.PointExactSequence

/-!
# Riemann-Roch Theorem for Algebraic Curves

This file proves the Riemann-Roch theorem using the infrastructure from AlgebraicCech.

## Main Theorems

* `LES_exactness_constraint` - The key formula a + b = 1 from the LES exactness
* `point_exact_dimension_formula` - The dimension formula for point exact sequence
* `eulerChar_point_exact` - χ(D) - χ(D-p) = 1
* `riemann_roch_algebraic` - χ(D) = deg(D) + 1 - g

## Proof Strategy

The proof uses induction on divisor support with the key step being χ(D) - χ(D-p) = 1.

This follows from the **long exact sequence** in sheaf cohomology for
0 → O(D-p) → O(D) → ℂ_p → 0. The LES is exact by abstract homological algebra
(sheaf cohomology is a delta functor). The alternating sum formula for exact
sequences gives the dimension constraint directly.

**Key insight**: No case analysis on (0,0) or (1,1) quotient dimensions is needed.
The formula a + b = 1 is a **consequence** of LES exactness, not something to be
proven by ruling out cases.
-/

namespace RiemannSurfaces.Algebraic.Cohomology

open Algebraic CompactAlgebraicCurve Core.Divisor
open scoped Classical

/-- Key exactness lemma: a + b = 1 from the LES.

    **Mathematical content**: The short exact sequence of sheaves
      0 → O(D-p) → O(D) → ℂ_p → 0
    induces a long exact sequence in cohomology:
      0 → H⁰(D-p) → H⁰(D) → H⁰(ℂ_p) → H¹(D-p) → H¹(D) → H¹(ℂ_p) → 0

    For a curve (H^i = 0 for i ≥ 2) with H⁰(ℂ_p) = ℂ and H¹(ℂ_p) = 0:
      0 → H⁰(D-p) → H⁰(D) → ℂ → H¹(D-p) → H¹(D) → 0

    The **alternating sum formula** for any exact sequence of finite-dimensional
    vector spaces 0 → V₁ → V₂ → ... → Vₙ → 0 gives Σ(-1)ⁱ dim(Vᵢ) = 0.

    Applied here (with h¹(E) = h⁰(K-E) by Serre duality):
      h⁰(D-p) - h⁰(D) + 1 - h⁰(K-D+p) + h⁰(K-D) = 0

    Rearranging: (h⁰(D) - h⁰(D-p)) + (h⁰(K-D+p) - h⁰(K-D)) = 1, i.e., a + b = 1.

    **Proof approach**: The LES is exact by the definition of sheaf cohomology
    (as a delta functor / derived functor). The formula follows directly from
    exactness; no case analysis on (0,0) or (1,1) is needed. -/
private theorem LES_exactness_constraint (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) :
    (h0 C D : ℤ) - h0 C (D - Core.Divisor.point p) +
    (h0 C (K.K - D + Core.Divisor.point p) : ℤ) - h0 C (K.K - D) = 1 := by
  -- Use the theorem from PointExactSequence
  -- The finite-dimensionality instances are automatically inferred
  haveI : FiniteDimensional ℂ (RiemannRochSubmodule C (D - Core.Divisor.point p)) :=
    RiemannRochSubmodule_finiteDimensional C (D - Core.Divisor.point p)
  haveI : FiniteDimensional ℂ (RiemannRochSubmodule C D) :=
    RiemannRochSubmodule_finiteDimensional C D
  haveI : FiniteDimensional ℂ (RiemannRochSubmodule C (K.K - D + Core.Divisor.point p)) :=
    RiemannRochSubmodule_finiteDimensional C (K.K - D + Core.Divisor.point p)
  haveI : FiniteDimensional ℂ (RiemannRochSubmodule C (K.K - D)) :=
    RiemannRochSubmodule_finiteDimensional C (K.K - D)
  exact PointExactSequence.LES_dimension_constraint C K D p

/-- **Point exact dimension formula**: The sum of quotient dimensions equals 1.

    This is a direct consequence of `LES_exactness_constraint`. -/
theorem point_exact_dimension_formula (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) :
    (h0 C D : ℤ) - h0 C (D - Core.Divisor.point p) +
    (h0 C (K.K - D + Core.Divisor.point p) : ℤ) - h0 C (K.K - D) = 1 :=
  LES_exactness_constraint C K D p

-- Helper: K - (D - p) = K - D + p
private theorem canonical_sub_sub (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) :
    K.K - (D - Core.Divisor.point p) = K.K - D + Core.Divisor.point p := by
  ext q
  simp only [Core.Divisor.add_coeff, Core.Divisor.sub_coeff, Core.Divisor.point]
  ring

/-- **Point exact sequence**: χ(D) - χ(D - p) = 1.

    **Proof**: From the short exact sequence 0 → O(D-p) → O(D) → ℂ_p → 0, we get
    the long exact sequence in cohomology. The key formula is:
      (h⁰(D) - h⁰(D-p)) + (h⁰(K-D+p) - h⁰(K-D)) = 1

    Using Serre duality h¹(D) = h⁰(K-D), this gives χ(D) - χ(D-p) = 1. -/
theorem eulerChar_point_exact (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) :
    eulerChar C K D - eulerChar C K (D - Core.Divisor.point p) = 1 := by
  unfold eulerChar h1
  rw [canonical_sub_sub C K D p]
  have hformula := point_exact_dimension_formula C K D p
  unfold h0 at hformula ⊢
  omega

/-- **Negative degree vanishing**: h⁰(D) = 0 when deg(D) < 0. -/
theorem h0_neg_degree (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) (hneg : D.degree < 0) : h0 C D = 0 := by
  have h_only_zero : ∀ f ∈ RiemannRochSubmodule C D, f = 0 := by
    intro f hf
    by_contra hfne
    simp only [RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
               RiemannRochSpace] at hf
    rcases hf with rfl | hf_val
    · exact hfne rfl
    have heff : Core.Divisor.IsEffective (Core.Divisor.divOf f hfne + D) := by
      intro p
      simp only [Core.Divisor.add_coeff, Core.Divisor.divOf_coeff]
      exact hf_val p
    have hdeg_nonneg := Core.Divisor.degree_nonneg_of_isEffective _ heff
    have hdeg_eq : (Core.Divisor.divOf f hfne + D).degree = D.degree := by
      rw [Core.Divisor.degree_add]
      rw [Core.Divisor.divOf_degree_eq_orderSum]
      rw [C.argumentPrinciple f hfne]
      ring
    rw [hdeg_eq] at hdeg_nonneg
    exact not_lt.mpr hdeg_nonneg hneg

  unfold h0
  have h_eq_bot : RiemannRochSubmodule C D = ⊥ := by
    ext x
    simp only [Submodule.mem_bot]
    constructor
    · exact h_only_zero x
    · intro hx; rw [hx]; exact (RiemannRochSubmodule C D).zero_mem
  rw [h_eq_bot]
  simp only [finrank_bot]

/-- **Serre duality**: h¹(D) = h⁰(K - D). -/
theorem serre_duality (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C) (D : Core.Divisor C.toAlgebraicCurve) :
    h1 C K D = h0 C (K.K - D) := by
  rfl

/-!
## Riemann-Roch Theorem

The main theorem follows from the lemmas above by induction.
-/

-- Helper lemmas for the induction
private theorem degree_sub_point (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) :
    (D - Core.Divisor.point p).degree = D.degree - 1 := by
  rw [Core.Divisor.sub_eq_add_neg, Core.Divisor.degree_add,
      Core.Divisor.degree_neg, Core.Divisor.degree_point]
  ring

private theorem sub_succ_smul_point (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) (n : ℕ) :
    D - ((n + 1 : ℕ) : ℤ) • Core.Divisor.point p =
    D - (n : ℤ) • Core.Divisor.point p - Core.Divisor.point p := by
  ext q
  simp only [Core.Divisor.sub_coeff, Core.Divisor.smul_coeff, Core.Divisor.point]
  split_ifs with hqp
  · simp only [mul_one]; omega
  · simp only [mul_zero, sub_zero]

private theorem chi_diff_nat (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) (n : ℕ) :
    eulerChar C K D - eulerChar C K (D - (n : ℤ) • Core.Divisor.point p) = n := by
  induction n with
  | zero =>
    have h : D - (0 : ℤ) • Core.Divisor.point p = D := by
      ext q; simp only [Core.Divisor.sub_coeff, Core.Divisor.smul_coeff, zero_mul, sub_zero]
    simp only [Nat.cast_zero, h, sub_self]
  | succ k ih =>
    rw [sub_succ_smul_point C D p k]
    let D' := D - (k : ℤ) • Core.Divisor.point p
    have hpt := eulerChar_point_exact C K D' p
    calc eulerChar C K D - eulerChar C K (D' - Core.Divisor.point p)
        = (eulerChar C K D - eulerChar C K D') + (eulerChar C K D' - eulerChar C K (D' - Core.Divisor.point p)) := by ring
      _ = (k : ℤ) + 1 := by rw [ih, hpt]
      _ = (k + 1 : ℕ) := by omega

private theorem chi_diff_nat_neg (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) (n : ℕ) :
    eulerChar C K D - eulerChar C K (D + (n : ℤ) • Core.Divisor.point p) = -(n : ℤ) := by
  let D' := D + (n : ℤ) • Core.Divisor.point p
  have h := chi_diff_nat C K D' p n
  have hD : D' - (n : ℤ) • Core.Divisor.point p = D := by
    ext q; simp only [Core.Divisor.sub_coeff, Core.Divisor.add_coeff,
                      Core.Divisor.smul_coeff, D']; ring
  rw [hD] at h; linarith

private theorem chi_deg_invariant_smul (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) (n : ℤ) :
    eulerChar C K D - D.degree =
    eulerChar C K (D - n • Core.Divisor.point p) - (D - n • Core.Divisor.point p).degree := by
  have hdeg : (D - n • Core.Divisor.point p).degree = D.degree - n := by
    rw [Core.Divisor.sub_eq_add_neg, Core.Divisor.degree_add,
        Core.Divisor.degree_neg, Core.Divisor.degree_smul, Core.Divisor.degree_point]
    ring
  have hchi : eulerChar C K D - eulerChar C K (D - n • Core.Divisor.point p) = n := by
    rcases n with (m | m)
    · exact chi_diff_nat C K D p m
    · have heq : D - Int.negSucc m • Core.Divisor.point p =
                 D + ((m + 1 : ℕ) : ℤ) • Core.Divisor.point p := by
        ext q
        simp only [Core.Divisor.sub_coeff, Core.Divisor.add_coeff,
                   Core.Divisor.smul_coeff, Int.negSucc_eq, Nat.cast_add, Nat.cast_one]
        ring
      rw [heq]
      have h := chi_diff_nat_neg C K D p (m + 1)
      simp only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one] at h ⊢
      exact h
  omega

private theorem chi_deg_base (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C) :
    eulerChar C K 0 - (0 : Core.Divisor C.toAlgebraicCurve).degree = 1 - C.genus := by
  simp only [Core.Divisor.degree_zero, sub_zero]
  unfold eulerChar
  rw [h0_zero C, h1_zero C K]
  ring

/-- **Riemann-Roch Theorem** for algebraic curves.

    χ(D) = deg(D) + 1 - g

    **Hypotheses**:
    - K: A canonical divisor

    **Proof**: The proof is by strong induction on the support cardinality of D.
    The key step uses `eulerChar_point_exact` (χ(D) - χ(D-p) = 1) derived from
    the long exact sequence in sheaf cohomology. -/
theorem riemann_roch_algebraic (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C)
    (D : Core.Divisor C.toAlgebraicCurve) :
    eulerChar C K D = D.degree + 1 - C.genus := by
  suffices h : eulerChar C K D - D.degree = 1 - C.genus by omega
  induction hind : D.supportCard using Nat.strong_induction_on generalizing D with
  | _ n ih =>
    by_cases hD : D = 0
    · rw [hD]; exact chi_deg_base C K
    · obtain ⟨p, hp⟩ := Core.Divisor.exists_mem_support_of_ne_zero D hD
      simp only [Core.Divisor.support, Set.mem_setOf_eq] at hp
      let D' := D - D.coeff p • Core.Divisor.point p
      have hlt : D'.supportCard < D.supportCard :=
        Core.Divisor.supportCard_sub_coeff_point_lt D p hp
      have hinv := chi_deg_invariant_smul C K D p (D.coeff p)
      rw [hinv]
      exact ih D'.supportCard (by rw [← hind]; exact hlt) D' rfl

end RiemannSurfaces.Algebraic.Cohomology
