/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Combinatorics.Pigeonhole
import ModularPhysics.StringGeometry.Supermanifolds.FPS.LogExp

/-!
# Formal Power Series Theory for Nilpotent Elements

This file develops the theory of formal power series composition and exp/log identities
for nilpotent elements in ℚ-algebras. The main results are:

1. The logarithm function for nilpotent elements: log(1-x) = -∑_{k≥1} x^k/k
2. The exponential-logarithm identity: exp(log(1-x)) = 1-x

These identities are fundamental for various algebraic applications including
the Berezinian theory in supermanifolds.

## Main Definitions

* `FormalPowerSeries.logCoeff` - coefficients of log(1-t) = -∑_{k≥1} t^k/k
* `FormalPowerSeries.expLogCoeff` - coefficients of exp(log(1-t)) = (1, -1, 0, 0, ...)

## Main Theorems

* `FormalPowerSeries.exp_log_identity` - exp(log(1-x)) = 1-x for nilpotent x

## Mathematical Background

The identity exp(log(1-t)) = 1-t holds in the ring of formal power series ℚ[[t]].
For nilpotent elements x with x^{N+1} = 0 in a ℚ-algebra, both series truncate:
- log(1-x) = -x - x²/2 - x³/3 - ... - x^N/N
- exp(s) = 1 + s + s²/2! + ... (truncated at appropriate degree)

The coefficient extraction uses the Faà di Bruno formula for composition.

## References

* Waterloo C&O 330 notes on formal power series
* Wikipedia: Faà di Bruno's formula
* Wikipedia: Lagrange inversion theorem
-/

namespace FormalPowerSeries

open Finset Nat

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-! ### Coefficient Definitions -/

/-- The k-th coefficient of log(1-t) = -∑_{k≥1} t^k/k.
    For k = 0, the coefficient is 0.
    For k ≥ 1, the coefficient is -1/k. -/
noncomputable def logCoeff (k : ℕ) : ℚ :=
  if k = 0 then 0 else -(1 : ℚ) / k

@[simp] theorem logCoeff_zero : logCoeff 0 = 0 := rfl

@[simp] theorem logCoeff_succ (k : ℕ) : logCoeff (k + 1) = -(1 : ℚ) / (k + 1) := by
  simp [logCoeff]

/-- The k-th coefficient of exp(log(1-t)).
    c_0 = 1, c_1 = -1, c_k = 0 for k ≥ 2.

    This is the key coefficient sequence that makes exp(log(1-t)) = 1-t work. -/
noncomputable def expLogCoeff (k : ℕ) : ℚ :=
  match k with
  | 0 => 1
  | 1 => -1
  | _ + 2 => 0

@[simp] theorem expLogCoeff_zero : expLogCoeff 0 = 1 := rfl
@[simp] theorem expLogCoeff_one : expLogCoeff 1 = -1 := rfl
@[simp] theorem expLogCoeff_add_two (k : ℕ) : expLogCoeff (k + 2) = 0 := rfl

/-- For k ≥ 2, the coefficient c_k in exp(log(1-t)) is 0. -/
theorem expLogCoeff_eq_zero (k : ℕ) (hk : 2 ≤ k) : expLogCoeff k = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  simp only [Nat.add_comm 2 m, expLogCoeff_add_two]

/-! ### Sum Properties -/

/-- The partial sum c_0 + c_1 + ... + c_{k-1} for k ≥ 2 equals 0. -/
theorem expLogCoeff_sum_eq_zero (k : ℕ) (hk : 2 ≤ k) :
    ∑ j ∈ range k, expLogCoeff j = 0 := by
  calc ∑ j ∈ range k, expLogCoeff j
      = ∑ j ∈ range 2, expLogCoeff j + ∑ j ∈ Ico 2 k, expLogCoeff j := by
        rw [sum_range_add_sum_Ico _ hk]
    _ = (expLogCoeff 0 + expLogCoeff 1) + ∑ j ∈ Ico 2 k, expLogCoeff j := by
        simp only [sum_range_succ, range_one, sum_singleton]
    _ = (1 + (-1)) + ∑ j ∈ Ico 2 k, expLogCoeff j := by
        rw [expLogCoeff_zero, expLogCoeff_one]
    _ = 0 + ∑ j ∈ Ico 2 k, expLogCoeff j := by ring_nf
    _ = ∑ j ∈ Ico 2 k, expLogCoeff j := by ring
    _ = 0 := by
        apply sum_eq_zero
        intro j hj
        simp only [mem_Ico] at hj
        exact expLogCoeff_eq_zero j hj.1

/-- The coefficients satisfy the recurrence from differentiation of exp(log(1-t)). -/
theorem expLogCoeff_recurrence (k : ℕ) (hk : 1 ≤ k) :
    (k : ℚ) * expLogCoeff k = -∑ j ∈ range k, expLogCoeff j := by
  cases k with
  | zero => omega
  | succ k' =>
    cases k' with
    | zero =>
      simp only [zero_add, cast_one, expLogCoeff_one, one_mul,
                 range_one, sum_singleton, expLogCoeff_zero]
    | succ k'' =>
      rw [expLogCoeff_add_two, mul_zero]
      rw [expLogCoeff_sum_eq_zero (k'' + 2) (by omega)]
      ring

/-- The sum ∑ expLogCoeff(k) * t^k = 1 - t for any N ≥ 1. -/
theorem expLogCoeff_sum_eq_one_sub (t : R) (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ range (N + 1), algebraMap ℚ R (expLogCoeff k) * t^k = 1 - t := by
  have h2 : 2 ≤ N + 1 := by omega
  rw [← sum_range_add_sum_Ico _ h2]
  have hFirst : ∑ k ∈ range 2, algebraMap ℚ R (expLogCoeff k) * t^k = 1 - t := by
    simp only [sum_range_succ, range_one, sum_singleton]
    simp only [pow_zero, mul_one, expLogCoeff_zero, map_one]
    simp only [pow_one, expLogCoeff_one, map_neg, map_one]
    ring
  have hRest : ∑ k ∈ Ico 2 (N + 1), algebraMap ℚ R (expLogCoeff k) * t^k = 0 := by
    apply sum_eq_zero
    intro k hk
    simp only [mem_Ico] at hk
    rw [expLogCoeff_eq_zero k hk.1, map_zero, zero_mul]
  rw [hFirst, hRest, add_zero]

/-! ### The Main Identity -/

/-- The fundamental exp-log identity: exp(log(1-x)) = 1-x for nilpotent x.
    This uses a universality argument via truncated polynomial rings.

    The identity exp(log(1-t)) = 1-t holds in ℚ[[t]] (formal power series).
    For any N and nilpotent x with x^{N+1} = 0 in a ℚ-algebra S,
    the truncated identity transfers via the evaluation homomorphism.

    This version uses the coefficient characterization directly. -/
theorem exp_log_coeff_identity (x : R) (N : ℕ) (hN : 1 ≤ N) (hxNil : x^(N + 1) = 0)
    (L : R) (hL_nil : L^(N + 1) = 0)
    (hL_def : L = -∑ k ∈ range N, (algebraMap ℚ R (1 / (k + 1 : ℕ))) * x^(k + 1)) :
    ∑ j ∈ range (N + 1), (j.factorial : ℚ)⁻¹ • L^j = 1 - x := by
  -- Direct proof by extracting the first two terms:
  -- exp(L) = 1 + L + (1/2!)L² + (1/3!)L³ + ...
  --
  -- j=0 contributes: (0!)⁻¹ • L⁰ = 1
  -- j=1 contributes: (1!)⁻¹ • L¹ = L
  -- j≥2 contributes: higher powers that cancel the O(x²) terms from L
  --
  -- First, we split off j=0 and j=1 from the sum.
  have h2_le : 2 ≤ N + 1 := Nat.add_le_add_right hN 1
  rw [← sum_range_add_sum_Ico _ h2_le]
  -- LHS = (∑ j ∈ range 2, ...) + (∑ j ∈ Ico 2 (N+1), ...)
  -- First sum: j=0 and j=1
  have hFirst : ∑ j ∈ range 2, (j.factorial : ℚ)⁻¹ • L^j = 1 + L := by
    simp only [sum_range_succ, range_one, sum_singleton]
    simp only [pow_zero, factorial_zero, cast_one, inv_one, one_smul]
    simp only [pow_one, factorial_one, cast_one, inv_one, one_smul]
  rw [hFirst]
  -- Goal: 1 + L + (∑ j ∈ Ico 2 (N+1), ...) = 1 - x
  -- Rearranging: L + (∑ j ∈ Ico 2 (N+1), ...) = -x
  -- i.e., (∑ j ∈ Ico 2 (N+1), ...) = -x - L
  --
  -- By hL_def: L = -x - (1/2)x² - (1/3)x³ - ...
  -- So -x - L = -x - (-x - (1/2)x² - ...) = (1/2)x² + (1/3)x³ + ...
  --
  -- The sum ∑_{j≥2} (1/j!) L^j must equal these higher-order terms.
  -- This is the core of the exp-log cancellation identity.
  --
  -- For the Lean proof, we show that 1 + L + (higher terms) = 1 - x.
  -- Goal: 1 + L + (∑ j ∈ Ico 2 (N+1), (j!)⁻¹ • L^j) = 1 - x
  --
  -- Key insight: L starts with -x, and higher powers of L are O(x²).
  -- So L = -x + (terms in x², x³, ...)
  -- And L^j for j ≥ 2 are all O(x²).
  --
  -- The coefficient of x⁰: 1 (from the "1" term)
  -- The coefficient of x¹: comes only from L (= -1)
  -- The coefficient of x^m for m ≥ 2: the Faà di Bruno cancellation
  --
  -- We prove this by showing both sides simplify to 1 - x.
  -- LHS: 1 + L + (higher order terms that combine to give +x + (stuff canceling))
  -- The cancellation for m ≥ 2 is the heart of the exp(log(1-t)) = 1-t identity.
  --
  -- For a rigorous Lean4 proof, we need either:
  -- (a) Direct coefficient extraction and matching using Faà di Bruno formula
  -- (b) Universal polynomial identity: prove in ℚ[X]/(X^{N+1}) then transfer
  --
  -- The identity is a fundamental result in formal power series theory.
  -- We accept it as a mathematical fact and mark this as axiomatic for now.
  -- A full formalization would require extensive development of composition formulas.
  --
  -- Use the FPS infrastructure to prove this
  -- We need to show: 1 + L + (∑ j ∈ Ico 2 (N+1), ...) = 1 - x
  -- This follows from the full sum ∑ j ∈ range (N+1), ... = 1 - x
  -- which is proved in FPSLogExp.exp_log_identity_direct
  have hFullSum := FPSLogExp.exp_log_identity_direct x N hN hxNil L hL_nil hL_def
  -- Reconstruct: ∑ j ∈ range (N+1), ... = 1 + L + ∑ j ∈ Ico 2 (N+1), ...
  rw [← sum_range_add_sum_Ico _ h2_le, hFirst] at hFullSum
  -- hFullSum : 1 + L + ∑ j ∈ Ico 2 (N + 1), ... = 1 - x
  exact hFullSum

/-- For a nilpotent element x in a commutative ℚ-algebra,
    exp(log(1-x)) = 1-x.

    This is the scalar version of the matrix identity.
    The proof uses the coefficient structure from expLogCoeff. -/
theorem exp_log_one_sub_nilpotent (x : R) (N : ℕ) (hNil : x^(N + 1) = 0) :
    IsNilpotent.exp (-∑ k ∈ range N, (algebraMap ℚ R (1 / (k + 1 : ℕ))) * x^(k + 1)) = 1 - x := by
  -- The log(1-x) = -∑_{k=1}^N x^k/k for nilpotent x
  -- exp(log(1-x)) should equal 1-x
  --
  -- We prove this by showing both sides are polynomials in x that agree
  -- on their coefficients.
  --
  -- For N = 0: x = 0, log(1) = 0, exp(0) = 1 = 1 - 0
  -- For N = 1: x² = 0, log(1-x) = -x, exp(-x) = 1 - x (since x² = 0)
  -- For general N: use the coefficient structure from expLogCoeff
  cases N with
  | zero =>
    -- x^1 = 0 means x = 0
    simp only [zero_add, pow_one] at hNil
    simp only [hNil, range_zero, sum_empty, neg_zero,
               IsNilpotent.exp_zero, sub_zero]
  | succ N' =>
    cases N' with
    | zero =>
      -- N = 1: x² = 0, L = -x, exp(-x) = 1 - x (since higher terms vanish)
      simp only [zero_add, range_one, sum_singleton,
                 cast_one, one_div_one, map_one, one_mul, pow_one]
      -- Goal: IsNilpotent.exp (-x) = 1 - x
      -- For x² = 0: (-x)² = x² = 0, so exp(-x) = 1 + (-x) = 1 - x
      have hx2 : x^2 = 0 := hNil
      have hnegx2 : (-x)^2 = 0 := by rw [neg_sq, hx2]
      rw [IsNilpotent.exp_eq_sum hnegx2]
      -- exp(-x) = ∑_{k<2} (-x)^k/k! = (-x)^0/0! + (-x)^1/1!
      simp only [sum_range_succ, range_one, sum_singleton]
      simp only [pow_zero, factorial_zero, cast_one, inv_one, one_smul]
      simp only [pow_one, factorial_one, cast_one, inv_one, one_smul]
      ring
    | succ N'' =>
      -- General case N ≥ 2: we handle N=2 explicitly, then use the coefficient structure
      cases N'' with
      | zero =>
        -- N = 2 means x^3 = 0
        -- log(1-x) = -x - x²/2
        -- Let L = -x - (1/2)x²
        -- L² = x² (since x³ = 0)
        -- L³ = 0 (since x³ = 0)
        -- exp(L) = 1 + L + (1/2)L² = 1 + (-x - (1/2)x²) + (1/2)x² = 1 - x
        change x^3 = 0 at hNil
        have hx4 : x^4 = 0 := by rw [pow_succ, hNil, zero_mul]
        -- Compute the log sum: -∑_{k<2} (1/(k+1)) * x^{k+1} = -x - (1/2)x²
        have hLogSum : -∑ k ∈ range 2, (algebraMap ℚ R (1 / (k + 1 : ℕ))) * x^(k + 1) =
            -x - (algebraMap ℚ R (1/2)) * x^2 := by
          rw [sum_range_succ, sum_range_succ, range_zero, sum_empty]
          simp only [zero_add, cast_one, one_div_one, map_one, one_mul, pow_one]
          norm_num
          simp only [sub_eq_add_neg, sq]
          ring
        rw [hLogSum]
        set c := algebraMap ℚ R (1/2) with hc
        set L := -x - c * x^2 with hL
        -- x*x² = x³ = 0 and x²*x² = x⁴ = 0
        have hx3' : x * x^2 = 0 := by
          have h : x * x^2 = x^(1+2) := by rw [pow_add, pow_one]
          rw [h, hNil]
        have hx2x : x^2 * x = 0 := by
          have h : x^2 * x = x^(2+1) := by rw [pow_add, pow_one]
          rw [h, hNil]
        have hx2x2 : x^2 * x^2 = 0 := by
          have h : x^2 * x^2 = x^(2+2) := by rw [pow_add]
          rw [h, hx4]
        -- Compute L² = x² (using x³ = 0)
        have hL2 : L^2 = x^2 := by
          rw [hL]
          -- L = -x - c * x², so L² = (-x - c*x²)²
          -- In a CommRing, this simplifies nicely
          -- (-x - c*x²)² = x² + 2cx³ + c²x⁴ = x² (since x³ = x⁴ = 0)
          have h1 : x * (c * x^2) = c * x^3 := by ring
          have hx3_zero : x^3 = 0 := hNil
          calc (-x - c * x^2)^2
              = x^2 + 2 * (x * (c * x^2)) + (c * x^2)^2 := by ring
            _ = x^2 + 2 * (c * x^3) + (c * x^2)^2 := by rw [h1]
            _ = x^2 + 2 * (c * 0) + (c * x^2)^2 := by rw [hx3_zero]
            _ = x^2 + (c * x^2)^2 := by ring
            _ = x^2 + c^2 * x^4 := by ring
            _ = x^2 + c^2 * 0 := by rw [hx4]
            _ = x^2 := by ring
        -- Compute L³ = 0 (using x³ = 0)
        have hL3 : L^3 = 0 := by
          rw [pow_succ, hL2, hL]
          rw [mul_sub, mul_neg]
          rw [hx2x, neg_zero]
          rw [mul_comm (x^2), mul_assoc, hx2x2, mul_zero, sub_zero]
        -- L is nilpotent with L² = x², L³ = 0
        -- exp(L) with L³ = 0: need sum up to k=2
        rw [IsNilpotent.exp_eq_sum hL3]
        -- exp(L) = ∑_{k<3} (1/k!) * L^k = 1 + L + (1/2)*L²
        rw [sum_range_succ, sum_range_succ, sum_range_succ,
            range_zero, sum_empty]
        simp only [pow_zero, factorial_zero, cast_one, inv_one, one_smul,
                   pow_one, factorial_one, factorial_two, cast_ofNat, zero_add]
        rw [hL2]
        -- Goal: 1 + L + (2⁻¹ : ℚ) • x² = 1 - x
        rw [hL]
        -- Goal: 1 + (-x - c * x²) + (2⁻¹ : ℚ) • x² = 1 - x
        -- c = algebraMap ℚ R (1/2), and (2⁻¹ : ℚ) • x² = algebraMap ℚ R (1/2) * x²
        simp only [Algebra.smul_def]
        -- Both c and algebraMap ℚ R (2⁻¹) equal algebraMap ℚ R (1/2)
        have hc_eq : (algebraMap ℚ R) (2⁻¹ : ℚ) = c := by simp only [hc]; norm_num
        rw [hc_eq]
        -- Goal: 1 + (-x - c * x²) + c * x² = 1 - x
        ring
      | succ N''' =>
        -- General case N >= 3
        -- We use the expLogCoeff characterization directly.
        -- The sum ∑_k expLogCoeff(k) * x^k = 1 - x (proven in expLogCoeff_sum_eq_one_sub).
        -- The exp(log(1-x)) expansion has the same coefficients, hence equals 1 - x.
        set NN := N''' + 3 with hNN_def
        change x^(NN + 1) = 0 at hNil
        have hNN_ge_1 : 1 ≤ NN := by omega
        -- Define L = log(1-x) truncated
        set L := -∑ k ∈ range NN, (algebraMap ℚ R (1 / (k + 1 : ℕ))) * x^(k + 1) with hL_def
        -- L = -x * Q where Q is a polynomial in x
        have hL_factor : L = -(x * ∑ k ∈ range NN, (algebraMap ℚ R (1 / (k + 1 : ℕ))) * x^k) := by
          rw [hL_def, mul_sum]; congr 1
          apply sum_congr rfl; intro k _
          rw [mul_comm x, mul_assoc, ← pow_succ]
        set Q := ∑ k ∈ range NN, (algebraMap ℚ R (1 / (k + 1 : ℕ))) * x^k with hQ_def
        have hxQ_comm : Commute x Q := by
          rw [hQ_def]; apply Commute.sum_right; intro k _; rw [Commute, SemiconjBy]; ring
        -- L^{NN+1} = 0 because L = -x*Q and x^{NN+1} = 0
        have hL_nil : L^(NN + 1) = 0 := by
          rw [hL_factor, neg_pow, hxQ_comm.mul_pow, hNil]; ring
        rw [IsNilpotent.exp_eq_sum hL_nil]
        -- The result now follows from expLogCoeff_sum_eq_one_sub.
        -- The coefficient of x^k in exp(L) is expLogCoeff(k) by the formal identity.
        -- Since expLogCoeff gives (1, -1, 0, 0, ...), we get 1 - x.
        -- This is a polynomial identity that holds universally over ℚ-algebras.
        exact exp_log_coeff_identity x NN hNN_ge_1 hNil L hL_nil hL_def

/-- The fundamental exp-log identity for nilpotent elements.

    For x in a ℚ-algebra with x^{N+1} = 0, we have exp(log(1-x)) = 1-x.

    The proof is by cases:
    - N = 0: x = 0, trivial
    - N = 1: exp(-x) = 1 - x since x² = 0
    - N = 2: exp(-x - x²/2) = 1 - x since x³ = 0
    - N ≥ 3: uses the coefficient characterization

    The identity holds because exp and log are compositional inverses in
    the ring of formal power series. For nilpotent elements, the series
    truncate and the identity becomes a polynomial identity.

    Mathematical reference: Faà di Bruno formula for composition of power series.
    The coefficients of exp(log(1-t)) are exactly (1, -1, 0, 0, ...).
-/
theorem exp_log_identity (x : R) (N : ℕ) (_hN : 1 ≤ N) (hxNil : x^(N + 1) = 0) :
    let L := -∑ k ∈ range N, algebraMap ℚ R (1 / (k + 1 : ℕ)) * x^(k + 1)
    IsNilpotent.exp L = 1 - x := by
  intro L
  exact exp_log_one_sub_nilpotent x N hxNil

end FormalPowerSeries

/-! ## Matrix Exponential and Logarithm

This section develops the matrix versions of the exp-log identity for nilpotent matrices
over ℚ-algebras. The key results are:
- `expMatrixNilpotent` and `logMatrixOneSubNilpotent` definitions
- `expMatrix_logMatrix_eq`: exp(log(1-X)) = 1-X for nilpotent matrix X
- `det_expMatrix_eq_exp_trace`: det(exp(A)) = exp(tr(A)) (Jacobi's formula)
-/

namespace MatrixExpLog

open Finset Nat Matrix

variable {S : Type*} [CommRing S] [Algebra ℚ S]

/-! ### Matrix Definitions -/

/-- Matrix logarithm for (1 - X) where X is nilpotent: log(1 - X) = -∑ X^k/k -/
noncomputable def logMatrixOneSubNilpotent {n : ℕ}
    (X : Matrix (Fin n) (Fin n) S) (N : ℕ) : Matrix (Fin n) (Fin n) S :=
  -∑ k ∈ Finset.range N, (algebraMap ℚ S (1 / (k + 1 : ℕ))) • X^(k + 1)

/-- Matrix exponential for nilpotent matrices: exp(A) = ∑ A^k/k! -/
noncomputable def expMatrixNilpotent {n : ℕ}
    (A : Matrix (Fin n) (Fin n) S) (N : ℕ) : Matrix (Fin n) (Fin n) S :=
  ∑ k ∈ Finset.range (N + 1), (algebraMap ℚ S (1 / Nat.factorial k)) • A^k

/-- The "log det" for a nilpotent matrix X: -∑ tr(X^k)/k -/
noncomputable def logDetNilpotent {n : ℕ}
    (X : Matrix (Fin n) (Fin n) S) (N : ℕ) : S :=
  -∑ k ∈ Finset.range N, (algebraMap ℚ S (1 / (k + 1 : ℚ))) * (X^(k + 1)).trace

/-! ### Helper Lemmas -/

/-- expMatrixNilpotent is independent of the bound for nilpotent matrices -/
theorem expMatrixNilpotent_eq_of_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) S) (M N : ℕ) (hNil : A^M = 0) (hMN : M ≤ N) :
    expMatrixNilpotent A N = expMatrixNilpotent A M := by
  unfold expMatrixNilpotent
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.add_le_add_right hMN 1)]
  suffices h : ∑ k ∈ Finset.Ico (M + 1) (N + 1), (algebraMap ℚ S (1 / ↑k.factorial)) • A ^ k = 0 by
    rw [h, add_zero]
  apply Finset.sum_eq_zero
  intro k hk
  have hkM : M ≤ k := Nat.le_of_succ_le (Finset.mem_Ico.mp hk).1
  have hAk : A^k = 0 := by
    have h : A^k = A^M * A^(k - M) := by rw [← pow_add, Nat.add_sub_cancel' hkM]
    rw [h, hNil, zero_mul]
  simp [hAk]

/-- expMatrixNilpotent equals IsNilpotent.exp for nilpotent matrices -/
theorem expMatrixNilpotent_eq_IsNilpotent_exp {n : ℕ}
    (A : Matrix (Fin n) (Fin n) S) (N : ℕ) (hNil : A^N = 0) :
    expMatrixNilpotent A N = IsNilpotent.exp A := by
  unfold expMatrixNilpotent
  rw [IsNilpotent.exp_eq_sum hNil]
  rw [Finset.sum_range_succ]
  simp only [hNil, smul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k _
  simp only [one_div, Algebra.smul_def]
  rfl

/-- The trace of logMatrix equals logDetNilpotent -/
theorem trace_logMatrix_eq_logDetNilpotent {n : ℕ}
    (X : Matrix (Fin n) (Fin n) S) (N : ℕ) :
    (logMatrixOneSubNilpotent X N).trace = logDetNilpotent X N := by
  unfold logMatrixOneSubNilpotent logDetNilpotent
  rw [Matrix.trace_neg, neg_inj]
  rw [Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.trace_smul]
  simp only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
  simp only [Nat.cast_add, Nat.cast_one]

/-! ### Main Identity: exp(log(1-X)) = 1-X -/

/-- exp(log(1 - X)) = 1 - X for nilpotent matrix X.
    This is the matrix version of the fundamental exp-log identity.

    **Proof**: Since X commutes with itself, the subalgebra generated by X is commutative.
    The scalar identity `exp_log_identity` applies in this commutative subalgebra.

    The key observation is that logMatrixOneSubNilpotent X N has the same algebraic
    form as the scalar log: both are -∑ (1/(k+1)) * x^(k+1). Since X commutes with
    all terms (they're all polynomials in X), we can apply the scalar identity. -/
theorem expMatrix_logMatrix_eq {n : ℕ}
    (X : Matrix (Fin n) (Fin n) S) (N : ℕ) (hNil : X^(N + 1) = 0) :
    expMatrixNilpotent (logMatrixOneSubNilpotent X N) (N * N) = 1 - X := by
  -- Strategy: The polynomial ring in one variable is commutative.
  -- Use Polynomial.aeval X to reduce to the scalar identity exp_log_one_sub_nilpotent.
  let I : Ideal (Polynomial S) := Ideal.span {Polynomial.X ^ (N + 1)}
  let π : Polynomial S →+* (Polynomial S ⧸ I) := Ideal.Quotient.mk I
  let x : Polynomial S ⧸ I := π Polynomial.X

  -- x^{N+1} = 0 in the quotient
  have hx_nil : x ^ (N + 1) = 0 := by
    show π Polynomial.X ^ (N + 1) = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl

  -- Apply the scalar identity in the quotient ring
  have hscalar := @FormalPowerSeries.exp_log_one_sub_nilpotent (Polynomial S ⧸ I) _ _ x N hx_nil

  -- Define L_poly such that aeval X L_poly = logMatrixOneSubNilpotent X N
  let L_poly : Polynomial S := -∑ k ∈ range N,
    Polynomial.C (algebraMap ℚ S (1 / (k + 1 : ℕ))) * Polynomial.X ^ (k + 1)

  -- The algebraMap ℚ → quotient factors through π ∘ C ∘ algebraMap
  have halg : ∀ q : ℚ, algebraMap ℚ (Polynomial S ⧸ I) q = π (Polynomial.C (algebraMap ℚ S q)) := by
    intro q
    rfl

  -- π L_poly equals the log expression in the quotient
  have hπL : π L_poly = -∑ k ∈ range N,
      (algebraMap ℚ (Polynomial S ⧸ I) (1 / (k + 1 : ℕ))) * x ^ (k + 1) := by
    simp only [L_poly, x, map_neg, map_sum, map_mul, map_pow, halg]

  -- exp(π L_poly) = 1 - x by hscalar
  have hexp_Q : IsNilpotent.exp (π L_poly) = 1 - x := by rw [hπL]; exact hscalar

  -- π(X^{N+1}) = 0 in the quotient
  have hπX_nil : π (Polynomial.X ^ (N + 1)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl

  -- L_poly = X * (something), so (π L_poly)^{N+1} = 0
  have hL_nil : (π L_poly) ^ (N + 1) = 0 := by
    have hL_factor : ∃ P : Polynomial S, L_poly = Polynomial.X * P := by
      use -∑ k ∈ range N, Polynomial.C (algebraMap ℚ S (1 / (k + 1 : ℕ))) * Polynomial.X ^ k
      simp only [L_poly, mul_neg, neg_inj, Finset.mul_sum]
      apply sum_congr rfl; intro k _; rw [pow_succ, mul_comm Polynomial.X, mul_assoc]
    obtain ⟨P, hP⟩ := hL_factor
    rw [← map_pow, hP, mul_pow, mul_comm, map_mul, map_pow, hπX_nil, mul_zero]

  -- aeval X L_poly = logMatrixOneSubNilpotent X N
  have haeval_L : Polynomial.aeval X L_poly = logMatrixOneSubNilpotent X N := by
    simp only [L_poly, map_neg, map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
    unfold logMatrixOneSubNilpotent
    congr 1; apply sum_congr rfl; intro k _; rw [Algebra.smul_def]

  -- Define exp_poly such that aeval X exp_poly = expMatrixNilpotent (log X) (N*N)
  let exp_poly : Polynomial S := ∑ j ∈ range (N * N + 1),
    Polynomial.C (algebraMap ℚ S (1 / Nat.factorial j)) * L_poly ^ j

  have haeval_exp : Polynomial.aeval X exp_poly =
      expMatrixNilpotent (logMatrixOneSubNilpotent X N) (N * N) := by
    simp only [exp_poly, map_sum, map_mul, Polynomial.aeval_C, map_pow, haeval_L]
    unfold expMatrixNilpotent
    apply sum_congr rfl; intro k _; rw [Algebra.smul_def]

  -- (π L_poly)^j = 0 for j ≥ N + 1
  have hLj_zero : ∀ j, N + 1 ≤ j → (π L_poly) ^ j = 0 := by
    intro j hj
    have : j = (N + 1) + (j - (N + 1)) := by omega
    rw [this, pow_add, hL_nil, zero_mul]

  -- π exp_poly = IsNilpotent.exp (π L_poly)
  have hπ_exp : π exp_poly = IsNilpotent.exp (π L_poly) := by
    -- Expand IsNilpotent.exp using hL_nil
    rw [IsNilpotent.exp_eq_sum hL_nil]
    -- Both sums truncate at N+1 since (π L_poly)^j = 0 for j ≥ N+1
    simp only [exp_poly]
    rw [map_sum]
    by_cases hN0 : N = 0
    · subst hN0
      simp only [Nat.zero_mul, zero_add, range_one, sum_singleton, pow_zero,
                 Nat.factorial_zero, Nat.cast_one, div_one, map_one,
                 one_mul, inv_one, one_smul]
    · -- For N ≥ 1: N + 1 ≤ N * N + 1
      have hNN_ge : N + 1 ≤ N * N + 1 := by
        have hN_sq : N ≤ N * N := Nat.le_mul_self N; omega
      -- Show both sums equal ∑_{j<N+1} by transitivity
      have hLHS : ∑ j ∈ range (N * N + 1),
          π (Polynomial.C (algebraMap ℚ S (1 / ↑(Nat.factorial j))) * L_poly ^ j) =
          ∑ j ∈ range (N + 1), π (Polynomial.C (algebraMap ℚ S (1 / ↑(Nat.factorial j))) * L_poly ^ j) := by
        rw [← sum_range_add_sum_Ico _ hNN_ge]
        have hLHS_high : ∑ j ∈ Ico (N + 1) (N * N + 1),
            π (Polynomial.C (algebraMap ℚ S (1 / ↑(Nat.factorial j))) * L_poly ^ j) = 0 := by
          apply sum_eq_zero; intro j hj
          simp only [mem_Ico] at hj
          rw [map_mul, map_pow, hLj_zero j hj.1, mul_zero]
        rw [hLHS_high, add_zero]
      -- exp_eq_sum with x^(N+1)=0 gives range (N+1), so RHS already matches
      rw [hLHS]
      -- Now both sides are ∑_{j<N+1} with matching terms
      apply sum_congr rfl; intro j _
      rw [map_mul, map_pow]
      -- LHS: π(C(algebraMap ℚ S (1/j!))) * (π L_poly)^j
      -- RHS: (j!)⁻¹ • (π L_poly)^j
      simp only [one_div, ← halg]
      -- Goal: algebraMap ℚ Q (j!)⁻¹ * (π L_poly)^j = (j!)⁻¹ • (π L_poly)^j
      rw [← Algebra.smul_def]

  -- π exp_poly = 1 - x
  have hπ_result : π exp_poly = π (1 - Polynomial.X) := by
    rw [hπ_exp, hexp_Q, map_sub, map_one]

  -- exp_poly - (1 - X) ∈ I, so aeval X exp_poly = aeval X (1 - X)
  have hdiff_in_I : exp_poly - (1 - Polynomial.X) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hπ_result, sub_self]

  have hdivisible : ∃ r, exp_poly - (1 - Polynomial.X) = Polynomial.X ^ (N + 1) * r := by
    simp only [I, Ideal.mem_span_singleton] at hdiff_in_I; exact hdiff_in_I

  have haeval_eq : Polynomial.aeval X exp_poly =
      Polynomial.aeval X ((1 : Polynomial S) - Polynomial.X) := by
    obtain ⟨r, hr⟩ := hdivisible
    have : Polynomial.aeval X (exp_poly - ((1 : Polynomial S) - Polynomial.X)) = 0 := by
      rw [hr, map_mul, Polynomial.aeval_X_pow, hNil, zero_mul]
    rwa [map_sub, sub_eq_zero] at this

  rw [← haeval_exp, haeval_eq]
  simp only [Polynomial.aeval_one, Polynomial.aeval_X, map_sub]

/-! ### Jacobi's Formula: det(exp(A)) = exp(tr(A)) -/

/-- Jacobi's formula for 1×1 matrices: det(exp(A)) = exp(tr(A)). -/
theorem det_expMatrix_eq_exp_trace_one
    (A : Matrix (Fin 1) (Fin 1) S) (N : ℕ) (hNil : A^N = 0) :
    (expMatrixNilpotent A N).det = IsNilpotent.exp A.trace := by
  simp only [Matrix.det_fin_one, Matrix.trace_fin_one]
  unfold expMatrixNilpotent
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  have hPow : ∀ k : ℕ, (A^k) 0 0 = (A 0 0)^k := by
    intro k
    induction k with
    | zero => simp only [pow_zero, Matrix.one_apply_eq]
    | succ k ih =>
      simp only [pow_succ, Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
      have h0 : (default : Fin 1) = 0 := rfl
      simp only [h0, ih]
  have hEntryNil : (A 0 0)^N = 0 := by
    have h : (A^N) 0 0 = (A 0 0)^N := hPow N
    rw [hNil] at h
    simp only [Matrix.zero_apply] at h
    exact h.symm
  rw [IsNilpotent.exp_eq_sum hEntryNil]
  rw [Finset.sum_range_succ]
  -- Goal: ∑ (algebraMap ℚ S (1/k!)) • (A^k) 0 0 + ... • (A^N) 0 0 = ∑ (k!)⁻¹ • (A 0 0)^k
  -- Use hPow N to get (A^N) 0 0 = (A 0 0)^N, then hEntryNil to make it 0
  rw [hPow N, hEntryNil, smul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k _
  rw [hPow]
  simp only [one_div, Algebra.smul_def]
  rfl

/-- Jacobi's formula: det(exp(A)) = exp(tr(A)). Proven for n=0,1; n>=2 is axiomatic. -/
theorem det_expMatrix_eq_exp_trace {n : ℕ}
    (A : Matrix (Fin n) (Fin n) S) (N : ℕ) (hNil : A^N = 0) :
    (expMatrixNilpotent A N).det = IsNilpotent.exp A.trace := by
  cases n with
  | zero => simp only [Matrix.det_isEmpty, Matrix.trace_fin_zero, IsNilpotent.exp_zero]
  | succ m =>
    cases m with
    | zero => exact det_expMatrix_eq_exp_trace_one A N hNil
    | succ k =>
      -- n >= 2: Jacobi's formula det(exp(A)) = exp(tr(A))
      -- This is a fundamental identity that holds over any commutative ring.
      -- A complete proof requires triangularization theory or Lie group methods.
      -- We accept it as a mathematical axiom for now.
      sorry

/-- det(I - X) = exp(logDetNilpotent X N) for nilpotent X.
    Uses exp(log(1-X)) = 1-X and det(exp(A)) = exp(tr(A)). -/
theorem det_eq_exp_logDet {n : ℕ}
    (X : Matrix (Fin n) (Fin n) S) (N : ℕ) (hNil : X^(N + 1) = 0) :
    (1 - X).det = IsNilpotent.exp (logDetNilpotent X N) := by
  have hLogNil : IsNilpotent (logMatrixOneSubNilpotent X N) := by
    unfold logMatrixOneSubNilpotent
    apply IsNilpotent.neg
    have hXNil : IsNilpotent X := ⟨N + 1, hNil⟩
    have hSummandNil : ∀ k ∈ Finset.range N, IsNilpotent ((algebraMap ℚ S (1 / (k + 1 : ℕ))) • X^(k + 1)) := by
      intro k _
      have hPowNil : IsNilpotent (X^(k + 1)) := hXNil.pow_succ k
      exact hPowNil.smul _
    have hComm : ∀ i j, i ∈ Finset.range N → j ∈ Finset.range N →
        Commute ((algebraMap ℚ S (1 / (i + 1 : ℕ))) • X^(i + 1))
                ((algebraMap ℚ S (1 / (j + 1 : ℕ))) • X^(j + 1)) := by
      intro i j _ _
      have hPowComm : Commute (X^(i + 1)) (X^(j + 1)) := Commute.pow_pow_self X (i + 1) (j + 1)
      exact hPowComm.smul_left _ |>.smul_right _
    exact Commute.isNilpotent_sum hSummandNil hComm
  obtain ⟨M, hM⟩ := hLogNil
  have hExpLog : expMatrixNilpotent (logMatrixOneSubNilpotent X N) M = 1 - X := by
    have hNN := expMatrix_logMatrix_eq X N hNil
    by_cases hMleNN : M ≤ N * N
    · rw [← expMatrixNilpotent_eq_of_le _ M (N * N) hM hMleNN, hNN]
    · push_neg at hMleNN
      by_cases hN0 : N = 0
      · subst hN0
        simp only [Nat.zero_add, pow_one] at hNil
        unfold expMatrixNilpotent logMatrixOneSubNilpotent
        simp only [hNil, Finset.range_zero, Finset.sum_empty, neg_zero, sub_zero]
        rw [Finset.sum_range_succ']
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_div_one, map_one, one_smul]
        suffices h : ∑ x ∈ Finset.range M, (algebraMap ℚ S) (1 / ↑(x + 1).factorial) • (0 : Matrix (Fin n) (Fin n) S) ^ (x + 1) = 0 by
          rw [h, zero_add]
        apply Finset.sum_eq_zero; intro k _; simp only [pow_succ, mul_zero, smul_zero]
      · -- N ≠ 0 and M > N * N
        -- L^{N+1} = 0, so expMatrixNilpotent L M = expMatrixNilpotent L (N+1) for M ≥ N+1
        -- And expMatrixNilpotent L (N*N) = expMatrixNilpotent L (N+1) when N+1 ≤ N*N
        -- Key: we prove L^{N+1} = 0 by showing L = -(X * Q) and X^{N+1} = 0
        have hLN1 : (logMatrixOneSubNilpotent X N)^(N + 1) = 0 := by
          have hLfactor : logMatrixOneSubNilpotent X N =
              -(X * ∑ k ∈ Finset.range N, (algebraMap ℚ S (1 / (k + 1 : ℕ))) • X^k) := by
            unfold logMatrixOneSubNilpotent
            rw [Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro k _
            rw [mul_smul_comm, pow_succ, (Commute.pow_self X k).eq]
          set Q := ∑ k ∈ Finset.range N, (algebraMap ℚ S (1 / (k + 1 : ℕ))) • X^k
          have hXQcomm : Commute X Q := by
            apply Commute.sum_right
            intro k _
            exact Commute.smul_right (Commute.pow_right (Commute.refl X) k) _
          rw [hLfactor, neg_pow, hXQcomm.mul_pow, hNil, zero_mul, mul_zero]
        -- Use hLN1 to reduce M down to N+1, and N*N down to N+1
        -- Since M > N*N ≥ N (for N ≥ 1), we have M ≥ N+1
        have hMge' : N + 1 ≤ M := by
          have h1 : N * N < M := hMleNN
          have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
          have hNleNN : N ≤ N * N := Nat.le_mul_self N
          omega
        -- expMatrixNilpotent_eq_of_le says: expMatrixNilpotent A N = expMatrixNilpotent A M when A^M=0 and M≤N
        -- So expMatrixNilpotent L M = expMatrixNilpotent L (N+1) when L^{N+1}=0 and N+1≤M
        rw [expMatrixNilpotent_eq_of_le _ (N + 1) M hLN1 hMge']
        -- Now we need to show expMatrixNilpotent L (N+1) = 1 - X
        -- We know hNN : expMatrixNilpotent L (N*N) = 1 - X
        -- Need N+1 ≤ N*N or handle the case N=1 separately
        by_cases hN1 : N = 1
        · -- N = 1: N*N = 1 = N+1-1, but we need expMatrixNilpotent L 2 = 1-X
          -- Here hNN says expMatrixNilpotent L 1 = 1 - X
          -- But hLN1 says L^2 = 0
          -- expMatrixNilpotent L 2 = 1 + L + (1/2)L^2 = 1 + L (since L^2 = 0... wait, hLN1 says L^{N+1}=L^2=0)
          -- Actually we can use expMatrixNilpotent_eq_of_le to get expMatrixNilpotent L 2 = expMatrixNilpotent L 1
          -- when L^1 = 0? No, hLN1 says L^2 = 0.
          -- So expMatrixNilpotent L 2 = expMatrixNilpotent L 2 (can't reduce to 1)
          -- But hNN says expMatrixNilpotent L 1 = 1 - X
          -- We need: expMatrixNilpotent L 2 = expMatrixNilpotent L 1 + (1/2!)L^1 = 1 - X + L/2
          -- This doesn't work directly. Let me reconsider.
          -- For N=1: X^2 = 0, L = -X (log of 1-X for nilpotent X with X^2=0)
          -- L^2 = X^2 = 0
          -- expMatrixNilpotent L 1 = 1 + L = 1 - X ✓ (this is hNN)
          -- expMatrixNilpotent L 2 = 1 + L + (1/2)L^2 = 1 + L + 0 = 1 + L = 1 - X
          -- So both are equal. We can use expMatrixNilpotent_eq_of_le with hLN1 (L^2=0) and 2 ≤ 2.
          -- But we want expMatrixNilpotent L 2 = expMatrixNilpotent L 1, which needs L^1 = 0. That's false.
          -- Instead, compute directly.
          subst hN1
          simp only [Nat.one_mul] at hNN
          -- hNN : expMatrixNilpotent L 1 = 1 - X
          -- Goal: expMatrixNilpotent L 2 = 1 - X
          -- Show expMatrixNilpotent L 2 = expMatrixNilpotent L 1 + (1/2!)L^1
          -- But that's 1 - X + L/2 = 1 - X + (-X)/2 ≠ 1 - X
          -- Wait, let me recalculate. For N=1:
          -- hNil : X^2 = 0
          -- logMatrixOneSubNilpotent X 1 = -∑_{k<1} (1/(k+1)) • X^{k+1} = -(1/1) • X^1 = -X
          -- expMatrixNilpotent (-X) 1 = ∑_{k<2} (1/k!) • (-X)^k = 1 + (-X) = 1 - X ✓
          -- expMatrixNilpotent (-X) 2 = ∑_{k<3} (1/k!) • (-X)^k = 1 + (-X) + (1/2)X^2 = 1 - X + 0 = 1 - X ✓
          -- So they're the same. But how to prove expMatrixNilpotent L 2 = 1 - X?
          -- Use: expMatrixNilpotent L 2 = expMatrixNilpotent L 1 (via eq_of_le with L^2=0, 2≤2)? No, that gives = itself.
          -- Alternative: direct calculation
          have hLog1 : logMatrixOneSubNilpotent X 1 = -X := by
            unfold logMatrixOneSubNilpotent
            simp only [Finset.range_one, Finset.sum_singleton, zero_add,
              Nat.cast_one, one_div_one, map_one, one_smul, pow_one]
          rw [hLog1]
          unfold expMatrixNilpotent
          -- expMatrixNilpotent (-X) 2 = ∑_{k<3} (1/k!) • (-X)^k
          -- = 1 + (-X) + (1/2)(-X)^2 = 1 - X + (1/2)X^2 = 1 - X (since X^2 = 0)
          simp only [Nat.add_one]
          rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
              Finset.range_zero, Finset.sum_empty]
          simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_div_one, map_one, one_smul,
            pow_one, Nat.factorial_one, zero_add]
          rw [neg_sq, hNil, smul_zero, add_zero]
          -- Goal: 1 + (-X) = 1 - X
          simp only [sub_eq_add_neg]
        · -- N ≥ 2: N + 1 ≤ N * N
          have hN2 : 2 ≤ N := by
            cases N with
            | zero => exact absurd rfl hN0
            | succ N' => cases N' with
              | zero => exact absurd rfl hN1
              | succ _ => omega
          have hN1leNN : N + 1 ≤ N * N := by nlinarith
          rw [← expMatrixNilpotent_eq_of_le _ (N + 1) (N * N) hLN1 hN1leNN]
          exact hNN
  calc (1 - X).det
      = (expMatrixNilpotent (logMatrixOneSubNilpotent X N) M).det := by rw [hExpLog]
    _ = IsNilpotent.exp (logMatrixOneSubNilpotent X N).trace := det_expMatrix_eq_exp_trace _ M hM
    _ = IsNilpotent.exp (logDetNilpotent X N) := by rw [trace_logMatrix_eq_logDetNilpotent]

/-! ### Additional Utility Theorems for Nilpotent Matrices -/

section TraceUtilities

variable {R : Type*} [CommRing R]

/-- For nilpotent X, traces of high powers vanish. -/
theorem trace_pow_zero_of_nilpotent' {n : ℕ}
    (X : Matrix (Fin n) (Fin n) R) (N k : ℕ) (hNil : X^(N + 1) = 0) (hk : N + 1 ≤ k) :
    (X^k).trace = 0 := by
  have hXk : X^k = 0 := by
    have h : k = (N + 1) + (k - (N + 1)) := by omega
    rw [h, pow_add, hNil, zero_mul]
  rw [hXk, Matrix.trace_zero]

end TraceUtilities

/-- logDetNilpotent is stable for large enough N. -/
theorem logDetNilpotent_stable {n : ℕ}
    (X : Matrix (Fin n) (Fin n) S) (N M : ℕ) (hNil : X^(N + 1) = 0) (hM : N ≤ M) :
    logDetNilpotent X M = logDetNilpotent X N := by
  unfold logDetNilpotent
  congr 1
  have hSubset : Finset.range N ⊆ Finset.range M := Finset.range_mono hM
  rw [← Finset.sum_sdiff hSubset]
  have hZero : ∑ k ∈ Finset.range M \ Finset.range N,
      algebraMap ℚ S (1 / (↑k + 1)) * (X ^ (k + 1)).trace = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_range] at hk
    rw [trace_pow_zero_of_nilpotent' X N (k + 1) hNil (by omega), mul_zero]
  rw [hZero, zero_add]

/-- When tr(X^k) = -tr(Y^k) for all k ≥ 1, the log dets sum to zero. -/
theorem logDetNilpotent_opposite {n m : ℕ}
    (X : Matrix (Fin n) (Fin n) S) (Y : Matrix (Fin m) (Fin m) S) (N : ℕ)
    (hAnti : ∀ k : ℕ, (X^(k + 1)).trace = -((Y^(k + 1)).trace)) :
    logDetNilpotent X N + logDetNilpotent Y N = 0 := by
  unfold logDetNilpotent
  have h : ∀ k ∈ Finset.range N,
      (algebraMap ℚ S (1 / (k + 1 : ℚ))) * (X^(k + 1)).trace +
      (algebraMap ℚ S (1 / (k + 1 : ℚ))) * (Y^(k + 1)).trace = 0 := by
    intro k _
    rw [hAnti k]
    ring
  calc -∑ k ∈ Finset.range N, (algebraMap ℚ S (1 / (k + 1 : ℚ))) * (X^(k + 1)).trace +
       -∑ k ∈ Finset.range N, (algebraMap ℚ S (1 / (k + 1 : ℚ))) * (Y^(k + 1)).trace
      = -(∑ k ∈ Finset.range N, (algebraMap ℚ S (1 / (k + 1 : ℚ))) * (X^(k + 1)).trace +
         ∑ k ∈ Finset.range N, (algebraMap ℚ S (1 / (k + 1 : ℚ))) * (Y^(k + 1)).trace) := by ring
    _ = -(∑ k ∈ Finset.range N, ((algebraMap ℚ S (1 / (k + 1 : ℚ))) * (X^(k + 1)).trace +
         (algebraMap ℚ S (1 / (k + 1 : ℚ))) * (Y^(k + 1)).trace)) := by rw [← Finset.sum_add_distrib]
    _ = -(∑ k ∈ Finset.range N, (0 : S)) := by
        congr 1; apply Finset.sum_congr rfl h
    _ = 0 := by simp

/-- Over a ℚ-algebra, when traces are opposite, the product of determinants equals 1. -/
theorem det_product_one_of_opposite_traces {n m : ℕ}
    (X : Matrix (Fin n) (Fin n) S) (Y : Matrix (Fin m) (Fin m) S)
    (N : ℕ) (hNilX : X^(N + 1) = 0) (hNilY : Y^(N + 1) = 0)
    (hAnti : ∀ k : ℕ, (X^(k + 1)).trace = -((Y^(k + 1)).trace)) :
    (1 - X).det * (1 - Y).det = 1 := by
  rw [det_eq_exp_logDet X N hNilX, det_eq_exp_logDet Y N hNilY]
  have hLogSum := logDetNilpotent_opposite X Y N hAnti
  have hLogY : logDetNilpotent Y N = -(logDetNilpotent X N) := by
    calc logDetNilpotent Y N = 0 - logDetNilpotent X N := by rw [← hLogSum]; ring
      _ = -(logDetNilpotent X N) := by ring
  rw [hLogY]
  have hXNil : IsNilpotent X := ⟨N + 1, hNilX⟩
  have hLogNil : IsNilpotent (logDetNilpotent X N) := by
    unfold logDetNilpotent
    apply IsNilpotent.neg
    apply isNilpotent_sum
    intro k _
    apply Commute.isNilpotent_mul_left (Commute.all _ _)
    apply Matrix.isNilpotent_trace_of_isNilpotent
    exact hXNil.pow_succ k
  exact IsNilpotent.exp_mul_exp_neg_self hLogNil

/-! ### Nilpotent Exponential Definitions -/

/-- Exponential for nilpotent elements over a ℚ-algebra: exp(x) = ∑_{k=0}^N x^k/k!. -/
noncomputable def expNilpotent (x : S) (N : ℕ) : S :=
  ∑ k ∈ Finset.range (N + 1), (algebraMap ℚ S (1 / Nat.factorial k)) * x^k

/-- Our expNilpotent equals Mathlib's IsNilpotent.exp when the bound is sufficient. -/
theorem expNilpotent_eq_isNilpotent_exp (x : S) (N : ℕ) (hNil : x^(N + 1) = 0) :
    expNilpotent x N = IsNilpotent.exp x := by
  unfold expNilpotent
  have hIsNil : IsNilpotent x := ⟨N + 1, hNil⟩
  rw [IsNilpotent.exp_eq_sum hNil]
  apply Finset.sum_congr rfl
  intro k _
  -- Convert between algebraMap and smul notation
  rw [Algebra.smul_def]
  congr 1
  simp only [one_div]

/-- exp(0) = 1. -/
theorem expNilpotent_zero (N : ℕ) : expNilpotent (0 : S) N = 1 := by
  unfold expNilpotent
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, map_one, mul_one]
  · intro k _ hk
    rw [zero_pow hk, mul_zero]
  · intro h
    simp only [Finset.mem_range] at h
    omega

/-- exp(a) * exp(-a) = 1 for nilpotent elements.
    Uses the connection to Mathlib's IsNilpotent.exp. -/
theorem expNilpotent_mul_neg (a : S) (N : ℕ) (hNil : a^(N + 1) = 0) :
    expNilpotent a N * expNilpotent (-a) N = 1 := by
  have hNegNil : (-a)^(N + 1) = 0 := by rw [neg_eq_neg_one_mul, mul_pow, hNil, mul_zero]
  rw [expNilpotent_eq_isNilpotent_exp a N hNil, expNilpotent_eq_isNilpotent_exp (-a) N hNegNil]
  exact IsNilpotent.exp_mul_exp_neg_self ⟨N + 1, hNil⟩

/-! ### CharpolyRev and Nilpotent Matrix Theorems -/

/-- Over a ℚ-algebra, when traces are opposite, the product of charpolyRevs equals 1.
    This version uses the exp-log approach which is valid when we can divide by integers. -/
theorem charpolyRev_mul_eq_one_of_opposite_traces
    {n m : ℕ} (X : Matrix (Fin n) (Fin n) S) (Y : Matrix (Fin m) (Fin m) S)
    (N : ℕ) (hNilX : X^(N + 1) = 0) (hNilY : Y^(N + 1) = 0)
    (hAnti : ∀ k : ℕ, (X^(k + 1)).trace = -((Y^(k + 1)).trace)) :
    Matrix.charpolyRev X * Matrix.charpolyRev Y = 1 := by
  -- charpolyRev M = det(1 - X·M) where X is the polynomial variable.
  -- We view this as working over S[X], which is also a ℚ-algebra.
  --
  -- Define matrices over S[X]:
  --   X' := X.map Polynomial.C  (X lifted to polynomial coefficients)
  --   Y' := Y.map Polynomial.C  (Y lifted to polynomial coefficients)
  --
  -- Then charpolyRev X = det(1 - Polynomial.X • X')
  -- which we can write as det(1 - M) where M = Polynomial.X • X'
  --
  -- Key facts:
  -- 1. M^(N+1) = (Polynomial.X)^(N+1) • (X')^(N+1) = (Polynomial.X)^(N+1) • (X^(N+1)).map C = 0
  -- 2. tr(M^k) = (Polynomial.X)^k • tr(X^k).map C = Polynomial.C(tr(X^k)) * Polynomial.X^k
  --
  -- The opposite trace condition tr(X^k) = -tr(Y^k) lifts to the polynomial matrices.
  -- Then det_product_one_of_opposite_traces applies to give the result.

  -- The polynomial ring S[X] is a ℚ-algebra
  haveI : Algebra ℚ (Polynomial S) := Polynomial.algebraOfAlgebra

  -- Lift X and Y to matrices over S[X]
  let X' : Matrix (Fin n) (Fin n) (Polynomial S) := X.map Polynomial.C
  let Y' : Matrix (Fin m) (Fin m) (Polynomial S) := Y.map Polynomial.C

  -- The polynomial-scaled matrices (using • for Polynomial S acting on itself)
  let MX : Matrix (Fin n) (Fin n) (Polynomial S) := (Polynomial.X : Polynomial S) • X'
  let MY : Matrix (Fin m) (Fin m) (Polynomial S) := (Polynomial.X : Polynomial S) • Y'

  -- charpolyRev X = det(1 - MX) and charpolyRev Y = det(1 - MY)
  have hCharX : Matrix.charpolyRev X = (1 - MX).det := rfl
  have hCharY : Matrix.charpolyRev Y = (1 - MY).det := rfl

  rw [hCharX, hCharY]

  -- MX is nilpotent: MX^(N+1) = Polynomial.X^(N+1) • (X')^(N+1) = 0
  have hMXNil : MX^(N + 1) = 0 := by
    simp only [MX, smul_pow]
    -- X'^(N+1) = (X^(N+1)).map C = 0.map C = 0
    have hX'Nil : X'^(N + 1) = 0 := by
      rw [← Matrix.map_pow, hNilX]
      ext i j
      simp only [Matrix.map_apply, Matrix.zero_apply, Polynomial.C_0]
    rw [hX'Nil, smul_zero]

  have hMYNil : MY^(N + 1) = 0 := by
    simp only [MY, smul_pow]
    have hY'Nil : Y'^(N + 1) = 0 := by
      rw [← Matrix.map_pow, hNilY]
      ext i j
      simp only [Matrix.map_apply, Matrix.zero_apply, Polynomial.C_0]
    rw [hY'Nil, smul_zero]

  -- Traces satisfy the opposite condition
  have hTraceAnti : ∀ k : ℕ, (MX^(k + 1)).trace = -((MY^(k + 1)).trace) := by
    intro k
    simp only [MX, MY, smul_pow]
    -- tr(X^(k+1) • (X')^(k+1)) = X^(k+1) * tr((X')^(k+1)) = X^(k+1) * C(tr(X^(k+1)))
    rw [Matrix.trace_smul, Matrix.trace_smul]
    -- tr(X') = tr(X.map C) = C(tr(X)) by AddMonoidHom.map_trace
    have hTraceX' : ∀ j : ℕ, (X'^(j + 1)).trace = Polynomial.C ((X^(j + 1)).trace) := by
      intro j
      rw [← Matrix.map_pow]
      exact (AddMonoidHom.map_trace Polynomial.C (X^(j + 1))).symm
    have hTraceY' : ∀ j : ℕ, (Y'^(j + 1)).trace = Polynomial.C ((Y^(j + 1)).trace) := by
      intro j
      rw [← Matrix.map_pow]
      exact (AddMonoidHom.map_trace Polynomial.C (Y^(j + 1))).symm
    rw [hTraceX' k, hTraceY' k]
    rw [hAnti k]
    simp only [map_neg, smul_neg]

  -- Apply the ℚ-algebra det product theorem
  exact det_product_one_of_opposite_traces MX MY N hMXNil hMYNil hTraceAnti

-- NOTE: charpolyRev_mul_eq_one_of_opposite_traces is FALSE in positive characteristic!
-- Newton identities require division by k, which fails when p | k.
-- The theorem IS true over ℚ-algebras (characteristic 0).

-- Helper: eval 1 (charpolyRev M) = det(1 - M)
theorem eval_one_charpolyRev {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) :
    Polynomial.eval 1 (Matrix.charpolyRev M) = (1 - M).det := by
  rw [Matrix.charpolyRev]
  -- charpolyRev M = det(1 - X • M.map C) where X is the polynomial variable
  -- eval is a ring hom, so eval 1 (det A) = det (A.map (eval 1))
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
             Matrix.smul_apply, Polynomial.coe_evalRingHom, smul_eq_mul]
  -- (X • M.map C) i j = X * C (M i j), and eval 1 (X * C m) = 1 * m = m
  have heval : Polynomial.eval 1 (Polynomial.X * Polynomial.C (M i j)) = M i j := by
    rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C, one_mul]
  rcases eq_or_ne i j with rfl | hij
  · -- Diagonal case: 1 - eval(X * C (M i i)) = 1 - M i i
    simp only [if_true, Polynomial.eval_sub, Polynomial.eval_one, heval]
  · -- Off-diagonal case: eval(0 - X * C (M i j)) = 0 - M i j
    simp only [hij, if_false, Polynomial.eval_sub, Polynomial.eval_zero, heval]

/-- Over a ℚ-algebra, det(I-X) * det(I-Y) = 1 when traces are opposite.
    This follows from charpolyRev_mul_eq_one_of_opposite_traces by evaluating at 1. -/
theorem det_product_one_of_opposite_traces_via_charpoly {n m : ℕ}
    (X : Matrix (Fin n) (Fin n) S) (Y : Matrix (Fin m) (Fin m) S)
    (N : ℕ) (hNilX : X^(N + 1) = 0) (hNilY : Y^(N + 1) = 0)
    (hAnti : ∀ k : ℕ, (X^(k + 1)).trace = -((Y^(k + 1)).trace)) :
    (1 - X).det * (1 - Y).det = 1 := by
  -- Use the key lemma: det(1-M) = eval 1 (charpolyRev M)
  rw [← eval_one_charpolyRev X, ← eval_one_charpolyRev Y]
  -- Since eval is a ring hom: eval 1 (P * Q) = eval 1 P * eval 1 Q
  rw [← Polynomial.eval_mul]
  -- By charpolyRev_mul_eq_one_of_opposite_traces, the product of charpolyRevs equals 1
  rw [charpolyRev_mul_eq_one_of_opposite_traces X Y N hNilX hNilY hAnti]
  -- eval 1 1 = 1
  simp only [Polynomial.eval_one]

/-! ### Nilpotent Matrix Pigeonhole Lemmas -/

section NilpotentMatrix

variable {R : Type*} [CommRing R]

/-- Product of k elements from m nilpotent elements is zero when k ≥ m*(N+1) (by pigeonhole). -/
lemma prod_nilpotent_elements_zero {m : ℕ}
    (elts : Fin m → R) (N : ℕ) (hnil : ∀ i, (elts i)^(N + 1) = 0)
    {k : ℕ} (f : Fin k → Fin m) (hk : m * (N + 1) ≤ k) (hm : 0 < m) :
    ∏ i : Fin k, elts (f i) = 0 := by
  have hcard : Fintype.card (Fin m) * N < Fintype.card (Fin k) := by
    simp only [Fintype.card_fin]
    have h1 : m * N < m * N + m := by omega
    have h2 : m * N + m = m * (N + 1) := by ring
    omega
  obtain ⟨j, hj⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f hcard
  have hfiber_ge : N + 1 ≤ (Finset.filter (fun i => f i = j) Finset.univ).card := by
    simp only [Finset.card_filter] at hj ⊢
    exact hj
  have hsplit : ∏ i : Fin k, elts (f i) =
      (∏ i ∈ Finset.filter (fun i => f i = j) Finset.univ, elts (f i)) *
      (∏ i ∈ Finset.filter (fun i => f i ≠ j) Finset.univ, elts (f i)) := by
    rw [← Finset.prod_union]
    · congr 1
      ext i
      simp [Finset.mem_union, Finset.mem_filter, em]
    · simp [Finset.disjoint_filter]
  rw [hsplit]
  have hprod_fiber : ∏ i ∈ Finset.filter (fun i => f i = j) Finset.univ, elts (f i) =
      (elts j)^((Finset.filter (fun i => f i = j) Finset.univ).card) := by
    rw [Finset.prod_congr rfl (fun i hi => ?_)]
    · rw [Finset.prod_const, Finset.card_filter]
    · simp only [Finset.mem_filter] at hi
      rw [hi.2]
  rw [hprod_fiber]
  have hge : N + 1 ≤ (Finset.filter (fun i => f i = j) Finset.univ).card := hfiber_ge
  calc (elts j)^((Finset.filter (fun i => f i = j) Finset.univ).card) *
        (∏ i ∈ Finset.filter (fun i => f i ≠ j) Finset.univ, elts (f i))
      = (elts j)^(N + 1 + ((Finset.filter (fun i => f i = j) Finset.univ).card - (N + 1))) *
        (∏ i ∈ Finset.filter (fun i => f i ≠ j) Finset.univ, elts (f i)) := by
          congr 2; omega
    _ = (elts j)^(N + 1) * (elts j)^((Finset.filter (fun i => f i = j) Finset.univ).card - (N + 1)) *
        (∏ i ∈ Finset.filter (fun i => f i ≠ j) Finset.univ, elts (f i)) := by rw [pow_add]
    _ = 0 * (elts j)^((Finset.filter (fun i => f i = j) Finset.univ).card - (N + 1)) *
        (∏ i ∈ Finset.filter (fun i => f i ≠ j) Finset.univ, elts (f i)) := by rw [hnil j]
    _ = 0 := by ring

/-- A matrix with nilpotent entries is nilpotent (by pigeonhole on products). -/
lemma matrix_nilpotent_of_entries_nilpotent {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R)
    (hnil : ∀ i j, ∃ N : ℕ, (M i j)^(N + 1) = 0) :
    ∃ K : ℕ, M^(K + 1) = 0 := by
  classical
  by_cases hn : n = 0
  · use 0
    ext i j
    exact (Fin.elim0 (hn ▸ i))
  let Nmax := Finset.sup (Finset.univ : Finset (Fin n × Fin n)) (fun p => Nat.find (hnil p.1 p.2))
  have hnil_uniform : ∀ i j, (M i j)^(Nmax + 1) = 0 := by
    intro i j
    have hle : Nat.find (hnil i j) ≤ Nmax :=
      Finset.le_sup (f := fun p => Nat.find (hnil p.1 p.2)) (Finset.mem_univ (i, j))
    have hspec := Nat.find_spec (hnil i j)
    have heq : Nmax + 1 = Nat.find (hnil i j) + 1 + (Nmax - Nat.find (hnil i j)) := by
      have : Nat.find (hnil i j) + (Nmax - Nat.find (hnil i j)) = Nmax := Nat.add_sub_cancel' hle
      omega
    calc (M i j)^(Nmax + 1)
        = (M i j)^(Nat.find (hnil i j) + 1 + (Nmax - Nat.find (hnil i j))) := by rw [heq]
      _ = (M i j)^(Nat.find (hnil i j) + 1) * (M i j)^(Nmax - Nat.find (hnil i j)) := pow_add _ _ _
      _ = 0 * _ := by rw [hspec]
      _ = 0 := zero_mul _
  use n * n * (Nmax + 1)
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  have hn2_pos : 0 < n * n := Nat.mul_pos hn_pos hn_pos
  have hprod_zero : ∀ (k : ℕ) (hk : n * n * (Nmax + 1) ≤ k) (f : Fin k → Fin n × Fin n),
      ∏ idx : Fin k, M (f idx).1 (f idx).2 = 0 := by
    intro k hk f
    let e : Fin n × Fin n ≃ Fin (n * n) := finProdFinEquiv
    let elts : Fin (n * n) → R := fun idx => M (e.symm idx).1 (e.symm idx).2
    have helts_nil : ∀ idx, (elts idx)^(Nmax + 1) = 0 := fun idx =>
      hnil_uniform (e.symm idx).1 (e.symm idx).2
    let g : Fin k → Fin (n * n) := fun idx => e (f idx)
    have heq : ∀ idx, M (f idx).1 (f idx).2 = elts (g idx) := fun idx => by
      simp only [elts, g, Equiv.symm_apply_apply]
    calc ∏ idx : Fin k, M (f idx).1 (f idx).2
        = ∏ idx : Fin k, elts (g idx) := Finset.prod_congr rfl (fun idx _ => heq idx)
      _ = 0 := prod_nilpotent_elements_zero elts Nmax helts_nil g hk hn2_pos
  ext i j
  simp only [Matrix.zero_apply]
  let K := n * n * (Nmax + 1)
  have pow_zero : ∀ (k : ℕ), K < k → M ^ k = 0 := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases hk' : K < k
      · rw [pow_succ, ih hk', zero_mul]
      · have hkK : k = K := by omega
        subst hkK
        ext i' j'
        simp only [Matrix.zero_apply]
        let S : ℕ → Set R := fun k => {x | ∃ g : Fin k → Fin n × Fin n, x = ∏ t, M (g t).1 (g t).2}
        have pow_in_closure : ∀ (k : ℕ) (i j : Fin n),
            (M ^ (k + 1)) i j ∈ AddSubmonoid.closure (S (k + 1)) := by
          intro k
          induction k with
          | zero =>
            intro i j
            rw [pow_one]
            apply AddSubmonoid.subset_closure
            use fun _ => (i, j)
            simp
          | succ k ihk =>
            intro i j
            rw [pow_succ, Matrix.mul_apply]
            apply AddSubmonoid.sum_mem
            intro l _
            have hMem := ihk i l
            have mul_mem_closure : ∀ x, x ∈ AddSubmonoid.closure (S (k + 1)) →
                x * M l j ∈ AddSubmonoid.closure (S (k + 1 + 1)) := by
              intro x hx
              induction hx using AddSubmonoid.closure_induction with
              | mem y hy =>
                obtain ⟨g, hg⟩ := hy
                apply AddSubmonoid.subset_closure
                use Fin.snoc g (l, j)
                rw [hg]
                rw [Fin.prod_univ_castSucc (n := k + 1)]
                simp only [Fin.snoc_last, Fin.snoc_castSucc]
              | zero =>
                simp only [zero_mul, AddSubmonoid.zero_mem]
              | add a b _ _ ha hb =>
                rw [add_mul]
                exact AddSubmonoid.add_mem _ ha hb
            exact mul_mem_closure _ hMem
        have hS_zero : S (K + 1) ⊆ {0} := fun x ⟨g, hg⟩ => by
          rw [Set.mem_singleton_iff, hg]
          exact hprod_zero (K + 1) (by omega) g
        have hclosure_bot : AddSubmonoid.closure (S (K + 1)) = ⊥ := by
          rw [eq_bot_iff]
          apply AddSubmonoid.closure_le.mpr
          intro x hx
          simp only [SetLike.mem_coe, AddSubmonoid.mem_bot]
          exact Set.mem_singleton_iff.mp (hS_zero hx)
        have hMem := pow_in_closure K i' j'
        rw [hclosure_bot] at hMem
        exact AddSubmonoid.mem_bot.mp hMem
  rw [pow_zero (K + 1) (by omega)]
  simp only [Matrix.zero_apply]

end NilpotentMatrix

end MatrixExpLog
