import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.Algebra.Rat
import ModularPhysics.StringGeometry.Supermanifolds.Superalgebra
import ModularPhysics.StringGeometry.Supermanifolds.Helpers.SuperMatrix
import ModularPhysics.StringGeometry.Supermanifolds.Helpers.FormalPowerSeries

/-!
# Matrix Parity Lemmas and Grassmann Properties

This file contains lemmas about matrix multiplication preserving parity (odd/even)
and key Grassmann algebra identities involving traces and determinants.

## Main results

* `grassmann_trace_anticomm` - tr(BC) = -tr(CB) for odd matrices B, C
* `grassmann_trace_pow_anticomm` - tr((BC)^k) = -tr((CB)^k) for odd matrices
* `grassmann_det_one_sub_mul_comm` - det(I-BC) * det(I-CB) = 1 for odd matrices
* `matrix_mul_odd_odd` - Product of odd matrices has even entries
* `matrix_mul_odd_even` - Product of odd and even matrices has odd entries

## Mathematical Background

In a supercommutative algebra, odd elements anticommute: ab = -ba for odd a, b.
This leads to crucial trace properties for matrices with odd entries.
-/

namespace Supermanifolds.Helpers

open Supermanifolds
open FormalPowerSeries
open MatrixExpLog

/-- For matrices B, C with odd entries in a supercommutative algebra, tr(BC) = -tr(CB). -/
theorem grassmann_trace_anticomm {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    [hSC : SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (B : Matrix (Fin n) (Fin m) Λ.carrier) (C : Matrix (Fin m) (Fin n) Λ.carrier)
    (hB : ∀ i j, B i j ∈ Λ.odd) (hC : ∀ i j, C i j ∈ Λ.odd) :
    (B * C).trace = -((C * B).trace) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  simp only [← Finset.sum_neg_distrib]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact @SuperCommutative.odd_anticomm k _ Λ.toSuperAlgebra hSC (B i j) (C j i) (hB i j) (hC j i)

/-! ### Determinant and Adjugate on evenCarrier

The theorems below work with matrices over `Λ.evenCarrier` (which is a `CommRing`),
not `Λ.carrier` (which is only a `Ring`).

For matrices with even entries in `Λ.carrier`, use `Λ.liftEvenMatrix` to lift them
to `Λ.evenCarrier` before computing determinants. -/

/-- The determinant of a matrix over evenCarrier. Trivially in evenCarrier by type. -/
theorem det_evenCarrier {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k} {n : ℕ}
    (M : Matrix (Fin n) (Fin n) Λ.evenCarrier) : M.det ∈ Set.univ :=
  Set.mem_univ _

/-- Each entry of the adjugate matrix over evenCarrier. -/
theorem adjugate_evenCarrier {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k} {n : ℕ}
    (M : Matrix (Fin n) (Fin n) Λ.evenCarrier) (i j : Fin n) : M.adjugate i j ∈ Set.univ :=
  Set.mem_univ _

/-- The inverse of an invertible matrix over evenCarrier is in evenCarrier.
    Since evenCarrier has CommRing structure, matrix inverse is well-defined. -/
theorem matrix_inv_evenCarrier {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k} {n : ℕ}
    (M : Matrix (Fin n) (Fin n) Λ.evenCarrier)
    (_hdet : Λ.IsInvertible M.det) (i j : Fin n) : M⁻¹ i j ∈ Set.univ :=
  Set.mem_univ _

/-- Matrix product of odd × even matrices has odd entries. -/
theorem matrix_mul_odd_even {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m p : ℕ}
    (C : Matrix (Fin n) (Fin m) Λ.carrier) (M : Matrix (Fin m) (Fin p) Λ.carrier)
    (hC : ∀ i j, C i j ∈ Λ.odd) (hM : ∀ i j, M i j ∈ Λ.even) :
    ∀ i j, (C * M) i j ∈ Λ.odd := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Λ.odd.sum_mem
  intro k _
  exact Λ.odd_mul_even _ _ (hC i k) (hM k j)

/-- Matrix product of even × odd matrices has odd entries. -/
theorem matrix_mul_even_odd {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m p : ℕ}
    (M : Matrix (Fin n) (Fin m) Λ.carrier) (C : Matrix (Fin m) (Fin p) Λ.carrier)
    (hM : ∀ i j, M i j ∈ Λ.even) (hC : ∀ i j, C i j ∈ Λ.odd) :
    ∀ i j, (M * C) i j ∈ Λ.odd := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Λ.odd.sum_mem
  intro k _
  exact Λ.even_mul_odd _ _ (hM i k) (hC k j)

/-- Matrix product of odd × odd matrices has even entries. -/
theorem matrix_mul_odd_odd {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m p : ℕ}
    (B : Matrix (Fin n) (Fin m) Λ.carrier) (C : Matrix (Fin m) (Fin p) Λ.carrier)
    (hB : ∀ i j, B i j ∈ Λ.odd) (hC : ∀ i j, C i j ∈ Λ.odd) :
    ∀ i j, (B * C) i j ∈ Λ.even := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Λ.even.sum_mem
  intro k _
  exact Λ.odd_mul_odd _ _ (hB i k) (hC k j)

/-- Matrix product of even × even matrices has even entries. -/
theorem matrix_mul_even_even {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m p : ℕ}
    (M : Matrix (Fin n) (Fin m) Λ.carrier) (N : Matrix (Fin m) (Fin p) Λ.carrier)
    (hM : ∀ i j, M i j ∈ Λ.even) (hN : ∀ i j, N i j ∈ Λ.even) :
    ∀ i j, (M * N) i j ∈ Λ.even := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Λ.even.sum_mem
  intro k _
  exact Λ.even_mul_even _ _ (hM i k) (hN k j)

/-- Power of a matrix with even entries has even entries. -/
theorem matrix_pow_even {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n : ℕ} (k : ℕ)
    (M : Matrix (Fin n) (Fin n) Λ.carrier)
    (hM : ∀ i j, M i j ∈ Λ.even)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0 : (0 : Λ.carrier) ∈ Λ.even) :
    ∀ i j, (M^k) i j ∈ Λ.even := by
  induction k with
  | zero =>
    intro i j
    simp only [pow_zero, Matrix.one_apply]
    split_ifs with h
    · exact h1
    · exact h0
  | succ k ih =>
    intro i j
    rw [pow_succ]
    exact matrix_mul_even_even _ _ ih hM i j

/-- For matrices B (odd) and C (odd), C * (B * C)^k has odd entries. -/
theorem matrix_C_BC_pow_odd {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (k : ℕ)
    (B : Matrix (Fin n) (Fin m) Λ.carrier) (C : Matrix (Fin m) (Fin n) Λ.carrier)
    (hB : ∀ i j, B i j ∈ Λ.odd) (hC : ∀ i j, C i j ∈ Λ.odd)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0 : (0 : Λ.carrier) ∈ Λ.even) :
    ∀ i j, (C * (B * C)^k) i j ∈ Λ.odd := by
  intro i j
  have hBCk_even : ∀ i j, ((B * C)^k) i j ∈ Λ.even :=
    matrix_pow_even k (B * C) (matrix_mul_odd_odd B C hB hC) h1 h0
  exact matrix_mul_odd_even C _ hC hBCk_even i j

/-- The trace anticommutation identity for powers: tr((BC)^(k+1)) = -tr((CB)^(k+1)) -/
theorem grassmann_trace_pow_anticomm {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    [hSC : SuperCommutative Λ.toSuperAlgebra] {n m : ℕ} (k : ℕ)
    (B : Matrix (Fin n) (Fin m) Λ.carrier) (C : Matrix (Fin m) (Fin n) Λ.carrier)
    (hB : ∀ i j, B i j ∈ Λ.odd) (hC : ∀ i j, C i j ∈ Λ.odd)
    (h1even : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even) :
    ((B * C)^(k + 1)).trace = -(((C * B)^(k + 1)).trace) := by
  have heq1 : (B * C)^(k + 1) = B * (C * (B * C)^k) := by
    rw [pow_succ', Matrix.mul_assoc]
  have hshift : ∀ j : ℕ, (C * B)^j * C = C * (B * C)^j := by
    intro j
    induction j with
    | zero => simp only [pow_zero, Matrix.one_mul, Matrix.mul_one]
    | succ j ih =>
      rw [pow_succ, Matrix.mul_assoc ((C * B)^j) (C * B) C]
      rw [Matrix.mul_assoc C B C]
      rw [← Matrix.mul_assoc ((C * B)^j) C (B * C)]
      rw [ih]
      rw [Matrix.mul_assoc C ((B * C)^j) (B * C), ← pow_succ]
  have heq2 : (C * B)^(k + 1) = C * (B * C)^k * B := by
    calc (C * B)^(k + 1)
        = (C * B)^k * (C * B) := by rw [pow_succ]
      _ = (C * B)^k * C * B := by rw [Matrix.mul_assoc]
      _ = C * (B * C)^k * B := by rw [hshift k]
  set X := C * (B * C)^k with hX_def
  have hX_odd : ∀ i j, X i j ∈ Λ.odd := matrix_C_BC_pow_odd k B C hB hC h1even h0even
  have heq3 : (B * X).trace = -((X * B).trace) := grassmann_trace_anticomm B X hB hX_odd
  rw [heq1, heq3, heq2, hX_def, Matrix.mul_assoc]

/-- The sum of traces for a matrix. -/
def sumTraces {S : Type*} [Ring S] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) S) (N : ℕ) : S :=
  ∑ k ∈ Finset.range N, (X^(k + 1)).trace

/-- When traces are opposite, sumTraces X N + sumTraces Y N = 0. -/
theorem sumTraces_add_neg {S : Type*} [Ring S] {n m : ℕ}
    (X : Matrix (Fin n) (Fin n) S) (Y : Matrix (Fin m) (Fin m) S) (N : ℕ)
    (hAnti : ∀ k : ℕ, k < N → (X^(k + 1)).trace = -((Y^(k + 1)).trace)) :
    sumTraces X N + sumTraces Y N = 0 := by
  unfold sumTraces
  have h : ∀ k ∈ Finset.range N,
      (X^(k + 1)).trace + (Y^(k + 1)).trace = 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [hAnti k hk, add_comm k 1]
    simp only [neg_add_cancel]
  calc ∑ k ∈ Finset.range N, (X^(k + 1)).trace +
       ∑ k ∈ Finset.range N, (Y^(k + 1)).trace
      = ∑ k ∈ Finset.range N, ((X^(k + 1)).trace + (Y^(k + 1)).trace) := by
        rw [← Finset.sum_add_distrib]
    _ = ∑ k ∈ Finset.range N, (0 : S) := by
        apply Finset.sum_congr rfl h
    _ = 0 := by simp

/-- det(I - X) is a polynomial in the entries of X by the Leibniz formula. -/
theorem det_one_sub_nilpotent_char_poly {S : Type*} [CommRing S] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) S) (_N : ℕ) (_hNil : X^(_N + 1) = 0) :
    ∃ (p : MvPolynomial (Fin n × Fin n) S), (1 - X).det = MvPolynomial.eval (fun ij => X ij.1 ij.2) p := by
  classical
  let p : MvPolynomial (Fin n × Fin n) S :=
    ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
      ∏ i : Fin n, (MvPolynomial.C (if σ i = i then 1 else 0) -
                    MvPolynomial.X (σ i, i))
  use p
  simp only [p, map_sum]
  rw [Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  have heval_prod : MvPolynomial.eval (fun ij => X ij.1 ij.2)
      (∏ i : Fin n, (MvPolynomial.C (if σ i = i then 1 else 0) - MvPolynomial.X (σ i, i))) =
      ∏ i : Fin n, (1 - X) (σ i) i := by
    rw [MvPolynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro i _
    simp only [MvPolynomial.eval_sub, MvPolynomial.eval_C, MvPolynomial.eval_X,
               Matrix.sub_apply, Matrix.one_apply]
  let evalX : MvPolynomial (Fin n × Fin n) S →+* S :=
    MvPolynomial.eval (fun ij : Fin n × Fin n => X ij.1 ij.2)
  have h_zsmul : evalX
      (Equiv.Perm.sign σ • ∏ i : Fin n, (MvPolynomial.C (if σ i = i then 1 else 0) - MvPolynomial.X (σ i, i))) =
      Equiv.Perm.sign σ • evalX
      (∏ i : Fin n, (MvPolynomial.C (if σ i = i then 1 else 0) - MvPolynomial.X (σ i, i))) := by
    exact AddMonoidHom.map_zsmul evalX.toAddMonoidHom _ _
  simp only [evalX] at h_zsmul
  rw [h_zsmul, heval_prod]

/-- The k-th elementary symmetric polynomial via Newton's identities. Requires a Field. -/
noncomputable def newtonESymm {S : Type*} [Field S] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) S) : ℕ → S
  | 0 => 1
  | k + 1 => (1 / (k + 1 : S)) * ∑ i ∈ Finset.range (k + 1),
      (-1 : S)^i * newtonESymm X (k - i) * (X^(i + 1)).trace

/-- Scaled elementary symmetric polynomial (no division needed). -/
def newtonESymmScaled {S : Type*} [CommRing S] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) S) : ℕ → S
  | 0 => 1
  | k + 1 => ∑ i ∈ Finset.range (k + 1),
      (-1 : S)^i * newtonESymmScaled X (k - i) * (X^(i + 1)).trace

/-- In a Grassmann algebra, odd elements are nilpotent.
    This uses the `odd_nilpotent` property from the GrassmannAlgebra structure. -/
lemma odd_nilpotent {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    (x : Λ.carrier) (hx : x ∈ Λ.odd) : ∃ N : ℕ, x^(N + 1) = 0 :=
  Λ.odd_nilpotent x hx

/-- Product of two odd elements is nilpotent: (xy)² = x(yx)y = x(-xy)y = -x²y² = 0. -/
lemma isNilpotent_odd_mul_odd {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    [hSC : SuperCommutative Λ.toSuperAlgebra]
    (x y : Λ.carrier) (hx : x ∈ Λ.odd) (hy : y ∈ Λ.odd) : IsNilpotent (x * y) := by
  -- yx = -xy by anticommutativity
  have hyx : y * x = -(x * y) := by
    have h := @SuperCommutative.odd_anticomm k _ Λ.toSuperAlgebra hSC x y hx hy
    rw [h, neg_neg]
  -- x² = 0 (from x² = -x² and CharZero)
  have hx2_zero : x * x = 0 := by
    have hx2 : x * x = -(x * x) := @SuperCommutative.odd_anticomm k _ Λ.toSuperAlgebra hSC x x hx hx
    -- From a = -a we get a + a = 0, i.e., 2 • a = 0
    have h2 : x * x + x * x = 0 := by
      conv_lhs => rhs; rw [hx2]
      exact add_neg_cancel (x * x)
    -- x*x + x*x = 2 • (x*x) in a k-module
    rw [← two_smul k (x * x)] at h2
    -- Since k has CharZero, (2 : k) ≠ 0, so smul by 2 is injective
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  -- (xy)² = x(yx)y = x(-xy)y = -x²y² = 0
  refine ⟨2, ?_⟩
  show (x * y) ^ 2 = 0
  rw [sq]
  calc (x * y) * (x * y)
      = x * (y * x * y) := by rw [mul_assoc, mul_assoc]
    _ = x * (-(x * y) * y) := by rw [hyx]
    _ = x * (-(x * y * y)) := by rw [neg_mul]
    _ = -(x * (x * y * y)) := by rw [mul_neg]
    _ = -(x * (x * (y * y))) := by rw [mul_assoc x y y]
    _ = -((x * x) * (y * y)) := by rw [← mul_assoc]
    _ = -(0 * (y * y)) := by rw [hx2_zero]
    _ = 0 := by rw [zero_mul, neg_zero]

/-- Body of zero in evenCarrier is zero. -/
lemma body_zero {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k} : Λ.body 0 = 0 := by
  have h1 : Λ.body (0 + 0) = Λ.body 0 + Λ.body 0 := Λ.body_add 0 0
  simp only [add_zero] at h1
  have : Λ.body 0 + Λ.body 0 = Λ.body 0 + 0 := by rw [← h1, add_zero]
  exact add_left_cancel this

/-- Each entry of B * C (odd × odd) is nilpotent. -/
lemma isNilpotent_matrix_mul_odd_odd_entry {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    [hSC : SuperCommutative Λ.toSuperAlgebra]
    {n m : ℕ} (B : Matrix (Fin n) (Fin m) Λ.carrier) (C : Matrix (Fin m) (Fin n) Λ.carrier)
    (hB : ∀ i j, B i j ∈ Λ.odd) (hC : ∀ i j, C i j ∈ Λ.odd)
    (i : Fin n) (j : Fin n) : IsNilpotent ((B * C) i j) := by
  simp only [Matrix.mul_apply]
  have hterm : ∀ l : Fin m, IsNilpotent (B i l * C l j) :=
    fun l => isNilpotent_odd_mul_odd (B i l) (C l j) (hB i l) (hC l j)
  -- Each term is even (odd × odd = even), and even elements commute
  have hterm_even : ∀ l : Fin m, B i l * C l j ∈ Λ.even :=
    fun l => Λ.odd_mul_odd _ _ (hB i l) (hC l j)
  have hcomm : ∀ l1 l2 : Fin m, Commute (B i l1 * C l1 j) (B i l2 * C l2 j) := fun l1 l2 =>
    @SuperCommutative.even_comm_even k _ Λ.toSuperAlgebra hSC _ _ (hterm_even l1) (hterm_even l2)
  exact Commute.isNilpotent_sum (fun l _ => hterm l) (fun l1 l2 _ _ => hcomm l1 l2)

/-- Product of matrices with odd entries is nilpotent (on evenCarrier).

    Since B*C has even entries, we lift it to evenCarrier (CommRing)
    where the matrix nilpotency theorem applies. -/
lemma odd_matrix_product_nilpotent {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (B : Matrix (Fin n) (Fin m) Λ.carrier) (C : Matrix (Fin m) (Fin n) Λ.carrier)
    (hB : ∀ i j, B i j ∈ Λ.odd) (hC : ∀ i j, C i j ∈ Λ.odd) :
    let hBC := matrix_mul_odd_odd B C hB hC
    let BC_lifted := Λ.liftEvenMatrix (B * C) hBC
    ∃ N : ℕ, BC_lifted^(N + 1) = 0 := by
  intro hBC BC_lifted
  -- Each entry of BC_lifted is nilpotent in evenCarrier (CommRing)
  have hentry_nil : ∀ i j, ∃ N : ℕ, (BC_lifted i j)^(N + 1) = 0 := by
    intro i j
    -- BC_lifted i j = liftEven ((B*C) i j)
    -- The element (B*C) i j is nilpotent in carrier
    have hnil_carrier := isNilpotent_matrix_mul_odd_odd_entry B C hB hC i j
    obtain ⟨n, hn⟩ := hnil_carrier
    cases n with
    | zero =>
      use 0
      rw [pow_one]
      -- hn : ((B*C) i j)^0 = 0, i.e., 1 = 0 in carrier
      have h1eq0 : (1 : Λ.carrier) = 0 := by rw [← pow_zero ((B * C) i j)]; exact hn
      -- This means evenCarrier is also trivial (since evenToCarrier 1 = 1)
      have h1eq0_even : (1 : Λ.evenCarrier) = 0 := by
        apply Λ.evenToCarrier_injective
        rw [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
        exact h1eq0
      calc BC_lifted i j = BC_lifted i j * 1 := (mul_one _).symm
        _ = BC_lifted i j * 0 := by rw [h1eq0_even]
        _ = 0 := mul_zero _
    | succ m =>
      use m
      -- Need: (BC_lifted i j)^(m+1) = 0
      -- We have: ((B*C) i j)^(m+1) = 0 in carrier
      -- BC_lifted i j = liftEven ((B*C) i j)
      -- Since evenToCarrier (liftEven x) = x, and evenToCarrier preserves multiplication,
      -- evenToCarrier ((BC_lifted i j)^(m+1)) = ((B*C) i j)^(m+1) = 0
      -- Since evenToCarrier is injective, (BC_lifted i j)^(m+1) = 0
      apply Λ.evenToCarrier_injective
      have hlift : Λ.evenToCarrier (BC_lifted i j) = (B * C) i j := Λ.liftEvenMatrix_spec (B * C) hBC i j
      -- evenToCarrier ((BC_lifted i j)^(m+1)) = (evenToCarrier (BC_lifted i j))^(m+1)
      rw [map_pow, hlift, hn, Λ.evenToCarrier.map_zero]
  exact matrix_nilpotent_of_entries_nilpotent BC_lifted hentry_nil

/-- det(I - BC) * det(I - CB) = 1 for odd matrices B, C (on evenCarrier).
    This is a key identity for the Berezinian multiplicativity.

    The matrices B*C and C*B have even entries, so they are lifted to
    evenCarrier (CommRing) where det is well-defined. -/
theorem grassmann_det_one_sub_mul_comm {k : Type*} [Field k] [CharZero k]
    {Λ : GrassmannAlgebra k} [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (B : Matrix (Fin n) (Fin m) Λ.carrier) (C : Matrix (Fin m) (Fin n) Λ.carrier)
    (hB : ∀ i j, B i j ∈ Λ.odd) (hC : ∀ i j, C i j ∈ Λ.odd)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0 : (0 : Λ.carrier) ∈ Λ.even) :
    let hBC := matrix_mul_odd_odd B C hB hC
    let hCB := matrix_mul_odd_odd C B hC hB
    let BC_lifted := Λ.liftEvenMatrix (B * C) hBC
    let CB_lifted := Λ.liftEvenMatrix (C * B) hCB
    (1 - BC_lifted).det * (1 - CB_lifted).det = 1 := by
  intro hBC hCB BC_lifted CB_lifted
  -- evenCarrier is a CommRing with Algebra ℚ structure
  letI : Algebra ℚ Λ.evenCarrier := Algebra.compHom Λ.evenCarrier (algebraMap ℚ k)
  -- Get nilpotency bounds
  obtain ⟨N_BC, hNilBC⟩ := odd_matrix_product_nilpotent B C hB hC
  obtain ⟨N_CB, hNilCB⟩ := odd_matrix_product_nilpotent C B hC hB
  let N := max N_BC N_CB
  have hNilBC' : BC_lifted^(N + 1) = 0 := by
    have hpow : N + 1 = N_BC + 1 + (N - N_BC) := by omega
    rw [hpow, pow_add, hNilBC, zero_mul]
  have hNilCB' : CB_lifted^(N + 1) = 0 := by
    have hpow : N + 1 = N_CB + 1 + (N - N_CB) := by omega
    rw [hpow, pow_add, hNilCB, zero_mul]
  -- Trace anticommutation lifts to evenCarrier
  have hTraceAnti : ∀ j : ℕ, (BC_lifted^(j + 1)).trace = -((CB_lifted^(j + 1)).trace) := by
    intro j
    -- First show that evenToCarrier (M_lifted^p) = M^p for any p
    have hBC_pow : ∀ p : ℕ, ∀ i₁ i₂, Λ.evenToCarrier ((BC_lifted^p) i₁ i₂) = ((B * C)^p) i₁ i₂ := by
      intro p
      induction p with
      | zero =>
        intro i₁ i₂
        simp only [pow_zero, Matrix.one_apply]
        split_ifs with h
        · rw [Λ.evenToCarrier.map_one]
        · rw [Λ.evenToCarrier.map_zero]
      | succ p ih =>
        intro i₁ i₂
        simp only [pow_succ, Matrix.mul_apply]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro l _
        rw [Λ.evenToCarrier.map_mul, ih i₁ l, Λ.liftEvenMatrix_spec (B * C) hBC l i₂]
        rfl
    have hCB_pow : ∀ p : ℕ, ∀ i₁ i₂, Λ.evenToCarrier ((CB_lifted^p) i₁ i₂) = ((C * B)^p) i₁ i₂ := by
      intro p
      induction p with
      | zero =>
        intro i₁ i₂
        simp only [pow_zero, Matrix.one_apply]
        split_ifs with h
        · rw [Λ.evenToCarrier.map_one]
        · rw [Λ.evenToCarrier.map_zero]
      | succ p ih =>
        intro i₁ i₂
        simp only [pow_succ, Matrix.mul_apply]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro l _
        rw [Λ.evenToCarrier.map_mul, ih i₁ l, Λ.liftEvenMatrix_spec (C * B) hCB l i₂]
        rfl
    -- trace(BC_lifted^(j+1)) in evenCarrier maps to trace((B*C)^(j+1)) in carrier
    have hBC_trace : Λ.evenToCarrier (BC_lifted^(j + 1)).trace = ((B * C)^(j + 1)).trace := by
      simp only [Matrix.trace, Matrix.diag]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact hBC_pow (j + 1) i i
    have hCB_trace : Λ.evenToCarrier (CB_lifted^(j + 1)).trace = ((C * B)^(j + 1)).trace := by
      simp only [Matrix.trace, Matrix.diag]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact hCB_pow (j + 1) i i
    -- Now use the trace anticomm in carrier
    have hanti_carrier := grassmann_trace_pow_anticomm j B C hB hC h1 h0
    -- And lift back
    apply Λ.evenToCarrier_injective
    rw [hBC_trace, Λ.evenToCarrier.map_neg, hCB_trace, hanti_carrier]
  exact det_product_one_of_opposite_traces BC_lifted CB_lifted N hNilBC' hNilCB' hTraceAnti

end Supermanifolds.Helpers
