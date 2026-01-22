import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Combinatorics.Pigeonhole
import ModularPhysics.StringGeometry.Supermanifolds.Superalgebra
import ModularPhysics.StringGeometry.Supermanifolds.Helpers.SuperMatrix

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

/-- For matrices B, C with odd entries in a supercommutative algebra,
    tr(BC) = -tr(CB).

    B : n × m matrix, C : m × n matrix, both with odd entries.
    BC : n × n matrix, CB : m × m matrix.

    This follows from entry-level anticommutation:
    (BC)ᵢᵢ = Σⱼ Bᵢⱼ Cⱼᵢ where each Bᵢⱼ, Cⱼᵢ is odd
    (CB)ₖₖ = Σₗ Cₖₗ Bₗₖ where each Cₖₗ, Bₗₖ is odd

    By anticommutation: Bᵢⱼ Cⱼᵢ = -Cⱼᵢ Bᵢⱼ
    After reindexing: tr(BC) = Σᵢ Σⱼ Bᵢⱼ Cⱼᵢ = -Σⱼ Σᵢ Cⱼᵢ Bᵢⱼ = -tr(CB) -/
theorem grassmann_trace_anticomm {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
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

/-- The determinant of a matrix with even entries is even. -/
theorem det_even {k : Type*} [Field k] {Λ : GrassmannAlgebra k} {n : ℕ}
    (M : Matrix (Fin n) (Fin n) Λ.carrier)
    (hM : ∀ i j, M i j ∈ Λ.even) (h1 : (1 : Λ.carrier) ∈ Λ.even) : M.det ∈ Λ.even := by
  rw [Matrix.det_apply]
  apply Λ.even.sum_mem
  intro σ _
  have hProd : (Finset.univ : Finset (Fin n)).prod (fun i => M (σ i) i) ∈ Λ.even := by
    apply Finset.prod_induction _ (· ∈ Λ.even)
    · intro a b ha hb; exact Λ.even_mul_even _ _ ha hb
    · exact h1
    · intro i _; exact hM (σ i) i
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign
  · rw [hsign, one_smul]; exact hProd
  · rw [hsign, Units.neg_smul, one_smul]
    exact Λ.even.neg_mem hProd

/-- Each entry of the adjugate matrix is even when the original matrix has even entries. -/
theorem adjugate_even {k : Type*} [Field k] {Λ : GrassmannAlgebra k} {n : ℕ}
    (M : Matrix (Fin n) (Fin n) Λ.carrier)
    (hM : ∀ i j, M i j ∈ Λ.even) (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0 : (0 : Λ.carrier) ∈ Λ.even)
    (i j : Fin n) : M.adjugate i j ∈ Λ.even := by
  rw [Matrix.adjugate_apply]
  apply det_even _ _ h1
  intro i' j'
  simp only [Matrix.updateRow_apply]
  split_ifs with h
  · simp only [Pi.single_apply]
    split_ifs with h'
    · exact h1
    · exact h0
  · exact hM i' j'

/-- The inverse of a matrix with even entries has even entries.

    In a Grassmann algebra, matrix inversion requires det(M) to be invertible
    (i.e., body(det(M)) ≠ 0). The inverse M⁻¹ = adj(M) · (det M)⁻¹ has even entries
    because:
    - adj(M) has even entries (minors of even matrices)
    - det(M)⁻¹ is even (inverse of invertible even element)

    Note: This uses Mathlib's matrix inverse which requires IsUnit det(M),
    which in a Grassmann algebra is equivalent to body(det M) ≠ 0. -/
theorem matrix_inv_even {k : Type*} [Field k] {Λ : GrassmannAlgebra k} {n : ℕ}
    (M : Matrix (Fin n) (Fin n) Λ.carrier)
    (hM : ∀ i j, M i j ∈ Λ.even) (hdet : Λ.IsInvertible M.det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0 : (0 : Λ.carrier) ∈ Λ.even)
    (i j : Fin n) : M⁻¹ i j ∈ Λ.even := by
  -- Derive hscalar from h1: since Λ.even is a Submodule, c • 1 ∈ even for all c
  have hscalar : ∀ c : k, algebraMap k Λ.carrier c ∈ Λ.even := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one]
    exact Λ.even.smul_mem c h1
  -- In a proper Grassmann algebra, matrix inverse is defined via:
  -- M⁻¹ = adj(M) · (det M)⁻¹
  -- where (det M)⁻¹ is computed using the geometric series for invertible elements.
  -- Both adj(M) and (det M)⁻¹ are even, so their product is even.
  have hDetEven : M.det ∈ Λ.even := det_even M hM h1
  have hAdjEven : M.adjugate i j ∈ Λ.even := adjugate_even M hM h1 h0 i j
  -- hdet : Λ.IsInvertible M.det means body(det M) ≠ 0
  -- By isUnit_iff_body_ne_zero, this gives IsUnit M.det
  have hDetIsUnit : IsUnit M.det := (Λ.isUnit_iff_body_ne_zero M.det).mpr hdet
  -- M⁻¹ i j = Ring.inverse M.det • M.adjugate i j by Matrix.inv_def
  rw [Matrix.inv_def, Matrix.smul_apply]
  -- Ring.inverse M.det = ↑(hDetIsUnit.unit⁻¹) by Ring.inverse_of_isUnit
  rw [Ring.inverse_of_isUnit hDetIsUnit]
  -- Now goal is: ↑(hDetIsUnit.unit⁻¹) * M.adjugate i j ∈ Λ.even
  -- hDetIsUnit.unit⁻¹ is the inverse of det M in units, its coercion is (det M)⁻¹
  -- We need to show (det M)⁻¹ ∈ Λ.even
  -- The unit inverse coerces to the ring inverse
  have hUnitInvEven : (↑(hDetIsUnit.unit⁻¹) : Λ.carrier) ∈ Λ.even := by
    -- hDetIsUnit.unit⁻¹ satisfies det M * unit⁻¹ = 1
    -- By uniqueness of inverses, it equals Λ.inv (det M)
    have h_is_inv : M.det * ↑(hDetIsUnit.unit⁻¹) = 1 := by
      have := Units.mul_inv hDetIsUnit.unit
      simp only [IsUnit.unit_spec] at this
      exact this
    have h_inv_is_inv : M.det * Λ.inv M.det hdet = 1 := Λ.mul_inv M.det hdet
    -- By uniqueness of inverses
    have h_eq : (↑(hDetIsUnit.unit⁻¹) : Λ.carrier) = Λ.inv M.det hdet := by
      have hLeft : Λ.inv M.det hdet * M.det = 1 := Λ.inv_mul M.det hdet
      -- ↑(unit⁻¹) * det M = 1 (from Units.inv_mul)
      have hInvMul : (↑(hDetIsUnit.unit⁻¹) : Λ.carrier) * M.det = 1 := by
        have := Units.inv_mul hDetIsUnit.unit
        simp only [IsUnit.unit_spec] at this
        exact this
      calc ↑(hDetIsUnit.unit⁻¹) = ↑(hDetIsUnit.unit⁻¹) * 1 := by rw [mul_one]
        _ = ↑(hDetIsUnit.unit⁻¹) * (M.det * Λ.inv M.det hdet) := by rw [h_inv_is_inv]
        _ = (↑(hDetIsUnit.unit⁻¹) * M.det) * Λ.inv M.det hdet := by rw [mul_assoc]
        _ = 1 * Λ.inv M.det hdet := by rw [hInvMul]
        _ = Λ.inv M.det hdet := by rw [one_mul]
    rw [h_eq]
    exact Λ.even_inv_even M.det hdet hDetEven h1 hscalar
  exact Λ.even_mul_even _ _ hUnitInvEven hAdjEven

/-- Matrix product of odd × even matrices has odd entries. -/
theorem matrix_mul_odd_even {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
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
theorem matrix_mul_even_odd {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
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
theorem matrix_mul_odd_odd {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
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
theorem matrix_mul_even_even {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
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
theorem matrix_pow_even {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
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
theorem matrix_C_BC_pow_odd {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
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
theorem grassmann_trace_pow_anticomm {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
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

/-- The "log det" for a nilpotent matrix X over a ℚ-algebra: -∑_{k=1}^N tr(X^k)/k. -/
noncomputable def logDetNilpotent {S : Type*} [CommRing S] [Algebra ℚ S] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) S) (N : ℕ) : S :=
  -∑ k ∈ Finset.range N, (algebraMap ℚ S (1 / (k + 1 : ℚ))) * (X^(k + 1)).trace

/-- When tr(X^k) = -tr(Y^k) for all k ≥ 1, the log dets sum to zero. -/
theorem logDetNilpotent_opposite {S : Type*} [CommRing S] [Algebra ℚ S] {n m : ℕ}
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

/-- det(I - X) = Σₖ₌₀ⁿ (-1)^k * eₖ(X) via characteristic polynomial. -/
theorem det_eq_alt_sum_esymm {S : Type*} [CommRing S] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) S) :
    (1 - X).det = ∑ k ∈ Finset.range (n + 1), (-1 : S)^k * newtonESymmScaled X k := by
  sorry

/-- Exponential for nilpotent elements over a ℚ-algebra: exp(x) = ∑_{k=0}^N x^k/k!. -/
noncomputable def expNilpotent {S : Type*} [CommRing S] [Algebra ℚ S]
    (x : S) (N : ℕ) : S :=
  ∑ k ∈ Finset.range (N + 1), (algebraMap ℚ S (1 / Nat.factorial k)) * x^k

/-- exp(0) = 1. -/
theorem expNilpotent_zero {S : Type*} [CommRing S] [Algebra ℚ S] (N : ℕ) :
    expNilpotent (0 : S) N = 1 := by
  unfold expNilpotent
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, map_one, mul_one]
  · intro k _ hk
    rw [zero_pow hk, mul_zero]
  · intro h
    simp only [Finset.mem_range] at h
    omega

/-- exp(a) * exp(-a) = 1 for nilpotent elements (via binomial theorem). -/
theorem expNilpotent_mul_neg {S : Type*} [CommRing S] [Algebra ℚ S]
    (a : S) (N : ℕ) (hNil : a^(N + 1) = 0) :
    expNilpotent a N * expNilpotent (-a) N = 1 := by
  sorry

/-- det(I - X) = exp(logDetNilpotent X N) for nilpotent X (Jacobi's formula). -/
theorem det_eq_exp_logDet {S : Type*} [CommRing S] [Algebra ℚ S] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) S) (N : ℕ) (hNil : X^(N + 1) = 0) :
    (1 - X).det = expNilpotent (logDetNilpotent X N) N := by
  sorry

/-- Product identity for ℚ-algebras: det(I-X) * det(I-Y) = 1 when traces are opposite. -/
theorem det_product_one_of_opposite_traces_rat {S : Type*} [CommRing S] [Algebra ℚ S] {n m : ℕ}
    (X : Matrix (Fin n) (Fin n) S) (Y : Matrix (Fin m) (Fin m) S)
    (N : ℕ) (hNilX : X^(N + 1) = 0) (hNilY : Y^(N + 1) = 0)
    (hAnti : ∀ k : ℕ, (X^(k + 1)).trace = -((Y^(k + 1)).trace)) :
    (1 - X).det * (1 - Y).det = 1 := by
  rw [det_eq_exp_logDet X N hNilX, det_eq_exp_logDet Y N hNilY]
  have hSum : logDetNilpotent X N + logDetNilpotent Y N = 0 := logDetNilpotent_opposite X Y N hAnti
  have hLogY : logDetNilpotent Y N = -logDetNilpotent X N := by
    have h : logDetNilpotent Y N + logDetNilpotent X N = 0 := by rw [add_comm]; exact hSum
    exact eq_neg_of_add_eq_zero_left h
  rw [hLogY]
  sorry

/-- det(I-X) * det(I-Y) = 1 for nilpotent X, Y with opposite traces. -/
theorem det_product_one_of_opposite_traces {S : Type*} [CommRing S] {n m : ℕ}
    (X : Matrix (Fin n) (Fin n) S) (Y : Matrix (Fin m) (Fin m) S)
    (N : ℕ) (hNilX : X^(N + 1) = 0) (hNilY : Y^(N + 1) = 0)
    (hAnti : ∀ k : ℕ, (X^(k + 1)).trace = -((Y^(k + 1)).trace)) :
    (1 - X).det * (1 - Y).det = 1 := by
  sorry

/-- In a Grassmann algebra, odd elements are nilpotent. -/
lemma odd_nilpotent {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    (x : Λ.carrier) (hx : x ∈ Λ.odd) : ∃ N : ℕ, x^(N + 1) = 0 := by
  have hbody : Λ.body x = 0 := Λ.body_odd_zero x hx
  obtain ⟨N, hnil⟩ := Λ.nilpotent_part x
  use N
  simp only [hbody, map_zero, sub_zero] at hnil
  exact hnil

/-- Product of two odd elements has body zero. -/
lemma body_odd_mul_odd {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    (x y : Λ.carrier) (hx : x ∈ Λ.odd) (hy : y ∈ Λ.odd) : Λ.body (x * y) = 0 := by
  rw [Λ.body_mul, Λ.body_odd_zero x hx, Λ.body_odd_zero y hy, zero_mul]

/-- An element with body zero is nilpotent. -/
lemma body_zero_nilpotent {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    (x : Λ.carrier) (hx : Λ.body x = 0) : ∃ N : ℕ, x^(N + 1) = 0 := by
  obtain ⟨N, hnil⟩ := Λ.nilpotent_part x
  use N
  simp only [hx, map_zero, sub_zero] at hnil
  exact hnil

/-- An element with body zero is nilpotent (IsNilpotent version). -/
lemma isNilpotent_of_body_zero {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    (x : Λ.carrier) (hx : Λ.body x = 0) : IsNilpotent x := by
  obtain ⟨N, hnil⟩ := body_zero_nilpotent x hx
  exact ⟨N + 1, hnil⟩

/-- Product of two odd elements is nilpotent. -/
lemma isNilpotent_odd_mul_odd {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    (x y : Λ.carrier) (hx : x ∈ Λ.odd) (hy : y ∈ Λ.odd) : IsNilpotent (x * y) :=
  isNilpotent_of_body_zero (x * y) (body_odd_mul_odd x y hx hy)

/-- Body of zero is zero. -/
lemma body_zero {k : Type*} [Field k] {Λ : GrassmannAlgebra k} : Λ.body 0 = 0 := by
  have h1 : Λ.body (0 + 0) = Λ.body 0 + Λ.body 0 := Λ.body_add 0 0
  simp only [add_zero] at h1
  have : Λ.body 0 + Λ.body 0 = Λ.body 0 + 0 := by rw [← h1, add_zero]
  exact add_left_cancel this

/-- Each entry of B * C (odd × odd) has body zero. -/
lemma body_matrix_mul_odd_odd {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (B : Matrix (Fin n) (Fin m) Λ.carrier) (C : Matrix (Fin m) (Fin n) Λ.carrier)
    (hB : ∀ i j, B i j ∈ Λ.odd) (hC : ∀ i j, C i j ∈ Λ.odd)
    (i : Fin n) (j : Fin n) : Λ.body ((B * C) i j) = 0 := by
  simp only [Matrix.mul_apply]
  have h : ∀ l : Fin m, Λ.body (B i l * C l j) = 0 :=
    fun l => body_odd_mul_odd (B i l) (C l j) (hB i l) (hC l j)
  have body_sum : ∀ (s : Finset (Fin m)),
      Λ.body (∑ l ∈ s, B i l * C l j) = ∑ l ∈ s, Λ.body (B i l * C l j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, body_zero]
    | insert a s hna ih => rw [Finset.sum_insert hna, Λ.body_add, Finset.sum_insert hna, ih]
  rw [body_sum]
  simp only [h, Finset.sum_const_zero]

/-- Each entry of B * C (odd × odd) is nilpotent. -/
lemma isNilpotent_matrix_mul_odd_odd_entry {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (B : Matrix (Fin n) (Fin m) Λ.carrier) (C : Matrix (Fin m) (Fin n) Λ.carrier)
    (hB : ∀ i j, B i j ∈ Λ.odd) (hC : ∀ i j, C i j ∈ Λ.odd)
    (i : Fin n) (j : Fin n) : IsNilpotent ((B * C) i j) := by
  simp only [Matrix.mul_apply]
  have hterm : ∀ l : Fin m, IsNilpotent (B i l * C l j) :=
    fun l => isNilpotent_odd_mul_odd (B i l) (C l j) (hB i l) (hC l j)
  exact isNilpotent_sum (fun l _ => hterm l)

/-- Product of k elements from m nilpotent elements is zero when k ≥ m*(N+1) (by pigeonhole). -/
lemma prod_nilpotent_elements_zero {R : Type*} [CommRing R] {m : ℕ}
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
lemma matrix_nilpotent_of_entries_nilpotent {R : Type*} [CommRing R] {n : ℕ}
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

/-- Product of matrices with odd entries is nilpotent. -/
lemma odd_matrix_product_nilpotent {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (B : Matrix (Fin n) (Fin m) Λ.carrier) (C : Matrix (Fin m) (Fin n) Λ.carrier)
    (hB : ∀ i j, B i j ∈ Λ.odd) (hC : ∀ i j, C i j ∈ Λ.odd) :
    ∃ N : ℕ, (B * C)^(N + 1) = 0 := by
  have hentry_nil : ∀ i j, ∃ N : ℕ, ((B * C) i j)^(N + 1) = 0 := by
    intro i j
    exact body_zero_nilpotent ((B * C) i j) (body_matrix_mul_odd_odd B C hB hC i j)
  exact matrix_nilpotent_of_entries_nilpotent (B * C) hentry_nil

/-- det(I - BC) * det(I - CB) = 1 for odd matrices B, C. -/
theorem grassmann_det_one_sub_mul_comm {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (B : Matrix (Fin n) (Fin m) Λ.carrier) (C : Matrix (Fin m) (Fin n) Λ.carrier)
    (hB : ∀ i j, B i j ∈ Λ.odd) (hC : ∀ i j, C i j ∈ Λ.odd)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0 : (0 : Λ.carrier) ∈ Λ.even) :
    (1 - B * C).det * (1 - C * B).det = 1 := by
  obtain ⟨N_BC, hNilBC⟩ := odd_matrix_product_nilpotent B C hB hC
  obtain ⟨N_CB, hNilCB⟩ := odd_matrix_product_nilpotent C B hC hB
  let N := max N_BC N_CB
  have hNilBC' : (B * C)^(N + 1) = 0 := by
    have h : N_BC ≤ N := le_max_left _ _
    have hpow : N + 1 = N_BC + 1 + (N - N_BC) := by omega
    rw [hpow, pow_add, hNilBC, zero_mul]
  have hNilCB' : (C * B)^(N + 1) = 0 := by
    have h : N_CB ≤ N := le_max_right _ _
    have hpow : N + 1 = N_CB + 1 + (N - N_CB) := by omega
    rw [hpow, pow_add, hNilCB, zero_mul]
  have hTraceAnti : ∀ j : ℕ, ((B * C)^(j + 1)).trace = -(((C * B)^(j + 1)).trace) :=
    fun j => grassmann_trace_pow_anticomm j B C hB hC h1 h0
  exact det_product_one_of_opposite_traces (B * C) (C * B) N hNilBC' hNilCB' hTraceAnti

end Supermanifolds.Helpers
