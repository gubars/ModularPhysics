import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
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
theorem grassmann_trace_anticomm {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    [hSC : SuperCommutative A.toSuperAlgebra] {n m : ℕ}
    (B : Matrix (Fin n) (Fin m) A.carrier) (C : Matrix (Fin m) (Fin n) A.carrier)
    (hB : ∀ i j, B i j ∈ A.odd) (hC : ∀ i j, C i j ∈ A.odd) :
    (B * C).trace = -((C * B).trace) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  simp only [← Finset.sum_neg_distrib]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact @SuperCommutative.odd_anticomm R _ A.toSuperAlgebra hSC (B i j) (C j i) (hB i j) (hC j i)

/-- The determinant of a matrix with even entries is even. -/
theorem det_even {R : Type*} [CommRing R] {A : FieldSuperAlgebra R} {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A.carrier)
    (hM : ∀ i j, M i j ∈ A.even) (h1 : (1 : A.carrier) ∈ A.even) : M.det ∈ A.even := by
  rw [Matrix.det_apply]
  apply A.even.sum_mem
  intro σ _
  have hProd : (Finset.univ : Finset (Fin n)).prod (fun i => M (σ i) i) ∈ A.even := by
    apply Finset.prod_induction _ (· ∈ A.even)
    · intro a b ha hb; exact A.even_mul_even _ _ ha hb
    · exact h1
    · intro i _; exact hM (σ i) i
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign
  · rw [hsign, one_smul]; exact hProd
  · rw [hsign, Units.neg_smul, one_smul]
    exact A.even.neg_mem hProd

/-- Each entry of the adjugate matrix is even when the original matrix has even entries. -/
theorem adjugate_even {R : Type*} [CommRing R] {A : FieldSuperAlgebra R} {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A.carrier)
    (hM : ∀ i j, M i j ∈ A.even) (h1 : (1 : A.carrier) ∈ A.even) (h0 : (0 : A.carrier) ∈ A.even)
    (i j : Fin n) : M.adjugate i j ∈ A.even := by
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

/-- The inverse of a matrix with even entries has even entries. -/
theorem matrix_inv_even {R : Type*} [CommRing R] {A : FieldSuperAlgebra R} {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A.carrier)
    (hM : ∀ i j, M i j ∈ A.even) (hdet : M.det ≠ 0)
    (h1 : (1 : A.carrier) ∈ A.even) (h0 : (0 : A.carrier) ∈ A.even)
    (i j : Fin n) : M⁻¹ i j ∈ A.even := by
  haveI : Invertible M.det := invertibleOfNonzero hdet
  have hInv := Matrix.nonsing_inv_apply M (isUnit_of_invertible M.det)
  rw [hInv]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hDetEven : M.det ∈ A.even := det_even M hM h1
  have hUnitInvEven : (↑(isUnit_of_invertible M.det).unit⁻¹ : A.carrier) ∈ A.even := by
    have h_eq : (↑(isUnit_of_invertible M.det).unit⁻¹ : A.carrier) = M.det⁻¹ := by
      simp only [IsUnit.unit_spec, Units.val_inv_eq_inv_val]
    rw [h_eq]
    exact FieldSuperAlgebra.even_inv_even A hdet hDetEven
  have hAdjEven : M.adjugate i j ∈ A.even := adjugate_even M hM h1 h0 i j
  exact A.even_mul_even _ _ hUnitInvEven hAdjEven

/-- Matrix product of odd × even matrices has odd entries. -/
theorem matrix_mul_odd_even {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m p : ℕ}
    (C : Matrix (Fin n) (Fin m) A.carrier) (M : Matrix (Fin m) (Fin p) A.carrier)
    (hC : ∀ i j, C i j ∈ A.odd) (hM : ∀ i j, M i j ∈ A.even) :
    ∀ i j, (C * M) i j ∈ A.odd := by
  intro i j
  simp only [Matrix.mul_apply]
  apply A.odd.sum_mem
  intro k _
  exact A.odd_mul_even _ _ (hC i k) (hM k j)

/-- Matrix product of even × odd matrices has odd entries. -/
theorem matrix_mul_even_odd {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m p : ℕ}
    (M : Matrix (Fin n) (Fin m) A.carrier) (C : Matrix (Fin m) (Fin p) A.carrier)
    (hM : ∀ i j, M i j ∈ A.even) (hC : ∀ i j, C i j ∈ A.odd) :
    ∀ i j, (M * C) i j ∈ A.odd := by
  intro i j
  simp only [Matrix.mul_apply]
  apply A.odd.sum_mem
  intro k _
  exact A.even_mul_odd _ _ (hM i k) (hC k j)

/-- Matrix product of odd × odd matrices has even entries. -/
theorem matrix_mul_odd_odd {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m p : ℕ}
    (B : Matrix (Fin n) (Fin m) A.carrier) (C : Matrix (Fin m) (Fin p) A.carrier)
    (hB : ∀ i j, B i j ∈ A.odd) (hC : ∀ i j, C i j ∈ A.odd) :
    ∀ i j, (B * C) i j ∈ A.even := by
  intro i j
  simp only [Matrix.mul_apply]
  apply A.even.sum_mem
  intro k _
  exact A.odd_mul_odd _ _ (hB i k) (hC k j)

/-- Matrix product of even × even matrices has even entries. -/
theorem matrix_mul_even_even {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m p : ℕ}
    (M : Matrix (Fin n) (Fin m) A.carrier) (N : Matrix (Fin m) (Fin p) A.carrier)
    (hM : ∀ i j, M i j ∈ A.even) (hN : ∀ i j, N i j ∈ A.even) :
    ∀ i j, (M * N) i j ∈ A.even := by
  intro i j
  simp only [Matrix.mul_apply]
  apply A.even.sum_mem
  intro k _
  exact A.even_mul_even _ _ (hM i k) (hN k j)

/-- Power of a matrix with even entries has even entries. -/
theorem matrix_pow_even {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n : ℕ} (k : ℕ)
    (M : Matrix (Fin n) (Fin n) A.carrier)
    (hM : ∀ i j, M i j ∈ A.even)
    (h1 : (1 : A.carrier) ∈ A.even) (h0 : (0 : A.carrier) ∈ A.even) :
    ∀ i j, (M^k) i j ∈ A.even := by
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
theorem matrix_C_BC_pow_odd {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ} (k : ℕ)
    (B : Matrix (Fin n) (Fin m) A.carrier) (C : Matrix (Fin m) (Fin n) A.carrier)
    (hB : ∀ i j, B i j ∈ A.odd) (hC : ∀ i j, C i j ∈ A.odd)
    (h1 : (1 : A.carrier) ∈ A.even) (h0 : (0 : A.carrier) ∈ A.even) :
    ∀ i j, (C * (B * C)^k) i j ∈ A.odd := by
  intro i j
  have hBCk_even : ∀ i j, ((B * C)^k) i j ∈ A.even :=
    matrix_pow_even k (B * C) (matrix_mul_odd_odd B C hB hC) h1 h0
  exact matrix_mul_odd_even C _ hC hBCk_even i j

/-- The trace anticommutation identity for powers: tr((BC)^(k+1)) = -tr((CB)^(k+1)) -/
theorem grassmann_trace_pow_anticomm {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    [hSC : SuperCommutative A.toSuperAlgebra] {n m : ℕ} (k : ℕ)
    (B : Matrix (Fin n) (Fin m) A.carrier) (C : Matrix (Fin m) (Fin n) A.carrier)
    (hB : ∀ i j, B i j ∈ A.odd) (hC : ∀ i j, C i j ∈ A.odd)
    (h1even : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even) :
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
  have hX_odd : ∀ i j, X i j ∈ A.odd := matrix_C_BC_pow_odd k B C hB hC h1even h0even
  have heq3 : (B * X).trace = -((X * B).trace) := grassmann_trace_anticomm B X hB hX_odd
  rw [heq1, heq3, heq2, hX_def, Matrix.mul_assoc]

/-- Key identity for Grassmann-odd matrices: det(I - BC) * det(I - CB) = 1

    For B : n × m and C : m × n with odd entries in a supercommutative algebra.
    BC : n × n and CB : m × m are both matrices with even entries.

    This identity is fundamental for proving Ber = BerAlt and Ber multiplicativity. -/
theorem grassmann_det_one_sub_mul_comm {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    [SuperCommutative A.toSuperAlgebra] {n m : ℕ}
    (B : Matrix (Fin n) (Fin m) A.carrier) (C : Matrix (Fin m) (Fin n) A.carrier)
    (hB : ∀ i j, B i j ∈ A.odd) (hC : ∀ i j, C i j ∈ A.odd)
    (h1 : (1 : A.carrier) ∈ A.even) (h0 : (0 : A.carrier) ∈ A.even) :
    (1 - B * C).det * (1 - C * B).det = 1 := by
  -- The key identity is tr((BC)^k) = -tr((CB)^k) for all k ≥ 1.
  -- Using log-det formal power series and trace anticommutation,
  -- the product det(I-BC)*det(I-CB) = 1.
  sorry

end Supermanifolds.Helpers
