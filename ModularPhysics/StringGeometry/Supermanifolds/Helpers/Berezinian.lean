import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import ModularPhysics.StringGeometry.Supermanifolds.Superalgebra
import ModularPhysics.StringGeometry.Supermanifolds.Helpers.SuperMatrix
import ModularPhysics.StringGeometry.Supermanifolds.Helpers.MatrixParity

/-!
# Berezinian (Superdeterminant) Theory

This file develops the theory of the Berezinian (superdeterminant) for supermatrices
over a superalgebra. Key results include:
* `SuperMatrix.ber` - The superdeterminant Ber(M) = det(A - BD⁻¹C) / det(D)
* `berezinian_mul` - Multiplicativity: Ber(MN) = Ber(M) · Ber(N)

For M = [A B; C D], odd elements anticommute (θη = -ηθ), which makes Ber multiplicative.
-/

namespace Supermanifolds.Helpers

open Supermanifolds

/-! ## Berezinian Definition -/

/-- Berezinian: Ber(M) = det(A - BD⁻¹C) · det(D)⁻¹ for supermatrix M = [A B; C D]. -/
noncomputable def SuperMatrix.ber {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m)
    (_hD : Λ.IsInvertible M.Dblock.det) : Λ.carrier :=
  (M.Ablock - M.Bblock * M.Dblock⁻¹ * M.Cblock).det * (M.Dblock.det)⁻¹

/-- A-based Berezinian: BerAlt(M) = det(A) · det(D - CA⁻¹B)⁻¹. Requires A invertible. -/
noncomputable def SuperMatrix.berAlt {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m)
    (_hA : Λ.IsInvertible M.Ablock.det) : Λ.carrier :=
  M.Ablock.det * (M.Dblock - M.Cblock * M.Ablock⁻¹ * M.Bblock).det⁻¹

/-- The two Berezinian formulas agree when both A and D are invertible. -/
theorem SuperMatrix.ber_eq_berAlt {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (M : SuperMatrix Λ n m)
    (hMA : Λ.IsInvertible M.Ablock.det) (hMD : Λ.IsInvertible M.Dblock.det)
    (hAinvB : ∀ i j, (M.Ablock⁻¹ * M.Bblock) i j ∈ Λ.odd)
    (hDinvC : ∀ i j, (M.Dblock⁻¹ * M.Cblock) i j ∈ Λ.odd)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0 : (0 : Λ.carrier) ∈ Λ.even) :
    M.ber hMD = M.berAlt hMA := by
  unfold SuperMatrix.ber SuperMatrix.berAlt
  let X := M.Dblock⁻¹ * M.Cblock
  let Y := M.Ablock⁻¹ * M.Bblock
  have hDetComm := grassmann_det_one_sub_mul_comm Y X hAinvB hDinvC h1 h0
  haveI : Invertible M.Ablock.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hMA).invertible
  haveI hInvA : Invertible M.Ablock := Matrix.invertibleOfDetInvertible M.Ablock
  haveI : Invertible M.Dblock.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hMD).invertible
  haveI hInvD : Invertible M.Dblock := Matrix.invertibleOfDetInvertible M.Dblock

  have hAAinv : M.Ablock * M.Ablock⁻¹ = 1 := Matrix.mul_nonsing_inv M.Ablock (isUnit_of_invertible _)
  have hDDinv : M.Dblock * M.Dblock⁻¹ = 1 := Matrix.mul_nonsing_inv M.Dblock (isUnit_of_invertible _)

  have hSD_factor : M.Ablock - M.Bblock * M.Dblock⁻¹ * M.Cblock = M.Ablock * (1 - Y * X) := by
    have h : M.Ablock * (1 - Y * X) = M.Ablock - M.Ablock * (Y * X) := by
      rw [Matrix.mul_sub, Matrix.mul_one]
    rw [h]
    congr 1
    calc M.Bblock * M.Dblock⁻¹ * M.Cblock
        = 1 * (M.Bblock * M.Dblock⁻¹ * M.Cblock) := (Matrix.one_mul _).symm
      _ = (M.Ablock * M.Ablock⁻¹) * (M.Bblock * M.Dblock⁻¹ * M.Cblock) := by rw [hAAinv]
      _ = M.Ablock * (M.Ablock⁻¹ * (M.Bblock * M.Dblock⁻¹ * M.Cblock)) := by
          simp only [Matrix.mul_assoc]
      _ = M.Ablock * (M.Ablock⁻¹ * M.Bblock * (M.Dblock⁻¹ * M.Cblock)) := by
          simp only [Matrix.mul_assoc]
      _ = M.Ablock * (Y * X) := rfl

  have hSA_factor : M.Dblock - M.Cblock * M.Ablock⁻¹ * M.Bblock = M.Dblock * (1 - X * Y) := by
    have h : M.Dblock * (1 - X * Y) = M.Dblock - M.Dblock * (X * Y) := by
      rw [Matrix.mul_sub, Matrix.mul_one]
    rw [h]
    congr 1
    calc M.Cblock * M.Ablock⁻¹ * M.Bblock
        = 1 * (M.Cblock * M.Ablock⁻¹ * M.Bblock) := (Matrix.one_mul _).symm
      _ = (M.Dblock * M.Dblock⁻¹) * (M.Cblock * M.Ablock⁻¹ * M.Bblock) := by rw [hDDinv]
      _ = M.Dblock * (M.Dblock⁻¹ * (M.Cblock * M.Ablock⁻¹ * M.Bblock)) := by
          simp only [Matrix.mul_assoc]
      _ = M.Dblock * (M.Dblock⁻¹ * M.Cblock * (M.Ablock⁻¹ * M.Bblock)) := by
          simp only [Matrix.mul_assoc]
      _ = M.Dblock * (X * Y) := rfl

  have hDetSD : (M.Ablock - M.Bblock * M.Dblock⁻¹ * M.Cblock).det = M.Ablock.det * (1 - Y * X).det := by
    rw [hSD_factor, Matrix.det_mul]

  have hDetSA : (M.Dblock - M.Cblock * M.Ablock⁻¹ * M.Bblock).det = M.Dblock.det * (1 - X * Y).det := by
    rw [hSA_factor, Matrix.det_mul]

  have h1YX_inv : Λ.IsInvertible (1 - Y * X).det := by
    unfold GrassmannAlgebra.IsInvertible
    have h : Λ.body ((1 - Y * X).det * (1 - X * Y).det) = Λ.body 1 := congrArg Λ.body hDetComm
    rw [Λ.body_mul, Λ.body_one] at h
    exact left_ne_zero_of_mul_eq_one h

  have h1XY_inv : Λ.IsInvertible (1 - X * Y).det := by
    unfold GrassmannAlgebra.IsInvertible
    have h : Λ.body ((1 - Y * X).det * (1 - X * Y).det) = Λ.body 1 := congrArg Λ.body hDetComm
    rw [Λ.body_mul, Λ.body_one, mul_comm] at h
    exact left_ne_zero_of_mul_eq_one h

  have hInvXY : (1 - X * Y).det⁻¹ = (1 - Y * X).det := by
    have h_prod_cancel : (1 - X * Y).det * (1 - X * Y).det⁻¹ = 1 := Λ.mul_inv_cancel _ h1XY_inv
    have h_inv_prod : (1 - X * Y).det⁻¹ * (1 - X * Y).det = 1 := Λ.inv_mul_cancel _ h1XY_inv
    calc (1 - X * Y).det⁻¹
        = (1 : Λ.carrier) * (1 - X * Y).det⁻¹ := (one_mul _).symm
      _ = ((1 - Y * X).det * (1 - X * Y).det) * (1 - X * Y).det⁻¹ := by rw [hDetComm]
      _ = (1 - Y * X).det * ((1 - X * Y).det * (1 - X * Y).det⁻¹) := by ring
      _ = (1 - Y * X).det * (1 : Λ.carrier) := by rw [h_prod_cancel]
      _ = (1 - Y * X).det := mul_one _

  rw [hDetSD, hDetSA]

  have h_inv_prod : (M.Dblock.det * (1 - X * Y).det)⁻¹ = M.Dblock.det⁻¹ * (1 - X * Y).det⁻¹ := by
    have h1 : M.Dblock.det * (1 - X * Y).det * (M.Dblock.det⁻¹ * (1 - X * Y).det⁻¹) = 1 := by
      have hD_cancel : M.Dblock.det * M.Dblock.det⁻¹ = 1 := Λ.mul_inv_cancel _ hMD
      have hXY_cancel : (1 - X * Y).det * (1 - X * Y).det⁻¹ = 1 := Λ.mul_inv_cancel _ h1XY_inv
      calc M.Dblock.det * (1 - X * Y).det * (M.Dblock.det⁻¹ * (1 - X * Y).det⁻¹)
          = (M.Dblock.det * M.Dblock.det⁻¹) * ((1 - X * Y).det * (1 - X * Y).det⁻¹) := by ring
        _ = 1 * 1 := by rw [hD_cancel, hXY_cancel]
        _ = 1 := one_mul _
    have h_prod_inv : Λ.IsInvertible (M.Dblock.det * (1 - X * Y).det) :=
      Λ.mul_invertible _ _ hMD h1XY_inv
    have h_prod_inv_cancel : (M.Dblock.det * (1 - X * Y).det)⁻¹ * (M.Dblock.det * (1 - X * Y).det) = 1 :=
      Λ.inv_mul_cancel _ h_prod_inv
    calc (M.Dblock.det * (1 - X * Y).det)⁻¹
        = (M.Dblock.det * (1 - X * Y).det)⁻¹ * 1 := (mul_one _).symm
      _ = (M.Dblock.det * (1 - X * Y).det)⁻¹ *
          (M.Dblock.det * (1 - X * Y).det * (M.Dblock.det⁻¹ * (1 - X * Y).det⁻¹)) := by rw [h1]
      _ = ((M.Dblock.det * (1 - X * Y).det)⁻¹ * (M.Dblock.det * (1 - X * Y).det)) *
          (M.Dblock.det⁻¹ * (1 - X * Y).det⁻¹) := by ring
      _ = 1 * (M.Dblock.det⁻¹ * (1 - X * Y).det⁻¹) := by rw [h_prod_inv_cancel]
      _ = M.Dblock.det⁻¹ * (1 - X * Y).det⁻¹ := one_mul _

  rw [h_inv_prod, hInvXY]
  ring

/-- The two Berezinian formulas agree when B = C = 0 (diagonal supermatrices). -/
theorem berezinian_formulas_agree_diagonal {n m : ℕ}
    (Amat : Matrix (Fin n) (Fin n) ℂ) (Dmat : Matrix (Fin m) (Fin m) ℂ)
    (_hA : Amat.det ≠ 0) (_hD : Dmat.det ≠ 0) :
    let B : Matrix (Fin n) (Fin m) ℂ := 0
    let C : Matrix (Fin m) (Fin n) ℂ := 0
    let schurD := Amat - B * Dmat⁻¹ * C
    let schurA := Dmat - C * Amat⁻¹ * B
    schurD.det * Dmat.det⁻¹ = Amat.det * schurA.det⁻¹ := by
  simp only [Matrix.zero_mul, Matrix.mul_zero, sub_zero]

/-! ## Schur Complements -/

/-- D-based Schur complement: A - BD⁻¹C -/
noncomputable def schurComplementD {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (_ : Λ.IsInvertible M.Dblock.det) :
    Matrix (Fin n) (Fin n) Λ.carrier :=
  M.Ablock - M.Bblock * M.Dblock⁻¹ * M.Cblock

/-- A-based Schur complement: D - CA⁻¹B -/
noncomputable def schurComplementA {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (_ : Λ.IsInvertible M.Ablock.det) :
    Matrix (Fin m) (Fin m) Λ.carrier :=
  M.Dblock - M.Cblock * M.Ablock⁻¹ * M.Bblock


/-! ## LDU and UDL Factorizations -/

/-- Lower triangular factor (D-based): L = [I 0; D⁻¹C I] -/
noncomputable def lowerTriangularFactorD {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (_hD : Λ.IsInvertible M.Dblock.det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hDinvC : ∀ i j, (M.Dblock⁻¹ * M.Cblock) i j ∈ Λ.odd) : SuperMatrix Λ n m :=
  ⟨1, 0, M.Dblock⁻¹ * M.Cblock, 1,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even],
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   hDinvC,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]⟩

/-- Upper triangular factor (D-based): U = [I BD⁻¹; 0 I] -/
noncomputable def upperTriangularFactorD {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (_hD : Λ.IsInvertible M.Dblock.det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hBDinv : ∀ i j, (M.Bblock * M.Dblock⁻¹) i j ∈ Λ.odd) : SuperMatrix Λ n m :=
  ⟨1, M.Bblock * M.Dblock⁻¹, 0, 1,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even],
   hBDinv,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]⟩

/-- Diagonal factor (D-based): Δ = [SchurD 0; 0 D] -/
noncomputable def diagonalFactorD {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (hD : Λ.IsInvertible M.Dblock.det)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hSchur : ∀ i j, (schurComplementD M hD) i j ∈ Λ.even) : SuperMatrix Λ n m :=
  ⟨schurComplementD M hD, 0, 0, M.Dblock,
   hSchur,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   M.Dblock_even⟩

/-- Lower triangular factor (A-based): L = [I 0; CA⁻¹ I] -/
noncomputable def lowerTriangularFactorA {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (_hA : Λ.IsInvertible M.Ablock.det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hCAinv : ∀ i j, (M.Cblock * M.Ablock⁻¹) i j ∈ Λ.odd) : SuperMatrix Λ n m :=
  ⟨1, 0, M.Cblock * M.Ablock⁻¹, 1,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even],
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   hCAinv,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]⟩

/-- Upper triangular factor (A-based): U = [I A⁻¹B; 0 I] -/
noncomputable def upperTriangularFactorA {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (_hA : Λ.IsInvertible M.Ablock.det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hAinvB : ∀ i j, (M.Ablock⁻¹ * M.Bblock) i j ∈ Λ.odd) : SuperMatrix Λ n m :=
  ⟨1, M.Ablock⁻¹ * M.Bblock, 0, 1,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even],
   hAinvB,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]⟩

/-- Diagonal factor (A-based): Δ = [A 0; 0 SchurA] -/
noncomputable def diagonalFactorA {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (hA : Λ.IsInvertible M.Ablock.det)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hSchur : ∀ i j, (schurComplementA M hA) i j ∈ Λ.even) : SuperMatrix Λ n m :=
  ⟨M.Ablock, 0, 0, schurComplementA M hA,
   M.Ablock_even,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   hSchur⟩

/-! ## Berezinian of Special Matrices -/

/-- Ber([I B; 0 I]) = 1 for ℂ-valued matrices. -/
theorem berezinian_upper_triangular_complex {n m : ℕ} (B : Matrix (Fin n) (Fin m) ℂ)
    (_hDdet : (1 : Matrix (Fin m) (Fin m) ℂ).det ≠ 0) :
    let C : Matrix (Fin m) (Fin n) ℂ := 0
    let schur := (1 : Matrix (Fin n) (Fin n) ℂ) - B * (1 : Matrix (Fin m) (Fin m) ℂ)⁻¹ * C
    schur.det * ((1 : Matrix (Fin m) (Fin m) ℂ).det)⁻¹ = 1 := by
  simp only [Matrix.mul_zero, sub_zero, Matrix.det_one, inv_one, mul_one]

/-- Ber([I 0; C I]) = 1 for ℂ-valued matrices. -/
theorem berezinian_lower_triangular_complex {n m : ℕ} (C : Matrix (Fin m) (Fin n) ℂ)
    (_hDdet : (1 : Matrix (Fin m) (Fin m) ℂ).det ≠ 0) :
    let B : Matrix (Fin n) (Fin m) ℂ := 0
    let schur := (1 : Matrix (Fin n) (Fin n) ℂ) - B * (1 : Matrix (Fin m) (Fin m) ℂ)⁻¹ * C
    schur.det * ((1 : Matrix (Fin m) (Fin m) ℂ).det)⁻¹ = 1 := by
  simp only [Matrix.zero_mul, sub_zero, Matrix.det_one, inv_one, mul_one]

/-- Ber([A 0; 0 D]) = det(A) · det(D)⁻¹ for ℂ-valued matrices. -/
theorem berezinian_diagonal_complex {n m : ℕ}
    (Amat : Matrix (Fin n) (Fin n) ℂ) (Dmat : Matrix (Fin m) (Fin m) ℂ)
    (_hDdet : Dmat.det ≠ 0) :
    let B : Matrix (Fin n) (Fin m) ℂ := 0
    let C : Matrix (Fin m) (Fin n) ℂ := 0
    let schur := Amat - B * Dmat⁻¹ * C
    schur.det * (Dmat.det)⁻¹ = Amat.det * (Dmat.det)⁻¹ := by
  simp only [Matrix.zero_mul, Matrix.mul_zero, sub_zero]

/-! ## Berezinian Multiplicativity -/

/-- Upper triangular supermatrix U = [I B'; 0 I] -/
noncomputable def SuperMatrix.upperTriangular {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd) :
    SuperMatrix Λ n m :=
  ⟨1, B', 0, 1,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even],
   hB',
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]⟩

/-- Lower triangular supermatrix L = [I 0; C' I] -/
noncomputable def SuperMatrix.lowerTriangular {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd) :
    SuperMatrix Λ n m :=
  ⟨1, 0, C', 1,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even],
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   hC',
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]⟩

/-- Diagonal supermatrix Δ = [A' 0; 0 D'] -/
noncomputable def SuperMatrix.diagonal {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ}
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (D' : Matrix (Fin m) (Fin m) Λ.carrier)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hA' : ∀ i j, A' i j ∈ Λ.even) (hD' : ∀ i j, D' i j ∈ Λ.even) :
    SuperMatrix Λ n m :=
  ⟨A', 0, 0, D',
   hA',
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   hD'⟩

/-- Helper: matrix subtraction with zero gives the matrix back -/
private theorem matrix_sub_zero {α : Type*} [AddGroup α] {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) α) :
    M - (0 : Matrix (Fin n) (Fin m) α) = M := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero]

/-- Ber(U) = 1 for upper triangular U = [I B'; 0 I]. -/
theorem SuperMatrix.ber_upperTriangular {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd)
    (hD : Λ.IsInvertible ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock).det) :
    (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').ber hD = 1 := by
  unfold SuperMatrix.ber
  have hAblock : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock = 1 := rfl
  have hCblock : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Cblock = 0 := rfl
  have hDblock : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock = 1 := rfl
  have hSchur : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock -
      (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Bblock *
      (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock⁻¹ *
      (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Cblock = 1 := by
    rw [hCblock]
    have h_mul_zero : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Bblock *
        (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock⁻¹ *
        (0 : Matrix (Fin m) (Fin n) Λ.carrier) = 0 := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]
    rw [h_mul_zero, hAblock]
    ext i j
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply, sub_zero]
  rw [hSchur, hDblock]
  simp only [Matrix.det_one]
  have h1body : Λ.body (1 : Λ.carrier) ≠ 0 := by rw [Λ.body_one]; exact one_ne_zero
  exact Λ.mul_inv_cancel 1 h1body

/-- Ber(L) = 1 for lower triangular L = [I 0; C' I]. -/
theorem SuperMatrix.ber_lowerTriangular {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd)
    (hD : Λ.IsInvertible ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock).det) :
    (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').ber hD = 1 := by
  unfold SuperMatrix.ber SuperMatrix.lowerTriangular
  have hBblock_zero : (0 : Matrix (Fin n) (Fin m) Λ.carrier) *
      (1 : Matrix (Fin m) (Fin m) Λ.carrier)⁻¹ * C' = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply, zero_mul, Finset.sum_const_zero]
  have hSchur : (1 : Matrix (Fin n) (Fin n) Λ.carrier) -
      (0 : Matrix (Fin n) (Fin m) Λ.carrier) *
      (1 : Matrix (Fin m) (Fin m) Λ.carrier)⁻¹ * C' = 1 := by
    rw [hBblock_zero]
    ext i j
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply, sub_zero]
  rw [hSchur]
  simp only [Matrix.det_one]
  have h1body : Λ.body (1 : Λ.carrier) ≠ 0 := by rw [Λ.body_one]; exact one_ne_zero
  exact Λ.mul_inv_cancel 1 h1body

/-- berAlt(L · N) = berAlt(N) when L = [I 0; C' I] is lower triangular. -/
theorem SuperMatrix.berAlt_mul_lowerTriangular_left {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (N : SuperMatrix Λ n m)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd)
    (hNA : Λ.IsInvertible N.Ablock.det)
    (hLNA : Λ.IsInvertible ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') * N).Ablock.det) :
    ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') * N).berAlt hLNA =
    N.berAlt hNA := by
  unfold SuperMatrix.berAlt
  have hLNA_eq : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).Ablock = N.Ablock := by
    show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock * N.Ablock +
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock * N.Cblock = N.Ablock
    simp only [SuperMatrix.lowerTriangular, Matrix.one_mul, Matrix.zero_mul, add_zero]
  have hLNB_eq : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).Bblock = N.Bblock := by
    show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock * N.Bblock +
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock * N.Dblock = N.Bblock
    simp only [SuperMatrix.lowerTriangular, Matrix.one_mul, Matrix.zero_mul, add_zero]
  have hLNC_eq : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).Cblock =
                 C' * N.Ablock + N.Cblock := by
    show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock * N.Ablock +
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock * N.Cblock =
         C' * N.Ablock + N.Cblock
    simp only [SuperMatrix.lowerTriangular, Matrix.one_mul]
  have hLND_eq : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).Dblock =
                 C' * N.Bblock + N.Dblock := by
    show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock * N.Bblock +
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock * N.Dblock =
         C' * N.Bblock + N.Dblock
    simp only [SuperMatrix.lowerTriangular, Matrix.one_mul]
  rw [hLNA_eq, hLNB_eq, hLNC_eq, hLND_eq]
  haveI : Invertible N.Ablock.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hNA).invertible
  haveI : Invertible N.Ablock := Matrix.invertibleOfDetInvertible N.Ablock
  have hSchur_eq : (C' * N.Bblock + N.Dblock) - (C' * N.Ablock + N.Cblock) * N.Ablock⁻¹ * N.Bblock =
                   N.Dblock - N.Cblock * N.Ablock⁻¹ * N.Bblock := by
    have hAAinv : N.Ablock * N.Ablock⁻¹ = 1 := Matrix.mul_nonsing_inv N.Ablock (isUnit_of_invertible _)
    have h_distrib : (C' * N.Ablock + N.Cblock) * N.Ablock⁻¹ * N.Bblock =
                     C' * N.Bblock + N.Cblock * N.Ablock⁻¹ * N.Bblock := by
      have h1 : C' * N.Ablock * N.Ablock⁻¹ = C' := by
        calc C' * N.Ablock * N.Ablock⁻¹
            = C' * (N.Ablock * N.Ablock⁻¹) := by rw [Matrix.mul_assoc]
          _ = C' * (1 : Matrix _ _ _) := by rw [hAAinv]
          _ = C' := by rw [Matrix.mul_one]
      rw [Matrix.add_mul, Matrix.add_mul, h1]
    rw [h_distrib]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply]
    ring
  rw [hSchur_eq]

/-- berAlt(M · U) = berAlt(M) when U = [I B'; 0 I] is upper triangular. -/
theorem SuperMatrix.berAlt_mul_upperTriangular_right {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (M : SuperMatrix Λ n m)
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd)
    (hMA : Λ.IsInvertible M.Ablock.det)
    (hMUA : Λ.IsInvertible (M * SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock.det) :
    (M * SuperMatrix.upperTriangular B' h1 h0even h0odd hB').berAlt hMUA =
    M.berAlt hMA := by
  unfold SuperMatrix.berAlt
  let U := SuperMatrix.upperTriangular B' h1 h0even h0odd hB'
  have hUA : U.Ablock = 1 := rfl
  have hUB : U.Bblock = B' := rfl
  have hUC : U.Cblock = 0 := rfl
  have hUD : U.Dblock = 1 := rfl
  have hMUA_eq : (M * U).Ablock = M.Ablock := by
    show M.Ablock * U.Ablock + M.Bblock * U.Cblock = M.Ablock
    rw [hUA, hUC]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero]
  have hMUB_eq : (M * U).Bblock = M.Ablock * B' + M.Bblock := by
    show M.Ablock * U.Bblock + M.Bblock * U.Dblock = M.Ablock * B' + M.Bblock
    rw [hUB, hUD]
    simp only [Matrix.mul_one]
  have hMUC_eq : (M * U).Cblock = M.Cblock := by
    show M.Cblock * U.Ablock + M.Dblock * U.Cblock = M.Cblock
    rw [hUA, hUC]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero]
  have hMUD_eq : (M * U).Dblock = M.Cblock * B' + M.Dblock := by
    show M.Cblock * U.Bblock + M.Dblock * U.Dblock = M.Cblock * B' + M.Dblock
    rw [hUB, hUD]
    simp only [Matrix.mul_one]
  rw [hMUA_eq, hMUB_eq, hMUC_eq, hMUD_eq]
  haveI : Invertible M.Ablock.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hMA).invertible
  haveI : Invertible M.Ablock := Matrix.invertibleOfDetInvertible M.Ablock
  have hSchur_eq : (M.Cblock * B' + M.Dblock) - M.Cblock * M.Ablock⁻¹ * (M.Ablock * B' + M.Bblock) =
                   M.Dblock - M.Cblock * M.Ablock⁻¹ * M.Bblock := by
    have hAinvA : M.Ablock⁻¹ * M.Ablock = 1 := Matrix.nonsing_inv_mul M.Ablock (isUnit_of_invertible _)
    have h_distrib : M.Cblock * M.Ablock⁻¹ * (M.Ablock * B' + M.Bblock) =
                     M.Cblock * B' + M.Cblock * M.Ablock⁻¹ * M.Bblock := by
      have h1 : M.Cblock * M.Ablock⁻¹ * M.Ablock = M.Cblock := by
        calc M.Cblock * M.Ablock⁻¹ * M.Ablock
            = M.Cblock * (M.Ablock⁻¹ * M.Ablock) := by rw [Matrix.mul_assoc]
          _ = M.Cblock * (1 : Matrix _ _ _) := by rw [hAinvA]
          _ = M.Cblock := by rw [Matrix.mul_one]
      rw [Matrix.mul_add]
      congr 1
      calc M.Cblock * M.Ablock⁻¹ * (M.Ablock * B')
          = M.Cblock * (M.Ablock⁻¹ * (M.Ablock * B')) := by rw [Matrix.mul_assoc]
        _ = M.Cblock * ((M.Ablock⁻¹ * M.Ablock) * B') := by rw [Matrix.mul_assoc]
        _ = M.Cblock * ((1 : Matrix _ _ _) * B') := by rw [hAinvA]
        _ = M.Cblock * B' := by rw [Matrix.one_mul]
    rw [h_distrib]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply]
    ring
  rw [hSchur_eq]

/-- Ber([A' 0; 0 D']) = det(A') · det(D')⁻¹. -/
theorem SuperMatrix.ber_diagonal {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ}
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (D' : Matrix (Fin m) (Fin m) Λ.carrier)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hA' : ∀ i j, A' i j ∈ Λ.even) (hD' : ∀ i j, D' i j ∈ Λ.even)
    (hD : Λ.IsInvertible ((SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock).det) :
    (SuperMatrix.diagonal A' D' h0odd hA' hD').ber hD = A'.det * D'.det⁻¹ := by
  unfold SuperMatrix.ber SuperMatrix.diagonal
  have hBC_zero : (0 : Matrix (Fin n) (Fin m) Λ.carrier) * D'⁻¹ *
      (0 : Matrix (Fin m) (Fin n) Λ.carrier) = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]
  have hSchur : A' - (0 : Matrix (Fin n) (Fin m) Λ.carrier) * D'⁻¹ *
      (0 : Matrix (Fin m) (Fin n) Λ.carrier) = A' := by
    rw [hBC_zero]
    ext i j
    simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero]
  rw [hSchur]

/-- Product of two upper triangular supermatrices has C-block = 0. -/
theorem SuperMatrix.upperTriangular_mul_Cblock_zero {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ}
    (U₁ U₂ : SuperMatrix Λ n m)
    (_hU₁A : U₁.Ablock = 1) (hU₁C : U₁.Cblock = 0) (hU₁D : U₁.Dblock = 1)
    (hU₂A : U₂.Ablock = 1) (hU₂C : U₂.Cblock = 0) (_hU₂D : U₂.Dblock = 1) :
    (U₁ * U₂).Cblock = 0 := by
  change (SuperMatrix.mul U₁ U₂).Cblock = 0
  unfold SuperMatrix.mul
  simp only [hU₁C, hU₁D, hU₂A, hU₂C]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]

/-- Product of diagonal and upper triangular has C-block = 0. -/
theorem SuperMatrix.diagonal_mul_upper_Cblock_zero {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ}
    (Δ U : SuperMatrix Λ n m)
    (_hΔB : Δ.Bblock = 0) (hΔC : Δ.Cblock = 0)
    (hUA : U.Ablock = 1) (hUC : U.Cblock = 0) (_hUD : U.Dblock = 1) :
    (Δ * U).Cblock = 0 := by
  show Δ.Cblock * U.Ablock + Δ.Dblock * U.Cblock = 0
  rw [hΔC, hUA, hUC]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]

/-- Multiplying a C=0 supermatrix by diagonal on right preserves C=0. -/
theorem SuperMatrix.Cblock_zero_mul_diagonal_Cblock_zero {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ}
    (Y Δ' : SuperMatrix Λ n m)
    (hYC : Y.Cblock = 0)
    (_hΔ'B : Δ'.Bblock = 0) (hΔ'C : Δ'.Cblock = 0) :
    (Y * Δ').Cblock = 0 := by
  show Y.Cblock * Δ'.Ablock + Y.Dblock * Δ'.Cblock = 0
  rw [hYC, hΔ'C]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]

/-- When Y has C-block = 0, multiplying by lower triangular on right preserves D-block. -/
theorem SuperMatrix.Cblock_zero_mul_lower_Dblock {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ}
    (Y L : SuperMatrix Λ n m)
    (hYC : Y.Cblock = 0)
    (_hLA : L.Ablock = 1) (hLB : L.Bblock = 0) (hLD : L.Dblock = 1) :
    (Y * L).Dblock = Y.Dblock := by
  show Y.Cblock * L.Bblock + Y.Dblock * L.Dblock = Y.Dblock
  rw [hYC, hLB, hLD]
  simp only [Matrix.zero_mul, Matrix.mul_one, zero_add]

/-- When Y has C-block = 0, Y·L has the same Schur complement as Y. -/
theorem SuperMatrix.Cblock_zero_mul_lower_schur {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ}
    (Y L : SuperMatrix Λ n m)
    (hYC : Y.Cblock = 0)
    (hLA : L.Ablock = 1) (hLB : L.Bblock = 0) (hLD : L.Dblock = 1)
    (hD : Λ.IsInvertible Y.Dblock.det) :
    schurComplementD (Y * L) (by rw [SuperMatrix.Cblock_zero_mul_lower_Dblock Y L hYC hLA hLB hLD]; exact hD) =
    schurComplementD Y hD := by
  unfold schurComplementD
  have hYLA : (Y * L).Ablock = Y.Ablock * L.Ablock + Y.Bblock * L.Cblock := rfl
  have hYLB : (Y * L).Bblock = Y.Ablock * L.Bblock + Y.Bblock * L.Dblock := rfl
  have hYLC : (Y * L).Cblock = Y.Cblock * L.Ablock + Y.Dblock * L.Cblock := rfl
  have hYLD : (Y * L).Dblock = Y.Dblock := SuperMatrix.Cblock_zero_mul_lower_Dblock Y L hYC hLA hLB hLD
  simp only [hLA, hLB, hLD, Matrix.mul_one, Matrix.mul_zero, zero_add] at hYLA hYLB hYLC
  simp only [hYC, zero_add] at hYLC
  simp only [hYLA, hYLB, hYLC, hYLD]
  simp only [Matrix.mul_assoc]
  haveI : Invertible Y.Dblock.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hD).invertible
  haveI : Invertible Y.Dblock := Matrix.invertibleOfDetInvertible Y.Dblock
  rw [Matrix.inv_mul_cancel_left_of_invertible]
  simp only [hYC, Matrix.mul_zero, sub_zero, add_sub_cancel_right]

/-- Ber(U * N) = Ber(N) when U = [I B'; 0 I] is upper triangular. -/
theorem SuperMatrix.ber_mul_upperTriangular_left {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (N : SuperMatrix Λ n m)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd)
    (hND : Λ.IsInvertible N.Dblock.det)
    (hUD : Λ.IsInvertible (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock.det)
    (hUND : Λ.IsInvertible ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB') * N).Dblock.det) :
    ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB') * N).ber hUND =
    N.ber hND := by
  have hU := SuperMatrix.ber_upperTriangular B' h1 h0even h0odd hB' hUD
  unfold SuperMatrix.ber
  have hUND_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).Dblock = N.Dblock := by
    show (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Cblock * N.Bblock +
         (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock * N.Dblock = N.Dblock
    simp only [SuperMatrix.upperTriangular]
    simp only [Matrix.zero_mul, Matrix.one_mul, zero_add]
  have hUNC_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).Cblock = N.Cblock := by
    show (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Cblock * N.Ablock +
         (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock * N.Cblock = N.Cblock
    simp only [SuperMatrix.upperTriangular]
    simp only [Matrix.zero_mul, Matrix.one_mul, zero_add]
  have hUNB_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).Bblock =
                 N.Bblock + B' * N.Dblock := by
    show (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock * N.Bblock +
         (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Bblock * N.Dblock =
         N.Bblock + B' * N.Dblock
    simp only [SuperMatrix.upperTriangular]
    simp only [Matrix.one_mul]
  have hUNA_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).Ablock =
                 N.Ablock + B' * N.Cblock := by
    show (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock * N.Ablock +
         (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Bblock * N.Cblock =
         N.Ablock + B' * N.Cblock
    simp only [SuperMatrix.upperTriangular]
    simp only [Matrix.one_mul]
  rw [hUND_eq, hUNC_eq, hUNB_eq, hUNA_eq]
  congr 1
  haveI : Invertible N.Dblock.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hND).invertible
  haveI : Invertible N.Dblock := Matrix.invertibleOfDetInvertible N.Dblock
  have h_DinvD : N.Dblock * N.Dblock⁻¹ = 1 := Matrix.mul_nonsing_inv N.Dblock (isUnit_of_invertible _)
  have h_cancel : B' * N.Dblock * N.Dblock⁻¹ * N.Cblock = B' * N.Cblock := by
    rw [Matrix.mul_assoc B' N.Dblock, h_DinvD, Matrix.mul_one]
  have h_distrib : (N.Bblock + B' * N.Dblock) * N.Dblock⁻¹ * N.Cblock =
                   N.Bblock * N.Dblock⁻¹ * N.Cblock + B' * N.Cblock := by
    rw [Matrix.add_mul, Matrix.add_mul, h_cancel]
  rw [h_distrib]
  have heq : N.Ablock + B' * N.Cblock - (N.Bblock * N.Dblock⁻¹ * N.Cblock + B' * N.Cblock) =
             N.Ablock - N.Bblock * N.Dblock⁻¹ * N.Cblock := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply]
    ring
  rw [heq]

/-- Ber(M * L) = Ber(M) when L = [I 0; C' I] is lower triangular. -/
theorem SuperMatrix.ber_mul_lowerTriangular_right {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (M : SuperMatrix Λ n m)
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd)
    (hMD : Λ.IsInvertible M.Dblock.det)
    (_hLD : Λ.IsInvertible (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock.det)
    (hMLD : Λ.IsInvertible (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock.det) :
    (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').ber hMLD =
    M.ber hMD := by
  unfold SuperMatrix.ber
  have hMLD_eq : (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock = M.Dblock := by
    show M.Cblock * (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock +
         M.Dblock * (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock = M.Dblock
    simp only [SuperMatrix.lowerTriangular]
    simp only [Matrix.mul_zero, Matrix.mul_one, zero_add]
  have hMLB_eq : (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock = M.Bblock := by
    show M.Ablock * (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock +
         M.Bblock * (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock = M.Bblock
    simp only [SuperMatrix.lowerTriangular]
    simp only [Matrix.mul_zero, Matrix.mul_one, zero_add]
  have hMLC_eq : (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock =
                 M.Cblock + M.Dblock * C' := by
    show M.Cblock * (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock +
         M.Dblock * (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock =
         M.Cblock + M.Dblock * C'
    simp only [SuperMatrix.lowerTriangular]
    simp only [Matrix.mul_one]
  have hMLA_eq : (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock =
                 M.Ablock + M.Bblock * C' := by
    show M.Ablock * (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock +
         M.Bblock * (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock =
         M.Ablock + M.Bblock * C'
    simp only [SuperMatrix.lowerTriangular]
    simp only [Matrix.mul_one]
  rw [hMLD_eq, hMLC_eq, hMLB_eq, hMLA_eq]
  congr 1
  haveI : Invertible M.Dblock.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hMD).invertible
  haveI : Invertible M.Dblock := Matrix.invertibleOfDetInvertible M.Dblock
  have h_DinvD : M.Dblock⁻¹ * M.Dblock = 1 := Matrix.nonsing_inv_mul M.Dblock (isUnit_of_invertible _)
  have h_distrib : M.Bblock * M.Dblock⁻¹ * (M.Cblock + M.Dblock * C') =
                   M.Bblock * M.Dblock⁻¹ * M.Cblock + M.Bblock * C' := by
    rw [Matrix.mul_add]
    congr 1
    calc M.Bblock * M.Dblock⁻¹ * (M.Dblock * C')
        = M.Bblock * (M.Dblock⁻¹ * (M.Dblock * C')) := by rw [Matrix.mul_assoc]
      _ = M.Bblock * ((M.Dblock⁻¹ * M.Dblock) * C') := by rw [Matrix.mul_assoc]
      _ = M.Bblock * ((1 : Matrix (Fin m) (Fin m) Λ.carrier) * C') := by rw [h_DinvD]
      _ = M.Bblock * C' := by rw [Matrix.one_mul]
  have heq : M.Ablock + M.Bblock * C' - M.Bblock * M.Dblock⁻¹ * (M.Cblock + M.Dblock * C') =
             M.Ablock - M.Bblock * M.Dblock⁻¹ * M.Cblock := by
    rw [h_distrib]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply]
    ring
  rw [heq]

/-- Ber(U · Δ · L) = Ber(Δ) when U is upper triangular, Δ is diagonal, L is lower triangular. -/
theorem SuperMatrix.ber_UDL {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (D' : Matrix (Fin m) (Fin m) Λ.carrier)
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hB' : ∀ i j, B' i j ∈ Λ.odd)
    (hA' : ∀ i j, A' i j ∈ Λ.even) (hD' : ∀ i j, D' i j ∈ Λ.even)
    (hC' : ∀ i j, C' i j ∈ Λ.odd)
    (_hD'det : Λ.IsInvertible D'.det)
    (hUD : Λ.IsInvertible (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock.det)
    (hΔD : Λ.IsInvertible (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock.det)
    (_hLD : Λ.IsInvertible (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock.det)
    (hΔLD : Λ.IsInvertible ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
            (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC')).Dblock.det)
    (hUΔLD : Λ.IsInvertible ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB') *
             ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
              (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC'))).Dblock.det) :
    ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB') *
     ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
      (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC'))).ber hUΔLD =
    (SuperMatrix.diagonal A' D' h0odd hA' hD').ber hΔD := by
  -- Step 1: Compute (Δ · L) blocks
  have hΔL_D : ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
               (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC')).Dblock = D' := by
    show (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock *
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock +
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock *
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock = D'
    simp only [SuperMatrix.diagonal, SuperMatrix.lowerTriangular]
    simp only [Matrix.zero_mul, Matrix.mul_one, zero_add]
  have hΔLA : ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
              (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC')).Ablock = A' := by
    show (SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock *
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock +
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock *
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock = A'
    simp only [SuperMatrix.diagonal, SuperMatrix.lowerTriangular]
    simp only [Matrix.mul_one, Matrix.zero_mul, add_zero]
  have hΔLB : ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
              (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC')).Bblock = 0 := by
    show (SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock *
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock +
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock *
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock = 0
    simp only [SuperMatrix.diagonal, SuperMatrix.lowerTriangular]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  have hΔL_Schur : ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
                   (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC')).Ablock -
                  ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
                   (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC')).Bblock *
                  ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
                   (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC')).Dblock⁻¹ *
                  ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
                   (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC')).Cblock = A' := by
    rw [hΔLA, hΔLB]
    simp only [Matrix.zero_mul, sub_zero]
  have hBerΔL : ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
                (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC')).ber hΔLD =
               (SuperMatrix.diagonal A' D' h0odd hA' hD').ber hΔD := by
    unfold SuperMatrix.ber
    rw [hΔL_Schur, hΔL_D]
    show A'.det * D'.det⁻¹ =
         ((SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock -
          (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock *
          (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock⁻¹ *
          (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock).det *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock.det⁻¹
    simp only [SuperMatrix.diagonal, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
  have hBerUΔL := SuperMatrix.ber_mul_upperTriangular_left B'
    ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
     (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC'))
    h1 h0even h0odd hB' hΔLD hUD hUΔLD
  rw [hBerUΔL, hBerΔL]

/-- Ber(L · Δ · U) = Ber(Δ) when L is lower triangular, Δ is diagonal, U is upper triangular. -/
theorem SuperMatrix.ber_LDU {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (D' : Matrix (Fin m) (Fin m) Λ.carrier)
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hC' : ∀ i j, C' i j ∈ Λ.odd)
    (hA' : ∀ i j, A' i j ∈ Λ.even) (hD' : ∀ i j, D' i j ∈ Λ.even)
    (hB' : ∀ i j, B' i j ∈ Λ.odd)
    (hA'det : Λ.IsInvertible A'.det)  -- Key: A' must be invertible for LDU
    (_hD'det : Λ.IsInvertible D'.det)
    (_hLD : Λ.IsInvertible (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock.det)
    (hΔD : Λ.IsInvertible (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock.det)
    (_hUD : Λ.IsInvertible (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock.det)
    (hLΔD : Λ.IsInvertible ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
            (SuperMatrix.diagonal A' D' h0odd hA' hD')).Dblock.det)
    (hLΔUD : Λ.IsInvertible (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
              (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
             (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Dblock.det)
    -- Parity conditions for ber = berAlt
    (hD'inv_C'A'_odd : ∀ i j, (D'⁻¹ * (C' * A')) i j ∈ Λ.odd)
    (_hA'inv_B'_odd : ∀ i j, (A'⁻¹ * B') i j ∈ Λ.odd)
    (hLΔU_DinvC_odd : ∀ i j, ((((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                               (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
                              (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Dblock⁻¹ *
                             (C' * A')) i j ∈ Λ.odd) :
    (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
      (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
     (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).ber hLΔUD =
    (SuperMatrix.diagonal A' D' h0odd hA' hD').ber hΔD := by
  have hLΔB : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
              (SuperMatrix.diagonal A' D' h0odd hA' hD')).Bblock = 0 := by
    show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock +
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock = 0
    simp only [SuperMatrix.lowerTriangular, SuperMatrix.diagonal]
    simp only [Matrix.one_mul, Matrix.zero_mul, add_zero]
  have hLΔA : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
              (SuperMatrix.diagonal A' D' h0odd hA' hD')).Ablock = A' := by
    show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock +
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock = A'
    simp only [SuperMatrix.lowerTriangular, SuperMatrix.diagonal]
    simp only [Matrix.one_mul, Matrix.zero_mul, add_zero]
  have hLΔD_eq : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                 (SuperMatrix.diagonal A' D' h0odd hA' hD')).Dblock = D' := by
    show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock +
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock = D'
    simp only [SuperMatrix.lowerTriangular, SuperMatrix.diagonal]
    simp only [Matrix.mul_zero, Matrix.one_mul, zero_add]
  have hLΔA_det : Λ.IsInvertible ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                   (SuperMatrix.diagonal A' D' h0odd hA' hD')).Ablock.det := by
    rw [hLΔA]; exact hA'det
  have hLΔUA : (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
               (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Ablock = A' := by
    show ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')).Ablock *
         (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock +
         ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')).Bblock *
         (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Cblock = A'
    rw [hLΔA, hLΔB]
    simp only [SuperMatrix.upperTriangular]
    simp only [Matrix.mul_one, Matrix.zero_mul, add_zero]
  have hLΔUA_det : Λ.IsInvertible (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                    (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
                    (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Ablock.det := by
    rw [hLΔUA]; exact hA'det
  have hBerLΔ : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                (SuperMatrix.diagonal A' D' h0odd hA' hD')).ber hLΔD =
               (SuperMatrix.diagonal A' D' h0odd hA' hD').ber hΔD := by
    unfold SuperMatrix.ber
    have hSchurLΔ : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                    (SuperMatrix.diagonal A' D' h0odd hA' hD')).Ablock -
                   ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                    (SuperMatrix.diagonal A' D' h0odd hA' hD')).Bblock *
                   ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                    (SuperMatrix.diagonal A' D' h0odd hA' hD')).Dblock⁻¹ *
                   ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                    (SuperMatrix.diagonal A' D' h0odd hA' hD')).Cblock = A' := by
      rw [hLΔA, hLΔB]
      simp only [Matrix.zero_mul, sub_zero]
    rw [hSchurLΔ, hLΔD_eq]
    show A'.det * D'.det⁻¹ =
         ((SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock -
          (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock *
          (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock⁻¹ *
          (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock).det *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock.det⁻¹
    simp only [SuperMatrix.diagonal, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
  have hLΔC : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
              (SuperMatrix.diagonal A' D' h0odd hA' hD')).Cblock = C' * A' := by
    show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock +
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock = C' * A'
    simp only [SuperMatrix.lowerTriangular, SuperMatrix.diagonal]
    simp only [Matrix.one_mul, add_zero]
  have hLΔ_AinvB : ∀ i j, (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                           (SuperMatrix.diagonal A' D' h0odd hA' hD')).Ablock⁻¹ *
                          ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                           (SuperMatrix.diagonal A' D' h0odd hA' hD')).Bblock) i j ∈ Λ.odd := by
    intro i j
    rw [hLΔB, Matrix.mul_zero]
    exact h0odd
  have hLΔ_DinvC : ∀ i j, (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                           (SuperMatrix.diagonal A' D' h0odd hA' hD')).Dblock⁻¹ *
                          ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                           (SuperMatrix.diagonal A' D' h0odd hA' hD')).Cblock) i j ∈ Λ.odd := by
    intro i j
    rw [hLΔD_eq, hLΔC]
    exact hD'inv_C'A'_odd i j
  have hLΔUB : (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
               (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Bblock = A' * B' := by
    show ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')).Ablock *
         (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Bblock +
         ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')).Bblock *
         (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock = A' * B'
    rw [hLΔA, hLΔB]
    simp only [SuperMatrix.upperTriangular]
    simp only [Matrix.zero_mul, add_zero]
  have hLΔUC : (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
               (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Cblock = C' * A' := by
    show ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')).Cblock *
         (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock +
         ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')).Dblock *
         (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Cblock = C' * A'
    rw [hLΔC, hLΔD_eq]
    simp only [SuperMatrix.upperTriangular]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero]
  have hLΔU_AinvB : ∀ i j, ((((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                             (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
                            (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Ablock⁻¹ *
                           (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                             (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
                            (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Bblock) i j ∈ Λ.odd := by
    intro i j
    rw [hLΔUA, hLΔUB]
    haveI : Invertible A'.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hA'det).invertible
    haveI : Invertible A' := Matrix.invertibleOfDetInvertible A'
    have hAinvA : A'⁻¹ * A' = 1 := Matrix.nonsing_inv_mul A' (isUnit_of_invertible _)
    have heq : A'⁻¹ * (A' * B') = B' := by
      calc A'⁻¹ * (A' * B') = (A'⁻¹ * A') * B' := by rw [Matrix.mul_assoc]
        _ = (1 : Matrix _ _ _) * B' := by rw [hAinvA]
        _ = B' := by rw [Matrix.one_mul]
    rw [heq]
    exact hB' i j
  have hLΔU_DinvC : ∀ i j, ((((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                             (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
                            (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Dblock⁻¹ *
                           (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                             (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
                            (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Cblock) i j ∈ Λ.odd := by
    intro i j
    rw [hLΔUC]
    exact hLΔU_DinvC_odd i j
  have hBerAltLΔ := SuperMatrix.ber_eq_berAlt
    ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
     (SuperMatrix.diagonal A' D' h0odd hA' hD'))
    hLΔA_det hLΔD hLΔ_AinvB hLΔ_DinvC h1 h0even
  have hBerAltLΔU := SuperMatrix.ber_eq_berAlt
    (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
      (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
     (SuperMatrix.upperTriangular B' h1 h0even h0odd hB'))
    hLΔUA_det hLΔUD hLΔU_AinvB hLΔU_DinvC h1 h0even
  have hBerAltU := SuperMatrix.berAlt_mul_upperTriangular_right
    ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
     (SuperMatrix.diagonal A' D' h0odd hA' hD'))
    B' h1 h0even h0odd hB' hLΔA_det hLΔUA_det
  rw [hBerAltLΔU, hBerAltU, ← hBerAltLΔ, hBerLΔ]

/-- LDU factorization: M = L · Δ · U. Requires A invertible. -/
theorem SuperMatrix.LDU_factorization {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (hA : Λ.IsInvertible M.Ablock.det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hCAinv : ∀ i j, (M.Cblock * M.Ablock⁻¹) i j ∈ Λ.odd)
    (hAinvB : ∀ i j, (M.Ablock⁻¹ * M.Bblock) i j ∈ Λ.odd)
    (hSchur : ∀ i j, (schurComplementA M hA) i j ∈ Λ.even) :
    M = ((SuperMatrix.lowerTriangular (M.Cblock * M.Ablock⁻¹) h1 h0even h0odd hCAinv) *
         (SuperMatrix.diagonal M.Ablock (schurComplementA M hA) h0odd M.Ablock_even hSchur)) *
        (SuperMatrix.upperTriangular (M.Ablock⁻¹ * M.Bblock) h1 h0even h0odd hAinvB) := by
  haveI : Invertible M.Ablock.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hA).invertible
  haveI : Invertible M.Ablock := Matrix.invertibleOfDetInvertible M.Ablock
  have hAinvA : M.Ablock⁻¹ * M.Ablock = 1 := Matrix.nonsing_inv_mul M.Ablock (isUnit_of_invertible _)
  have hAAinv : M.Ablock * M.Ablock⁻¹ = 1 := Matrix.mul_nonsing_inv M.Ablock (isUnit_of_invertible _)
  have hA_eq : (((SuperMatrix.lowerTriangular (M.Cblock * M.Ablock⁻¹) h1 h0even h0odd hCAinv) *
                (SuperMatrix.diagonal M.Ablock (schurComplementA M hA) h0odd M.Ablock_even hSchur)) *
               (SuperMatrix.upperTriangular (M.Ablock⁻¹ * M.Bblock) h1 h0even h0odd hAinvB)).Ablock =
              M.Ablock := by
    simp only [SuperMatrix.mul_Ablock, SuperMatrix.lowerTriangular, SuperMatrix.diagonal,
               SuperMatrix.upperTriangular]
    simp only [Matrix.one_mul, add_zero, Matrix.mul_one, Matrix.mul_zero]
  have hB_eq : (((SuperMatrix.lowerTriangular (M.Cblock * M.Ablock⁻¹) h1 h0even h0odd hCAinv) *
                (SuperMatrix.diagonal M.Ablock (schurComplementA M hA) h0odd M.Ablock_even hSchur)) *
               (SuperMatrix.upperTriangular (M.Ablock⁻¹ * M.Bblock) h1 h0even h0odd hAinvB)).Bblock =
              M.Bblock := by
    simp only [SuperMatrix.mul_Bblock, SuperMatrix.mul_Ablock, SuperMatrix.lowerTriangular,
               SuperMatrix.diagonal, SuperMatrix.upperTriangular]
    simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.mul_one, Matrix.mul_zero]
    calc M.Ablock * (M.Ablock⁻¹ * M.Bblock)
        = (M.Ablock * M.Ablock⁻¹) * M.Bblock := by rw [Matrix.mul_assoc]
      _ = (1 : Matrix _ _ _) * M.Bblock := by rw [hAAinv]
      _ = M.Bblock := by rw [Matrix.one_mul]
  have hC_eq : (((SuperMatrix.lowerTriangular (M.Cblock * M.Ablock⁻¹) h1 h0even h0odd hCAinv) *
                (SuperMatrix.diagonal M.Ablock (schurComplementA M hA) h0odd M.Ablock_even hSchur)) *
               (SuperMatrix.upperTriangular (M.Ablock⁻¹ * M.Bblock) h1 h0even h0odd hAinvB)).Cblock =
              M.Cblock := by
    simp only [SuperMatrix.mul_Cblock, SuperMatrix.mul_Dblock, SuperMatrix.lowerTriangular,
               SuperMatrix.diagonal, SuperMatrix.upperTriangular]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, zero_add]
    calc (M.Cblock * M.Ablock⁻¹) * M.Ablock
        = M.Cblock * (M.Ablock⁻¹ * M.Ablock) := by rw [Matrix.mul_assoc]
      _ = M.Cblock * (1 : Matrix _ _ _) := by rw [hAinvA]
      _ = M.Cblock := by rw [Matrix.mul_one]
  have hD_eq : (((SuperMatrix.lowerTriangular (M.Cblock * M.Ablock⁻¹) h1 h0even h0odd hCAinv) *
                (SuperMatrix.diagonal M.Ablock (schurComplementA M hA) h0odd M.Ablock_even hSchur)) *
               (SuperMatrix.upperTriangular (M.Ablock⁻¹ * M.Bblock) h1 h0even h0odd hAinvB)).Dblock =
              M.Dblock := by
    simp only [SuperMatrix.mul_Dblock, SuperMatrix.mul_Cblock, SuperMatrix.lowerTriangular,
               SuperMatrix.diagonal, SuperMatrix.upperTriangular]
    simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.one_mul, zero_add, add_zero]
    unfold schurComplementA
    -- Goal: M.Cblock * M.Ablock⁻¹ * M.Ablock * (M.Ablock⁻¹ * M.Bblock) + (M.Dblock - M.Cblock * M.Ablock⁻¹ * M.Bblock) = M.Dblock
    -- First simplify: C * A⁻¹ * A = C
    have hCA : M.Cblock * M.Ablock⁻¹ * M.Ablock = M.Cblock := by
      calc M.Cblock * M.Ablock⁻¹ * M.Ablock
          = M.Cblock * (M.Ablock⁻¹ * M.Ablock) := by rw [Matrix.mul_assoc]
        _ = M.Cblock * (1 : Matrix _ _ _) := by rw [hAinvA]
        _ = M.Cblock := by rw [Matrix.mul_one]
    rw [hCA]
    have hAssoc : M.Cblock * (M.Ablock⁻¹ * M.Bblock) = M.Cblock * M.Ablock⁻¹ * M.Bblock := by
      rw [Matrix.mul_assoc]
    rw [hAssoc]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply]
    ring
  ext <;> simp only [hA_eq, hB_eq, hC_eq, hD_eq]

/-- UDL factorization: M = U · Δ · L. Requires D invertible. -/
theorem SuperMatrix.UDL_factorization {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (hD : Λ.IsInvertible M.Dblock.det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hBDinv : ∀ i j, (M.Bblock * M.Dblock⁻¹) i j ∈ Λ.odd)
    (hDinvC : ∀ i j, (M.Dblock⁻¹ * M.Cblock) i j ∈ Λ.odd)
    (hSchur : ∀ i j, (schurComplementD M hD) i j ∈ Λ.even) :
    M = ((SuperMatrix.upperTriangular (M.Bblock * M.Dblock⁻¹) h1 h0even h0odd hBDinv) *
         (SuperMatrix.diagonal (schurComplementD M hD) M.Dblock h0odd hSchur M.Dblock_even)) *
        (SuperMatrix.lowerTriangular (M.Dblock⁻¹ * M.Cblock) h1 h0even h0odd hDinvC) := by
  haveI : Invertible M.Dblock.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hD).invertible
  haveI : Invertible M.Dblock := Matrix.invertibleOfDetInvertible M.Dblock
  have hDinvD : M.Dblock⁻¹ * M.Dblock = 1 := Matrix.nonsing_inv_mul M.Dblock (isUnit_of_invertible _)
  have hDDinv : M.Dblock * M.Dblock⁻¹ = 1 := Matrix.mul_nonsing_inv M.Dblock (isUnit_of_invertible _)
  have hA_eq : (((SuperMatrix.upperTriangular (M.Bblock * M.Dblock⁻¹) h1 h0even h0odd hBDinv) *
                (SuperMatrix.diagonal (schurComplementD M hD) M.Dblock h0odd hSchur M.Dblock_even)) *
               (SuperMatrix.lowerTriangular (M.Dblock⁻¹ * M.Cblock) h1 h0even h0odd hDinvC)).Ablock =
              M.Ablock := by
    simp only [SuperMatrix.mul_Ablock, SuperMatrix.mul_Bblock, SuperMatrix.upperTriangular,
               SuperMatrix.diagonal, SuperMatrix.lowerTriangular]
    simp only [Matrix.one_mul, add_zero, Matrix.mul_one, Matrix.mul_zero, zero_add]
    unfold schurComplementD
    have hBD : M.Bblock * M.Dblock⁻¹ * M.Dblock = M.Bblock := by
      calc M.Bblock * M.Dblock⁻¹ * M.Dblock
          = M.Bblock * (M.Dblock⁻¹ * M.Dblock) := by rw [Matrix.mul_assoc]
        _ = M.Bblock * (1 : Matrix _ _ _) := by rw [hDinvD]
        _ = M.Bblock := by rw [Matrix.mul_one]
    rw [hBD]
    have hAssoc : M.Bblock * (M.Dblock⁻¹ * M.Cblock) = M.Bblock * M.Dblock⁻¹ * M.Cblock := by
      rw [Matrix.mul_assoc]
    rw [hAssoc]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply]
    ring
  have hB_eq : (((SuperMatrix.upperTriangular (M.Bblock * M.Dblock⁻¹) h1 h0even h0odd hBDinv) *
                (SuperMatrix.diagonal (schurComplementD M hD) M.Dblock h0odd hSchur M.Dblock_even)) *
               (SuperMatrix.lowerTriangular (M.Dblock⁻¹ * M.Cblock) h1 h0even h0odd hDinvC)).Bblock =
              M.Bblock := by
    simp only [SuperMatrix.mul_Bblock, SuperMatrix.mul_Ablock, SuperMatrix.upperTriangular,
               SuperMatrix.diagonal, SuperMatrix.lowerTriangular]
    simp only [Matrix.one_mul, add_zero, Matrix.mul_one, Matrix.mul_zero, zero_add]
    calc M.Bblock * M.Dblock⁻¹ * M.Dblock
        = M.Bblock * (M.Dblock⁻¹ * M.Dblock) := by rw [Matrix.mul_assoc]
      _ = M.Bblock * (1 : Matrix _ _ _) := by rw [hDinvD]
      _ = M.Bblock := by rw [Matrix.mul_one]
  have hC_eq : (((SuperMatrix.upperTriangular (M.Bblock * M.Dblock⁻¹) h1 h0even h0odd hBDinv) *
                (SuperMatrix.diagonal (schurComplementD M hD) M.Dblock h0odd hSchur M.Dblock_even)) *
               (SuperMatrix.lowerTriangular (M.Dblock⁻¹ * M.Cblock) h1 h0even h0odd hDinvC)).Cblock =
              M.Cblock := by
    simp only [SuperMatrix.mul_Cblock, SuperMatrix.mul_Dblock, SuperMatrix.upperTriangular,
               SuperMatrix.diagonal, SuperMatrix.lowerTriangular]
    simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.mul_one, Matrix.mul_zero, zero_add]
    calc M.Dblock * (M.Dblock⁻¹ * M.Cblock)
        = (M.Dblock * M.Dblock⁻¹) * M.Cblock := by rw [Matrix.mul_assoc]
      _ = (1 : Matrix _ _ _) * M.Cblock := by rw [hDDinv]
      _ = M.Cblock := by rw [Matrix.one_mul]
  have hD_eq : (((SuperMatrix.upperTriangular (M.Bblock * M.Dblock⁻¹) h1 h0even h0odd hBDinv) *
                (SuperMatrix.diagonal (schurComplementD M hD) M.Dblock h0odd hSchur M.Dblock_even)) *
               (SuperMatrix.lowerTriangular (M.Dblock⁻¹ * M.Cblock) h1 h0even h0odd hDinvC)).Dblock =
              M.Dblock := by
    simp only [SuperMatrix.mul_Dblock, SuperMatrix.mul_Cblock, SuperMatrix.upperTriangular,
               SuperMatrix.diagonal, SuperMatrix.lowerTriangular]
    simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.mul_one, Matrix.mul_zero, zero_add]
  ext <;> simp only [hA_eq, hB_eq, hC_eq, hD_eq]

/-- Berezinian multiplicativity when M.A is invertible. -/
theorem SuperMatrix.ber_mul_A_invertible {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (M N : SuperMatrix Λ n m)
    (hMA : Λ.IsInvertible M.Ablock.det)
    (hMD : Λ.IsInvertible M.Dblock.det)
    (hND : Λ.IsInvertible N.Dblock.det)
    (hMND : Λ.IsInvertible (M * N).Dblock.det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hBDinvN : ∀ i j, (N.Bblock * N.Dblock⁻¹) i j ∈ Λ.odd)
    (hDinvCN : ∀ i j, (N.Dblock⁻¹ * N.Cblock) i j ∈ Λ.odd)
    (hCAinvM : ∀ i j, (M.Cblock * M.Ablock⁻¹) i j ∈ Λ.odd)
    (hAinvBM : ∀ i j, (M.Ablock⁻¹ * M.Bblock) i j ∈ Λ.odd)
    (hDinvCM : ∀ i j, (M.Dblock⁻¹ * M.Cblock) i j ∈ Λ.odd)
    (hSchurM : ∀ i j, (schurComplementA M hMA) i j ∈ Λ.even)
    (hSchurN : ∀ i j, (schurComplementD N hND) i j ∈ Λ.even)
    (hSchurM_det : Λ.IsInvertible (schurComplementA M hMA).det) :
    (M * N).ber hMND = M.ber hMD * N.ber hND := by
  haveI : Invertible M.Ablock.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hMA).invertible
  haveI hInvMA : Invertible M.Ablock := Matrix.invertibleOfDetInvertible M.Ablock
  haveI : Invertible M.Dblock.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hMD).invertible
  haveI hInvMD : Invertible M.Dblock := Matrix.invertibleOfDetInvertible M.Dblock
  haveI : Invertible N.Dblock.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hND).invertible
  haveI hInvND : Invertible N.Dblock := Matrix.invertibleOfDetInvertible N.Dblock

  let C_M := M.Cblock * M.Ablock⁻¹
  let A_M := M.Ablock
  let D_M := schurComplementA M hMA
  let B_M := M.Ablock⁻¹ * M.Bblock

  let B_N := N.Bblock * N.Dblock⁻¹
  let A_N := schurComplementD N hND
  let D_N := N.Dblock
  let C_N := N.Dblock⁻¹ * N.Cblock

  let L := SuperMatrix.lowerTriangular C_M h1 h0even h0odd hCAinvM
  let Δ := SuperMatrix.diagonal A_M D_M h0odd M.Ablock_even hSchurM
  let U := SuperMatrix.upperTriangular B_M h1 h0even h0odd hAinvBM

  let U' := SuperMatrix.upperTriangular B_N h1 h0even h0odd hBDinvN
  let Δ' := SuperMatrix.diagonal A_N D_N h0odd hSchurN N.Dblock_even
  let L' := SuperMatrix.lowerTriangular C_N h1 h0even h0odd hDinvCN

  have hM_eq : M = (L * Δ) * U := SuperMatrix.LDU_factorization M hMA h1 h0even h0odd
    hCAinvM hAinvBM hSchurM

  have hN_eq : N = (U' * Δ') * L' := SuperMatrix.UDL_factorization N hND h1 h0even h0odd
    hBDinvN hDinvCN hSchurN

  have hLD : Λ.IsInvertible L.Dblock.det := by
    show Λ.IsInvertible (SuperMatrix.lowerTriangular C_M h1 h0even h0odd hCAinvM).Dblock.det
    simp only [SuperMatrix.lowerTriangular, Matrix.det_one]
    unfold GrassmannAlgebra.IsInvertible
    rw [Λ.body_one]
    exact one_ne_zero
  have hΔD : Λ.IsInvertible Δ.Dblock.det := hSchurM_det
  have hUD : Λ.IsInvertible U.Dblock.det := by
    show Λ.IsInvertible (SuperMatrix.upperTriangular B_M h1 h0even h0odd hAinvBM).Dblock.det
    simp only [SuperMatrix.upperTriangular, Matrix.det_one]
    unfold GrassmannAlgebra.IsInvertible
    rw [Λ.body_one]
    exact one_ne_zero
  have hU'D : Λ.IsInvertible U'.Dblock.det := by
    show Λ.IsInvertible (SuperMatrix.upperTriangular B_N h1 h0even h0odd hBDinvN).Dblock.det
    simp only [SuperMatrix.upperTriangular, Matrix.det_one]
    unfold GrassmannAlgebra.IsInvertible
    rw [Λ.body_one]
    exact one_ne_zero
  have hΔ'D : Λ.IsInvertible Δ'.Dblock.det := hND
  have hL'D : Λ.IsInvertible L'.Dblock.det := by
    show Λ.IsInvertible (SuperMatrix.lowerTriangular C_N h1 h0even h0odd hDinvCN).Dblock.det
    simp only [SuperMatrix.lowerTriangular, Matrix.det_one]
    unfold GrassmannAlgebra.IsInvertible
    rw [Λ.body_one]
    exact one_ne_zero

  have hMN_eq : M * N = ((L * Δ) * U) * ((U' * Δ') * L') := by
    rw [hM_eq, hN_eq]

  have hMN_assoc : M * N = (L * Δ * U * (U' * Δ')) * L' := by
    rw [hMN_eq]
    simp only [mul_assoc]
  have hXL'_D_eq' : (L * Δ * U * (U' * Δ') * L').Dblock = (L * Δ * U * (U' * Δ')).Dblock := by
    show (L * Δ * U * (U' * Δ')).Cblock * L'.Bblock + (L * Δ * U * (U' * Δ')).Dblock * L'.Dblock =
         (L * Δ * U * (U' * Δ')).Dblock
    have hL'B : L'.Bblock = 0 := rfl
    have hL'D : L'.Dblock = 1 := rfl
    simp only [hL'B, hL'D, Matrix.mul_zero, zero_add, Matrix.mul_one]
  have hXD : Λ.IsInvertible (L * Δ * U * (U' * Δ')).Dblock.det := by
    rw [← hXL'_D_eq']
    have h : (L * Δ * U * (U' * Δ') * L').Dblock = (M * N).Dblock := by rw [← hMN_assoc]
    rw [h]; exact hMND
  have hXL'D : Λ.IsInvertible (L * Δ * U * (U' * Δ') * L').Dblock.det := by
    have h : (L * Δ * U * (U' * Δ') * L').Dblock = (M * N).Dblock := by
      rw [← hMN_assoc]
    rw [h]; exact hMND

  have hStrip1 : (M * N).ber hMND = (L * Δ * U * (U' * Δ')).ber hXD := by
    have hXL'_D_eq : (L * Δ * U * (U' * Δ') * L').Dblock = (L * Δ * U * (U' * Δ')).Dblock := by
      show (L * Δ * U * (U' * Δ')).Cblock * L'.Bblock + (L * Δ * U * (U' * Δ')).Dblock * L'.Dblock =
           (L * Δ * U * (U' * Δ')).Dblock
      have hL'B : L'.Bblock = 0 := rfl
      have hL'D : L'.Dblock = 1 := rfl
      simp only [hL'B, hL'D, Matrix.mul_zero, zero_add, Matrix.mul_one]
    have hMN_blocks : M * N = (L * Δ * U * (U' * Δ')) * L' := hMN_assoc
    have hStrip := SuperMatrix.ber_mul_lowerTriangular_right (L * Δ * U * (U' * Δ')) C_N
      h1 h0even h0odd hDinvCN hXD hL'D
    have hDet_eq : (M * N).Dblock.det = ((L * Δ * U * (U' * Δ')) * L').Dblock.det := by
      rw [hMN_blocks]
    have hXL'D_ne : Λ.IsInvertible ((L * Δ * U * (U' * Δ')) * L').Dblock.det := by
      rw [hXL'_D_eq]; exact hXD
    have hStrip' := SuperMatrix.ber_mul_lowerTriangular_right (L * Δ * U * (U' * Δ')) C_N
      h1 h0even h0odd hDinvCN hXD hL'D hXL'D_ne
    unfold SuperMatrix.ber at hStrip' ⊢
    rw [hMN_blocks]
    exact hStrip'

  have hZΔ'_D_eq : (L * Δ * U * (U' * Δ')).Dblock = (L * Δ * U * U').Dblock * Δ'.Dblock := by
    have hXΔ' : L * Δ * U * (U' * Δ') = (L * Δ * U * U') * Δ' := by simp only [mul_assoc]
    rw [hXΔ']
    show (L * Δ * U * U').Cblock * Δ'.Bblock + (L * Δ * U * U').Dblock * Δ'.Dblock =
         (L * Δ * U * U').Dblock * Δ'.Dblock
    have hΔ'B : Δ'.Bblock = 0 := rfl
    simp only [hΔ'B, Matrix.mul_zero, zero_add]
  have hYD : Λ.IsInvertible (L * Δ * U * U').Dblock.det := by
    unfold GrassmannAlgebra.IsInvertible at hXD hND ⊢
    have hΔ'D_eq : Δ'.Dblock = N.Dblock := rfl
    have hXD_eq : (L * Δ * U * (U' * Δ')).Dblock.det = (L * Δ * U * U').Dblock.det * Δ'.Dblock.det := by
      rw [hZΔ'_D_eq]
      exact Matrix.det_mul _ _
    have h : Λ.body (L * Δ * U * (U' * Δ')).Dblock.det =
             Λ.body (L * Δ * U * U').Dblock.det * Λ.body N.Dblock.det := by
      rw [hXD_eq, hΔ'D_eq, Λ.body_mul]
    rw [h] at hXD
    exact left_ne_zero_of_mul hXD
  have hStrip2 : (L * Δ * U * (U' * Δ')).ber hXD =
                 (L * Δ * U * U').ber hYD * Δ'.ber hΔ'D := by
    let Z := L * Δ * U * U'
    have hXΔ' : L * Δ * U * (U' * Δ') = Z * Δ' := by
      show L * Δ * U * (U' * Δ') = (L * Δ * U * U') * Δ'
      simp only [mul_assoc]
    have hZΔ'A : (Z * Δ').Ablock = Z.Ablock * A_N := by
      show Z.Ablock * Δ'.Ablock + Z.Bblock * Δ'.Cblock = Z.Ablock * A_N
      have hΔ'A : Δ'.Ablock = A_N := rfl
      have hΔ'C : Δ'.Cblock = 0 := rfl
      simp only [hΔ'A, hΔ'C, Matrix.mul_zero, add_zero]
    have hZΔ'B : (Z * Δ').Bblock = Z.Bblock * D_N := by
      show Z.Ablock * Δ'.Bblock + Z.Bblock * Δ'.Dblock = Z.Bblock * D_N
      have hΔ'B : Δ'.Bblock = 0 := rfl
      have hΔ'D_eq : Δ'.Dblock = D_N := rfl
      simp only [hΔ'B, hΔ'D_eq, Matrix.mul_zero, zero_add]
    have hZΔ'C : (Z * Δ').Cblock = Z.Cblock * A_N := by
      show Z.Cblock * Δ'.Ablock + Z.Dblock * Δ'.Cblock = Z.Cblock * A_N
      have hΔ'A : Δ'.Ablock = A_N := rfl
      have hΔ'C : Δ'.Cblock = 0 := rfl
      simp only [hΔ'A, hΔ'C, Matrix.mul_zero, add_zero]
    have hZΔ'D_eq : (Z * Δ').Dblock = Z.Dblock * D_N := by
      show Z.Cblock * Δ'.Bblock + Z.Dblock * Δ'.Dblock = Z.Dblock * D_N
      have hΔ'B : Δ'.Bblock = 0 := rfl
      have hΔ'D_eq : Δ'.Dblock = D_N := rfl
      simp only [hΔ'B, hΔ'D_eq, Matrix.mul_zero, zero_add]
    -- Set up invertibility
    haveI : Invertible D_N.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hND).invertible
    haveI hInvDN : Invertible D_N := Matrix.invertibleOfDetInvertible D_N
    haveI : Invertible Z.Dblock.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hYD).invertible
    haveI hInvZD : Invertible Z.Dblock := Matrix.invertibleOfDetInvertible Z.Dblock
    -- Compute Schur complement: (Z*Δ').A - (Z*Δ').B * (Z*Δ').D⁻¹ * (Z*Δ').C
    -- = Z.A*A_N - Z.B*D_N * (Z.D*D_N)⁻¹ * Z.C*A_N
    -- = Z.A*A_N - Z.B*D_N * D_N⁻¹*Z.D⁻¹ * Z.C*A_N
    -- = Z.A*A_N - Z.B * Z.D⁻¹ * Z.C * A_N
    have h_inv : (Z.Dblock * D_N)⁻¹ = D_N⁻¹ * Z.Dblock⁻¹ := Matrix.mul_inv_rev Z.Dblock D_N
    have hSchur_eq : Z.Ablock * A_N - Z.Bblock * D_N * (Z.Dblock * D_N)⁻¹ * (Z.Cblock * A_N) =
                     (Z.Ablock - Z.Bblock * Z.Dblock⁻¹ * Z.Cblock) * A_N := by
      rw [h_inv]
      have hDNinv : D_N * D_N⁻¹ = 1 := Matrix.mul_nonsing_inv D_N (isUnit_of_invertible _)
      have h_cancel : Z.Bblock * D_N * (D_N⁻¹ * Z.Dblock⁻¹) * (Z.Cblock * A_N) =
                      Z.Bblock * Z.Dblock⁻¹ * Z.Cblock * A_N := by
        calc Z.Bblock * D_N * (D_N⁻¹ * Z.Dblock⁻¹) * (Z.Cblock * A_N)
            = Z.Bblock * (D_N * (D_N⁻¹ * Z.Dblock⁻¹)) * (Z.Cblock * A_N) := by simp only [Matrix.mul_assoc]
          _ = Z.Bblock * ((D_N * D_N⁻¹) * Z.Dblock⁻¹) * (Z.Cblock * A_N) := by simp only [Matrix.mul_assoc]
          _ = Z.Bblock * (1 * Z.Dblock⁻¹) * (Z.Cblock * A_N) := by rw [hDNinv]
          _ = Z.Bblock * Z.Dblock⁻¹ * (Z.Cblock * A_N) := by rw [Matrix.one_mul]
          _ = Z.Bblock * Z.Dblock⁻¹ * Z.Cblock * A_N := by simp only [Matrix.mul_assoc]
      rw [h_cancel, Matrix.sub_mul]
    unfold SuperMatrix.ber
    rw [hXΔ', hZΔ'A, hZΔ'B, hZΔ'C, hZΔ'D_eq, hSchur_eq]
    have hdet_schur : ((Z.Ablock - Z.Bblock * Z.Dblock⁻¹ * Z.Cblock) * A_N).det =
                      (Z.Ablock - Z.Bblock * Z.Dblock⁻¹ * Z.Cblock).det * A_N.det := Matrix.det_mul _ _
    have hdet_D : (Z.Dblock * D_N).det = Z.Dblock.det * D_N.det := Matrix.det_mul _ _
    rw [hdet_schur, hdet_D]
    have hZD_inv : Λ.IsInvertible Z.Dblock.det := hYD
    have hDN_inv : Λ.IsInvertible D_N.det := hND
    have h_inv_prod : (Z.Dblock.det * D_N.det)⁻¹ = Z.Dblock.det⁻¹ * D_N.det⁻¹ := by
      have hZD_unit : IsUnit Z.Dblock.det := (Λ.isUnit_iff_body_ne_zero _).mpr hZD_inv
      have hDN_unit : IsUnit D_N.det := (Λ.isUnit_iff_body_ne_zero _).mpr hDN_inv
      obtain ⟨uZ, huZ⟩ := hZD_unit
      obtain ⟨uD, huD⟩ := hDN_unit
      have h1 : Z.Dblock.det * D_N.det * (Z.Dblock.det⁻¹ * D_N.det⁻¹) = 1 := by
        have hZD_cancel : Z.Dblock.det * Z.Dblock.det⁻¹ = 1 := Λ.mul_inv_cancel _ hZD_inv
        have hDN_cancel : D_N.det * D_N.det⁻¹ = 1 := Λ.mul_inv_cancel _ hDN_inv
        calc Z.Dblock.det * D_N.det * (Z.Dblock.det⁻¹ * D_N.det⁻¹)
            = Z.Dblock.det * (D_N.det * Z.Dblock.det⁻¹) * D_N.det⁻¹ := by ring
          _ = Z.Dblock.det * (Z.Dblock.det⁻¹ * D_N.det) * D_N.det⁻¹ := by ring
          _ = (Z.Dblock.det * Z.Dblock.det⁻¹) * D_N.det * D_N.det⁻¹ := by ring
          _ = 1 * D_N.det * D_N.det⁻¹ := by rw [hZD_cancel]
          _ = D_N.det * D_N.det⁻¹ := by ring
          _ = 1 := hDN_cancel
      have h_prod_inv : Λ.IsInvertible (Z.Dblock.det * D_N.det) := Λ.mul_invertible _ _ hZD_inv hDN_inv
      have h_prod_cancel : (Z.Dblock.det * D_N.det) * (Z.Dblock.det * D_N.det)⁻¹ = 1 :=
        Λ.mul_inv_cancel _ h_prod_inv
      have h_prod_inv_cancel : (Z.Dblock.det * D_N.det)⁻¹ * (Z.Dblock.det * D_N.det) = 1 :=
        Λ.inv_mul_cancel _ h_prod_inv
      calc (Z.Dblock.det * D_N.det)⁻¹
          = (Z.Dblock.det * D_N.det)⁻¹ * 1 := (mul_one _).symm
        _ = (Z.Dblock.det * D_N.det)⁻¹ * (Z.Dblock.det * D_N.det * (Z.Dblock.det⁻¹ * D_N.det⁻¹)) := by rw [h1]
        _ = ((Z.Dblock.det * D_N.det)⁻¹ * (Z.Dblock.det * D_N.det)) * (Z.Dblock.det⁻¹ * D_N.det⁻¹) := by ring_nf
        _ = 1 * (Z.Dblock.det⁻¹ * D_N.det⁻¹) := by rw [h_prod_inv_cancel]
        _ = Z.Dblock.det⁻¹ * D_N.det⁻¹ := one_mul _
    rw [h_inv_prod]
    have hΔ'_schur : Δ'.Ablock - Δ'.Bblock * Δ'.Dblock⁻¹ * Δ'.Cblock = A_N := by
      have hΔ'B : Δ'.Bblock = 0 := rfl
      have hΔ'C : Δ'.Cblock = 0 := rfl
      have hΔ'A : Δ'.Ablock = A_N := rfl
      simp only [hΔ'B, hΔ'C, hΔ'A, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
    have hΔ'D : Δ'.Dblock = D_N := rfl
    have hZ_eq : Z = L * Δ * U * U' := rfl
    have hZA : Z.Ablock = (L * Δ * U * U').Ablock := rfl
    have hZB : Z.Bblock = (L * Δ * U * U').Bblock := rfl
    have hZC : Z.Cblock = (L * Δ * U * U').Cblock := rfl
    have hZD : Z.Dblock = (L * Δ * U * U').Dblock := rfl
    conv_rhs =>
      rw [← hZA, ← hZB, ← hZC, ← hZD]
      rw [hΔ'_schur, hΔ'D]
    ring

  have hStrip3 : (L * Δ * U * U').ber hYD = Δ.ber hΔD := by
    have hLΔ_A : (L * Δ).Ablock = M.Ablock := by
      show L.Ablock * Δ.Ablock + L.Bblock * Δ.Cblock = M.Ablock
      have hLA : L.Ablock = 1 := rfl
      have hLB : L.Bblock = 0 := rfl
      have hΔA : Δ.Ablock = M.Ablock := rfl
      simp only [hLA, hLB, hΔA, Matrix.one_mul, Matrix.zero_mul, add_zero]
    have hLΔ_B : (L * Δ).Bblock = 0 := by
      show L.Ablock * Δ.Bblock + L.Bblock * Δ.Dblock = 0
      have hLA : L.Ablock = 1 := rfl
      have hLB : L.Bblock = 0 := rfl
      have hΔB : Δ.Bblock = 0 := rfl
      simp only [hLA, hLB, hΔB, Matrix.mul_zero, Matrix.zero_mul, add_zero]
    have hLΔ_C : (L * Δ).Cblock = C_M * M.Ablock := by
      show L.Cblock * Δ.Ablock + L.Dblock * Δ.Cblock = C_M * M.Ablock
      have hLC : L.Cblock = C_M := rfl
      have hLD : L.Dblock = 1 := rfl
      have hΔA : Δ.Ablock = M.Ablock := rfl
      have hΔC : Δ.Cblock = 0 := rfl
      simp only [hLC, hLD, hΔA, hΔC, Matrix.mul_zero, add_zero]
    have hLΔ_D : (L * Δ).Dblock = D_M := by
      show L.Cblock * Δ.Bblock + L.Dblock * Δ.Dblock = D_M
      have hLC : L.Cblock = C_M := rfl
      have hLD : L.Dblock = 1 := rfl
      have hΔB : Δ.Bblock = 0 := rfl
      have hΔD : Δ.Dblock = D_M := rfl
      simp only [hLC, hLD, hΔB, hΔD, Matrix.mul_zero, zero_add, Matrix.one_mul]
    have hUU'_A : (U * U').Ablock = 1 := by
      show U.Ablock * U'.Ablock + U.Bblock * U'.Cblock = 1
      have hUA : U.Ablock = 1 := rfl
      have hUB : U.Bblock = B_M := rfl
      have hU'A : U'.Ablock = 1 := rfl
      have hU'C : U'.Cblock = 0 := rfl
      simp only [hUA, hU'A, hUB, hU'C, Matrix.one_mul, Matrix.mul_zero, add_zero]
    have hUU'_B : (U * U').Bblock = B_M + B_N := by
      show U.Ablock * U'.Bblock + U.Bblock * U'.Dblock = B_M + B_N
      have hUA : U.Ablock = 1 := rfl
      have hUB : U.Bblock = B_M := rfl
      have hU'B : U'.Bblock = B_N := rfl
      have hU'D : U'.Dblock = 1 := rfl
      simp only [hUA, hUB, hU'B, hU'D, Matrix.one_mul, Matrix.mul_one]
      ext i j; simp only [Matrix.add_apply]; ring
    have hUU'_C : (U * U').Cblock = 0 := by
      show U.Cblock * U'.Ablock + U.Dblock * U'.Cblock = 0
      have hUC : U.Cblock = 0 := rfl
      have hUD : U.Dblock = 1 := rfl
      have hU'A : U'.Ablock = 1 := rfl
      have hU'C : U'.Cblock = 0 := rfl
      simp only [hUC, hUD, hU'A, hU'C, Matrix.zero_mul, Matrix.one_mul, add_zero]
    have hUU'_D : (U * U').Dblock = 1 := by
      show U.Cblock * U'.Bblock + U.Dblock * U'.Dblock = 1
      have hUC : U.Cblock = 0 := rfl
      have hUD : U.Dblock = 1 := rfl
      have hU'B : U'.Bblock = B_N := rfl
      have hU'D : U'.Dblock = 1 := rfl
      simp only [hUC, hUD, hU'B, hU'D, Matrix.zero_mul, Matrix.one_mul, zero_add]
    let LΔ := L * Δ
    let UU' := U * U'
    have hW_eq : L * Δ * U * U' = LΔ * UU' := by
      calc L * Δ * U * U' = (L * Δ * U) * U' := rfl
        _ = (L * Δ) * U * U' := by rfl
        _ = (L * Δ) * (U * U') := by rw [mul_assoc]
        _ = LΔ * UU' := rfl
    have hW_A : (LΔ * UU').Ablock = M.Ablock := by
      show LΔ.Ablock * UU'.Ablock + LΔ.Bblock * UU'.Cblock = M.Ablock
      rw [hLΔ_A, hLΔ_B, hUU'_A, hUU'_C]
      simp only [Matrix.mul_one, Matrix.zero_mul, add_zero]
    have hW_B : (LΔ * UU').Bblock = M.Ablock * (B_M + B_N) := by
      show LΔ.Ablock * UU'.Bblock + LΔ.Bblock * UU'.Dblock = M.Ablock * (B_M + B_N)
      rw [hLΔ_A, hLΔ_B, hUU'_B, hUU'_D]
      simp only [Matrix.zero_mul, add_zero]
    have hW_C : (LΔ * UU').Cblock = C_M * M.Ablock := by
      show LΔ.Cblock * UU'.Ablock + LΔ.Dblock * UU'.Cblock = C_M * M.Ablock
      rw [hLΔ_C, hLΔ_D, hUU'_A, hUU'_C]
      simp only [Matrix.mul_one, Matrix.mul_zero, add_zero]
    have hW_D : (LΔ * UU').Dblock = C_M * M.Ablock * (B_M + B_N) + D_M := by
      show LΔ.Cblock * UU'.Bblock + LΔ.Dblock * UU'.Dblock = C_M * M.Ablock * (B_M + B_N) + D_M
      rw [hLΔ_C, hLΔ_D, hUU'_B, hUU'_D]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    have hW_A_eq : (L * Δ * U * U').Ablock = M.Ablock := by rw [hW_eq]; exact hW_A
    have hW_A_det : Λ.IsInvertible (L * Δ * U * U').Ablock.det := by rw [hW_A_eq]; exact hMA
    -- Need parity conditions for W.A⁻¹*W.B and W.D⁻¹*W.C
    -- W.A = M.A (even), W.B = M.A*(B_M+B_N) where B_M, B_N are odd
    -- W.A⁻¹*W.B = M.A⁻¹ * M.A * (B_M+B_N) = B_M + B_N which is odd
    have hW_AinvB_odd : ∀ i j, ((L * Δ * U * U').Ablock⁻¹ * (L * Δ * U * U').Bblock) i j ∈ Λ.odd := by
      intro i j
      rw [hW_eq, hW_A, hW_B]
      have hAinvA : M.Ablock⁻¹ * M.Ablock = 1 := Matrix.nonsing_inv_mul M.Ablock (isUnit_of_invertible _)
      have h_eq : M.Ablock⁻¹ * (M.Ablock * (B_M + B_N)) = B_M + B_N := by
        calc M.Ablock⁻¹ * (M.Ablock * (B_M + B_N))
            = (M.Ablock⁻¹ * M.Ablock) * (B_M + B_N) := by rw [Matrix.mul_assoc]
          _ = (1 : Matrix _ _ _) * (B_M + B_N) := by rw [hAinvA]
          _ = B_M + B_N := by rw [Matrix.one_mul]
      rw [h_eq]
      have hBM_odd : B_M i j ∈ Λ.odd := hAinvBM i j
      have hBN_odd : B_N i j ∈ Λ.odd := hBDinvN i j
      exact Λ.odd.add_mem hBM_odd hBN_odd
    have hW_C_eq_MC : (L * Δ * U * U').Cblock = M.Cblock := by
      rw [hW_eq, hW_C]
      have hAinvA : M.Ablock⁻¹ * M.Ablock = 1 := Matrix.nonsing_inv_mul M.Ablock (isUnit_of_invertible _)
      calc C_M * M.Ablock
          = (M.Cblock * M.Ablock⁻¹) * M.Ablock := rfl
        _ = M.Cblock * (M.Ablock⁻¹ * M.Ablock) := by rw [Matrix.mul_assoc]
        _ = M.Cblock * (1 : Matrix _ _ _) := by rw [hAinvA]
        _ = M.Cblock := by rw [Matrix.mul_one]
    have hW_D_even : ∀ i j, (L * Δ * U * U').Dblock i j ∈ Λ.even := by
      intro i j
      rw [hW_eq, hW_D]
      have hCM_MA_eq : C_M * M.Ablock = M.Cblock := by
        have hAinvA : M.Ablock⁻¹ * M.Ablock = 1 := Matrix.nonsing_inv_mul M.Ablock (isUnit_of_invertible _)
        calc C_M * M.Ablock
            = (M.Cblock * M.Ablock⁻¹) * M.Ablock := rfl
          _ = M.Cblock * (M.Ablock⁻¹ * M.Ablock) := by rw [Matrix.mul_assoc]
          _ = M.Cblock * (1 : Matrix _ _ _) := by rw [hAinvA]
          _ = M.Cblock := by rw [Matrix.mul_one]
      simp only [Matrix.add_apply]
      have hProd_even : (C_M * M.Ablock * (B_M + B_N)) i j ∈ Λ.even := by
        have h_eq : C_M * M.Ablock * (B_M + B_N) = M.Cblock * (B_M + B_N) := by
          rw [hCM_MA_eq]
        rw [h_eq]
        simp only [Matrix.mul_apply]
        apply Λ.even.sum_mem
        intro k _
        have hMC_odd : M.Cblock i k ∈ Λ.odd := M.Cblock_odd i k
        have hBsum_odd : (B_M + B_N) k j ∈ Λ.odd := by
          simp only [Matrix.add_apply]
          exact Λ.odd.add_mem (hAinvBM k j) (hBDinvN k j)
        exact Λ.odd_mul_odd _ _ hMC_odd hBsum_odd
      have hDM_even : D_M i j ∈ Λ.even := hSchurM i j
      exact Λ.even.add_mem hProd_even hDM_even
    have hW_DinvC_odd : ∀ i j, ((L * Δ * U * U').Dblock⁻¹ * (L * Δ * U * U').Cblock) i j ∈ Λ.odd := by
      intro i j
      rw [hW_C_eq_MC]
      simp only [Matrix.mul_apply]
      apply Λ.odd.sum_mem
      intro k _
      have hMC_odd : M.Cblock k j ∈ Λ.odd := M.Cblock_odd k j
      have hWDinv_even : (L * Δ * U * U').Dblock⁻¹ i k ∈ Λ.even := by
        exact matrix_inv_even (L * Δ * U * U').Dblock hW_D_even hYD h1 h0even i k
      exact Λ.even_mul_odd _ _ hWDinv_even hMC_odd
    have hW_berAlt := SuperMatrix.ber_eq_berAlt (L * Δ * U * U') hW_A_det hYD
      hW_AinvB_odd hW_DinvC_odd h1 h0even
    rw [hW_berAlt]
    unfold SuperMatrix.berAlt
    rw [hW_eq, hW_A, hW_B, hW_C, hW_D]
    have hAAinv : M.Ablock * M.Ablock⁻¹ = 1 := Matrix.mul_nonsing_inv M.Ablock (isUnit_of_invertible _)
    have hSchurA_W : C_M * M.Ablock * (B_M + B_N) + D_M - C_M * M.Ablock * M.Ablock⁻¹ * (M.Ablock * (B_M + B_N)) = D_M := by
      have h_cancel : C_M * M.Ablock * M.Ablock⁻¹ = C_M := by
        calc C_M * M.Ablock * M.Ablock⁻¹
            = C_M * (M.Ablock * M.Ablock⁻¹) := by rw [Matrix.mul_assoc]
          _ = C_M * (1 : Matrix _ _ _) := by rw [hAAinv]
          _ = C_M := by rw [Matrix.mul_one]
      calc C_M * M.Ablock * (B_M + B_N) + D_M - C_M * M.Ablock * M.Ablock⁻¹ * (M.Ablock * (B_M + B_N))
          = C_M * M.Ablock * (B_M + B_N) + D_M - C_M * (M.Ablock * (B_M + B_N)) := by rw [h_cancel]
        _ = C_M * M.Ablock * (B_M + B_N) + D_M - C_M * M.Ablock * (B_M + B_N) := by rw [Matrix.mul_assoc]
        _ = D_M := by ext i j; simp only [Matrix.add_apply, Matrix.sub_apply]; ring
    rw [hSchurA_W]
    unfold SuperMatrix.ber
    have hΔA : Δ.Ablock = M.Ablock := rfl
    have hΔB : Δ.Bblock = 0 := rfl
    have hΔC : Δ.Cblock = 0 := rfl
    have hΔD_eq : Δ.Dblock = D_M := rfl
    simp only [hΔA, hΔB, hΔC, hΔD_eq, Matrix.zero_mul, Matrix.mul_zero, sub_zero]

  have hLΔU_D : (L * Δ * U).Dblock.det = M.Dblock.det := by rw [← hM_eq]
  have hLΔU_D' : Λ.IsInvertible (L * Δ * U).Dblock.det := hLΔU_D ▸ hMD

  have hBerM : M.ber hMD = Δ.ber hΔD := by
    have hBerAlt := SuperMatrix.ber_eq_berAlt M hMA hMD hAinvBM hDinvCM h1 h0even
    rw [hBerAlt]
    unfold SuperMatrix.ber SuperMatrix.berAlt
    have hΔA : Δ.Ablock = M.Ablock := rfl
    have hΔB : Δ.Bblock = 0 := rfl
    have hΔC : Δ.Cblock = 0 := rfl
    have hΔD_eq : Δ.Dblock = schurComplementA M hMA := rfl
    simp only [hΔA, hΔB, hΔC, hΔD_eq, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
    rfl

  have hU'Δ'L'_D : (U' * Δ' * L').Dblock.det = N.Dblock.det := by rw [← hN_eq]
  have hU'Δ'L'_D' : Λ.IsInvertible (U' * Δ' * L').Dblock.det := hU'Δ'L'_D ▸ hND

  have hBerN : N.ber hND = Δ'.ber hΔ'D := by
    unfold SuperMatrix.ber
    have hΔ'A : Δ'.Ablock = schurComplementD N hND := rfl
    have hΔ'B : Δ'.Bblock = 0 := rfl
    have hΔ'C : Δ'.Cblock = 0 := rfl
    have hΔ'D_eq : Δ'.Dblock = N.Dblock := rfl
    simp only [hΔ'A, hΔ'B, hΔ'C, hΔ'D_eq, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
    rfl

  rw [hStrip1, hStrip2, hStrip3, hBerM, hBerN]

/-- Ber(L * N) = Ber(N) for lower triangular L = [I 0; C' I]. -/
theorem SuperMatrix.ber_mul_lowerTriangular_left {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (N : SuperMatrix Λ n m)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd)
    (hND : Λ.IsInvertible N.Dblock.det)
    (hLD : Λ.IsInvertible (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock.det)
    (hLND : Λ.IsInvertible ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') * N).Dblock.det)
    (hBDinvN : ∀ i j, (N.Bblock * N.Dblock⁻¹) i j ∈ Λ.odd)
    (hDinvCN : ∀ i j, (N.Dblock⁻¹ * N.Cblock) i j ∈ Λ.odd)
    (hSchurN : ∀ i j, (schurComplementD N hND) i j ∈ Λ.even) :
    ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') * N).ber hLND =
    N.ber hND := by
  let L := SuperMatrix.lowerTriangular C' h1 h0even h0odd hC'
  have hLA : Λ.IsInvertible L.Ablock.det := by
    show Λ.IsInvertible (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock.det
    simp only [SuperMatrix.lowerTriangular, Matrix.det_one]
    unfold GrassmannAlgebra.IsInvertible
    rw [Λ.body_one]
    exact one_ne_zero
  have hBerL : L.ber hLD = 1 := SuperMatrix.ber_lowerTriangular C' h1 h0even h0odd hC' hLD
  have hCAinvL : ∀ i j, (L.Cblock * L.Ablock⁻¹) i j ∈ Λ.odd := by
    intro i j
    show ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock *
          (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock⁻¹) i j ∈ Λ.odd
    simp only [SuperMatrix.lowerTriangular]
    rw [inv_one, Matrix.mul_one]
    exact hC' i j
  have hAinvBL : ∀ i j, (L.Ablock⁻¹ * L.Bblock) i j ∈ Λ.odd := by
    intro i j
    show ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock⁻¹ *
          (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock) i j ∈ Λ.odd
    simp only [SuperMatrix.lowerTriangular]
    rw [Matrix.mul_zero]
    exact h0odd
  have hSchurL : ∀ i j, (schurComplementA L hLA) i j ∈ Λ.even := by
    intro i j
    unfold schurComplementA
    have hLB : L.Bblock = 0 := rfl
    have hLD_eq : L.Dblock = 1 := rfl
    rw [hLB, Matrix.mul_zero, sub_zero, hLD_eq]
    simp only [Matrix.one_apply]
    split_ifs
    · exact h1
    · exact h0even
  have hSchurL_det : Λ.IsInvertible (schurComplementA L hLA).det := by
    unfold schurComplementA
    have hLB : L.Bblock = 0 := rfl
    have hLD_eq : L.Dblock = 1 := rfl
    simp only [hLB, Matrix.mul_zero, sub_zero, hLD_eq, Matrix.det_one]
    unfold GrassmannAlgebra.IsInvertible
    rw [Λ.body_one]
    exact one_ne_zero
  have hDinvCL : ∀ i j, (L.Dblock⁻¹ * L.Cblock) i j ∈ Λ.odd := by
    intro i j
    show ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock⁻¹ *
          (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock) i j ∈ Λ.odd
    simp only [SuperMatrix.lowerTriangular]
    rw [inv_one, Matrix.one_mul]
    exact hC' i j
  have hMul := SuperMatrix.ber_mul_A_invertible L N hLA hLD hND hLND h1 h0even h0odd
    hBDinvN hDinvCN hCAinvL hAinvBL hDinvCL hSchurL hSchurN hSchurL_det
  rw [hMul, hBerL, one_mul]

/-- Ber(Δ * Z) = Ber(Δ) * Ber(Z) for diagonal Δ = [A' 0; 0 D']. -/
theorem SuperMatrix.ber_mul_diagonal_left {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (D' : Matrix (Fin m) (Fin m) Λ.carrier)
    (Z : SuperMatrix Λ n m)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hA' : ∀ i j, A' i j ∈ Λ.even) (hD' : ∀ i j, D' i j ∈ Λ.even)
    (hD'det : Λ.IsInvertible D'.det) (hZD : Λ.IsInvertible Z.Dblock.det)
    (hΔD : Λ.IsInvertible (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock.det)
    (hΔZD : Λ.IsInvertible ((SuperMatrix.diagonal A' D' h0odd hA' hD') * Z).Dblock.det) :
    ((SuperMatrix.diagonal A' D' h0odd hA' hD') * Z).ber hΔZD =
    (SuperMatrix.diagonal A' D' h0odd hA' hD').ber hΔD * Z.ber hZD := by
  unfold SuperMatrix.ber
  have hΔZA : ((SuperMatrix.diagonal A' D' h0odd hA' hD') * Z).Ablock = A' * Z.Ablock := by
    show (SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock * Z.Ablock +
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock * Z.Cblock = A' * Z.Ablock
    simp only [SuperMatrix.diagonal]
    simp only [Matrix.zero_mul, add_zero]
  have hΔZB : ((SuperMatrix.diagonal A' D' h0odd hA' hD') * Z).Bblock = A' * Z.Bblock := by
    show (SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock * Z.Bblock +
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock * Z.Dblock = A' * Z.Bblock
    simp only [SuperMatrix.diagonal]
    simp only [Matrix.zero_mul, add_zero]
  have hΔZC : ((SuperMatrix.diagonal A' D' h0odd hA' hD') * Z).Cblock = D' * Z.Cblock := by
    show (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock * Z.Ablock +
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock * Z.Cblock = D' * Z.Cblock
    simp only [SuperMatrix.diagonal]
    simp only [Matrix.zero_mul, zero_add]
  have hΔZD_eq : ((SuperMatrix.diagonal A' D' h0odd hA' hD') * Z).Dblock = D' * Z.Dblock := by
    show (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock * Z.Bblock +
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock * Z.Dblock = D' * Z.Dblock
    simp only [SuperMatrix.diagonal]
    simp only [Matrix.zero_mul, zero_add]
  rw [hΔZA, hΔZB, hΔZC, hΔZD_eq]
  haveI : Invertible D'.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hD'det).invertible
  haveI : Invertible D' := Matrix.invertibleOfDetInvertible D'
  haveI : Invertible Z.Dblock.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hZD).invertible
  haveI : Invertible Z.Dblock := Matrix.invertibleOfDetInvertible Z.Dblock
  have h_inv : (D' * Z.Dblock)⁻¹ = Z.Dblock⁻¹ * D'⁻¹ := by
    rw [Matrix.mul_inv_rev]
  have h_det : (D' * Z.Dblock).det = D'.det * Z.Dblock.det := by
    rw [Matrix.det_mul]
  have h_schur : A' * Z.Ablock - A' * Z.Bblock * (D' * Z.Dblock)⁻¹ * (D' * Z.Cblock) =
                 A' * (Z.Ablock - Z.Bblock * Z.Dblock⁻¹ * Z.Cblock) := by
    rw [h_inv]
    -- A'·Z.A - A'·Z.B · Z.D⁻¹·D'⁻¹ · D'·Z.C
    -- = A'·Z.A - A'·Z.B · Z.D⁻¹ · (D'⁻¹·D') · Z.C
    -- = A'·Z.A - A'·Z.B · Z.D⁻¹ · Z.C
    have h_cancel : Z.Bblock * (Z.Dblock⁻¹ * D'⁻¹) * (D' * Z.Cblock) =
                    Z.Bblock * Z.Dblock⁻¹ * Z.Cblock := by
      have h1 : D'⁻¹ * (D' * Z.Cblock) = Z.Cblock := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul D' (isUnit_of_invertible _), Matrix.one_mul]
      calc Z.Bblock * (Z.Dblock⁻¹ * D'⁻¹) * (D' * Z.Cblock)
          = Z.Bblock * (Z.Dblock⁻¹ * (D'⁻¹ * (D' * Z.Cblock))) := by
              simp only [Matrix.mul_assoc]
        _ = Z.Bblock * (Z.Dblock⁻¹ * Z.Cblock) := by rw [h1]
        _ = Z.Bblock * Z.Dblock⁻¹ * Z.Cblock := by rw [Matrix.mul_assoc]
    calc A' * Z.Ablock - A' * Z.Bblock * (Z.Dblock⁻¹ * D'⁻¹) * (D' * Z.Cblock)
        = A' * Z.Ablock - A' * (Z.Bblock * (Z.Dblock⁻¹ * D'⁻¹) * (D' * Z.Cblock)) := by
            simp only [Matrix.mul_assoc]
      _ = A' * Z.Ablock - A' * (Z.Bblock * Z.Dblock⁻¹ * Z.Cblock) := by rw [h_cancel]
      _ = A' * (Z.Ablock - Z.Bblock * Z.Dblock⁻¹ * Z.Cblock) := by rw [← Matrix.mul_sub]
  rw [h_schur]
  have h_det_schur : (A' * (Z.Ablock - Z.Bblock * Z.Dblock⁻¹ * Z.Cblock)).det =
                     A'.det * (Z.Ablock - Z.Bblock * Z.Dblock⁻¹ * Z.Cblock).det := by
    rw [Matrix.det_mul]
  rw [h_det_schur, h_det]
  have h_inv_prod : (D'.det * Z.Dblock.det)⁻¹ = D'.det⁻¹ * Z.Dblock.det⁻¹ := by
    have h1 : D'.det * Z.Dblock.det * (D'.det⁻¹ * Z.Dblock.det⁻¹) = 1 := by
      have hD'_cancel : D'.det * D'.det⁻¹ = 1 := Λ.mul_inv_cancel _ hD'det
      have hZD_cancel : Z.Dblock.det * Z.Dblock.det⁻¹ = 1 := Λ.mul_inv_cancel _ hZD
      calc D'.det * Z.Dblock.det * (D'.det⁻¹ * Z.Dblock.det⁻¹)
          = (D'.det * D'.det⁻¹) * (Z.Dblock.det * Z.Dblock.det⁻¹) := by ring
        _ = 1 * 1 := by rw [hD'_cancel, hZD_cancel]
        _ = 1 := one_mul _
    have h_prod_inv : Λ.IsInvertible (D'.det * Z.Dblock.det) :=
      Λ.mul_invertible _ _ hD'det hZD
    have h_prod_inv_cancel : (D'.det * Z.Dblock.det)⁻¹ * (D'.det * Z.Dblock.det) = 1 :=
      Λ.inv_mul_cancel _ h_prod_inv
    calc (D'.det * Z.Dblock.det)⁻¹
        = (D'.det * Z.Dblock.det)⁻¹ * 1 := (mul_one _).symm
      _ = (D'.det * Z.Dblock.det)⁻¹ *
          (D'.det * Z.Dblock.det * (D'.det⁻¹ * Z.Dblock.det⁻¹)) := by rw [h1]
      _ = ((D'.det * Z.Dblock.det)⁻¹ * (D'.det * Z.Dblock.det)) *
          (D'.det⁻¹ * Z.Dblock.det⁻¹) := by ring
      _ = 1 * (D'.det⁻¹ * Z.Dblock.det⁻¹) := by rw [h_prod_inv_cancel]
      _ = D'.det⁻¹ * Z.Dblock.det⁻¹ := one_mul _
  rw [h_inv_prod]
  have hΔA : (SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock = A' := rfl
  have hΔB : (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock = 0 := rfl
  have hΔC : (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock = 0 := rfl
  have hΔD : (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock = D' := rfl
  have hΔ_schur2 : (SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock -
                   (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock *
                   D'⁻¹ *
                   (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock = A' := by
    simp only [hΔA, hΔB, hΔC, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
  simp only [hΔD, hΔ_schur2]
  ring

/-- Ber(Z * Δ') = Ber(Z) * Ber(Δ') for diagonal Δ' = [A'' 0; 0 D'']. -/
theorem SuperMatrix.ber_mul_diagonal_right {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (Z : SuperMatrix Λ n m)
    (A'' : Matrix (Fin n) (Fin n) Λ.carrier) (D'' : Matrix (Fin m) (Fin m) Λ.carrier)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hA'' : ∀ i j, A'' i j ∈ Λ.even) (hD'' : ∀ i j, D'' i j ∈ Λ.even)
    (hD''det : Λ.IsInvertible D''.det) (hZD : Λ.IsInvertible Z.Dblock.det)
    (hΔD : Λ.IsInvertible (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Dblock.det)
    (hZΔD : Λ.IsInvertible (Z * (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'')).Dblock.det) :
    (Z * (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'')).ber hZΔD =
    Z.ber hZD * (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').ber hΔD := by
  unfold SuperMatrix.ber
  have hZΔA : (Z * SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Ablock = Z.Ablock * A'' := by
    show Z.Ablock * (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Ablock +
         Z.Bblock * (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Cblock = Z.Ablock * A''
    simp only [SuperMatrix.diagonal]
    simp only [Matrix.mul_zero, add_zero]
  have hZΔB : (Z * SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Bblock = Z.Bblock * D'' := by
    show Z.Ablock * (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Bblock +
         Z.Bblock * (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Dblock = Z.Bblock * D''
    simp only [SuperMatrix.diagonal]
    simp only [Matrix.mul_zero, zero_add]
  have hZΔC : (Z * SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Cblock = Z.Cblock * A'' := by
    show Z.Cblock * (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Ablock +
         Z.Dblock * (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Cblock = Z.Cblock * A''
    simp only [SuperMatrix.diagonal]
    simp only [Matrix.mul_zero, add_zero]
  have hZΔD_eq : (Z * SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Dblock = Z.Dblock * D'' := by
    show Z.Cblock * (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Bblock +
         Z.Dblock * (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Dblock = Z.Dblock * D''
    simp only [SuperMatrix.diagonal]
    simp only [Matrix.mul_zero, zero_add]
  rw [hZΔA, hZΔB, hZΔC, hZΔD_eq]
  haveI : Invertible D''.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hD''det).invertible
  haveI : Invertible D'' := Matrix.invertibleOfDetInvertible D''
  haveI : Invertible Z.Dblock.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hZD).invertible
  haveI : Invertible Z.Dblock := Matrix.invertibleOfDetInvertible Z.Dblock
  have h_inv : (Z.Dblock * D'')⁻¹ = D''⁻¹ * Z.Dblock⁻¹ := by
    rw [Matrix.mul_inv_rev]
  have h_det : (Z.Dblock * D'').det = Z.Dblock.det * D''.det := by
    rw [Matrix.det_mul]
  have h_schur : Z.Ablock * A'' - Z.Bblock * D'' * (Z.Dblock * D'')⁻¹ * (Z.Cblock * A'') =
                 (Z.Ablock - Z.Bblock * Z.Dblock⁻¹ * Z.Cblock) * A'' := by
    rw [h_inv]
    have h_cancel : Z.Bblock * D'' * (D''⁻¹ * Z.Dblock⁻¹) * (Z.Cblock * A'') =
                    Z.Bblock * Z.Dblock⁻¹ * Z.Cblock * A'' := by
      have hD''inv : D'' * D''⁻¹ = 1 := Matrix.mul_nonsing_inv D'' (isUnit_of_invertible _)
      calc Z.Bblock * D'' * (D''⁻¹ * Z.Dblock⁻¹) * (Z.Cblock * A'')
          = Z.Bblock * (D'' * (D''⁻¹ * Z.Dblock⁻¹)) * (Z.Cblock * A'') := by
              simp only [Matrix.mul_assoc]
        _ = Z.Bblock * ((D'' * D''⁻¹) * Z.Dblock⁻¹) * (Z.Cblock * A'') := by
              simp only [Matrix.mul_assoc]
        _ = Z.Bblock * (1 * Z.Dblock⁻¹) * (Z.Cblock * A'') := by rw [hD''inv]
        _ = Z.Bblock * Z.Dblock⁻¹ * (Z.Cblock * A'') := by rw [Matrix.one_mul]
        _ = Z.Bblock * (Z.Dblock⁻¹ * (Z.Cblock * A'')) := by simp only [Matrix.mul_assoc]
        _ = Z.Bblock * (Z.Dblock⁻¹ * Z.Cblock * A'') := by simp only [Matrix.mul_assoc]
        _ = Z.Bblock * Z.Dblock⁻¹ * Z.Cblock * A'' := by simp only [Matrix.mul_assoc]
    rw [h_cancel]
    rw [Matrix.sub_mul]
  rw [h_schur]
  have h_det_schur : ((Z.Ablock - Z.Bblock * Z.Dblock⁻¹ * Z.Cblock) * A'').det =
                     (Z.Ablock - Z.Bblock * Z.Dblock⁻¹ * Z.Cblock).det * A''.det := by
    rw [Matrix.det_mul]
  rw [h_det_schur, h_det]
  have h_inv_prod : (Z.Dblock.det * D''.det)⁻¹ = Z.Dblock.det⁻¹ * D''.det⁻¹ := by
    have h1 : Z.Dblock.det * D''.det * (Z.Dblock.det⁻¹ * D''.det⁻¹) = 1 := by
      have hZD_cancel : Z.Dblock.det * Z.Dblock.det⁻¹ = 1 := Λ.mul_inv_cancel _ hZD
      have hD''_cancel : D''.det * D''.det⁻¹ = 1 := Λ.mul_inv_cancel _ hD''det
      calc Z.Dblock.det * D''.det * (Z.Dblock.det⁻¹ * D''.det⁻¹)
          = (Z.Dblock.det * Z.Dblock.det⁻¹) * (D''.det * D''.det⁻¹) := by ring
        _ = 1 * 1 := by rw [hZD_cancel, hD''_cancel]
        _ = 1 := one_mul _
    have h_prod_inv : Λ.IsInvertible (Z.Dblock.det * D''.det) :=
      Λ.mul_invertible _ _ hZD hD''det
    have h_prod_inv_cancel : (Z.Dblock.det * D''.det)⁻¹ * (Z.Dblock.det * D''.det) = 1 :=
      Λ.inv_mul_cancel _ h_prod_inv
    calc (Z.Dblock.det * D''.det)⁻¹
        = (Z.Dblock.det * D''.det)⁻¹ * 1 := (mul_one _).symm
      _ = (Z.Dblock.det * D''.det)⁻¹ *
          (Z.Dblock.det * D''.det * (Z.Dblock.det⁻¹ * D''.det⁻¹)) := by rw [h1]
      _ = ((Z.Dblock.det * D''.det)⁻¹ * (Z.Dblock.det * D''.det)) *
          (Z.Dblock.det⁻¹ * D''.det⁻¹) := by ring
      _ = 1 * (Z.Dblock.det⁻¹ * D''.det⁻¹) := by rw [h_prod_inv_cancel]
      _ = Z.Dblock.det⁻¹ * D''.det⁻¹ := one_mul _
  rw [h_inv_prod]
  have hΔA : (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Ablock = A'' := rfl
  have hΔB : (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Bblock = 0 := rfl
  have hΔC : (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Cblock = 0 := rfl
  have hΔD : (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Dblock = D'' := rfl
  have hΔ_schur2 : (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Ablock -
                  (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Bblock *
                  D''⁻¹ *
                  (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Cblock = A'' := by
    simp only [hΔA, hΔB, hΔC, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
  simp only [hΔ_schur2, hΔD]
  ring

/-- Ber(MN) = Ber(M) * Ber(N) for SuperMatrices. -/
theorem SuperMatrix.ber_mul {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (M N : SuperMatrix Λ n m)
    (hMD : Λ.IsInvertible M.Dblock.det)
    (hND : Λ.IsInvertible N.Dblock.det)
    (hMND : Λ.IsInvertible (M * N).Dblock.det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hBDinvM : ∀ i j, (M.Bblock * M.Dblock⁻¹) i j ∈ Λ.odd)
    (hDinvCM : ∀ i j, (M.Dblock⁻¹ * M.Cblock) i j ∈ Λ.odd)
    (hBDinvN : ∀ i j, (N.Bblock * N.Dblock⁻¹) i j ∈ Λ.odd)
    (hDinvCN : ∀ i j, (N.Dblock⁻¹ * N.Cblock) i j ∈ Λ.odd)
    (hSchurM : ∀ i j, (schurComplementD M hMD) i j ∈ Λ.even)
    (hSchurN : ∀ i j, (schurComplementD N hND) i j ∈ Λ.even) :
    (M * N).ber hMND = M.ber hMD * N.ber hND := by
  let B_M := M.Bblock * M.Dblock⁻¹
  let C_M := M.Dblock⁻¹ * M.Cblock
  let S_M := schurComplementD M hMD
  let U_M := SuperMatrix.upperTriangular B_M h1 h0even h0odd hBDinvM
  let Δ_M := SuperMatrix.diagonal S_M M.Dblock h0odd hSchurM M.Dblock_even
  let L_M := SuperMatrix.lowerTriangular C_M h1 h0even h0odd hDinvCM

  let B_N := N.Bblock * N.Dblock⁻¹
  let C_N := N.Dblock⁻¹ * N.Cblock
  let S_N := schurComplementD N hND
  let U_N := SuperMatrix.upperTriangular B_N h1 h0even h0odd hBDinvN
  let Δ_N := SuperMatrix.diagonal S_N N.Dblock h0odd hSchurN N.Dblock_even
  let L_N := SuperMatrix.lowerTriangular C_N h1 h0even h0odd hDinvCN

  have hM_UDL : M = (U_M * Δ_M) * L_M :=
    SuperMatrix.UDL_factorization M hMD h1 h0even h0odd hBDinvM hDinvCM hSchurM
  have hN_UDL : N = (U_N * Δ_N) * L_N :=
    SuperMatrix.UDL_factorization N hND h1 h0even h0odd hBDinvN hDinvCN hSchurN

  have hU_M_D : Λ.IsInvertible U_M.Dblock.det := by
    show Λ.IsInvertible (SuperMatrix.upperTriangular B_M h1 h0even h0odd hBDinvM).Dblock.det
    simp only [SuperMatrix.upperTriangular, Matrix.det_one]
    unfold GrassmannAlgebra.IsInvertible
    rw [Λ.body_one]
    exact one_ne_zero

  have hL_M_D : Λ.IsInvertible L_M.Dblock.det := by
    show Λ.IsInvertible (SuperMatrix.lowerTriangular C_M h1 h0even h0odd hDinvCM).Dblock.det
    simp only [SuperMatrix.lowerTriangular, Matrix.det_one]
    unfold GrassmannAlgebra.IsInvertible
    rw [Λ.body_one]
    exact one_ne_zero

  have hΔ_M_D : Λ.IsInvertible Δ_M.Dblock.det := by
    show Λ.IsInvertible (SuperMatrix.diagonal S_M M.Dblock h0odd hSchurM M.Dblock_even).Dblock.det
    simp only [SuperMatrix.diagonal]
    exact hMD

  have hU_N_D : Λ.IsInvertible U_N.Dblock.det := by
    show Λ.IsInvertible (SuperMatrix.upperTriangular B_N h1 h0even h0odd hBDinvN).Dblock.det
    simp only [SuperMatrix.upperTriangular, Matrix.det_one]
    unfold GrassmannAlgebra.IsInvertible
    rw [Λ.body_one]
    exact one_ne_zero

  have hL_N_D : Λ.IsInvertible L_N.Dblock.det := by
    show Λ.IsInvertible (SuperMatrix.lowerTriangular C_N h1 h0even h0odd hDinvCN).Dblock.det
    simp only [SuperMatrix.lowerTriangular, Matrix.det_one]
    unfold GrassmannAlgebra.IsInvertible
    rw [Λ.body_one]
    exact one_ne_zero

  have hΔ_N_D : Λ.IsInvertible Δ_N.Dblock.det := by
    show Λ.IsInvertible (SuperMatrix.diagonal S_N N.Dblock h0odd hSchurN N.Dblock_even).Dblock.det
    simp only [SuperMatrix.diagonal]
    exact hND

  have hΔL_M_D : Λ.IsInvertible (Δ_M * L_M).Dblock.det := by
    have : (Δ_M * L_M).Dblock = M.Dblock := by
      show (SuperMatrix.diagonal S_M M.Dblock h0odd hSchurM M.Dblock_even *
            SuperMatrix.lowerTriangular C_M h1 h0even h0odd hDinvCM).Dblock = M.Dblock
      simp only [SuperMatrix.mul_Dblock, SuperMatrix.diagonal, SuperMatrix.lowerTriangular]
      simp only [Matrix.zero_mul, Matrix.mul_one, zero_add]
    rw [this]
    exact hMD

  have hUΔL_M_D : Λ.IsInvertible (U_M * (Δ_M * L_M)).Dblock.det := by
    have : (U_M * (Δ_M * L_M)).Dblock = M.Dblock := by
      show (SuperMatrix.upperTriangular B_M h1 h0even h0odd hBDinvM *
            (SuperMatrix.diagonal S_M M.Dblock h0odd hSchurM M.Dblock_even *
             SuperMatrix.lowerTriangular C_M h1 h0even h0odd hDinvCM)).Dblock = M.Dblock
      simp only [SuperMatrix.mul_Dblock]
      simp only [SuperMatrix.upperTriangular]
      simp only [Matrix.zero_mul, zero_add, Matrix.one_mul]
      simp only [SuperMatrix.diagonal, SuperMatrix.lowerTriangular]
      simp only [Matrix.zero_mul, Matrix.mul_one, zero_add]
    rw [this]
    exact hMD
  have hBerM_eq : M.ber hMD = Δ_M.ber hΔ_M_D := by
    have hUDL := SuperMatrix.ber_UDL B_M S_M M.Dblock C_M h1 h0even h0odd hBDinvM hSchurM
             M.Dblock_even hDinvCM hMD hU_M_D hΔ_M_D hL_M_D hΔL_M_D hUΔL_M_D
    have hM_eq2 : M = U_M * (Δ_M * L_M) := by rw [hM_UDL]; exact mul_assoc U_M Δ_M L_M
    calc M.ber hMD
        = (U_M * (Δ_M * L_M)).ber (by rw [← hM_eq2]; exact hMD) := by congr 1
      _ = (U_M * (Δ_M * L_M)).ber hUΔL_M_D := rfl
      _ = Δ_M.ber hΔ_M_D := hUDL

  have hΔL_N_D : Λ.IsInvertible (Δ_N * L_N).Dblock.det := by
    have : (Δ_N * L_N).Dblock = N.Dblock := by
      show (SuperMatrix.diagonal S_N N.Dblock h0odd hSchurN N.Dblock_even *
            SuperMatrix.lowerTriangular C_N h1 h0even h0odd hDinvCN).Dblock = N.Dblock
      simp only [SuperMatrix.mul_Dblock, SuperMatrix.diagonal, SuperMatrix.lowerTriangular]
      simp only [Matrix.zero_mul, Matrix.mul_one, zero_add]
    rw [this]
    exact hND

  have hUΔL_N_D : Λ.IsInvertible (U_N * (Δ_N * L_N)).Dblock.det := by
    have : (U_N * (Δ_N * L_N)).Dblock = N.Dblock := by
      show (SuperMatrix.upperTriangular B_N h1 h0even h0odd hBDinvN *
            (SuperMatrix.diagonal S_N N.Dblock h0odd hSchurN N.Dblock_even *
             SuperMatrix.lowerTriangular C_N h1 h0even h0odd hDinvCN)).Dblock = N.Dblock
      simp only [SuperMatrix.mul_Dblock]
      simp only [SuperMatrix.upperTriangular]
      simp only [Matrix.zero_mul, zero_add, Matrix.one_mul]
      simp only [SuperMatrix.diagonal, SuperMatrix.lowerTriangular]
      simp only [Matrix.zero_mul, Matrix.mul_one, zero_add]
    rw [this]
    exact hND

  have hBerN_eq : N.ber hND = Δ_N.ber hΔ_N_D := by
    have hUDL := SuperMatrix.ber_UDL B_N S_N N.Dblock C_N h1 h0even h0odd hBDinvN hSchurN
             N.Dblock_even hDinvCN hND hU_N_D hΔ_N_D hL_N_D hΔL_N_D hUΔL_N_D
    have hN_eq2 : N = U_N * (Δ_N * L_N) := by rw [hN_UDL]; exact mul_assoc U_N Δ_N L_N
    calc N.ber hND
        = (U_N * (Δ_N * L_N)).ber (by rw [← hN_eq2]; exact hND) := by congr 1
      _ = (U_N * (Δ_N * L_N)).ber hUΔL_N_D := rfl
      _ = Δ_N.ber hΔ_N_D := hUDL

  have hMN_eq : M * N = U_M * (Δ_M * (L_M * (U_N * (Δ_N * L_N)))) := by
    rw [hM_UDL, hN_UDL]
    simp only [mul_assoc]

  have hUΔL_N : Λ.IsInvertible (U_N * (Δ_N * L_N)).Dblock.det := hUΔL_N_D

  let X₁ := Δ_N * L_N
  let X₂ := U_N * X₁
  let X₃ := L_M * X₂
  let X₄ := Δ_M * X₃
  let X₅ := U_M * X₄

  have hX₁_D : Λ.IsInvertible X₁.Dblock.det := by
    show Λ.IsInvertible (Δ_N * L_N).Dblock.det
    exact hΔL_N_D

  have hX₂_D : Λ.IsInvertible X₂.Dblock.det := by
    show Λ.IsInvertible (U_N * (Δ_N * L_N)).Dblock.det
    exact hUΔL_N_D

  have hX₃_D : Λ.IsInvertible X₃.Dblock.det := by
    have hX₅_D_eq : X₅.Dblock = M.Dblock * X₃.Dblock := by
      show (U_M * (Δ_M * X₃)).Dblock = M.Dblock * X₃.Dblock
      simp only [SuperMatrix.mul_Dblock]
      show (SuperMatrix.upperTriangular B_M h1 h0even h0odd hBDinvM).Cblock * (Δ_M * X₃).Bblock +
           (SuperMatrix.upperTriangular B_M h1 h0even h0odd hBDinvM).Dblock * (Δ_M * X₃).Dblock =
           M.Dblock * X₃.Dblock
      simp only [SuperMatrix.upperTriangular, Matrix.zero_mul, zero_add, Matrix.one_mul]
      simp only [SuperMatrix.mul_Dblock]
      show (SuperMatrix.diagonal S_M M.Dblock h0odd hSchurM M.Dblock_even).Cblock * X₃.Bblock +
           (SuperMatrix.diagonal S_M M.Dblock h0odd hSchurM M.Dblock_even).Dblock * X₃.Dblock =
           M.Dblock * X₃.Dblock
      simp only [SuperMatrix.diagonal, Matrix.zero_mul, zero_add]
    have hX₅_eq : X₅ = M * N := by
      show U_M * (Δ_M * (L_M * (U_N * (Δ_N * L_N)))) = M * N
      rw [hM_UDL, hN_UDL]
      simp only [mul_assoc]
    have hX₅_D_eq2 : X₅.Dblock = (M * N).Dblock := by rw [hX₅_eq]
    have hX₅_det : Λ.IsInvertible X₅.Dblock.det := by rw [hX₅_D_eq2]; exact hMND
    rw [hX₅_D_eq, Matrix.det_mul] at hX₅_det
    unfold GrassmannAlgebra.IsInvertible at hX₅_det hMD ⊢
    rw [Λ.body_mul] at hX₅_det
    exact (mul_ne_zero_iff.mp hX₅_det).2

  have hX₄_D : Λ.IsInvertible X₄.Dblock.det := by
    have hX₄_D_eq : X₄.Dblock = M.Dblock * X₃.Dblock := by
      show (Δ_M * X₃).Dblock = M.Dblock * X₃.Dblock
      simp only [SuperMatrix.mul_Dblock]
      show (SuperMatrix.diagonal S_M M.Dblock h0odd hSchurM M.Dblock_even).Cblock * X₃.Bblock +
           (SuperMatrix.diagonal S_M M.Dblock h0odd hSchurM M.Dblock_even).Dblock * X₃.Dblock =
           M.Dblock * X₃.Dblock
      simp only [SuperMatrix.diagonal, Matrix.zero_mul, zero_add]
    rw [hX₄_D_eq, Matrix.det_mul]
    exact Λ.mul_invertible _ _ hMD hX₃_D

  have hX₅_D : Λ.IsInvertible X₅.Dblock.det := by
    have hX₅_D_eq : X₅.Dblock = X₄.Dblock := by
      show (U_M * X₄).Dblock = X₄.Dblock
      simp only [SuperMatrix.mul_Dblock]
      show (SuperMatrix.upperTriangular B_M h1 h0even h0odd hBDinvM).Cblock * X₄.Bblock +
           (SuperMatrix.upperTriangular B_M h1 h0even h0odd hBDinvM).Dblock * X₄.Dblock =
           X₄.Dblock
      simp only [SuperMatrix.upperTriangular, Matrix.zero_mul, zero_add, Matrix.one_mul]
    rw [hX₅_D_eq]
    exact hX₄_D

  have hX₅_eq_MN : X₅ = M * N := by
    show U_M * (Δ_M * (L_M * (U_N * (Δ_N * L_N)))) = M * N
    rw [hM_UDL, hN_UDL]
    simp only [mul_assoc]

  have hStrip_U_M : X₅.ber hX₅_D = X₄.ber hX₄_D := by
    show (U_M * X₄).ber hX₅_D = X₄.ber hX₄_D
    exact SuperMatrix.ber_mul_upperTriangular_left B_M X₄ h1 h0even h0odd hBDinvM hX₄_D hU_M_D hX₅_D

  have hStrip_Δ_M : X₄.ber hX₄_D = Δ_M.ber hΔ_M_D * X₃.ber hX₃_D := by
    show (Δ_M * X₃).ber hX₄_D = Δ_M.ber hΔ_M_D * X₃.ber hX₃_D
    exact SuperMatrix.ber_mul_diagonal_left S_M M.Dblock X₃ h0odd hSchurM M.Dblock_even
          hMD hX₃_D hΔ_M_D hX₄_D

  have hStrip_L_M : X₃.ber hX₃_D = X₂.ber hX₂_D := by
    show (L_M * X₂).ber hX₃_D = X₂.ber hX₂_D
    have hX₂_eq_N : X₂ = N := by
      show U_N * (Δ_N * L_N) = N
      rw [← mul_assoc, hN_UDL]
    have hX₂_BDinv : ∀ i j, (X₂.Bblock * X₂.Dblock⁻¹) i j ∈ Λ.odd := by
      rw [hX₂_eq_N]
      exact hBDinvN
    have hX₂_DinvC : ∀ i j, (X₂.Dblock⁻¹ * X₂.Cblock) i j ∈ Λ.odd := by
      rw [hX₂_eq_N]
      exact hDinvCN
    have hX₂_Schur : ∀ i j, (schurComplementD X₂ hX₂_D) i j ∈ Λ.even := by
      intro i j
      have hA : X₂.Ablock = N.Ablock := by rw [hX₂_eq_N]
      have hB : X₂.Bblock = N.Bblock := by rw [hX₂_eq_N]
      have hC : X₂.Cblock = N.Cblock := by rw [hX₂_eq_N]
      have hD : X₂.Dblock = N.Dblock := by rw [hX₂_eq_N]
      unfold schurComplementD
      simp only [hA, hB, hC, hD]
      exact hSchurN i j
    exact SuperMatrix.ber_mul_lowerTriangular_left C_M X₂ h1 h0even h0odd hDinvCM
          hX₂_D hL_M_D hX₃_D hX₂_BDinv hX₂_DinvC hX₂_Schur

  have hStrip_U_N : X₂.ber hX₂_D = X₁.ber hX₁_D := by
    show (U_N * X₁).ber hX₂_D = X₁.ber hX₁_D
    exact SuperMatrix.ber_mul_upperTriangular_left B_N X₁ h1 h0even h0odd hBDinvN hX₁_D hU_N_D hX₂_D

  have hX₁_ber : X₁.ber hX₁_D = Δ_N.ber hΔ_N_D := by
    show (Δ_N * L_N).ber hX₁_D = Δ_N.ber hΔ_N_D
    exact SuperMatrix.ber_mul_lowerTriangular_right Δ_N C_N h1 h0even h0odd hDinvCN
          hΔ_N_D hL_N_D hX₁_D

  have hMN_D_eq : Λ.IsInvertible (M * N).Dblock.det := hMND

  calc (M * N).ber hMND
      = X₅.ber hX₅_D := by congr 1
    _ = X₄.ber hX₄_D := hStrip_U_M
    _ = Δ_M.ber hΔ_M_D * X₃.ber hX₃_D := hStrip_Δ_M
    _ = Δ_M.ber hΔ_M_D * X₂.ber hX₂_D := by rw [hStrip_L_M]
    _ = Δ_M.ber hΔ_M_D * X₁.ber hX₁_D := by rw [hStrip_U_N]
    _ = Δ_M.ber hΔ_M_D * Δ_N.ber hΔ_N_D := by rw [hX₁_ber]
    _ = M.ber hMD * N.ber hND := by rw [← hBerM_eq, ← hBerN_eq]

end Supermanifolds.Helpers
