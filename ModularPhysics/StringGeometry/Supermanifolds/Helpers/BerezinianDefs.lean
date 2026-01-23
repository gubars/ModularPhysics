import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import ModularPhysics.StringGeometry.Supermanifolds.Superalgebra
import ModularPhysics.StringGeometry.Supermanifolds.Helpers.SuperMatrix

/-!
# Berezinian Basic Definitions

This file contains the fundamental definitions needed for Berezinian theory.
These are separated out to allow helper lemmas to be defined without circular imports.

## Main definitions

* `one_mem_even_matrix` - The identity matrix has even entries
* `matrixEvenToCarrier_one` - Mapping identity from evenCarrier to carrier preserves it
* `SuperMatrix.D_lifted` - Lift D block to evenCarrier
* `SuperMatrix.A_lifted` - Lift A block to evenCarrier
* `matrixEvenToCarrier` - Map a matrix from evenCarrier back to carrier
* `SuperMatrix.D_inv_carrier` - D⁻¹ computed on evenCarrier then mapped to carrier
* `SuperMatrix.A_inv_carrier` - A⁻¹ computed on evenCarrier then mapped to carrier
* `SuperMatrix.schurD_carrier` - D-based Schur complement: A - B·D⁻¹·C
* `SuperMatrix.schurA_carrier` - A-based Schur complement: D - C·A⁻¹·B
* `SuperMatrix.upperTriangular` - Upper triangular supermatrix [I B'; 0 I]
* `SuperMatrix.lowerTriangular` - Lower triangular supermatrix [I 0; C' I]
* `SuperMatrix.diagonal` - Diagonal supermatrix [A' 0; 0 D']
-/

namespace Supermanifolds.Helpers

open Supermanifolds

variable {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}

/-! ## Identity Matrix Parity -/

/-- The identity matrix has even entries. -/
theorem one_mem_even_matrix {n : ℕ}
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0 : (0 : Λ.carrier) ∈ Λ.even) :
    ∀ i j, (1 : Matrix (Fin n) (Fin n) Λ.carrier) i j ∈ Λ.even := fun i j => by
  simp only [Matrix.one_apply]
  split_ifs <;> [exact h1; exact h0]

/-- Lift D block to evenCarrier for matrix operations -/
noncomputable def SuperMatrix.D_lifted {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) : Matrix (Fin m) (Fin m) Λ.evenCarrier :=
  Λ.liftEvenMatrix M.Dblock M.Dblock_even

/-- Lift A block to evenCarrier for matrix operations -/
noncomputable def SuperMatrix.A_lifted {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) : Matrix (Fin n) (Fin n) Λ.evenCarrier :=
  Λ.liftEvenMatrix M.Ablock M.Ablock_even

/-- Map a matrix from evenCarrier back to carrier -/
noncomputable def matrixEvenToCarrier {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : Matrix (Fin n) (Fin m) Λ.evenCarrier) : Matrix (Fin n) (Fin m) Λ.carrier :=
  M.map Λ.evenToCarrier

/-- D⁻¹ computed on evenCarrier then mapped to carrier -/
noncomputable def SuperMatrix.D_inv_carrier {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) : Matrix (Fin m) (Fin m) Λ.carrier :=
  matrixEvenToCarrier M.D_lifted⁻¹

/-- A⁻¹ computed on evenCarrier then mapped to carrier -/
noncomputable def SuperMatrix.A_inv_carrier {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) : Matrix (Fin n) (Fin n) Λ.carrier :=
  matrixEvenToCarrier M.A_lifted⁻¹

/-- D-based Schur complement computed in carrier: A - B·D⁻¹·C -/
noncomputable def SuperMatrix.schurD_carrier {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) : Matrix (Fin n) (Fin n) Λ.carrier :=
  M.Ablock - M.Bblock * M.D_inv_carrier * M.Cblock

/-- A-based Schur complement computed in carrier: D - C·A⁻¹·B -/
noncomputable def SuperMatrix.schurA_carrier {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) : Matrix (Fin m) (Fin m) Λ.carrier :=
  M.Dblock - M.Cblock * M.A_inv_carrier * M.Bblock

/-- The Schur complement A - BD⁻¹C has even entries (since BD⁻¹ is odd, BD⁻¹C is even) -/
theorem SuperMatrix.schurD_even {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m)
    (hBDinv : ∀ i j, (M.Bblock * M.D_inv_carrier) i j ∈ Λ.odd) :
    ∀ i j, M.schurD_carrier i j ∈ Λ.even := by
  intro i j
  unfold schurD_carrier
  simp only [Matrix.sub_apply]
  apply Λ.even.sub_mem
  · exact M.Ablock_even i j
  · simp only [Matrix.mul_apply]
    apply Λ.even.sum_mem
    intro l _
    -- (B * D_inv_carrier) i l is odd, C l j is odd, so their product is even
    exact Λ.odd_mul_odd _ _ (hBDinv i l) (M.Cblock_odd l j)

/-- The Schur complement D - CA⁻¹B has even entries -/
theorem SuperMatrix.schurA_even {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m)
    (hCAinv : ∀ i j, (M.Cblock * M.A_inv_carrier) i j ∈ Λ.odd) :
    ∀ i j, M.schurA_carrier i j ∈ Λ.even := by
  intro i j
  unfold schurA_carrier
  simp only [Matrix.sub_apply]
  apply Λ.even.sub_mem
  · exact M.Dblock_even i j
  · simp only [Matrix.mul_apply]
    apply Λ.even.sum_mem
    intro l _
    exact Λ.odd_mul_odd _ _ (hCAinv i l) (M.Bblock_odd l j)

/-! ## Special Supermatrices -/

/-- Upper triangular supermatrix U = [I B'; 0 I] -/
noncomputable def SuperMatrix.upperTriangular
    {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd) :
    SuperMatrix Λ n m :=
  ⟨1, B', 0, 1,
   one_mem_even_matrix h1 h0even,
   hB',
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   one_mem_even_matrix h1 h0even⟩

/-- Lower triangular supermatrix L = [I 0; C' I] -/
noncomputable def SuperMatrix.lowerTriangular
    {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd) :
    SuperMatrix Λ n m :=
  ⟨1, 0, C', 1,
   one_mem_even_matrix h1 h0even,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   hC',
   one_mem_even_matrix h1 h0even⟩

/-- Diagonal supermatrix Δ = [A' 0; 0 D'] -/
noncomputable def SuperMatrix.diagonal
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

/-- Mapping identity matrix from evenCarrier to carrier preserves it. -/
theorem matrixEvenToCarrier_one {n : ℕ} :
    (1 : Matrix (Fin n) (Fin n) Λ.evenCarrier).map Λ.evenToCarrier = 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  split_ifs with h
  · exact Λ.evenToCarrier.map_one
  · exact Λ.evenToCarrier.map_zero

end Supermanifolds.Helpers
