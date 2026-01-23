import ModularPhysics.StringGeometry.Supermanifolds.Helpers.BerezinianDefs

/-!
# Berezinian Helper Lemmas

This file contains helper lemmas that are repeatedly used in the Berezinian proofs.
These lemmas abstract common patterns to make the main proofs shorter and cleaner.

## Main results

### Identity matrix and parity
* `one_mem_even_matrix` - The identity matrix has even entries
* `matrixEvenToCarrier_one` - Mapping identity from evenCarrier to carrier preserves it
* `liftEvenMatrix_one_det` - det(liftEvenMatrix 1 _) = 1

### D_inv_carrier lemmas
* `D_inv_carrier_of_identity` - D_inv_carrier = 1 when Dblock = 1
* `D_inv_carrier_entry_even` - Entries of D_inv_carrier are even
* `D_lifted_identity_invertible` - det(D_lifted) is invertible when D = 1

### Block multiplication for special matrices
* `lowerTriangular_mul_Bblock` - (L * N).Bblock = N.Bblock for lower triangular L
* `lowerTriangular_mul_Dblock` - (L * N).Dblock = C' * N.Bblock + N.Dblock
* `upperTriangular_mul_Dblock` - (U * N).Dblock = N.Dblock for upper triangular U
* `diagonal_mul_Ablock` - (Δ * N).Ablock = A' * N.Ablock for diagonal Δ

### Inverse operations
* `Ablock_mul_A_inv_carrier` - A * A_inv_carrier = 1 in carrier
* `inv_unique` - Uniqueness of Λ.inv in evenCarrier
* `inv_mul_eq` - If a*b=1 then inv(a)=b

### D_lifted multiplication
* `D_lifted_diagonal_mul` - (Δ * N).D_lifted = Δ.D_lifted * N.D_lifted for diagonal Δ
-/

namespace Supermanifolds.Helpers

open Supermanifolds

variable {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}

-- Note: one_mem_even_matrix and matrixEvenToCarrier_one are now in BerezinianDefs.lean

/-- det(liftEvenMatrix 1) = 1. -/
theorem liftEvenMatrix_one_det {n : ℕ}
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0 : (0 : Λ.carrier) ∈ Λ.even) :
    (Λ.liftEvenMatrix (1 : Matrix (Fin n) (Fin n) Λ.carrier) (one_mem_even_matrix h1 h0)).det = 1 := by
  rw [Λ.liftEvenMatrix_one (one_mem_even_matrix h1 h0), Matrix.det_one]

/-! ## D_inv_carrier Lemmas -/

/-- matrixEvenToCarrier of an inverted lifted matrix. Helper for D_inv_carrier proofs. -/
theorem matrixEvenToCarrier_inv_liftEvenMatrix_one {n : ℕ}
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0 : (0 : Λ.carrier) ∈ Λ.even) :
    matrixEvenToCarrier (Λ.liftEvenMatrix (1 : Matrix (Fin n) (Fin n) Λ.carrier)
      (one_mem_even_matrix h1 h0))⁻¹ = 1 := by
  rw [Λ.liftEvenMatrix_one (one_mem_even_matrix h1 h0), inv_one]
  exact matrixEvenToCarrier_one

/-- D_inv_carrier equals identity when Dblock equals identity. -/
theorem D_inv_carrier_of_identity {n m : ℕ} (M : SuperMatrix Λ n m)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0 : (0 : Λ.carrier) ∈ Λ.even)
    (hD : M.Dblock = 1) :
    M.D_inv_carrier = 1 := by
  unfold SuperMatrix.D_inv_carrier SuperMatrix.D_lifted
  have h1_even : ∀ i j, (1 : Matrix (Fin m) (Fin m) Λ.carrier) i j ∈ Λ.even :=
    one_mem_even_matrix (n := m) h1 h0
  have hD_lifted : Λ.liftEvenMatrix M.Dblock M.Dblock_even =
      Λ.liftEvenMatrix (1 : Matrix (Fin m) (Fin m) Λ.carrier) h1_even := by
    ext i j
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec, hD]
  rw [hD_lifted, Λ.liftEvenMatrix_one h1_even, inv_one]
  exact matrixEvenToCarrier_one

/-- Entries of D_inv_carrier are always even. -/
theorem D_inv_carrier_entry_even {n m : ℕ} (M : SuperMatrix Λ n m) (i j : Fin m) :
    M.D_inv_carrier i j ∈ Λ.even := by
  unfold SuperMatrix.D_inv_carrier
  rw [Λ.even_mem_iff]
  use (M.D_lifted⁻¹ i j)
  rfl

/-- det(D_lifted) is invertible when Dblock = 1. -/
theorem D_lifted_identity_invertible {n m : ℕ} (M : SuperMatrix Λ n m)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0 : (0 : Λ.carrier) ∈ Λ.even)
    (hD : M.Dblock = 1) :
    Λ.IsInvertible M.D_lifted.det := by
  unfold SuperMatrix.D_lifted
  have h1_even : ∀ i j, (1 : Matrix (Fin m) (Fin m) Λ.carrier) i j ∈ Λ.even :=
    one_mem_even_matrix (n := m) h1 h0
  have hD_lifted : Λ.liftEvenMatrix M.Dblock M.Dblock_even =
      Λ.liftEvenMatrix (1 : Matrix (Fin m) (Fin m) Λ.carrier) h1_even := by
    ext i j
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec, hD]
  rw [hD_lifted, liftEvenMatrix_one_det (n := m) h1 h0]
  exact Λ.one_invertible

/-! ## Block Multiplication for Triangular Matrices -/

/-- (L * N).Bblock = N.Bblock when L is lower triangular [I 0; C' I]. -/
theorem lowerTriangular_mul_Bblock {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier) (N : SuperMatrix Λ n m)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd) :
    (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).Bblock = N.Bblock := by
  show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock * N.Bblock +
       (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock * N.Dblock = N.Bblock
  simp only [SuperMatrix.lowerTriangular, Matrix.one_mul, Matrix.zero_mul, add_zero]

/-- (L * N).Ablock = N.Ablock when L is lower triangular [I 0; C' I]. -/
theorem lowerTriangular_mul_Ablock {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier) (N : SuperMatrix Λ n m)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd) :
    (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).Ablock = N.Ablock := by
  show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock * N.Ablock +
       (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock * N.Cblock = N.Ablock
  simp only [SuperMatrix.lowerTriangular, Matrix.one_mul, Matrix.zero_mul, add_zero]

/-- (L * N).Cblock = C' * N.Ablock + N.Cblock when L is lower triangular. -/
theorem lowerTriangular_mul_Cblock {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier) (N : SuperMatrix Λ n m)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd) :
    (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).Cblock = C' * N.Ablock + N.Cblock := by
  show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock * N.Ablock +
       (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock * N.Cblock =
       C' * N.Ablock + N.Cblock
  simp only [SuperMatrix.lowerTriangular, Matrix.one_mul]

/-- (L * N).Dblock = C' * N.Bblock + N.Dblock when L is lower triangular. -/
theorem lowerTriangular_mul_Dblock {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier) (N : SuperMatrix Λ n m)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd) :
    (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).Dblock =
    C' * N.Bblock + N.Dblock := by
  show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock * N.Bblock +
       (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock * N.Dblock =
       C' * N.Bblock + N.Dblock
  simp only [SuperMatrix.lowerTriangular, Matrix.one_mul]

/-- (U * N).Dblock = N.Dblock when U is upper triangular [I B'; 0 I]. -/
theorem upperTriangular_mul_Dblock {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier) (N : SuperMatrix Λ n m)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd) :
    (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).Dblock = N.Dblock := by
  show (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Cblock * N.Bblock +
       (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock * N.Dblock = N.Dblock
  simp only [SuperMatrix.upperTriangular, Matrix.zero_mul, Matrix.one_mul, zero_add]

/-- (U * N).Cblock = N.Cblock when U is upper triangular [I B'; 0 I]. -/
theorem upperTriangular_mul_Cblock {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier) (N : SuperMatrix Λ n m)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd) :
    (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).Cblock = N.Cblock := by
  show (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Cblock * N.Ablock +
       (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock * N.Cblock = N.Cblock
  simp only [SuperMatrix.upperTriangular, Matrix.zero_mul, Matrix.one_mul, zero_add]

/-- (U * N).Ablock = N.Ablock + B' * N.Cblock when U is upper triangular [I B'; 0 I]. -/
theorem upperTriangular_mul_Ablock {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier) (N : SuperMatrix Λ n m)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd) :
    (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).Ablock = N.Ablock + B' * N.Cblock := by
  show (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock * N.Ablock +
       (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Bblock * N.Cblock = N.Ablock + B' * N.Cblock
  simp only [SuperMatrix.upperTriangular, Matrix.one_mul]

/-- (U * N).Bblock = N.Bblock + B' * N.Dblock when U is upper triangular [I B'; 0 I]. -/
theorem upperTriangular_mul_Bblock {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier) (N : SuperMatrix Λ n m)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd) :
    (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).Bblock = N.Bblock + B' * N.Dblock := by
  show (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock * N.Bblock +
       (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Bblock * N.Dblock = N.Bblock + B' * N.Dblock
  simp only [SuperMatrix.upperTriangular, Matrix.one_mul]

/-- (Δ * N).Ablock = A' * N.Ablock when Δ is diagonal [A' 0; 0 D']. -/
theorem diagonal_mul_Ablock {n m : ℕ}
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (D' : Matrix (Fin m) (Fin m) Λ.carrier)
    (N : SuperMatrix Λ n m)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hA' : ∀ i j, A' i j ∈ Λ.even) (hD' : ∀ i j, D' i j ∈ Λ.even) :
    (SuperMatrix.diagonal A' D' h0odd hA' hD' * N).Ablock = A' * N.Ablock := by
  show (SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock * N.Ablock +
       (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock * N.Cblock = A' * N.Ablock
  simp only [SuperMatrix.diagonal, Matrix.zero_mul, add_zero]

/-- (Δ * N).Bblock = A' * N.Bblock when Δ is diagonal [A' 0; 0 D']. -/
theorem diagonal_mul_Bblock {n m : ℕ}
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (D' : Matrix (Fin m) (Fin m) Λ.carrier)
    (N : SuperMatrix Λ n m)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hA' : ∀ i j, A' i j ∈ Λ.even) (hD' : ∀ i j, D' i j ∈ Λ.even) :
    (SuperMatrix.diagonal A' D' h0odd hA' hD' * N).Bblock = A' * N.Bblock := by
  show (SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock * N.Bblock +
       (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock * N.Dblock = A' * N.Bblock
  simp only [SuperMatrix.diagonal, Matrix.zero_mul, add_zero]

/-- (Δ * N).Cblock = D' * N.Cblock when Δ is diagonal [A' 0; 0 D']. -/
theorem diagonal_mul_Cblock {n m : ℕ}
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (D' : Matrix (Fin m) (Fin m) Λ.carrier)
    (N : SuperMatrix Λ n m)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hA' : ∀ i j, A' i j ∈ Λ.even) (hD' : ∀ i j, D' i j ∈ Λ.even) :
    (SuperMatrix.diagonal A' D' h0odd hA' hD' * N).Cblock = D' * N.Cblock := by
  show (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock * N.Ablock +
       (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock * N.Cblock = D' * N.Cblock
  simp only [SuperMatrix.diagonal, Matrix.zero_mul, zero_add]

/-- (Δ * N).Dblock = D' * N.Dblock when Δ is diagonal [A' 0; 0 D']. -/
theorem diagonal_mul_Dblock {n m : ℕ}
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (D' : Matrix (Fin m) (Fin m) Λ.carrier)
    (N : SuperMatrix Λ n m)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hA' : ∀ i j, A' i j ∈ Λ.even) (hD' : ∀ i j, D' i j ∈ Λ.even) :
    (SuperMatrix.diagonal A' D' h0odd hA' hD' * N).Dblock = D' * N.Dblock := by
  show (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock * N.Bblock +
       (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock * N.Dblock = D' * N.Dblock
  simp only [SuperMatrix.diagonal, Matrix.zero_mul, zero_add]

/-! ## Inverse Operations -/

/-- Uniqueness of inverse in evenCarrier: if a*x=1 and a*y=1 then x=y. -/
theorem inv_unique (a x y : Λ.evenCarrier) (hax : a * x = 1) (hay : a * y = 1) : x = y := by
  calc x = 1 * x := (one_mul x).symm
    _ = (y * a) * x := by rw [← hay, mul_comm a y]
    _ = y * (a * x) := by ring
    _ = y * 1 := by rw [hax]
    _ = y := mul_one y

/-- If a is invertible and a*b=1, then Λ.inv a h = b. -/
theorem inv_eq_of_mul_eq_one (a b : Λ.evenCarrier) (h : Λ.IsInvertible a) (hab : a * b = 1) :
    Λ.inv a h = b := by
  have hinv : a * Λ.inv a h = 1 := Λ.mul_inv a h
  exact inv_unique a (Λ.inv a h) b hinv hab

/-- Product of inverses: inv(a*b) = inv(b) * inv(a) for invertible a, b. -/
theorem inv_mul_inv (a b : Λ.evenCarrier) (ha : Λ.IsInvertible a) (hb : Λ.IsInvertible b)
    (hab : Λ.IsInvertible (a * b)) :
    Λ.inv (a * b) hab = Λ.inv b hb * Λ.inv a ha := by
  have h : (a * b) * (Λ.inv b hb * Λ.inv a ha) = 1 := by
    calc (a * b) * (Λ.inv b hb * Λ.inv a ha)
        = a * (b * Λ.inv b hb) * Λ.inv a ha := by ring
      _ = a * 1 * Λ.inv a ha := by rw [Λ.mul_inv b hb]
      _ = a * Λ.inv a ha := by ring
      _ = 1 := Λ.mul_inv a ha
  exact inv_eq_of_mul_eq_one (a * b) (Λ.inv b hb * Λ.inv a ha) hab h

/-- Product of inverses (commutative version): inv(a*b) = inv(a) * inv(b) for invertible a, b. -/
theorem inv_mul_inv_comm (a b : Λ.evenCarrier) (ha : Λ.IsInvertible a) (hb : Λ.IsInvertible b)
    (hab : Λ.IsInvertible (a * b)) :
    Λ.inv (a * b) hab = Λ.inv a ha * Λ.inv b hb := by
  rw [inv_mul_inv a b ha hb hab, mul_comm]

/-! ## A * A_inv_carrier = 1 -/

/-- A * A_inv_carrier = 1 in carrier (when A_lifted is invertible). -/
theorem Ablock_mul_A_inv_carrier {n m : ℕ} (M : SuperMatrix Λ n m)
    (hA : Λ.IsInvertible M.A_lifted.det) :
    M.Ablock * M.A_inv_carrier = 1 := by
  haveI : Invertible M.A_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hA).invertible
  haveI : Invertible M.A_lifted := Matrix.invertibleOfDetInvertible M.A_lifted
  have hA_inv_def : M.A_inv_carrier = matrixEvenToCarrier M.A_lifted⁻¹ := rfl
  have hA_lifted_carrier : matrixEvenToCarrier M.A_lifted = M.Ablock := by
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, SuperMatrix.A_lifted]
    exact Λ.liftEvenMatrix_spec M.Ablock M.Ablock_even i j
  have hAAinv_lifted : M.A_lifted * M.A_lifted⁻¹ = 1 :=
    Matrix.mul_nonsing_inv M.A_lifted (isUnit_of_invertible _)
  rw [hA_inv_def, ← hA_lifted_carrier]
  have h_mul : matrixEvenToCarrier M.A_lifted * matrixEvenToCarrier M.A_lifted⁻¹ =
      matrixEvenToCarrier (M.A_lifted * M.A_lifted⁻¹) := by
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Λ.evenToCarrier.map_mul]
  rw [h_mul, hAAinv_lifted]
  exact matrixEvenToCarrier_one

/-- A_inv_carrier * A = 1 in carrier (when A_lifted is invertible). -/
theorem A_inv_carrier_mul_Ablock {n m : ℕ} (M : SuperMatrix Λ n m)
    (hA : Λ.IsInvertible M.A_lifted.det) :
    M.A_inv_carrier * M.Ablock = 1 := by
  haveI : Invertible M.A_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hA).invertible
  haveI : Invertible M.A_lifted := Matrix.invertibleOfDetInvertible M.A_lifted
  have hA_inv_def : M.A_inv_carrier = matrixEvenToCarrier M.A_lifted⁻¹ := rfl
  have hA_lifted_carrier : matrixEvenToCarrier M.A_lifted = M.Ablock := by
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, SuperMatrix.A_lifted]
    exact Λ.liftEvenMatrix_spec M.Ablock M.Ablock_even i j
  have hAinvA_lifted : M.A_lifted⁻¹ * M.A_lifted = 1 :=
    Matrix.nonsing_inv_mul M.A_lifted (isUnit_of_invertible _)
  rw [hA_inv_def, ← hA_lifted_carrier]
  have h_mul : matrixEvenToCarrier M.A_lifted⁻¹ * matrixEvenToCarrier M.A_lifted =
      matrixEvenToCarrier (M.A_lifted⁻¹ * M.A_lifted) := by
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Λ.evenToCarrier.map_mul]
  rw [h_mul, hAinvA_lifted]
  exact matrixEvenToCarrier_one

/-- D * D_inv_carrier = 1 in carrier (when D_lifted is invertible). -/
theorem Dblock_mul_D_inv_carrier {n m : ℕ} (M : SuperMatrix Λ n m)
    (hD : Λ.IsInvertible M.D_lifted.det) :
    M.Dblock * M.D_inv_carrier = 1 := by
  haveI : Invertible M.D_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hD).invertible
  haveI : Invertible M.D_lifted := Matrix.invertibleOfDetInvertible M.D_lifted
  have hD_inv_def : M.D_inv_carrier = matrixEvenToCarrier M.D_lifted⁻¹ := rfl
  have hD_lifted_carrier : matrixEvenToCarrier M.D_lifted = M.Dblock := by
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, SuperMatrix.D_lifted]
    exact Λ.liftEvenMatrix_spec M.Dblock M.Dblock_even i j
  have hDDinv_lifted : M.D_lifted * M.D_lifted⁻¹ = 1 :=
    Matrix.mul_nonsing_inv M.D_lifted (isUnit_of_invertible _)
  rw [hD_inv_def, ← hD_lifted_carrier]
  have h_mul : matrixEvenToCarrier M.D_lifted * matrixEvenToCarrier M.D_lifted⁻¹ =
      matrixEvenToCarrier (M.D_lifted * M.D_lifted⁻¹) := by
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Λ.evenToCarrier.map_mul]
  rw [h_mul, hDDinv_lifted]
  exact matrixEvenToCarrier_one

/-- D_inv_carrier * D = 1 in carrier (when D_lifted is invertible). -/
theorem D_inv_carrier_mul_Dblock {n m : ℕ} (M : SuperMatrix Λ n m)
    (hD : Λ.IsInvertible M.D_lifted.det) :
    M.D_inv_carrier * M.Dblock = 1 := by
  haveI : Invertible M.D_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hD).invertible
  haveI : Invertible M.D_lifted := Matrix.invertibleOfDetInvertible M.D_lifted
  have hD_inv_def : M.D_inv_carrier = matrixEvenToCarrier M.D_lifted⁻¹ := rfl
  have hD_lifted_carrier : matrixEvenToCarrier M.D_lifted = M.Dblock := by
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, SuperMatrix.D_lifted]
    exact Λ.liftEvenMatrix_spec M.Dblock M.Dblock_even i j
  have hDinvD_lifted : M.D_lifted⁻¹ * M.D_lifted = 1 :=
    Matrix.nonsing_inv_mul M.D_lifted (isUnit_of_invertible _)
  rw [hD_inv_def, ← hD_lifted_carrier]
  have h_mul : matrixEvenToCarrier M.D_lifted⁻¹ * matrixEvenToCarrier M.D_lifted =
      matrixEvenToCarrier (M.D_lifted⁻¹ * M.D_lifted) := by
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Λ.evenToCarrier.map_mul]
  rw [h_mul, hDinvD_lifted]
  exact matrixEvenToCarrier_one

/-! ## D_lifted Multiplication -/

/-- (Δ * N).D_lifted = Δ.D_lifted * N.D_lifted when Δ is diagonal. -/
theorem D_lifted_diagonal_mul {n m : ℕ}
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (D' : Matrix (Fin m) (Fin m) Λ.carrier)
    (N : SuperMatrix Λ n m)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hA' : ∀ i j, A' i j ∈ Λ.even) (hD' : ∀ i j, D' i j ∈ Λ.even) :
    (SuperMatrix.diagonal A' D' h0odd hA' hD' * N).D_lifted =
    (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted * N.D_lifted := by
  ext i j
  simp only [SuperMatrix.D_lifted, Matrix.mul_apply]
  apply Λ.evenToCarrier_injective
  rw [Λ.liftEvenMatrix_spec _ (SuperMatrix.diagonal A' D' h0odd hA' hD' * N).Dblock_even i j]
  rw [diagonal_mul_Dblock A' D' N h0odd hA' hD']
  simp only [Matrix.mul_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hD'_eq : D' i k = Λ.evenToCarrier (Λ.liftEvenMatrix D' hD' i k) := by
    rw [Λ.liftEvenMatrix_spec]
  have hND_eq : N.Dblock k j = Λ.evenToCarrier (Λ.liftEvenMatrix N.Dblock N.Dblock_even k j) := by
    rw [Λ.liftEvenMatrix_spec]
  rw [hD'_eq, hND_eq, ← Λ.evenToCarrier.map_mul]
  congr 1

/-- det((Δ * N).D_lifted) = det(Δ.D_lifted) * det(N.D_lifted) when Δ is diagonal. -/
theorem D_lifted_det_diagonal_mul {n m : ℕ}
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (D' : Matrix (Fin m) (Fin m) Λ.carrier)
    (N : SuperMatrix Λ n m)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hA' : ∀ i j, A' i j ∈ Λ.even) (hD' : ∀ i j, D' i j ∈ Λ.even) :
    (SuperMatrix.diagonal A' D' h0odd hA' hD' * N).D_lifted.det =
    (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det * N.D_lifted.det := by
  rw [D_lifted_diagonal_mul A' D' N h0odd hA' hD', Matrix.det_mul]

/-! ## A_lifted Lemmas (analogous to D_lifted) -/

/-- A_inv_carrier equals identity when Ablock equals identity. -/
theorem A_inv_carrier_of_identity {n m : ℕ} (M : SuperMatrix Λ n m)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0 : (0 : Λ.carrier) ∈ Λ.even)
    (hA : M.Ablock = 1) :
    M.A_inv_carrier = 1 := by
  unfold SuperMatrix.A_inv_carrier SuperMatrix.A_lifted
  have h1_even : ∀ i j, (1 : Matrix (Fin n) (Fin n) Λ.carrier) i j ∈ Λ.even :=
    one_mem_even_matrix (n := n) h1 h0
  have hA_lifted : Λ.liftEvenMatrix M.Ablock M.Ablock_even =
      Λ.liftEvenMatrix (1 : Matrix (Fin n) (Fin n) Λ.carrier) h1_even := by
    ext i j
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec, hA]
  rw [hA_lifted, Λ.liftEvenMatrix_one h1_even, inv_one]
  exact matrixEvenToCarrier_one

/-- det(A_lifted) is invertible when Ablock = 1. -/
theorem A_lifted_identity_invertible {n m : ℕ} (M : SuperMatrix Λ n m)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0 : (0 : Λ.carrier) ∈ Λ.even)
    (hA : M.Ablock = 1) :
    Λ.IsInvertible M.A_lifted.det := by
  unfold SuperMatrix.A_lifted
  have h1_even : ∀ i j, (1 : Matrix (Fin n) (Fin n) Λ.carrier) i j ∈ Λ.even :=
    one_mem_even_matrix (n := n) h1 h0
  have hA_lifted : Λ.liftEvenMatrix M.Ablock M.Ablock_even =
      Λ.liftEvenMatrix (1 : Matrix (Fin n) (Fin n) Λ.carrier) h1_even := by
    ext i j
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec, hA]
  rw [hA_lifted, liftEvenMatrix_one_det (n := n) h1 h0]
  exact Λ.one_invertible

/-! ## Triangular Matrix Helpers -/

/-- det(L.D_lifted) is invertible for lower triangular L (since D = 1). -/
theorem lowerTriangular_D_lifted_invertible {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd) :
    Λ.IsInvertible (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det := by
  have hD : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock = 1 := rfl
  exact D_lifted_identity_invertible _ h1 h0even hD

/-- det(L.A_lifted) is invertible for lower triangular L (since A = 1). -/
theorem lowerTriangular_A_lifted_invertible {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd) :
    Λ.IsInvertible (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').A_lifted.det := by
  have hA : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock = 1 := rfl
  exact A_lifted_identity_invertible _ h1 h0even hA

/-- det(U.D_lifted) is invertible for upper triangular U (since D = 1). -/
theorem upperTriangular_D_lifted_invertible {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd) :
    Λ.IsInvertible (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').D_lifted.det := by
  have hD : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock = 1 := rfl
  exact D_lifted_identity_invertible _ h1 h0even hD

/-- det(U.A_lifted) is invertible for upper triangular U (since A = 1). -/
theorem upperTriangular_A_lifted_invertible {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd) :
    Λ.IsInvertible (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').A_lifted.det := by
  have hA : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock = 1 := rfl
  exact A_lifted_identity_invertible _ h1 h0even hA

/-- L.D_inv_carrier = 1 for lower triangular L. -/
theorem lowerTriangular_D_inv_carrier_one {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd) :
    (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_inv_carrier = 1 := by
  have hD : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock = 1 := rfl
  exact D_inv_carrier_of_identity _ h1 h0even hD

/-- L.A_inv_carrier = 1 for lower triangular L. -/
theorem lowerTriangular_A_inv_carrier_one {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd) :
    (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').A_inv_carrier = 1 := by
  have hA : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock = 1 := rfl
  exact A_inv_carrier_of_identity _ h1 h0even hA

/-- U.D_inv_carrier = 1 for upper triangular U. -/
theorem upperTriangular_D_inv_carrier_one {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd) :
    (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').D_inv_carrier = 1 := by
  have hD : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock = 1 := rfl
  exact D_inv_carrier_of_identity _ h1 h0even hD

/-- U.A_inv_carrier = 1 for upper triangular U. -/
theorem upperTriangular_A_inv_carrier_one {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd) :
    (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').A_inv_carrier = 1 := by
  have hA : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock = 1 := rfl
  exact A_inv_carrier_of_identity _ h1 h0even hA

/-! ## Parity Conditions for Triangular/Diagonal Matrices -/

/-- (L.Bblock * L.D_inv_carrier) i j ∈ odd for lower triangular L (since B = 0). -/
theorem lowerTriangular_BDinv_odd {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd) :
    ∀ i j, ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock *
            (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_inv_carrier) i j ∈ Λ.odd := by
  intro i j
  simp only [SuperMatrix.lowerTriangular, Matrix.zero_mul]
  exact h0odd

/-- (L.A_inv_carrier * L.Bblock) i j ∈ odd for lower triangular L (since B = 0). -/
theorem lowerTriangular_AinvB_odd {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd) :
    ∀ i j, ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').A_inv_carrier *
            (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock) i j ∈ Λ.odd := by
  intro i j
  simp only [SuperMatrix.lowerTriangular, Matrix.mul_zero]
  exact h0odd

/-- (L.Cblock * L.A_inv_carrier) i j ∈ odd for lower triangular L (since C = C' and A_inv = 1). -/
theorem lowerTriangular_CAinv_odd {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd) :
    ∀ i j, ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock *
            (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').A_inv_carrier) i j ∈ Λ.odd := by
  intro i j
  rw [lowerTriangular_A_inv_carrier_one C' h1 h0even h0odd hC', Matrix.mul_one]
  exact hC' i j

/-- (L.D_inv_carrier * L.Cblock) i j ∈ odd for lower triangular L (since D_inv = 1). -/
theorem lowerTriangular_DinvC_odd {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd) :
    ∀ i j, ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_inv_carrier *
            (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock) i j ∈ Λ.odd := by
  intro i j
  rw [lowerTriangular_D_inv_carrier_one C' h1 h0even h0odd hC', Matrix.one_mul]
  exact hC' i j

/-- (U.Bblock * U.D_inv_carrier) i j ∈ odd for upper triangular U (since D_inv = 1). -/
theorem upperTriangular_BDinv_odd {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd) :
    ∀ i j, ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Bblock *
            (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').D_inv_carrier) i j ∈ Λ.odd := by
  intro i j
  rw [upperTriangular_D_inv_carrier_one B' h1 h0even h0odd hB', Matrix.mul_one]
  exact hB' i j

/-- (U.A_inv_carrier * U.Bblock) i j ∈ odd for upper triangular U (since A_inv = 1). -/
theorem upperTriangular_AinvB_odd {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd) :
    ∀ i j, ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB').A_inv_carrier *
            (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Bblock) i j ∈ Λ.odd := by
  intro i j
  rw [upperTriangular_A_inv_carrier_one B' h1 h0even h0odd hB', Matrix.one_mul]
  exact hB' i j

/-- (U.Cblock * U.A_inv_carrier) i j ∈ odd for upper triangular U (since C = 0). -/
theorem upperTriangular_CAinv_odd {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd) :
    ∀ i j, ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Cblock *
            (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').A_inv_carrier) i j ∈ Λ.odd := by
  intro i j
  simp only [SuperMatrix.upperTriangular, Matrix.zero_mul]
  exact h0odd

/-- (U.D_inv_carrier * U.Cblock) i j ∈ odd for upper triangular U (since C = 0). -/
theorem upperTriangular_DinvC_odd {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd) :
    ∀ i j, ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB').D_inv_carrier *
            (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Cblock) i j ∈ Λ.odd := by
  intro i j
  simp only [SuperMatrix.upperTriangular, Matrix.mul_zero]
  exact h0odd

/-- (Δ.Bblock * Δ.D_inv_carrier) i j ∈ odd for diagonal Δ (since B = 0). -/
theorem diagonal_BDinv_odd {n m : ℕ}
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (D' : Matrix (Fin m) (Fin m) Λ.carrier)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hA' : ∀ i j, A' i j ∈ Λ.even) (hD' : ∀ i j, D' i j ∈ Λ.even) :
    ∀ i j, ((SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock *
            (SuperMatrix.diagonal A' D' h0odd hA' hD').D_inv_carrier) i j ∈ Λ.odd := by
  intro i j
  simp only [SuperMatrix.diagonal, Matrix.zero_mul]
  exact h0odd

/-- (Δ.Cblock * Δ.A_inv_carrier) i j ∈ odd for diagonal Δ (since C = 0). -/
theorem diagonal_CAinv_odd {n m : ℕ}
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (D' : Matrix (Fin m) (Fin m) Λ.carrier)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hA' : ∀ i j, A' i j ∈ Λ.even) (hD' : ∀ i j, D' i j ∈ Λ.even) :
    ∀ i j, ((SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock *
            (SuperMatrix.diagonal A' D' h0odd hA' hD').A_inv_carrier) i j ∈ Λ.odd := by
  intro i j
  simp only [SuperMatrix.diagonal, Matrix.zero_mul]
  exact h0odd

/-- (Δ.A_inv_carrier * Δ.Bblock) i j ∈ odd for diagonal Δ (since B = 0). -/
theorem diagonal_AinvB_odd {n m : ℕ}
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (D' : Matrix (Fin m) (Fin m) Λ.carrier)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hA' : ∀ i j, A' i j ∈ Λ.even) (hD' : ∀ i j, D' i j ∈ Λ.even) :
    ∀ i j, ((SuperMatrix.diagonal A' D' h0odd hA' hD').A_inv_carrier *
            (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock) i j ∈ Λ.odd := by
  intro i j
  simp only [SuperMatrix.diagonal, Matrix.mul_zero]
  exact h0odd

/-- (Δ.D_inv_carrier * Δ.Cblock) i j ∈ odd for diagonal Δ (since C = 0). -/
theorem diagonal_DinvC_odd {n m : ℕ}
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (D' : Matrix (Fin m) (Fin m) Λ.carrier)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hA' : ∀ i j, A' i j ∈ Λ.even) (hD' : ∀ i j, D' i j ∈ Λ.even) :
    ∀ i j, ((SuperMatrix.diagonal A' D' h0odd hA' hD').D_inv_carrier *
            (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock) i j ∈ Λ.odd := by
  intro i j
  simp only [SuperMatrix.diagonal, Matrix.mul_zero]
  exact h0odd

/-! ## Lifted Matrix Equality Helpers

These helpers reduce repeated patterns where M.A_lifted (or D_lifted) equals some
liftEvenMatrix, and consequently A_inv_carrier (or D_inv_carrier) equals something.
-/

/-- If M.Ablock = A' then M.A_lifted = Λ.liftEvenMatrix A' hA'. -/
theorem A_lifted_eq_of_Ablock_eq {n m : ℕ} (M : SuperMatrix Λ n m)
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (hA' : ∀ i j, A' i j ∈ Λ.even)
    (hEq : M.Ablock = A') :
    M.A_lifted = Λ.liftEvenMatrix A' hA' := by
  ext i j
  simp only [SuperMatrix.A_lifted]
  apply Λ.evenToCarrier_injective
  rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec, hEq]

/-- If M.Ablock = N.Ablock then M.A_lifted = N.A_lifted. -/
theorem A_lifted_eq_of_Ablock_eq' {n m : ℕ} (M N : SuperMatrix Λ n m)
    (hEq : M.Ablock = N.Ablock) :
    M.A_lifted = N.A_lifted := by
  ext i j
  simp only [SuperMatrix.A_lifted]
  apply Λ.evenToCarrier_injective
  rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec, hEq]

/-- If M.Dblock = D' then M.D_lifted = Λ.liftEvenMatrix D' hD'. -/
theorem D_lifted_eq_of_Dblock_eq {n m : ℕ} (M : SuperMatrix Λ n m)
    (D' : Matrix (Fin m) (Fin m) Λ.carrier) (hD' : ∀ i j, D' i j ∈ Λ.even)
    (hEq : M.Dblock = D') :
    M.D_lifted = Λ.liftEvenMatrix D' hD' := by
  ext i j
  simp only [SuperMatrix.D_lifted]
  apply Λ.evenToCarrier_injective
  rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec, hEq]

/-- If M.Dblock = N.Dblock then M.D_lifted = N.D_lifted. -/
theorem D_lifted_eq_of_Dblock_eq' {n m : ℕ} (M N : SuperMatrix Λ n m)
    (hEq : M.Dblock = N.Dblock) :
    M.D_lifted = N.D_lifted := by
  ext i j
  simp only [SuperMatrix.D_lifted]
  apply Λ.evenToCarrier_injective
  rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec, hEq]

/-- If M.A_lifted = N.A_lifted then M.A_inv_carrier = N.A_inv_carrier. -/
theorem A_inv_carrier_eq_of_A_lifted_eq {n m : ℕ} (M N : SuperMatrix Λ n m)
    (hEq : M.A_lifted = N.A_lifted) :
    M.A_inv_carrier = N.A_inv_carrier := by
  simp only [SuperMatrix.A_inv_carrier, hEq]

/-- If M.D_lifted = N.D_lifted then M.D_inv_carrier = N.D_inv_carrier. -/
theorem D_inv_carrier_eq_of_D_lifted_eq {n m : ℕ} (M N : SuperMatrix Λ n m)
    (hEq : M.D_lifted = N.D_lifted) :
    M.D_inv_carrier = N.D_inv_carrier := by
  simp only [SuperMatrix.D_inv_carrier, hEq]

/-- If M.Dblock = N.Dblock then M.D_inv_carrier = N.D_inv_carrier (combines lifting and carrier). -/
theorem D_inv_carrier_eq_of_Dblock_eq {n m : ℕ} (M N : SuperMatrix Λ n m)
    (hEq : M.Dblock = N.Dblock) :
    M.D_inv_carrier = N.D_inv_carrier :=
  D_inv_carrier_eq_of_D_lifted_eq M N (D_lifted_eq_of_Dblock_eq' M N hEq)

/-- If M.Ablock = N.Ablock then M.A_inv_carrier = N.A_inv_carrier (combines lifting and carrier). -/
theorem A_inv_carrier_eq_of_Ablock_eq {n m : ℕ} (M N : SuperMatrix Λ n m)
    (hEq : M.Ablock = N.Ablock) :
    M.A_inv_carrier = N.A_inv_carrier :=
  A_inv_carrier_eq_of_A_lifted_eq M N (A_lifted_eq_of_Ablock_eq' M N hEq)

/-- If det(M) = det(N) (as evenCarrier elements) then Λ.inv det(M) hM = Λ.inv det(N) hN.
    This is a key helper that eliminates many calc chains involving inverse uniqueness. -/
theorem inv_eq_of_val_eq {M N : Λ.evenCarrier}
    (val_eq : M = N) (hM : Λ.IsInvertible M) (hN : Λ.IsInvertible N) :
    Λ.inv M hM = Λ.inv N hN := by
  subst val_eq
  have h : M * Λ.inv M hM = 1 := Λ.mul_inv M hM
  exact inv_eq_of_mul_eq_one M (Λ.inv M hM) hN h

/-- matrixEvenToCarrier M.D_lifted = M.Dblock -/
theorem matrixEvenToCarrier_D_lifted {n m : ℕ} (M : SuperMatrix Λ n m) :
    matrixEvenToCarrier M.D_lifted = M.Dblock := by
  ext i j
  simp only [matrixEvenToCarrier, Matrix.map_apply, SuperMatrix.D_lifted]
  exact Λ.liftEvenMatrix_spec M.Dblock M.Dblock_even i j

/-- matrixEvenToCarrier M.A_lifted = M.Ablock -/
theorem matrixEvenToCarrier_A_lifted {n m : ℕ} (M : SuperMatrix Λ n m) :
    matrixEvenToCarrier M.A_lifted = M.Ablock := by
  ext i j
  simp only [matrixEvenToCarrier, Matrix.map_apply, SuperMatrix.A_lifted]
  exact Λ.liftEvenMatrix_spec M.Ablock M.Ablock_even i j

/-- matrixEvenToCarrier (liftEvenMatrix A hA) = A -/
theorem matrixEvenToCarrier_liftEvenMatrix {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) Λ.carrier) (hA : ∀ i j, A i j ∈ Λ.even) :
    matrixEvenToCarrier (Λ.liftEvenMatrix A hA) = A := by
  ext i j
  simp only [matrixEvenToCarrier, Matrix.map_apply]
  exact Λ.liftEvenMatrix_spec A hA i j

/-- If two matrices are equal, their liftEvenMatrix results are equal. -/
theorem liftEvenMatrix_eq_of_eq {n m : ℕ}
    (M N : Matrix (Fin n) (Fin m) Λ.carrier)
    (hM : ∀ i j, M i j ∈ Λ.even) (hN : ∀ i j, N i j ∈ Λ.even)
    (hEq : M = N) :
    Λ.liftEvenMatrix M hM = Λ.liftEvenMatrix N hN := by
  ext i j; apply Λ.evenToCarrier_injective
  simp only [Λ.liftEvenMatrix_spec, hEq]

/-- If two matrices are equal, their lifted determinants are equal. -/
theorem liftEvenMatrix_det_eq_of_eq {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) Λ.carrier)
    (hM : ∀ i j, M i j ∈ Λ.even) (hN : ∀ i j, N i j ∈ Λ.even)
    (hEq : M = N) :
    (Λ.liftEvenMatrix M hM).det = (Λ.liftEvenMatrix N hN).det := by
  rw [liftEvenMatrix_eq_of_eq M N hM hN hEq]

/-- liftEvenMatrix preserves matrix multiplication for even matrices. -/
theorem liftEvenMatrix_mul {n m p : ℕ}
    (A : Matrix (Fin n) (Fin m) Λ.carrier) (B : Matrix (Fin m) (Fin p) Λ.carrier)
    (hA : ∀ i j, A i j ∈ Λ.even) (hB : ∀ i j, B i j ∈ Λ.even)
    (hAB : ∀ i j, (A * B) i j ∈ Λ.even) :
    Λ.liftEvenMatrix (A * B) hAB = Λ.liftEvenMatrix A hA * Λ.liftEvenMatrix B hB := by
  ext i j
  simp only [Matrix.mul_apply]
  apply Λ.evenToCarrier_injective
  rw [Λ.liftEvenMatrix_spec _ hAB i j]
  simp only [Matrix.mul_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  -- Goal: A i k * B k j = Λ.evenToCarrier (liftEvenMatrix A hA i k * liftEvenMatrix B hB k j)
  have hLHS_A : A i k = Λ.evenToCarrier (Λ.liftEvenMatrix A hA i k) := (Λ.liftEvenMatrix_spec A hA i k).symm
  have hLHS_B : B k j = Λ.evenToCarrier (Λ.liftEvenMatrix B hB k j) := (Λ.liftEvenMatrix_spec B hB k j).symm
  rw [hLHS_A, hLHS_B, ← Λ.evenToCarrier.map_mul]

/-- matrixEvenToCarrier preserves matrix multiplication. -/
theorem matrixEvenToCarrier_mul {n m p : ℕ}
    (A : Matrix (Fin n) (Fin m) Λ.evenCarrier) (B : Matrix (Fin m) (Fin p) Λ.evenCarrier) :
    matrixEvenToCarrier (A * B) = matrixEvenToCarrier A * matrixEvenToCarrier B := by
  ext i j
  simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Λ.evenToCarrier.map_mul]

/-- D_lifted for a product factors when the left matrix is diagonal.
    This generalizes D_lifted_diagonal_mul. -/
theorem D_lifted_mul_eq {n m : ℕ} (M N : SuperMatrix Λ n m)
    (hMD_eq : (M * N).Dblock = M.Dblock * N.Dblock) :
    (M * N).D_lifted = M.D_lifted * N.D_lifted := by
  ext i j
  simp only [SuperMatrix.D_lifted, Matrix.mul_apply]
  apply Λ.evenToCarrier_injective
  rw [Λ.liftEvenMatrix_spec _ (M * N).Dblock_even i j]
  rw [hMD_eq]
  simp only [Matrix.mul_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hLHS_M : M.Dblock i k = Λ.evenToCarrier (Λ.liftEvenMatrix M.Dblock M.Dblock_even i k) :=
    (Λ.liftEvenMatrix_spec M.Dblock M.Dblock_even i k).symm
  have hLHS_N : N.Dblock k j = Λ.evenToCarrier (Λ.liftEvenMatrix N.Dblock N.Dblock_even k j) :=
    (Λ.liftEvenMatrix_spec N.Dblock N.Dblock_even k j).symm
  rw [hLHS_M, hLHS_N, ← Λ.evenToCarrier.map_mul]

/-- Multiplying on the right by lower triangular preserves Dblock. -/
theorem mul_lowerTriangular_Dblock_eq {n m : ℕ} (M : SuperMatrix Λ n m)
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd) :
    (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock = M.Dblock := by
  show M.Cblock * (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock +
       M.Dblock * (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock = M.Dblock
  simp only [SuperMatrix.lowerTriangular, Matrix.mul_zero, Matrix.mul_one, zero_add]

/-- Multiplying on the right by lower triangular preserves Bblock. -/
theorem mul_lowerTriangular_Bblock_eq {n m : ℕ} (M : SuperMatrix Λ n m)
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd) :
    (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock = M.Bblock := by
  show M.Ablock * (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock +
       M.Bblock * (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock = M.Bblock
  simp only [SuperMatrix.lowerTriangular, Matrix.mul_zero, Matrix.mul_one, zero_add]

/-- Multiplying on the right by upper triangular preserves Cblock. -/
theorem mul_upperTriangular_Cblock_eq {n m : ℕ} (M : SuperMatrix Λ n m)
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd) :
    (M * SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Cblock = M.Cblock := by
  show M.Cblock * (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock +
       M.Dblock * (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Cblock = M.Cblock
  simp only [SuperMatrix.upperTriangular, Matrix.mul_one, Matrix.mul_zero, add_zero]

/-- Multiplying on the right by upper triangular preserves Ablock. -/
theorem mul_upperTriangular_Ablock_eq {n m : ℕ} (M : SuperMatrix Λ n m)
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd) :
    (M * SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock = M.Ablock := by
  show M.Ablock * (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock +
       M.Bblock * (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Cblock = M.Ablock
  simp only [SuperMatrix.upperTriangular, Matrix.mul_one, Matrix.mul_zero, add_zero]

end Supermanifolds.Helpers
