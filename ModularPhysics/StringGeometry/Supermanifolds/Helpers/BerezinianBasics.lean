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

/-! ## Berezinian Definition

The Berezinian is computed on evenCarrier (CommRing) where determinants and inverses
are well-defined. Since A and D blocks have even entries, they can be lifted to evenCarrier.
The Schur complement A - BD⁻¹C also has even entries (since BD⁻¹ is odd×even=odd, and
BD⁻¹C is odd×odd=even, so A - BD⁻¹C is even-even=even).
-/

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

/-- Berezinian: Ber(M) = det(A - BD⁻¹C) · det(D)⁻¹ for supermatrix M = [A B; C D].

    Computed on evenCarrier where det and inv are well-defined. -/
noncomputable def SuperMatrix.ber {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m)
    (hD : Λ.IsInvertible M.D_lifted.det)
    (hBDinv : ∀ i j, (M.Bblock * M.D_inv_carrier) i j ∈ Λ.odd) : Λ.evenCarrier :=
  let schurD_lifted := Λ.liftEvenMatrix M.schurD_carrier (M.schurD_even hBDinv)
  schurD_lifted.det * Λ.inv M.D_lifted.det hD

/-- A-based Berezinian: BerAlt(M) = det(A) · det(D - CA⁻¹B)⁻¹. Requires A invertible. -/
noncomputable def SuperMatrix.berAlt {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m)
    (_hA : Λ.IsInvertible M.A_lifted.det)
    (hCAinv : ∀ i j, (M.Cblock * M.A_inv_carrier) i j ∈ Λ.odd)
    (hSchurA : Λ.IsInvertible (Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hCAinv)).det) :
    Λ.evenCarrier :=
  let schurA_lifted := Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hCAinv)
  M.A_lifted.det * Λ.inv schurA_lifted.det hSchurA

/-- The two Berezinian formulas agree when both A and D are invertible. -/
theorem SuperMatrix.ber_eq_berAlt {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (M : SuperMatrix Λ n m)
    (hMA : Λ.IsInvertible M.A_lifted.det) (hMD : Λ.IsInvertible M.D_lifted.det)
    (hAinvB : ∀ i j, (M.A_inv_carrier * M.Bblock) i j ∈ Λ.odd)
    (hDinvC : ∀ i j, (M.D_inv_carrier * M.Cblock) i j ∈ Λ.odd)
    (hBDinv : ∀ i j, (M.Bblock * M.D_inv_carrier) i j ∈ Λ.odd)
    (hCAinv : ∀ i j, (M.Cblock * M.A_inv_carrier) i j ∈ Λ.odd)
    (hSchurA : Λ.IsInvertible (Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hCAinv)).det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0 : (0 : Λ.carrier) ∈ Λ.even) :
    M.ber hMD hBDinv = M.berAlt hMA hCAinv hSchurA := by
  unfold SuperMatrix.ber SuperMatrix.berAlt
  -- X = D⁻¹C and Y = A⁻¹B computed in carrier (via evenCarrier inverses)
  let X := M.D_inv_carrier * M.Cblock
  let Y := M.A_inv_carrier * M.Bblock
  -- Use the key identity from MatrixParity: det(1-YX) * det(1-XY) = 1 on evenCarrier
  have hDetComm := grassmann_det_one_sub_mul_comm Y X hAinvB hDinvC h1 h0
  -- Get Invertible instances on evenCarrier
  haveI : Invertible M.A_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hMA).invertible
  haveI hInvA : Invertible M.A_lifted := Matrix.invertibleOfDetInvertible M.A_lifted
  haveI : Invertible M.D_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hMD).invertible
  haveI hInvD : Invertible M.D_lifted := Matrix.invertibleOfDetInvertible M.D_lifted

  -- The lifted matrices satisfy M_lifted * M_lifted⁻¹ = 1 on evenCarrier
  have hAAinv : M.A_lifted * M.A_lifted⁻¹ = 1 := Matrix.mul_nonsing_inv M.A_lifted (isUnit_of_invertible _)
  have hDDinv : M.D_lifted * M.D_lifted⁻¹ = 1 := Matrix.mul_nonsing_inv M.D_lifted (isUnit_of_invertible _)

  -- The Schur complements factor: schurD = A(1 - YX) and schurA = D(1 - XY)
  -- These identities hold in carrier, then we lift to evenCarrier

  -- Lift the products YX and XY to evenCarrier (they have even entries since odd×odd=even)
  have hYX_even : ∀ i j, (Y * X) i j ∈ Λ.even := matrix_mul_odd_odd Y X hAinvB hDinvC
  have hXY_even : ∀ i j, (X * Y) i j ∈ Λ.even := matrix_mul_odd_odd X Y hDinvC hAinvB
  let YX_lifted := Λ.liftEvenMatrix (Y * X) hYX_even
  let XY_lifted := Λ.liftEvenMatrix (X * Y) hXY_even

  -- The determinant identity from grassmann_det_one_sub_mul_comm gives us:
  -- (1 - YX_lifted).det * (1 - XY_lifted).det = 1
  have h1YX_inv : Λ.IsInvertible (1 - YX_lifted).det := by
    unfold GrassmannAlgebra.IsInvertible
    have h : Λ.body ((1 - YX_lifted).det * (1 - XY_lifted).det) = Λ.body 1 := congrArg Λ.body hDetComm
    rw [Λ.body_mul, Λ.body_one] at h
    exact left_ne_zero_of_mul_eq_one h

  have h1XY_inv : Λ.IsInvertible (1 - XY_lifted).det := by
    unfold GrassmannAlgebra.IsInvertible
    have h : Λ.body ((1 - YX_lifted).det * (1 - XY_lifted).det) = Λ.body 1 := congrArg Λ.body hDetComm
    rw [Λ.body_mul, Λ.body_one, mul_comm] at h
    exact left_ne_zero_of_mul_eq_one h

  -- Key: det(1-XY)⁻¹ = det(1-YX) follows from their product being 1
  have hInvXY : Λ.inv (1 - XY_lifted).det h1XY_inv = (1 - YX_lifted).det := by
    have h_prod_cancel : (1 - XY_lifted).det * Λ.inv (1 - XY_lifted).det h1XY_inv = 1 :=
      Λ.mul_inv (1 - XY_lifted).det h1XY_inv
    have hprod : (1 - YX_lifted).det * (1 - XY_lifted).det = 1 := hDetComm
    -- From a * b = 1, we get b⁻¹ = a
    calc Λ.inv (1 - XY_lifted).det h1XY_inv
        = 1 * Λ.inv (1 - XY_lifted).det h1XY_inv := (one_mul _).symm
      _ = ((1 - YX_lifted).det * (1 - XY_lifted).det) *
            Λ.inv (1 - XY_lifted).det h1XY_inv := by rw [hprod]
      _ = (1 - YX_lifted).det * ((1 - XY_lifted).det *
            Λ.inv (1 - XY_lifted).det h1XY_inv) := by ring
      _ = (1 - YX_lifted).det * 1 := by rw [h_prod_cancel]
      _ = (1 - YX_lifted).det := by rw [mul_one]

  -- Now we need to show the Berezinians are equal
  -- ber = det(schurD_lifted) * inv(det(D_lifted))
  -- berAlt = det(A_lifted) * inv(det(schurA_lifted))

  -- The key is to show the Schur complement factorizations hold when lifted to evenCarrier.
  -- schurD_carrier = A - B*D_inv_carrier*C
  -- We need: when lifted, det(schurD_lifted) = det(A_lifted) * det(1 - YX_lifted)

  -- First, show the factorization: schurD_carrier = A - B*D_inv_carrier*C factors as A*(1 - Y*X)
  -- where Y = A_inv_carrier * B and X = D_inv_carrier * C

  -- The factorization holds because in carrier:
  -- A - B*D_inv*C = A - A*A_inv*B*D_inv*C = A*(1 - A_inv*B*D_inv*C) = A*(1 - Y*X)
  -- But we need M.A_lifted * matrixEvenToCarrier(M.A_lifted⁻¹) = 1 in carrier...
  -- Actually the factorization A - B*D_inv*C = A*(1 - Y*X) requires showing
  -- B*D_inv*C = A*(A_inv*B)*(D_inv*C) = A*Y*X

  -- For matrices with even entries (A, D have even entries), multiplication in carrier
  -- corresponds to multiplication in evenCarrier when lifted.

  -- Key lemma: M.Ablock * M.A_inv_carrier = matrixEvenToCarrier(M.A_lifted * M.A_lifted⁻¹)
  --          = matrixEvenToCarrier(1) = 1

  have hA_A_inv : matrixEvenToCarrier (M.A_lifted * M.A_lifted⁻¹) =
      (matrixEvenToCarrier M.A_lifted) * (matrixEvenToCarrier M.A_lifted⁻¹) := by
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Λ.evenToCarrier.map_mul]

  have hA_lifted_carrier : matrixEvenToCarrier M.A_lifted = M.Ablock := by
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, SuperMatrix.A_lifted]
    exact Λ.liftEvenMatrix_spec M.Ablock M.Ablock_even i j

  have hD_lifted_carrier : matrixEvenToCarrier M.D_lifted = M.Dblock := by
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, SuperMatrix.D_lifted]
    exact Λ.liftEvenMatrix_spec M.Dblock M.Dblock_even i j

  -- M.Ablock * M.A_inv_carrier = 1 in carrier
  have hAblock_Ainv : M.Ablock * M.A_inv_carrier = 1 := by
    -- A_inv_carrier = matrixEvenToCarrier M.A_lifted⁻¹ by definition
    have hA_inv_def : M.A_inv_carrier = matrixEvenToCarrier M.A_lifted⁻¹ := rfl
    rw [hA_inv_def, ← hA_lifted_carrier, ← hA_A_inv, hAAinv]
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]

  have hDblock_Dinv : M.Dblock * M.D_inv_carrier = 1 := by
    -- D_inv_carrier = matrixEvenToCarrier M.D_lifted⁻¹ by definition
    have hD_inv_def : M.D_inv_carrier = matrixEvenToCarrier M.D_lifted⁻¹ := rfl
    rw [hD_inv_def, ← hD_lifted_carrier]
    have hD_D_inv : matrixEvenToCarrier M.D_lifted * matrixEvenToCarrier M.D_lifted⁻¹ =
        matrixEvenToCarrier (M.D_lifted * M.D_lifted⁻¹) := by
      ext i j
      simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Λ.evenToCarrier.map_mul]
    rw [hD_D_inv, hDDinv]
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]

  -- Now show the Schur complement factorization
  -- schurD_carrier = A - B * D_inv_carrier * C
  -- We want: A - B*D_inv*C = A*(1 - Y*X) where Y = A_inv*B, X = D_inv*C

  have hSD_factor : M.schurD_carrier = M.Ablock * (1 - Y * X) := by
    unfold SuperMatrix.schurD_carrier
    have h : M.Ablock * (1 - Y * X) = M.Ablock - M.Ablock * (Y * X) := by
      rw [Matrix.mul_sub, Matrix.mul_one]
    rw [h]
    congr 1
    -- Show: B * D_inv_carrier * C = A * (Y * X) = A * (A_inv_carrier * B) * (D_inv_carrier * C)
    calc M.Bblock * M.D_inv_carrier * M.Cblock
        = 1 * (M.Bblock * M.D_inv_carrier * M.Cblock) := (Matrix.one_mul _).symm
      _ = (M.Ablock * M.A_inv_carrier) * (M.Bblock * M.D_inv_carrier * M.Cblock) := by rw [hAblock_Ainv]
      _ = M.Ablock * (M.A_inv_carrier * (M.Bblock * M.D_inv_carrier * M.Cblock)) := by
          simp only [Matrix.mul_assoc]
      _ = M.Ablock * (M.A_inv_carrier * M.Bblock * (M.D_inv_carrier * M.Cblock)) := by
          simp only [Matrix.mul_assoc]
      _ = M.Ablock * (Y * X) := rfl

  have hSA_factor : M.schurA_carrier = M.Dblock * (1 - X * Y) := by
    unfold SuperMatrix.schurA_carrier
    have h : M.Dblock * (1 - X * Y) = M.Dblock - M.Dblock * (X * Y) := by
      rw [Matrix.mul_sub, Matrix.mul_one]
    rw [h]
    congr 1
    calc M.Cblock * M.A_inv_carrier * M.Bblock
        = 1 * (M.Cblock * M.A_inv_carrier * M.Bblock) := (Matrix.one_mul _).symm
      _ = (M.Dblock * M.D_inv_carrier) * (M.Cblock * M.A_inv_carrier * M.Bblock) := by rw [hDblock_Dinv]
      _ = M.Dblock * (M.D_inv_carrier * (M.Cblock * M.A_inv_carrier * M.Bblock)) := by
          simp only [Matrix.mul_assoc]
      _ = M.Dblock * (M.D_inv_carrier * M.Cblock * (M.A_inv_carrier * M.Bblock)) := by
          simp only [Matrix.mul_assoc]
      _ = M.Dblock * (X * Y) := rfl

  -- Now we need to show the determinant factorization when lifted to evenCarrier
  -- det(lift(A*(1-YX))) = det(lift(A)) * det(lift(1-YX))
  --                     = det(A_lifted) * det(1 - YX_lifted)

  -- The lifting of A*(1-YX) to evenCarrier equals A_lifted * (1 - YX_lifted)
  -- because A has even entries and 1-YX has even entries (YX has even entries since odd*odd=even)

  -- Key: 1 - YX has even entries
  have h1_YX_even : ∀ i j, ((1 : Matrix (Fin n) (Fin n) Λ.carrier) - Y * X) i j ∈ Λ.even := by
    intro i j
    simp only [Matrix.sub_apply, Matrix.one_apply]
    split_ifs with h
    · apply Λ.even.sub_mem h1 (hYX_even i j)
    · apply Λ.even.sub_mem h0 (hYX_even i j)

  have h1_XY_even : ∀ i j, ((1 : Matrix (Fin m) (Fin m) Λ.carrier) - X * Y) i j ∈ Λ.even := by
    intro i j
    simp only [Matrix.sub_apply, Matrix.one_apply]
    split_ifs with h
    · apply Λ.even.sub_mem h1 (hXY_even i j)
    · apply Λ.even.sub_mem h0 (hXY_even i j)

  -- Lift 1 - YX to evenCarrier
  let one_sub_YX_lifted := Λ.liftEvenMatrix (1 - Y * X) h1_YX_even
  let one_sub_XY_lifted := Λ.liftEvenMatrix (1 - X * Y) h1_XY_even

  -- Show that one_sub_YX_lifted = 1 - YX_lifted
  have h_one_sub_YX : one_sub_YX_lifted = 1 - YX_lifted := by
    ext i j
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec]
    simp only [Matrix.sub_apply, Matrix.one_apply]
    rw [Λ.evenToCarrier.map_sub]
    congr 1
    · split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
    · exact (Λ.liftEvenMatrix_spec (Y * X) hYX_even i j).symm

  have h_one_sub_XY : one_sub_XY_lifted = 1 - XY_lifted := by
    ext i j
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec]
    simp only [Matrix.sub_apply, Matrix.one_apply]
    rw [Λ.evenToCarrier.map_sub]
    congr 1
    · split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
    · exact (Λ.liftEvenMatrix_spec (X * Y) hXY_even i j).symm

  -- The schurD_carrier has even entries (by hypothesis hBDinv and schurD_even)
  -- Lift schurD to evenCarrier
  let schurD_lifted := Λ.liftEvenMatrix M.schurD_carrier (M.schurD_even hBDinv)
  let schurA_lifted := Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hCAinv)

  -- Key factorization: schurD_lifted = A_lifted * one_sub_YX_lifted
  have h_schurD_factor_lifted : schurD_lifted = M.A_lifted * one_sub_YX_lifted := by
    ext i j
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec, hSD_factor]
    simp only [Matrix.mul_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Λ.evenToCarrier.map_mul]
    congr 1
    · exact (Λ.liftEvenMatrix_spec M.Ablock M.Ablock_even i k).symm
    · rw [Λ.liftEvenMatrix_spec]

  have h_schurA_factor_lifted : schurA_lifted = M.D_lifted * one_sub_XY_lifted := by
    ext i j
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec, hSA_factor]
    simp only [Matrix.mul_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Λ.evenToCarrier.map_mul]
    congr 1
    · exact (Λ.liftEvenMatrix_spec M.Dblock M.Dblock_even i k).symm
    · rw [Λ.liftEvenMatrix_spec]

  -- Now compute the determinants using det multiplicativity
  have hDetSD : schurD_lifted.det = M.A_lifted.det * one_sub_YX_lifted.det := by
    rw [h_schurD_factor_lifted, Matrix.det_mul]

  have hDetSA : schurA_lifted.det = M.D_lifted.det * one_sub_XY_lifted.det := by
    rw [h_schurA_factor_lifted, Matrix.det_mul]

  -- Substitute in the one_sub equalities
  rw [h_one_sub_YX] at hDetSD
  rw [h_one_sub_XY] at hDetSA

  -- Now we need to show:
  -- schurD_lifted.det * inv(D_lifted.det) = A_lifted.det * inv(schurA_lifted.det)
  -- i.e., A_lifted.det * (1 - YX_lifted).det * inv(D_lifted.det) =
  --       A_lifted.det * inv(D_lifted.det * (1 - XY_lifted).det)

  -- The goal after unfold has internal let-bindings. We show they are definitionally equal
  -- to our local schurD_lifted and schurA_lifted.
  -- Goal: (let schurD_lifted := ...; schurD_lifted.det * Λ.inv M.D_lifted.det hMD) =
  --       (let schurA_lifted := ...; M.A_lifted.det * Λ.inv schurA_lifted.det hSchurA)
  -- After beta reduction, this becomes:
  -- schurD_lifted.det * Λ.inv M.D_lifted.det hMD =
  -- M.A_lifted.det * Λ.inv schurA_lifted.det hSchurA

  -- Use determinant factorization
  have hDetSD' : schurD_lifted.det = M.A_lifted.det * (1 - YX_lifted).det := by
    rw [h_schurD_factor_lifted, h_one_sub_YX, Matrix.det_mul]

  have hDetSA' : schurA_lifted.det = M.D_lifted.det * (1 - XY_lifted).det := by
    rw [h_schurA_factor_lifted, h_one_sub_XY, Matrix.det_mul]

  -- Product inverse: inv(a*b) = inv(a) * inv(b) for invertible a, b in CommRing
  have h_prod_inv : Λ.IsInvertible (M.D_lifted.det * (1 - XY_lifted).det) :=
    Λ.mul_invertible _ _ hMD h1XY_inv

  -- Show that schurA_lifted.det = D.det * (1-XY).det has the same invertibility
  have hSchurA_inv : Λ.IsInvertible schurA_lifted.det := by
    rw [hDetSA']; exact h_prod_inv

  -- inv(D.det * (1-XY).det) = inv(D.det) * inv((1-XY).det)
  have h_inv_prod : Λ.inv (M.D_lifted.det * (1 - XY_lifted).det) h_prod_inv =
      Λ.inv M.D_lifted.det hMD * Λ.inv (1 - XY_lifted).det h1XY_inv := by
    -- Show that (inv(D.det) * inv((1-XY).det)) is the inverse of D.det * (1-XY).det
    have h1' : M.D_lifted.det * (1 - XY_lifted).det *
        (Λ.inv M.D_lifted.det hMD * Λ.inv (1 - XY_lifted).det h1XY_inv) = 1 := by
      have hD_cancel : M.D_lifted.det * Λ.inv M.D_lifted.det hMD = 1 := Λ.mul_inv _ hMD
      have hXY_cancel : (1 - XY_lifted).det * Λ.inv (1 - XY_lifted).det h1XY_inv = 1 :=
        Λ.mul_inv _ h1XY_inv
      calc M.D_lifted.det * (1 - XY_lifted).det *
              (Λ.inv M.D_lifted.det hMD * Λ.inv (1 - XY_lifted).det h1XY_inv)
          = (M.D_lifted.det * Λ.inv M.D_lifted.det hMD) *
            ((1 - XY_lifted).det * Λ.inv (1 - XY_lifted).det h1XY_inv) := by ring
        _ = 1 * 1 := by rw [hD_cancel, hXY_cancel]
        _ = 1 := one_mul _
    -- Use uniqueness of inverse
    have h_prod_inv_cancel : Λ.inv (M.D_lifted.det * (1 - XY_lifted).det) h_prod_inv *
        (M.D_lifted.det * (1 - XY_lifted).det) = 1 := Λ.inv_mul _ h_prod_inv
    calc Λ.inv (M.D_lifted.det * (1 - XY_lifted).det) h_prod_inv
        = Λ.inv (M.D_lifted.det * (1 - XY_lifted).det) h_prod_inv * 1 := (mul_one _).symm
      _ = Λ.inv (M.D_lifted.det * (1 - XY_lifted).det) h_prod_inv *
          (M.D_lifted.det * (1 - XY_lifted).det *
           (Λ.inv M.D_lifted.det hMD * Λ.inv (1 - XY_lifted).det h1XY_inv)) := by rw [h1']
      _ = (Λ.inv (M.D_lifted.det * (1 - XY_lifted).det) h_prod_inv *
           (M.D_lifted.det * (1 - XY_lifted).det)) *
          (Λ.inv M.D_lifted.det hMD * Λ.inv (1 - XY_lifted).det h1XY_inv) := by ring
      _ = 1 * (Λ.inv M.D_lifted.det hMD * Λ.inv (1 - XY_lifted).det h1XY_inv) := by
          rw [h_prod_inv_cancel]
      _ = Λ.inv M.D_lifted.det hMD * Λ.inv (1 - XY_lifted).det h1XY_inv := one_mul _

  -- Now work with the goal directly, showing that it equals the RHS
  -- The key is that the internal let-bindings in ber/berAlt are definitionally equal to our local ones
  show (let schurD_lifted := Λ.liftEvenMatrix M.schurD_carrier (M.schurD_even hBDinv)
        schurD_lifted.det * Λ.inv M.D_lifted.det hMD) =
       (let schurA_lifted := Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hCAinv)
        M.A_lifted.det * Λ.inv schurA_lifted.det hSchurA)
  -- Beta-reduce the let bindings
  simp only []
  -- Now the goal is:
  -- schurD_lifted.det * Λ.inv M.D_lifted.det hMD = M.A_lifted.det * Λ.inv schurA_lifted.det hSchurA

  -- Use conv to rewrite only in the LHS (avoiding the proof term hSchurA dependency)
  conv_lhs => rw [hDetSD']
  -- LHS is now: M.A_lifted.det * (1 - YX_lifted).det * Λ.inv M.D_lifted.det hMD

  -- For the RHS, we need to show that Λ.inv schurA_lifted.det hSchurA = Λ.inv (D.det * (1-XY).det) h_prod_inv
  -- Since schurA_lifted.det = D.det * (1-XY).det by hDetSA', and Λ.inv is uniquely determined
  have h_inv_schurA : Λ.inv schurA_lifted.det hSchurA =
      Λ.inv (M.D_lifted.det * (1 - XY_lifted).det) h_prod_inv := by
    -- Both are inverses of the same element (schurA_lifted.det = D.det * (1-XY).det)
    -- Use uniqueness of inverse
    have hprod_eq : schurA_lifted.det = M.D_lifted.det * (1 - XY_lifted).det := hDetSA'
    -- Both inv values satisfy x * inv = 1, so they are equal
    have h_left : schurA_lifted.det * Λ.inv schurA_lifted.det hSchurA = 1 := Λ.mul_inv _ hSchurA
    have h_right : (M.D_lifted.det * (1 - XY_lifted).det) *
        Λ.inv (M.D_lifted.det * (1 - XY_lifted).det) h_prod_inv = 1 := Λ.mul_inv _ h_prod_inv
    -- Now h_left : schurA_lifted.det * Λ.inv schurA_lifted.det hSchurA = 1
    -- Substitute hprod_eq in h_left to get: (D.det * (1-XY).det) * Λ.inv schurA_lifted.det hSchurA = 1
    -- From a * x = 1 and a * y = 1, we get x = y (in commutative ring)
    -- Use calc without rewriting under the dependent proof
    have h_left' : (M.D_lifted.det * (1 - XY_lifted).det) * Λ.inv schurA_lifted.det hSchurA = 1 := by
      calc (M.D_lifted.det * (1 - XY_lifted).det) * Λ.inv schurA_lifted.det hSchurA
          = schurA_lifted.det * Λ.inv schurA_lifted.det hSchurA := by rw [← hprod_eq]
        _ = 1 := h_left
    calc Λ.inv schurA_lifted.det hSchurA
        = 1 * Λ.inv schurA_lifted.det hSchurA := (one_mul _).symm
      _ = (Λ.inv (M.D_lifted.det * (1 - XY_lifted).det) h_prod_inv *
           (M.D_lifted.det * (1 - XY_lifted).det)) * Λ.inv schurA_lifted.det hSchurA := by
          rw [Λ.inv_mul _ h_prod_inv]
      _ = Λ.inv (M.D_lifted.det * (1 - XY_lifted).det) h_prod_inv *
          ((M.D_lifted.det * (1 - XY_lifted).det) * Λ.inv schurA_lifted.det hSchurA) := by ring
      _ = Λ.inv (M.D_lifted.det * (1 - XY_lifted).det) h_prod_inv * 1 := by rw [h_left']
      _ = Λ.inv (M.D_lifted.det * (1 - XY_lifted).det) h_prod_inv := mul_one _

  rw [h_inv_schurA, h_inv_prod, hInvXY]
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

/-- D-based Schur complement: A - BD⁻¹C (uses evenCarrier inverse) -/
noncomputable def schurComplementD {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (_ : Λ.IsInvertible M.D_lifted.det) :
    Matrix (Fin n) (Fin n) Λ.carrier :=
  M.Ablock - M.Bblock * M.D_inv_carrier * M.Cblock

/-- A-based Schur complement: D - CA⁻¹B (uses evenCarrier inverse) -/
noncomputable def schurComplementA {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (_ : Λ.IsInvertible M.A_lifted.det) :
    Matrix (Fin m) (Fin m) Λ.carrier :=
  M.Dblock - M.Cblock * M.A_inv_carrier * M.Bblock


/-! ## LDU and UDL Factorizations -/

/-- Lower triangular factor (D-based): L = [I 0; D⁻¹C I] (uses evenCarrier inverse) -/
noncomputable def lowerTriangularFactorD {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (_hD : Λ.IsInvertible M.D_lifted.det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hDinvC : ∀ i j, (M.D_inv_carrier * M.Cblock) i j ∈ Λ.odd) : SuperMatrix Λ n m :=
  ⟨1, 0, M.D_inv_carrier * M.Cblock, 1,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even],
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   hDinvC,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]⟩

/-- Upper triangular factor (D-based): U = [I BD⁻¹; 0 I] (uses evenCarrier inverse) -/
noncomputable def upperTriangularFactorD {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (_hD : Λ.IsInvertible M.D_lifted.det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hBDinv : ∀ i j, (M.Bblock * M.D_inv_carrier) i j ∈ Λ.odd) : SuperMatrix Λ n m :=
  ⟨1, M.Bblock * M.D_inv_carrier, 0, 1,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even],
   hBDinv,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]⟩

/-- Diagonal factor (D-based): Δ = [SchurD 0; 0 D] (uses evenCarrier inverse) -/
noncomputable def diagonalFactorD {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (hD : Λ.IsInvertible M.D_lifted.det)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hSchur : ∀ i j, (schurComplementD M hD) i j ∈ Λ.even) : SuperMatrix Λ n m :=
  ⟨schurComplementD M hD, 0, 0, M.Dblock,
   hSchur,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   M.Dblock_even⟩

/-- Lower triangular factor (A-based): L = [I 0; CA⁻¹ I] (uses evenCarrier inverse) -/
noncomputable def lowerTriangularFactorA {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (_hA : Λ.IsInvertible M.A_lifted.det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hCAinv : ∀ i j, (M.Cblock * M.A_inv_carrier) i j ∈ Λ.odd) : SuperMatrix Λ n m :=
  ⟨1, 0, M.Cblock * M.A_inv_carrier, 1,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even],
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   hCAinv,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]⟩

/-- Upper triangular factor (A-based): U = [I A⁻¹B; 0 I] (uses evenCarrier inverse) -/
noncomputable def upperTriangularFactorA {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (_hA : Λ.IsInvertible M.A_lifted.det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hAinvB : ∀ i j, (M.A_inv_carrier * M.Bblock) i j ∈ Λ.odd) : SuperMatrix Λ n m :=
  ⟨1, M.A_inv_carrier * M.Bblock, 0, 1,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even],
   hAinvB,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]⟩

/-- Diagonal factor (A-based): Δ = [A 0; 0 SchurA] (uses evenCarrier inverse) -/
noncomputable def diagonalFactorA {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (hA : Λ.IsInvertible M.A_lifted.det)
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
noncomputable def SuperMatrix.upperTriangular {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
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
noncomputable def SuperMatrix.lowerTriangular {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
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
noncomputable def SuperMatrix.diagonal {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
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

/-- Ber(U) = 1 for upper triangular U = [I B'; 0 I]. (uses evenCarrier) -/
theorem SuperMatrix.ber_upperTriangular {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd)
    (hD : Λ.IsInvertible (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').D_lifted.det)
    (hBDinv : ∀ i j, ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Bblock *
        (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').D_inv_carrier) i j ∈ Λ.odd) :
    (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').ber hD hBDinv = 1 := by
  unfold SuperMatrix.ber
  have hAblock : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock = 1 := rfl
  have hCblock : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Cblock = 0 := rfl
  have hDblock : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock = 1 := rfl
  -- schurD_carrier = A - B * D_inv_carrier * C = 1 - B * D_inv * 0 = 1
  have hSchurD : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').schurD_carrier = 1 := by
    unfold SuperMatrix.schurD_carrier
    rw [hCblock]
    ext i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply, mul_zero,
               Finset.sum_const_zero, sub_zero, hAblock, Matrix.one_apply]
  -- Show det(schurD_lifted) = 1 and det(D_lifted) = 1
  have hSchurD_lifted_eq_one : Λ.liftEvenMatrix (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').schurD_carrier
      ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB').schurD_even hBDinv) = 1 := by
    ext i j
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec, hSchurD]
    simp only [Matrix.one_apply]
    split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
  have hD_lifted_det_eq_one : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').D_lifted.det = 1 := by
    unfold SuperMatrix.D_lifted
    have h : Λ.liftEvenMatrix (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock
        (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock_even = 1 := by
      ext i j
      apply Λ.evenToCarrier_injective
      rw [Λ.liftEvenMatrix_spec, hDblock]
      simp only [Matrix.one_apply]
      split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
    rw [h, Matrix.det_one]
  simp only [hSchurD_lifted_eq_one, Matrix.det_one, hD_lifted_det_eq_one]
  have h1body : Λ.body (1 : Λ.evenCarrier) ≠ 0 := by rw [Λ.body_one]; exact one_ne_zero
  exact Λ.mul_inv 1 h1body

/-- Ber(L) = 1 for lower triangular L = [I 0; C' I]. (uses evenCarrier) -/
theorem SuperMatrix.ber_lowerTriangular {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd)
    (hD : Λ.IsInvertible (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det)
    (hBDinv : ∀ i j, ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock *
        (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_inv_carrier) i j ∈ Λ.odd) :
    (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').ber hD hBDinv = 1 := by
  unfold SuperMatrix.ber
  have hAblock : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock = 1 := rfl
  have hBblock : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock = 0 := rfl
  have hDblock : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock = 1 := rfl
  -- schurD_carrier = A - B * D_inv_carrier * C = 1 - 0 * D_inv * C = 1
  have hSchurD : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').schurD_carrier = 1 := by
    unfold SuperMatrix.schurD_carrier
    rw [hBblock]
    ext i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply, zero_mul,
               Finset.sum_const_zero, sub_zero, hAblock, Matrix.one_apply]
  have hSchurD_lifted_eq_one : Λ.liftEvenMatrix (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').schurD_carrier
      ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').schurD_even hBDinv) = 1 := by
    ext i j
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec, hSchurD]
    simp only [Matrix.one_apply]
    split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
  have hD_lifted_det_eq_one : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det = 1 := by
    unfold SuperMatrix.D_lifted
    have h : Λ.liftEvenMatrix (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock
        (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock_even = 1 := by
      ext i j
      apply Λ.evenToCarrier_injective
      rw [Λ.liftEvenMatrix_spec, hDblock]
      simp only [Matrix.one_apply]
      split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
    rw [h, Matrix.det_one]
  simp only [hSchurD_lifted_eq_one, Matrix.det_one, hD_lifted_det_eq_one]
  have h1body : Λ.body (1 : Λ.evenCarrier) ≠ 0 := by rw [Λ.body_one]; exact one_ne_zero
  exact Λ.mul_inv 1 h1body

/-- berAlt(L · N) = berAlt(N) when L = [I 0; C' I] is lower triangular. -/
theorem SuperMatrix.berAlt_mul_lowerTriangular_left {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (N : SuperMatrix Λ n m)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd)
    (hNA : Λ.IsInvertible N.A_lifted.det)
    (hNCAinv : ∀ i j, (N.Cblock * N.A_inv_carrier) i j ∈ Λ.odd)
    (hNSchurA : Λ.IsInvertible (Λ.liftEvenMatrix N.schurA_carrier (N.schurA_even hNCAinv)).det)
    (hLNA : Λ.IsInvertible ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') * N).A_lifted.det)
    (hLNCAinv : ∀ i j, (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') * N).Cblock *
        ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') * N).A_inv_carrier) i j ∈ Λ.odd)
    (hLNSchurA : Λ.IsInvertible (Λ.liftEvenMatrix
        ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') * N).schurA_carrier
        (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') * N).schurA_even hLNCAinv)).det) :
    ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') * N).berAlt hLNA hLNCAinv hLNSchurA =
    N.berAlt hNA hNCAinv hNSchurA := by
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
  -- The A_lifted for (L * N) equals N.A_lifted since (L*N).Ablock = N.Ablock
  have hLNA_lifted_eq : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).A_lifted = N.A_lifted := by
    ext i j
    simp only [SuperMatrix.A_lifted]
    -- Goal: Λ.liftEvenMatrix (L*N).Ablock ... i j = Λ.liftEvenMatrix N.Ablock ... i j
    -- Since (L*N).Ablock = N.Ablock, these are definitionally equal after unfolding
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec]
    exact congrFun (congrFun hLNA_eq i) j
  -- Use the fact that A blocks are equal to show berAlt values are equal
  -- Both berAlt values use A_lifted.det and schurA_carrier
  -- Since Ablock is the same, A_lifted is the same, so det(A_lifted) is the same
  have hA_lifted_det_eq : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).A_lifted.det = N.A_lifted.det := by
    rw [hLNA_lifted_eq]
  -- For schurA_carrier, we need to show (L*N).schurA_carrier = N.schurA_carrier
  -- schurA_carrier = D - C * A_inv_carrier * B
  -- (L*N).Dblock = C' * N.Bblock + N.Dblock
  -- (L*N).Cblock = C' * N.Ablock + N.Cblock
  -- (L*N).A_inv_carrier = N.A_inv_carrier (since Ablock is the same)
  -- (L*N).Bblock = N.Bblock
  have hA_inv_carrier_eq : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).A_inv_carrier = N.A_inv_carrier := by
    unfold SuperMatrix.A_inv_carrier
    rw [hLNA_lifted_eq]
  have hSchurA_eq : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_carrier = N.schurA_carrier := by
    unfold SuperMatrix.schurA_carrier
    -- Goal: (L*N).Dblock - (L*N).Cblock * (L*N).A_inv_carrier * (L*N).Bblock = N.Dblock - N.Cblock * N.A_inv_carrier * N.Bblock
    -- Use simp with the equalities
    simp only [hLNB_eq, hLNC_eq, hLND_eq, hA_inv_carrier_eq]
    -- Need to show: (C' * N.Bblock + N.Dblock) - (C' * N.Ablock + N.Cblock) * N.A_inv_carrier * N.Bblock
    --             = N.Dblock - N.Cblock * N.A_inv_carrier * N.Bblock
    haveI : Invertible N.A_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hNA).invertible
    haveI : Invertible N.A_lifted := Matrix.invertibleOfDetInvertible N.A_lifted
    have hAAinv : N.Ablock * N.A_inv_carrier = 1 := by
      have hA_inv_def : N.A_inv_carrier = matrixEvenToCarrier N.A_lifted⁻¹ := rfl
      have hA_lifted_carrier : matrixEvenToCarrier N.A_lifted = N.Ablock := by
        ext i j
        simp only [matrixEvenToCarrier, Matrix.map_apply, SuperMatrix.A_lifted]
        exact Λ.liftEvenMatrix_spec N.Ablock N.Ablock_even i j
      have hAAinv_lifted : N.A_lifted * N.A_lifted⁻¹ = 1 := Matrix.mul_nonsing_inv N.A_lifted (isUnit_of_invertible _)
      rw [hA_inv_def, ← hA_lifted_carrier]
      have hA_A_inv : matrixEvenToCarrier N.A_lifted * matrixEvenToCarrier N.A_lifted⁻¹ =
          matrixEvenToCarrier (N.A_lifted * N.A_lifted⁻¹) := by
        ext i j
        simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [← Λ.evenToCarrier.map_mul]
      rw [hA_A_inv, hAAinv_lifted]
      ext i j
      simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply]
      split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
    have h_distrib : (C' * N.Ablock + N.Cblock) * N.A_inv_carrier * N.Bblock =
                     C' * N.Bblock + N.Cblock * N.A_inv_carrier * N.Bblock := by
      have h1' : C' * N.Ablock * N.A_inv_carrier = C' := by
        calc C' * N.Ablock * N.A_inv_carrier
            = C' * (N.Ablock * N.A_inv_carrier) := by rw [Matrix.mul_assoc]
          _ = C' * (1 : Matrix _ _ _) := by rw [hAAinv]
          _ = C' := by rw [Matrix.mul_one]
      rw [Matrix.add_mul, Matrix.add_mul, h1']
    rw [h_distrib]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply]
    -- Goal: (C' * N.Bblock) i j + N.Dblock i j - ((C' * N.Bblock) i j + (N.Cblock * N.A_inv_carrier * N.Bblock) i j) =
    --       N.Dblock i j - (N.Cblock * N.A_inv_carrier * N.Bblock) i j
    -- In an additive group: a + b - (a + c) = b - c
    abel
  -- Now show the berAlt values are equal
  -- Need to show: N.A_lifted.det * Λ.inv (lift (L*N).schurA_carrier).det hLNSchurA =
  --               N.A_lifted.det * Λ.inv (lift N.schurA_carrier).det hNSchurA
  -- Since (L*N).schurA_carrier = N.schurA_carrier, the lifted matrices are equal
  have h_lift_eq : Λ.liftEvenMatrix (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_carrier
      ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_even hLNCAinv) =
      Λ.liftEvenMatrix N.schurA_carrier (N.schurA_even hNCAinv) := by
    ext i j
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec, hSchurA_eq]
  have h_det_eq : (Λ.liftEvenMatrix (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_carrier
      ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_even hLNCAinv)).det =
      (Λ.liftEvenMatrix N.schurA_carrier (N.schurA_even hNCAinv)).det := by
    rw [h_lift_eq]
  -- Show the inverses are equal
  have h_inv_eq : Λ.inv (Λ.liftEvenMatrix (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_carrier
      ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_even hLNCAinv)).det hLNSchurA =
      Λ.inv (Λ.liftEvenMatrix N.schurA_carrier (N.schurA_even hNCAinv)).det hNSchurA := by
    have h_left : (Λ.liftEvenMatrix (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_carrier
        ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_even hLNCAinv)).det *
        Λ.inv (Λ.liftEvenMatrix (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_carrier
        ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_even hLNCAinv)).det hLNSchurA = 1 :=
      Λ.mul_inv _ hLNSchurA
    have h_right : (Λ.liftEvenMatrix N.schurA_carrier (N.schurA_even hNCAinv)).det *
        Λ.inv (Λ.liftEvenMatrix N.schurA_carrier (N.schurA_even hNCAinv)).det hNSchurA = 1 :=
      Λ.mul_inv _ hNSchurA
    -- Since det(lift (L*N).schurA) = det(lift N.schurA), both are inverses of the same element
    have h_left' : (Λ.liftEvenMatrix N.schurA_carrier (N.schurA_even hNCAinv)).det *
        Λ.inv (Λ.liftEvenMatrix (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_carrier
        ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_even hLNCAinv)).det hLNSchurA = 1 := by
      rw [← h_det_eq]; exact h_left
    calc Λ.inv (Λ.liftEvenMatrix (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_carrier _).det hLNSchurA
        = 1 * Λ.inv (Λ.liftEvenMatrix (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_carrier _).det hLNSchurA := (one_mul _).symm
      _ = (Λ.inv (Λ.liftEvenMatrix N.schurA_carrier (N.schurA_even hNCAinv)).det hNSchurA *
           (Λ.liftEvenMatrix N.schurA_carrier (N.schurA_even hNCAinv)).det) *
          Λ.inv (Λ.liftEvenMatrix (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_carrier _).det hLNSchurA := by
          rw [Λ.inv_mul _ hNSchurA]
      _ = Λ.inv (Λ.liftEvenMatrix N.schurA_carrier (N.schurA_even hNCAinv)).det hNSchurA *
          ((Λ.liftEvenMatrix N.schurA_carrier (N.schurA_even hNCAinv)).det *
           Λ.inv (Λ.liftEvenMatrix (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_carrier _).det hLNSchurA) := by ring
      _ = Λ.inv (Λ.liftEvenMatrix N.schurA_carrier (N.schurA_even hNCAinv)).det hNSchurA * 1 := by rw [h_left']
      _ = Λ.inv (Λ.liftEvenMatrix N.schurA_carrier (N.schurA_even hNCAinv)).det hNSchurA := mul_one _
  -- Beta reduce the let bindings in the goal, then rewrite
  simp only []
  rw [hA_lifted_det_eq, h_inv_eq]

/-- berAlt(M · U) = berAlt(M) when U = [I B'; 0 I] is upper triangular. -/
theorem SuperMatrix.berAlt_mul_upperTriangular_right {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (M : SuperMatrix Λ n m)
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd)
    (hMA : Λ.IsInvertible M.A_lifted.det)
    (hMCAinv : ∀ i j, (M.Cblock * M.A_inv_carrier) i j ∈ Λ.odd)
    (hMSchurA : Λ.IsInvertible (Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hMCAinv)).det)
    (hMUA : Λ.IsInvertible ((M * SuperMatrix.upperTriangular B' h1 h0even h0odd hB').A_lifted.det))
    (hMUCAinv : ∀ i j, (((M * SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Cblock *
        (M * SuperMatrix.upperTriangular B' h1 h0even h0odd hB').A_inv_carrier) i j ∈ Λ.odd))
    (hMUSchurA : Λ.IsInvertible (Λ.liftEvenMatrix
        ((M * SuperMatrix.upperTriangular B' h1 h0even h0odd hB').schurA_carrier)
        (((M * SuperMatrix.upperTriangular B' h1 h0even h0odd hB').schurA_even hMUCAinv))).det) :
    (M * SuperMatrix.upperTriangular B' h1 h0even h0odd hB').berAlt hMUA hMUCAinv hMUSchurA =
    M.berAlt hMA hMCAinv hMSchurA := by
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
  -- (M*U).A_lifted = M.A_lifted since Ablock is the same
  have hMUA_lifted_eq : (M * U).A_lifted = M.A_lifted := by
    ext i j
    simp only [SuperMatrix.A_lifted]
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec]
    exact congrFun (congrFun hMUA_eq i) j
  have hA_lifted_det_eq : (M * U).A_lifted.det = M.A_lifted.det := by
    rw [hMUA_lifted_eq]
  have hA_inv_carrier_eq : (M * U).A_inv_carrier = M.A_inv_carrier := by
    unfold SuperMatrix.A_inv_carrier
    rw [hMUA_lifted_eq]
  have hSchurA_eq : (M * U).schurA_carrier = M.schurA_carrier := by
    unfold SuperMatrix.schurA_carrier
    simp only [hMUB_eq, hMUC_eq, hMUD_eq, hA_inv_carrier_eq]
    -- Goal: (M.Cblock * B' + M.Dblock) - M.Cblock * M.A_inv_carrier * (M.Ablock * B' + M.Bblock)
    --     = M.Dblock - M.Cblock * M.A_inv_carrier * M.Bblock
    haveI : Invertible M.A_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hMA).invertible
    haveI : Invertible M.A_lifted := Matrix.invertibleOfDetInvertible M.A_lifted
    have hAAinv : M.Ablock * M.A_inv_carrier = 1 := by
      have hA_inv_def : M.A_inv_carrier = matrixEvenToCarrier M.A_lifted⁻¹ := rfl
      have hA_lifted_carrier : matrixEvenToCarrier M.A_lifted = M.Ablock := by
        ext i j
        simp only [matrixEvenToCarrier, Matrix.map_apply, SuperMatrix.A_lifted]
        exact Λ.liftEvenMatrix_spec M.Ablock M.Ablock_even i j
      have hAAinv_lifted : M.A_lifted * M.A_lifted⁻¹ = 1 := Matrix.mul_nonsing_inv M.A_lifted (isUnit_of_invertible _)
      rw [hA_inv_def, ← hA_lifted_carrier]
      have hA_A_inv : matrixEvenToCarrier M.A_lifted * matrixEvenToCarrier M.A_lifted⁻¹ =
          matrixEvenToCarrier (M.A_lifted * M.A_lifted⁻¹) := by
        ext i j
        simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [← Λ.evenToCarrier.map_mul]
      rw [hA_A_inv, hAAinv_lifted]
      ext i j
      simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply]
      split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
    have hAinvA : M.A_inv_carrier * M.Ablock = 1 := by
      have hA_inv_def : M.A_inv_carrier = matrixEvenToCarrier M.A_lifted⁻¹ := rfl
      have hA_lifted_carrier : matrixEvenToCarrier M.A_lifted = M.Ablock := by
        ext i j
        simp only [matrixEvenToCarrier, Matrix.map_apply, SuperMatrix.A_lifted]
        exact Λ.liftEvenMatrix_spec M.Ablock M.Ablock_even i j
      have hAinvA_lifted : M.A_lifted⁻¹ * M.A_lifted = 1 := Matrix.nonsing_inv_mul M.A_lifted (isUnit_of_invertible _)
      rw [hA_inv_def, ← hA_lifted_carrier]
      have hA_inv_A : matrixEvenToCarrier M.A_lifted⁻¹ * matrixEvenToCarrier M.A_lifted =
          matrixEvenToCarrier (M.A_lifted⁻¹ * M.A_lifted) := by
        ext i j
        simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [← Λ.evenToCarrier.map_mul]
      rw [hA_inv_A, hAinvA_lifted]
      ext i j
      simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply]
      split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
    have h_distrib : M.Cblock * M.A_inv_carrier * (M.Ablock * B' + M.Bblock) =
                     M.Cblock * B' + M.Cblock * M.A_inv_carrier * M.Bblock := by
      have h1' : M.Cblock * M.A_inv_carrier * M.Ablock = M.Cblock := by
        calc M.Cblock * M.A_inv_carrier * M.Ablock
            = M.Cblock * (M.A_inv_carrier * M.Ablock) := by rw [Matrix.mul_assoc]
          _ = M.Cblock * (1 : Matrix _ _ _) := by rw [hAinvA]
          _ = M.Cblock := by rw [Matrix.mul_one]
      rw [Matrix.mul_add]
      congr 1
      calc M.Cblock * M.A_inv_carrier * (M.Ablock * B')
          = M.Cblock * (M.A_inv_carrier * (M.Ablock * B')) := by rw [Matrix.mul_assoc]
        _ = M.Cblock * ((M.A_inv_carrier * M.Ablock) * B') := by rw [Matrix.mul_assoc]
        _ = M.Cblock * ((1 : Matrix _ _ _) * B') := by rw [hAinvA]
        _ = M.Cblock * B' := by rw [Matrix.one_mul]
    rw [h_distrib]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply]
    abel
  -- Now show the berAlt values are equal
  have h_lift_eq : Λ.liftEvenMatrix (M * U).schurA_carrier ((M * U).schurA_even hMUCAinv) =
      Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hMCAinv) := by
    ext i j
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec, hSchurA_eq]
  have h_det_eq : (Λ.liftEvenMatrix (M * U).schurA_carrier ((M * U).schurA_even hMUCAinv)).det =
      (Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hMCAinv)).det := by
    rw [h_lift_eq]
  have h_inv_eq : Λ.inv (Λ.liftEvenMatrix (M * U).schurA_carrier ((M * U).schurA_even hMUCAinv)).det hMUSchurA =
      Λ.inv (Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hMCAinv)).det hMSchurA := by
    have h_left : (Λ.liftEvenMatrix (M * U).schurA_carrier ((M * U).schurA_even hMUCAinv)).det *
        Λ.inv (Λ.liftEvenMatrix (M * U).schurA_carrier ((M * U).schurA_even hMUCAinv)).det hMUSchurA = 1 :=
      Λ.mul_inv _ hMUSchurA
    have h_right : (Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hMCAinv)).det *
        Λ.inv (Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hMCAinv)).det hMSchurA = 1 :=
      Λ.mul_inv _ hMSchurA
    have h_left' : (Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hMCAinv)).det *
        Λ.inv (Λ.liftEvenMatrix (M * U).schurA_carrier ((M * U).schurA_even hMUCAinv)).det hMUSchurA = 1 := by
      rw [← h_det_eq]; exact h_left
    calc Λ.inv (Λ.liftEvenMatrix (M * U).schurA_carrier _).det hMUSchurA
        = 1 * Λ.inv (Λ.liftEvenMatrix (M * U).schurA_carrier _).det hMUSchurA := (one_mul _).symm
      _ = (Λ.inv (Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hMCAinv)).det hMSchurA *
           (Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hMCAinv)).det) *
          Λ.inv (Λ.liftEvenMatrix (M * U).schurA_carrier _).det hMUSchurA := by
          rw [Λ.inv_mul _ hMSchurA]
      _ = Λ.inv (Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hMCAinv)).det hMSchurA *
          ((Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hMCAinv)).det *
           Λ.inv (Λ.liftEvenMatrix (M * U).schurA_carrier _).det hMUSchurA) := by ring
      _ = Λ.inv (Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hMCAinv)).det hMSchurA * 1 := by rw [h_left']
      _ = Λ.inv (Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hMCAinv)).det hMSchurA := mul_one _
  -- Goal: (M * U).A_lifted.det * inv(...) = M.A_lifted.det * inv(...)
  -- Since (M * U) = (M * upperTriangular ...), need to show they match
  show (M * U).A_lifted.det * Λ.inv (Λ.liftEvenMatrix (M * U).schurA_carrier _).det hMUSchurA =
       M.A_lifted.det * Λ.inv (Λ.liftEvenMatrix M.schurA_carrier _).det hMSchurA
  rw [hA_lifted_det_eq, h_inv_eq]

/-- Ber([A' 0; 0 D']) = det(A'_lifted) · inv(det(D'_lifted)).
    For a diagonal supermatrix, the Berezinian is det(A) * det(D)⁻¹ computed on evenCarrier. -/
theorem SuperMatrix.ber_diagonal {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ}
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (D' : Matrix (Fin m) (Fin m) Λ.carrier)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hA' : ∀ i j, A' i j ∈ Λ.even) (hD' : ∀ i j, D' i j ∈ Λ.even)
    (hD : Λ.IsInvertible (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det)
    (hBDinv : ∀ i j, ((SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock *
        (SuperMatrix.diagonal A' D' h0odd hA' hD').D_inv_carrier) i j ∈ Λ.odd) :
    (SuperMatrix.diagonal A' D' h0odd hA' hD').ber hD hBDinv =
    (Λ.liftEvenMatrix A' hA').det * Λ.inv (Λ.liftEvenMatrix D' hD').det hD := by
  unfold SuperMatrix.ber
  -- The diagonal supermatrix has Bblock = 0 and Cblock = 0
  have hBblock : (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock = 0 := rfl
  have hCblock : (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock = 0 := rfl
  have hAblock : (SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock = A' := rfl
  have hDblock : (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock = D' := rfl
  -- schurD_carrier = A - B * D_inv_carrier * C = A - 0 * ... * 0 = A
  have hSchurD : (SuperMatrix.diagonal A' D' h0odd hA' hD').schurD_carrier = A' := by
    unfold SuperMatrix.schurD_carrier
    rw [hAblock, hBblock, hCblock]
    ext i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply, zero_mul,
               Finset.sum_const_zero, sub_zero]
  -- D_lifted for diagonal = lift(D')
  have hD_lifted_eq : (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted = Λ.liftEvenMatrix D' hD' := by
    ext i j
    simp only [SuperMatrix.D_lifted]
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec]
    rfl
  -- schurD_lifted = lift(A')
  have hSchurD_lifted : Λ.liftEvenMatrix (SuperMatrix.diagonal A' D' h0odd hA' hD').schurD_carrier
      ((SuperMatrix.diagonal A' D' h0odd hA' hD').schurD_even hBDinv) = Λ.liftEvenMatrix A' hA' := by
    ext i j
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec, hSchurD]
  simp only []
  rw [hSchurD_lifted]
  -- Now need to show the inverses are equal
  -- Goal: det(A') * inv(D_lifted.det) = det(A') * inv(lift(D').det)
  -- Since D_lifted = lift(D'), they have the same det, so inverses are equal
  have h_det_eq : (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det = (Λ.liftEvenMatrix D' hD').det := by
    rw [hD_lifted_eq]
  have hD_inv : Λ.IsInvertible (Λ.liftEvenMatrix D' hD').det := by
    rw [← h_det_eq]; exact hD
  have h_inv_eq : Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hD =
      Λ.inv (Λ.liftEvenMatrix D' hD').det hD_inv := by
    have h_left : (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det *
        Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hD = 1 := Λ.mul_inv _ hD
    have h_left' : (Λ.liftEvenMatrix D' hD').det *
        Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hD = 1 := by
      rw [← h_det_eq]; exact h_left
    calc Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hD
        = 1 * Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hD := (one_mul _).symm
      _ = (Λ.inv (Λ.liftEvenMatrix D' hD').det hD_inv * (Λ.liftEvenMatrix D' hD').det) *
          Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hD := by rw [Λ.inv_mul _ hD_inv]
      _ = Λ.inv (Λ.liftEvenMatrix D' hD').det hD_inv *
          ((Λ.liftEvenMatrix D' hD').det * Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hD) := by ring
      _ = Λ.inv (Λ.liftEvenMatrix D' hD').det hD_inv * 1 := by rw [h_left']
      _ = Λ.inv (Λ.liftEvenMatrix D' hD').det hD_inv := mul_one _
  rw [h_inv_eq]

/-- Product of two upper triangular supermatrices has C-block = 0. -/
theorem SuperMatrix.upperTriangular_mul_Cblock_zero {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
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
theorem SuperMatrix.diagonal_mul_upper_Cblock_zero {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ}
    (Δ U : SuperMatrix Λ n m)
    (_hΔB : Δ.Bblock = 0) (hΔC : Δ.Cblock = 0)
    (hUA : U.Ablock = 1) (hUC : U.Cblock = 0) (_hUD : U.Dblock = 1) :
    (Δ * U).Cblock = 0 := by
  show Δ.Cblock * U.Ablock + Δ.Dblock * U.Cblock = 0
  rw [hΔC, hUA, hUC]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]

/-- Multiplying a C=0 supermatrix by diagonal on right preserves C=0. -/
theorem SuperMatrix.Cblock_zero_mul_diagonal_Cblock_zero {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ}
    (Y Δ' : SuperMatrix Λ n m)
    (hYC : Y.Cblock = 0)
    (_hΔ'B : Δ'.Bblock = 0) (hΔ'C : Δ'.Cblock = 0) :
    (Y * Δ').Cblock = 0 := by
  show Y.Cblock * Δ'.Ablock + Y.Dblock * Δ'.Cblock = 0
  rw [hYC, hΔ'C]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]

/-- When Y has C-block = 0, multiplying by lower triangular on right preserves D-block. -/
theorem SuperMatrix.Cblock_zero_mul_lower_Dblock {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ}
    (Y L : SuperMatrix Λ n m)
    (hYC : Y.Cblock = 0)
    (_hLA : L.Ablock = 1) (hLB : L.Bblock = 0) (hLD : L.Dblock = 1) :
    (Y * L).Dblock = Y.Dblock := by
  show Y.Cblock * L.Bblock + Y.Dblock * L.Dblock = Y.Dblock
  rw [hYC, hLB, hLD]
  simp only [Matrix.zero_mul, Matrix.mul_one, zero_add]

/-- When Y has C-block = 0, Y·L has the same Schur complement as Y.
    Note: This version uses D_lifted.det for invertibility on evenCarrier. -/
theorem SuperMatrix.Cblock_zero_mul_lower_schur {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ}
    (Y L : SuperMatrix Λ n m)
    (hYC : Y.Cblock = 0)
    (hLA : L.Ablock = 1) (hLB : L.Bblock = 0) (hLD : L.Dblock = 1)
    (hD : Λ.IsInvertible Y.D_lifted.det)
    (hYLD_lifted_eq : (Y * L).D_lifted = Y.D_lifted) :
    (Y * L).schurD_carrier = Y.schurD_carrier := by
  unfold SuperMatrix.schurD_carrier
  have hYLA : (Y * L).Ablock = Y.Ablock * L.Ablock + Y.Bblock * L.Cblock := rfl
  have hYLB : (Y * L).Bblock = Y.Ablock * L.Bblock + Y.Bblock * L.Dblock := rfl
  have hYLC : (Y * L).Cblock = Y.Cblock * L.Ablock + Y.Dblock * L.Cblock := rfl
  have hYLD : (Y * L).Dblock = Y.Dblock := SuperMatrix.Cblock_zero_mul_lower_Dblock Y L hYC hLA hLB hLD
  simp only [hLA, hLB, hLD, Matrix.mul_one, Matrix.mul_zero, zero_add] at hYLA hYLB hYLC
  simp only [hYC, zero_add] at hYLC
  simp only [hYLA, hYLB, hYLC]
  -- (Y * L).D_inv_carrier = Y.D_inv_carrier since D_lifted is the same
  have hD_inv_eq : (Y * L).D_inv_carrier = Y.D_inv_carrier := by
    unfold SuperMatrix.D_inv_carrier
    rw [hYLD_lifted_eq]
  rw [hD_inv_eq]
  -- Now goal: Y.Ablock - Y.Bblock * Y.D_inv_carrier * L.Cblock = Y.Ablock - Y.Bblock * Y.D_inv_carrier * Y.Cblock
  -- Since L.Cblock is from lower triangular, we need to determine what it is
  -- Actually, L is lower triangular with L.Cblock being the C' parameter
  -- But since Y.Cblock = 0, the result simplifies
  haveI : Invertible Y.D_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hD).invertible
  haveI : Invertible Y.D_lifted := Matrix.invertibleOfDetInvertible Y.D_lifted
  have hYDinv : Y.Dblock * Y.D_inv_carrier = 1 := by
    have hD_inv_def : Y.D_inv_carrier = matrixEvenToCarrier Y.D_lifted⁻¹ := rfl
    have hD_lifted_carrier : matrixEvenToCarrier Y.D_lifted = Y.Dblock := by
      ext i j
      simp only [matrixEvenToCarrier, Matrix.map_apply, SuperMatrix.D_lifted]
      exact Λ.liftEvenMatrix_spec Y.Dblock Y.Dblock_even i j
    have hDDinv_lifted : Y.D_lifted * Y.D_lifted⁻¹ = 1 := Matrix.mul_nonsing_inv Y.D_lifted (isUnit_of_invertible _)
    rw [hD_inv_def, ← hD_lifted_carrier]
    have hD_D_inv : matrixEvenToCarrier Y.D_lifted * matrixEvenToCarrier Y.D_lifted⁻¹ =
        matrixEvenToCarrier (Y.D_lifted * Y.D_lifted⁻¹) := by
      ext i j
      simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Λ.evenToCarrier.map_mul]
    rw [hD_D_inv, hDDinv_lifted]
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
  -- Goal: Y.Ablock + Y.Bblock * L.Cblock - Y.Bblock * Y.D_inv_carrier * (Y.Dblock * L.Cblock) = Y.Ablock
  -- Simplify: Y.Bblock * Y.D_inv_carrier * (Y.Dblock * L.Cblock) = Y.Bblock * (Y.D_inv_carrier * Y.Dblock) * L.Cblock
  --         = Y.Bblock * 1 * L.Cblock (using D_inv * D = 1... but we have D * D_inv = 1)
  -- Actually we need D_inv * D = 1
  have hDinvD : Y.D_inv_carrier * Y.Dblock = 1 := by
    have hD_inv_def : Y.D_inv_carrier = matrixEvenToCarrier Y.D_lifted⁻¹ := rfl
    have hD_lifted_carrier : matrixEvenToCarrier Y.D_lifted = Y.Dblock := by
      ext i j
      simp only [matrixEvenToCarrier, Matrix.map_apply, SuperMatrix.D_lifted]
      exact Λ.liftEvenMatrix_spec Y.Dblock Y.Dblock_even i j
    have hDinvD_lifted : Y.D_lifted⁻¹ * Y.D_lifted = 1 := Matrix.nonsing_inv_mul Y.D_lifted (isUnit_of_invertible _)
    rw [hD_inv_def, ← hD_lifted_carrier]
    have hD_inv_D : matrixEvenToCarrier Y.D_lifted⁻¹ * matrixEvenToCarrier Y.D_lifted =
        matrixEvenToCarrier (Y.D_lifted⁻¹ * Y.D_lifted) := by
      ext i j
      simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Λ.evenToCarrier.map_mul]
    rw [hD_inv_D, hDinvD_lifted]
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
  -- Now: Y.Bblock * Y.D_inv_carrier * (Y.Dblock * L.Cblock) = Y.Bblock * (Y.D_inv_carrier * Y.Dblock) * L.Cblock
  --    = Y.Bblock * 1 * L.Cblock = Y.Bblock * L.Cblock
  have h_cancel : Y.Bblock * Y.D_inv_carrier * (Y.Dblock * L.Cblock) = Y.Bblock * L.Cblock := by
    calc Y.Bblock * Y.D_inv_carrier * (Y.Dblock * L.Cblock)
        = Y.Bblock * (Y.D_inv_carrier * (Y.Dblock * L.Cblock)) := by rw [Matrix.mul_assoc]
      _ = Y.Bblock * ((Y.D_inv_carrier * Y.Dblock) * L.Cblock) := by rw [Matrix.mul_assoc]
      _ = Y.Bblock * ((1 : Matrix (Fin m) (Fin m) _) * L.Cblock) := by rw [hDinvD]
      _ = Y.Bblock * L.Cblock := by rw [Matrix.one_mul]
  rw [h_cancel]
  -- Goal: Y.Ablock + Y.Bblock * L.Cblock - Y.Bblock * L.Cblock = Y.Ablock - Y.Bblock * Y.D_inv_carrier * Y.Cblock
  -- Since Y.Cblock = 0, RHS = Y.Ablock - Y.Bblock * Y.D_inv_carrier * 0 = Y.Ablock
  simp only [hYC, Matrix.mul_zero, sub_zero, add_sub_cancel_right]

/-- Ber(U * N) = Ber(N) when U = [I B'; 0 I] is upper triangular. -/
theorem SuperMatrix.ber_mul_upperTriangular_left {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (N : SuperMatrix Λ n m)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hB' : ∀ i j, B' i j ∈ Λ.odd)
    (hND : Λ.IsInvertible N.D_lifted.det)
    (hNBDinv : ∀ i j, (N.Bblock * N.D_inv_carrier) i j ∈ Λ.odd)
    (_hUD : Λ.IsInvertible (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').D_lifted.det)
    (_hUBDinv : ∀ i j, ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Bblock *
        (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').D_inv_carrier) i j ∈ Λ.odd)
    (hUND : Λ.IsInvertible ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB') * N).D_lifted.det)
    (hUNBDinv : ∀ i j, (((SuperMatrix.upperTriangular B' h1 h0even h0odd hB') * N).Bblock *
        ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB') * N).D_inv_carrier) i j ∈ Λ.odd) :
    ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB') * N).ber hUND hUNBDinv =
    N.ber hND hNBDinv := by
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
  -- (U*N).D_lifted = N.D_lifted since Dblock is the same
  have hUND_lifted_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).D_lifted = N.D_lifted := by
    ext i j
    simp only [SuperMatrix.D_lifted]
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec]
    exact congrFun (congrFun hUND_eq i) j
  have hD_lifted_det_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).D_lifted.det = N.D_lifted.det := by
    rw [hUND_lifted_eq]
  have hD_inv_carrier_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).D_inv_carrier = N.D_inv_carrier := by
    unfold SuperMatrix.D_inv_carrier
    rw [hUND_lifted_eq]
  -- schurD_carrier = A - B * D_inv_carrier * C
  have hSchurD_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).schurD_carrier = N.schurD_carrier := by
    unfold SuperMatrix.schurD_carrier
    rw [hUNA_eq, hUNB_eq, hUNC_eq, hD_inv_carrier_eq]
    -- Goal: (N.Ablock + B' * N.Cblock) - (N.Bblock + B' * N.Dblock) * N.D_inv_carrier * N.Cblock
    --     = N.Ablock - N.Bblock * N.D_inv_carrier * N.Cblock
    haveI : Invertible N.D_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hND).invertible
    haveI : Invertible N.D_lifted := Matrix.invertibleOfDetInvertible N.D_lifted
    have h_DinvD : N.Dblock * N.D_inv_carrier = 1 := by
      have hD_inv_def : N.D_inv_carrier = matrixEvenToCarrier N.D_lifted⁻¹ := rfl
      have hD_lifted_carrier : matrixEvenToCarrier N.D_lifted = N.Dblock := by
        ext i j
        simp only [matrixEvenToCarrier, Matrix.map_apply, SuperMatrix.D_lifted]
        exact Λ.liftEvenMatrix_spec N.Dblock N.Dblock_even i j
      have hDDinv_lifted : N.D_lifted * N.D_lifted⁻¹ = 1 := Matrix.mul_nonsing_inv N.D_lifted (isUnit_of_invertible _)
      rw [hD_inv_def, ← hD_lifted_carrier]
      have hD_D_inv : matrixEvenToCarrier N.D_lifted * matrixEvenToCarrier N.D_lifted⁻¹ =
          matrixEvenToCarrier (N.D_lifted * N.D_lifted⁻¹) := by
        ext i j
        simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [← Λ.evenToCarrier.map_mul]
      rw [hD_D_inv, hDDinv_lifted]
      ext i j
      simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply]
      split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
    have h_cancel : B' * N.Dblock * N.D_inv_carrier * N.Cblock = B' * N.Cblock := by
      calc B' * N.Dblock * N.D_inv_carrier * N.Cblock
          = B' * N.Dblock * (N.D_inv_carrier * N.Cblock) := by rw [Matrix.mul_assoc]
        _ = B' * (N.Dblock * (N.D_inv_carrier * N.Cblock)) := by rw [Matrix.mul_assoc]
        _ = B' * ((N.Dblock * N.D_inv_carrier) * N.Cblock) := by rw [← Matrix.mul_assoc N.Dblock]
        _ = B' * ((1 : Matrix _ _ _) * N.Cblock) := by rw [h_DinvD]
        _ = B' * N.Cblock := by rw [Matrix.one_mul]
    have h_distrib : (N.Bblock + B' * N.Dblock) * N.D_inv_carrier * N.Cblock =
                     N.Bblock * N.D_inv_carrier * N.Cblock + B' * N.Cblock := by
      rw [Matrix.add_mul, Matrix.add_mul, h_cancel]
    rw [h_distrib]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply]
    abel
  -- Now show the ber values are equal
  have h_lift_eq : Λ.liftEvenMatrix (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).schurD_carrier
      ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).schurD_even hUNBDinv) =
      Λ.liftEvenMatrix N.schurD_carrier (N.schurD_even hNBDinv) := by
    ext i j
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec, hSchurD_eq]
  have h_det_eq : (Λ.liftEvenMatrix (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).schurD_carrier
      ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).schurD_even hUNBDinv)).det =
      (Λ.liftEvenMatrix N.schurD_carrier (N.schurD_even hNBDinv)).det := by
    rw [h_lift_eq]
  have hND_inv : Λ.IsInvertible N.D_lifted.det := hND
  have h_inv_eq : Λ.inv (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).D_lifted.det hUND =
      Λ.inv N.D_lifted.det hND_inv := by
    have h_left : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).D_lifted.det *
        Λ.inv (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).D_lifted.det hUND = 1 := Λ.mul_inv _ hUND
    have h_left' : N.D_lifted.det *
        Λ.inv (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).D_lifted.det hUND = 1 := by
      rw [← hD_lifted_det_eq]; exact h_left
    calc Λ.inv (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).D_lifted.det hUND
        = 1 * Λ.inv (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).D_lifted.det hUND := (one_mul _).symm
      _ = (Λ.inv N.D_lifted.det hND_inv * N.D_lifted.det) *
          Λ.inv (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).D_lifted.det hUND := by rw [Λ.inv_mul _ hND_inv]
      _ = Λ.inv N.D_lifted.det hND_inv *
          (N.D_lifted.det * Λ.inv (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).D_lifted.det hUND) := by ring
      _ = Λ.inv N.D_lifted.det hND_inv * 1 := by rw [h_left']
      _ = Λ.inv N.D_lifted.det hND_inv := mul_one _
  simp only []
  rw [h_det_eq, h_inv_eq]

/-- Ber(M * L) = Ber(M) when L = [I 0; C' I] is lower triangular.
    Note: This version uses D_lifted.det for invertibility on evenCarrier. -/
theorem SuperMatrix.ber_mul_lowerTriangular_right {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (M : SuperMatrix Λ n m)
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd)
    (hMD : Λ.IsInvertible M.D_lifted.det)
    (_hLD : Λ.IsInvertible (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det)
    (hMLD : Λ.IsInvertible (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det)
    (hBDinv : ∀ i j, (M.Bblock * M.D_inv_carrier) i j ∈ Λ.odd) :
    (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').ber hMLD
      (by -- hBDinv for (M * L): Bblock and D_inv_carrier are the same as M
          have hMLB_eq : (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock = M.Bblock := by
            show M.Ablock * (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock +
                 M.Bblock * (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock = M.Bblock
            simp only [SuperMatrix.lowerTriangular, Matrix.mul_zero, Matrix.mul_one, zero_add]
          have hMLD_eq : (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock = M.Dblock := by
            show M.Cblock * (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock +
                 M.Dblock * (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock = M.Dblock
            simp only [SuperMatrix.lowerTriangular, Matrix.mul_zero, Matrix.mul_one, zero_add]
          have hMLD_lifted_eq : (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted = M.D_lifted := by
            ext i j
            simp only [SuperMatrix.D_lifted]
            apply Λ.evenToCarrier_injective
            rw [Λ.liftEvenMatrix_spec _ (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock_even i j]
            rw [Λ.liftEvenMatrix_spec _ M.Dblock_even i j]
            rw [hMLD_eq]
          have hD_inv_carrier_eq : (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_inv_carrier = M.D_inv_carrier := by
            unfold SuperMatrix.D_inv_carrier
            rw [hMLD_lifted_eq]
          intro i j
          rw [hMLB_eq, hD_inv_carrier_eq]
          exact hBDinv i j) =
    M.ber hMD hBDinv := by
  -- Prove the key equalities for (M * L)
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
  -- D_lifted is the same, so D_inv_carrier is the same
  have hMLD_lifted_eq : (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted = M.D_lifted := by
    ext i j
    simp only [SuperMatrix.D_lifted]
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec _ (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock_even i j]
    rw [Λ.liftEvenMatrix_spec _ M.Dblock_even i j]
    rw [hMLD_eq]
  have hD_inv_carrier_eq : (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_inv_carrier = M.D_inv_carrier := by
    unfold SuperMatrix.D_inv_carrier
    rw [hMLD_lifted_eq]
  -- Setup for inverse calculation
  haveI : Invertible M.D_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hMD).invertible
  haveI : Invertible M.D_lifted := Matrix.invertibleOfDetInvertible M.D_lifted
  have h_DinvD : M.D_inv_carrier * M.Dblock = 1 := by
    have hD_inv_def : M.D_inv_carrier = matrixEvenToCarrier M.D_lifted⁻¹ := rfl
    have hD_lifted_carrier : matrixEvenToCarrier M.D_lifted = M.Dblock := by
      ext i j
      simp only [matrixEvenToCarrier, Matrix.map_apply, SuperMatrix.D_lifted]
      exact Λ.liftEvenMatrix_spec M.Dblock M.Dblock_even i j
    have hDinvD_lifted : M.D_lifted⁻¹ * M.D_lifted = 1 := Matrix.nonsing_inv_mul M.D_lifted (isUnit_of_invertible _)
    rw [hD_inv_def, ← hD_lifted_carrier]
    have hD_inv_D : matrixEvenToCarrier M.D_lifted⁻¹ * matrixEvenToCarrier M.D_lifted =
        matrixEvenToCarrier (M.D_lifted⁻¹ * M.D_lifted) := by
      ext i j
      simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Λ.evenToCarrier.map_mul]
    rw [hD_inv_D, hDinvD_lifted]
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
  -- The schurD_carrier of (M * L) equals schurD_carrier of M
  have hSchurD_carrier_eq : (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').schurD_carrier = M.schurD_carrier := by
    unfold SuperMatrix.schurD_carrier
    rw [hMLA_eq, hMLB_eq, hMLC_eq, hD_inv_carrier_eq]
    have h_distrib : M.Bblock * M.D_inv_carrier * (M.Cblock + M.Dblock * C') =
                     M.Bblock * M.D_inv_carrier * M.Cblock + M.Bblock * C' := by
      rw [Matrix.mul_add]
      congr 1
      calc M.Bblock * M.D_inv_carrier * (M.Dblock * C')
          = M.Bblock * (M.D_inv_carrier * (M.Dblock * C')) := by rw [Matrix.mul_assoc]
        _ = M.Bblock * ((M.D_inv_carrier * M.Dblock) * C') := by rw [Matrix.mul_assoc]
        _ = M.Bblock * ((1 : Matrix (Fin m) (Fin m) Λ.carrier) * C') := by rw [h_DinvD]
        _ = M.Bblock * C' := by rw [Matrix.one_mul]
    rw [h_distrib]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply]
    abel
  -- Now prove the main equality by showing each component
  simp only [SuperMatrix.ber]
  -- We need to show that:
  -- schurD_lifted.det * Λ.inv (M * L).D_lifted.det hMLD = schurD_lifted'.det * Λ.inv M.D_lifted.det hMD
  -- First, det equalities
  have h_det_eq : (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det = M.D_lifted.det := by
    rw [hMLD_lifted_eq]
  -- Use inverse uniqueness to show inverses are equal
  have h_inv_eq : Λ.inv (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det hMLD =
                  Λ.inv M.D_lifted.det hMD := by
    have h_left : M.D_lifted.det * Λ.inv M.D_lifted.det hMD = 1 := Λ.mul_inv _ hMD
    have h_left' : (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det *
                   Λ.inv M.D_lifted.det hMD = 1 := by rw [h_det_eq]; exact h_left
    have h_right : (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det *
                   Λ.inv (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det hMLD = 1 :=
      Λ.mul_inv _ hMLD
    -- Both Λ.inv M.D_lifted.det hMD and Λ.inv (M*L).D_lifted.det hMLD are right inverses
    -- of the same element (M*L).D_lifted.det = M.D_lifted.det, so they're equal
    have h_right' : M.D_lifted.det *
                   Λ.inv (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det hMLD = 1 := by
      calc M.D_lifted.det * Λ.inv (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det hMLD
          = (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det *
            Λ.inv (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det hMLD := by
              rw [← h_det_eq]
        _ = 1 := h_right
    -- Now use uniqueness: if a * x = 1 and a * y = 1, then x = y (in a commutative ring)
    -- Both are right inverses of the same element, so they're equal
    have h_both_right_inv :
        Λ.inv (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det hMLD =
        Λ.inv M.D_lifted.det hMD := by
      -- They're both inverses of the same determinant value
      have hmul1 : M.D_lifted.det * Λ.inv M.D_lifted.det hMD = 1 := Λ.mul_inv _ hMD
      have hmul2 : M.D_lifted.det * Λ.inv (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det hMLD = 1 := h_right'
      -- In a commutative ring, right inverse is unique
      have hinv1 : Λ.inv M.D_lifted.det hMD * M.D_lifted.det = 1 := Λ.inv_mul _ hMD
      -- x * y = 1 and x * z = 1 implies y = z (multiply both by y⁻¹ on the left)
      calc Λ.inv (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det hMLD
          = 1 * Λ.inv (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det hMLD := by rw [one_mul]
        _ = (Λ.inv M.D_lifted.det hMD * M.D_lifted.det) *
            Λ.inv (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det hMLD := by rw [hinv1]
        _ = Λ.inv M.D_lifted.det hMD *
            (M.D_lifted.det * Λ.inv (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det hMLD) := by
              group
        _ = Λ.inv M.D_lifted.det hMD * 1 := by rw [hmul2]
        _ = Λ.inv M.D_lifted.det hMD := by rw [mul_one]
    exact h_both_right_inv
  -- hBDinv for (M * L) follows from hMLB_eq and hD_inv_carrier_eq
  have hBDinv_ML : ∀ i j, ((M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock *
      (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_inv_carrier) i j ∈ Λ.odd := by
    intro i j
    rw [hMLB_eq, hD_inv_carrier_eq]
    exact hBDinv i j
  -- Now show schurD_lifted are the same
  have h_schurD_lifted_eq : Λ.liftEvenMatrix (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').schurD_carrier
      ((M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').schurD_even hBDinv_ML) =
      Λ.liftEvenMatrix M.schurD_carrier (M.schurD_even hBDinv) := by
    ext i j
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec]
    rw [Λ.liftEvenMatrix_spec]
    rw [hSchurD_carrier_eq]
  -- Final step: use congrArg to combine
  have h_det_schur_eq : (Λ.liftEvenMatrix (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').schurD_carrier
      ((M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').schurD_even hBDinv_ML)).det =
      (Λ.liftEvenMatrix M.schurD_carrier (M.schurD_even hBDinv)).det := by
    rw [h_schurD_lifted_eq]
  rw [h_det_schur_eq, h_inv_eq]

/-- Ber(U · Δ · L) = Ber(Δ) when U is upper triangular, Δ is diagonal, L is lower triangular.
    Note: This version uses D_lifted.det for invertibility on evenCarrier. -/
theorem SuperMatrix.ber_UDL {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (D' : Matrix (Fin m) (Fin m) Λ.carrier)
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hB' : ∀ i j, B' i j ∈ Λ.odd)
    (hA' : ∀ i j, A' i j ∈ Λ.even) (hD' : ∀ i j, D' i j ∈ Λ.even)
    (hC' : ∀ i j, C' i j ∈ Λ.odd)
    (_hD'det : Λ.IsInvertible (Λ.liftEvenMatrix D' hD').det)
    (_hUD : Λ.IsInvertible (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').D_lifted.det)
    (hΔD : Λ.IsInvertible (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det)
    (_hLD : Λ.IsInvertible (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det)
    (hΔLD : Λ.IsInvertible ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
            (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC')).D_lifted.det)
    (hUΔLD : Λ.IsInvertible ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB') *
             ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
              (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC'))).D_lifted.det)
    (hBDinv_UDL : ∀ i j, (((SuperMatrix.upperTriangular B' h1 h0even h0odd hB') *
             ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
              (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC'))).Bblock *
             ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB') *
             ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
              (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC'))).D_inv_carrier) i j ∈ Λ.odd)
    (hBDinv_DL : ∀ i j, (((SuperMatrix.diagonal A' D' h0odd hA' hD') *
            (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC')).Bblock *
            ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
            (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC')).D_inv_carrier) i j ∈ Λ.odd)
    (hBDinv_D : ∀ i j, ((SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock *
            (SuperMatrix.diagonal A' D' h0odd hA' hD').D_inv_carrier) i j ∈ Λ.odd)
    (hBDinv_U : ∀ i j, ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Bblock *
            (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').D_inv_carrier) i j ∈ Λ.odd) :
    ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB') *
     ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
      (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC'))).ber hUΔLD hBDinv_UDL =
    (SuperMatrix.diagonal A' D' h0odd hA' hD').ber hΔD hBDinv_D := by
  -- Apply the upper triangular theorem first
  -- Signature: B' N h1 h0even h0odd hB' hND hNBDinv hUD hUBDinv hUND hUNBDinv
  have hBerUΔL := SuperMatrix.ber_mul_upperTriangular_left B'
    ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
     (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC'))
    h1 h0even h0odd hB' hΔLD hBDinv_DL _hUD hBDinv_U hUΔLD hBDinv_UDL
  -- Then apply the lower triangular theorem
  have hBerΔL := SuperMatrix.ber_mul_lowerTriangular_right
    (SuperMatrix.diagonal A' D' h0odd hA' hD')
    C' h1 h0even h0odd hC' hΔD _hLD hΔLD hBDinv_D
  rw [hBerUΔL, hBerΔL]

/-- Ber(L · Δ · U) = Ber(Δ) when L is lower triangular, Δ is diagonal, U is upper triangular.
    Note: This version uses D_lifted.det for invertibility on evenCarrier. -/
theorem SuperMatrix.ber_LDU {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (D' : Matrix (Fin m) (Fin m) Λ.carrier)
    (B' : Matrix (Fin n) (Fin m) Λ.carrier)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hC' : ∀ i j, C' i j ∈ Λ.odd)
    (hA' : ∀ i j, A' i j ∈ Λ.even) (hD' : ∀ i j, D' i j ∈ Λ.even)
    (hB' : ∀ i j, B' i j ∈ Λ.odd)
    (hA'det : Λ.IsInvertible (Λ.liftEvenMatrix A' hA').det)  -- Key: A' must be invertible for LDU
    (_hD'det : Λ.IsInvertible (Λ.liftEvenMatrix D' hD').det)
    (_hLD : Λ.IsInvertible (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det)
    (hΔD : Λ.IsInvertible (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det)
    (_hUD : Λ.IsInvertible (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').D_lifted.det)
    (hLΔD : Λ.IsInvertible ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
            (SuperMatrix.diagonal A' D' h0odd hA' hD')).D_lifted.det)
    (hLΔUD : Λ.IsInvertible (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
              (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
             (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).D_lifted.det)
    -- Parity conditions for Bblock * D_inv_carrier
    (hBDinv_LDU : ∀ i j, ((((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
              (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
             (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Bblock *
             (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
              (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
             (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).D_inv_carrier) i j ∈ Λ.odd)
    (hBDinv_LD : ∀ i j, (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
            (SuperMatrix.diagonal A' D' h0odd hA' hD')).Bblock *
            ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
            (SuperMatrix.diagonal A' D' h0odd hA' hD')).D_inv_carrier) i j ∈ Λ.odd)
    (hBDinv_D : ∀ i j, ((SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock *
            (SuperMatrix.diagonal A' D' h0odd hA' hD').D_inv_carrier) i j ∈ Λ.odd)
    (_hBDinv_L : ∀ i j, ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock *
            (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_inv_carrier) i j ∈ Λ.odd)
    (_hBDinv_U : ∀ i j, ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Bblock *
            (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').D_inv_carrier) i j ∈ Λ.odd) :
    (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
      (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
     (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).ber hLΔUD hBDinv_LDU =
    (SuperMatrix.diagonal A' D' h0odd hA' hD').ber hΔD hBDinv_D := by
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
                   (SuperMatrix.diagonal A' D' h0odd hA' hD')).A_lifted.det := by
    have h_A_lifted_eq : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
        (SuperMatrix.diagonal A' D' h0odd hA' hD')).A_lifted = Λ.liftEvenMatrix A' hA' := by
      ext i j
      simp only [SuperMatrix.A_lifted]
      apply Λ.evenToCarrier_injective
      rw [Λ.liftEvenMatrix_spec _ ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')).Ablock_even i j]
      rw [Λ.liftEvenMatrix_spec _ hA' i j]
      rw [hLΔA]
    rw [h_A_lifted_eq]; exact hA'det
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
                    (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).A_lifted.det := by
    have h_A_lifted_eq : (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
        (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
        (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).A_lifted = Λ.liftEvenMatrix A' hA' := by
      ext i j
      simp only [SuperMatrix.A_lifted]
      apply Λ.evenToCarrier_injective
      rw [Λ.liftEvenMatrix_spec _ (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
          (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Ablock_even i j]
      rw [Λ.liftEvenMatrix_spec _ hA' i j]
      rw [hLΔUA]
    rw [h_A_lifted_eq]; exact hA'det
  have hBerLΔ : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                (SuperMatrix.diagonal A' D' h0odd hA' hD')).ber hLΔD hBDinv_LD =
               (SuperMatrix.diagonal A' D' h0odd hA' hD').ber hΔD hBDinv_D := by
    -- Key: (L * Δ).Bblock = 0, so Schur complement simplifies to Ablock = A'
    -- And (L * Δ).Dblock = D', same as Δ.Dblock
    -- The schur complement of L*Δ (with B=0) is just A'
    have hSchurLΔ_carrier : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
        (SuperMatrix.diagonal A' D' h0odd hA' hD')).schurD_carrier = A' := by
      unfold SuperMatrix.schurD_carrier
      rw [hLΔA, hLΔB]
      simp only [Matrix.zero_mul, sub_zero]
    -- The schur complement of Δ (with B=0) is also A'
    have hSchurΔ_carrier : (SuperMatrix.diagonal A' D' h0odd hA' hD').schurD_carrier = A' := by
      unfold SuperMatrix.schurD_carrier
      simp only [SuperMatrix.diagonal, Matrix.zero_mul, sub_zero]
    -- D_lifted for L*Δ equals D_lifted for Δ (both equal Λ.liftEvenMatrix D' hD')
    have hLΔ_D_lifted_eq : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
        (SuperMatrix.diagonal A' D' h0odd hA' hD')).D_lifted =
        (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted := by
      ext i j
      simp only [SuperMatrix.D_lifted]
      apply Λ.evenToCarrier_injective
      rw [Λ.liftEvenMatrix_spec _ ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')).Dblock_even i j]
      rw [Λ.liftEvenMatrix_spec _ (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock_even i j]
      rw [hLΔD_eq]
      simp only [SuperMatrix.diagonal]
    -- The lifted Schur complements are equal
    have hSchur_lifted_eq : Λ.liftEvenMatrix ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
        (SuperMatrix.diagonal A' D' h0odd hA' hD')).schurD_carrier
        (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
        (SuperMatrix.diagonal A' D' h0odd hA' hD')).schurD_even hBDinv_LD) =
        Λ.liftEvenMatrix (SuperMatrix.diagonal A' D' h0odd hA' hD').schurD_carrier
        ((SuperMatrix.diagonal A' D' h0odd hA' hD').schurD_even hBDinv_D) := by
      ext i j
      apply Λ.evenToCarrier_injective
      rw [Λ.liftEvenMatrix_spec _ (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')).schurD_even hBDinv_LD) i j]
      rw [Λ.liftEvenMatrix_spec _ ((SuperMatrix.diagonal A' D' h0odd hA' hD').schurD_even hBDinv_D) i j]
      rw [hSchurLΔ_carrier, hSchurΔ_carrier]
    -- Now unfold ber and show equality
    unfold SuperMatrix.ber
    -- Need to show equality of schur_lifted.det * Λ.inv D_lifted.det
    -- Since schur_lifted and D_lifted are equal, and inv is unique, the result follows
    have h_det_eq : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
        (SuperMatrix.diagonal A' D' h0odd hA' hD')).D_lifted.det =
        (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det := by rw [hLΔ_D_lifted_eq]
    have h_inv_eq : Λ.inv ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
        (SuperMatrix.diagonal A' D' h0odd hA' hD')).D_lifted.det hLΔD =
        Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD := by
      have h_right' : (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det *
          Λ.inv ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')).D_lifted.det hLΔD = 1 := by
        calc (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det *
            Λ.inv ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
            (SuperMatrix.diagonal A' D' h0odd hA' hD')).D_lifted.det hLΔD
            = ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
              (SuperMatrix.diagonal A' D' h0odd hA' hD')).D_lifted.det *
              Λ.inv ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
              (SuperMatrix.diagonal A' D' h0odd hA' hD')).D_lifted.det hLΔD := by rw [← h_det_eq]
          _ = 1 := Λ.mul_inv _ hLΔD
      calc Λ.inv ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')).D_lifted.det hLΔD
          = 1 * Λ.inv ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
              (SuperMatrix.diagonal A' D' h0odd hA' hD')).D_lifted.det hLΔD := (one_mul _).symm
        _ = (Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD *
            (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det) *
            Λ.inv ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
            (SuperMatrix.diagonal A' D' h0odd hA' hD')).D_lifted.det hLΔD := by rw [Λ.inv_mul _ hΔD]
        _ = Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD *
            ((SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det *
            Λ.inv ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
            (SuperMatrix.diagonal A' D' h0odd hA' hD')).D_lifted.det hLΔD) := by ring
        _ = Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD * 1 := by rw [h_right']
        _ = Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD := mul_one _
    simp only [hSchur_lifted_eq, h_inv_eq]
  have hLΔC : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
              (SuperMatrix.diagonal A' D' h0odd hA' hD')).Cblock = C' * A' := by
    show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock +
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock = C' * A'
    simp only [SuperMatrix.lowerTriangular, SuperMatrix.diagonal]
    simp only [Matrix.one_mul, add_zero]
  have hLΔ_AinvB : ∀ i j, (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                           (SuperMatrix.diagonal A' D' h0odd hA' hD')).A_inv_carrier *
                          ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                           (SuperMatrix.diagonal A' D' h0odd hA' hD')).Bblock) i j ∈ Λ.odd := by
    intro i j
    rw [hLΔB, Matrix.mul_zero]
    exact h0odd
  have hLΔ_DinvC : ∀ i j, (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                           (SuperMatrix.diagonal A' D' h0odd hA' hD')).D_inv_carrier *
                          ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                           (SuperMatrix.diagonal A' D' h0odd hA' hD')).Cblock) i j ∈ Λ.odd := by
    intro i j
    rw [hLΔC]
    -- Need: (L*Δ).D_inv_carrier * (C' * A') has odd entries
    -- (L*Δ).Dblock = D', so (L*Δ).D_inv_carrier maps D'⁻¹ (in evenCarrier) to carrier
    -- D_inv_carrier * (C' * A') entry = sum over k of (D_inv_carrier i k) * (C' * A') k j
    -- Since D_inv_carrier has even entries and C'*A' entries are odd*even = odd, the product is odd
    simp only [Matrix.mul_apply]
    apply Λ.odd.sum_mem
    intro k _
    -- D_inv_carrier i k is even (comes from even D')
    have hDinv_even : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
        (SuperMatrix.diagonal A' D' h0odd hA' hD')).D_inv_carrier i k ∈ Λ.even := by
      unfold SuperMatrix.D_inv_carrier
      -- D_inv_carrier = matrixEvenToCarrier (D_lifted⁻¹)
      -- matrixEvenToCarrier maps evenCarrier to carrier via evenToCarrier
      -- The result is in even since it's the image of evenCarrier
      rw [Λ.even_mem_iff]
      use (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')).D_lifted⁻¹ i k)
      rfl
    -- (C' * A') k j = sum over l of C' k l * A' l j
    -- C' k l is odd, A' l j is even, so product is odd, and sum of odd is odd
    have hCA_odd : (C' * A') k j ∈ Λ.odd := by
      simp only [Matrix.mul_apply]
      apply Λ.odd.sum_mem
      intro l _
      exact Λ.odd_mul_even _ _ (hC' k l) (hA' l j)
    exact Λ.even_mul_odd _ _ hDinv_even hCA_odd
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
                            (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).A_inv_carrier *
                           (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                             (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
                            (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Bblock) i j ∈ Λ.odd := by
    intro i j
    rw [hLΔUB]
    -- Goal: (LDU.A_inv_carrier * (A' * B')) i j ∈ Λ.odd
    -- LDU.Ablock = A', so LDU.A_inv_carrier is the mapping of A'_lifted⁻¹ to carrier
    -- A_inv_carrier * A' * B' should equal B' (using inverse property on evenCarrier)
    simp only [Matrix.mul_apply]
    apply Λ.odd.sum_mem
    intro k _
    -- A_inv_carrier i k is even
    have hAinv_even : ((((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
        (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
        (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).A_inv_carrier i k) ∈ Λ.even := by
      unfold SuperMatrix.A_inv_carrier
      rw [Λ.even_mem_iff]
      use (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
          (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).A_lifted⁻¹ i k
      rfl
    -- (A' * B') k j = sum over l of A' k l * B' l j
    -- A' k l is even, B' l j is odd, so product is odd, and sum of odd is odd
    have hAB_odd : (A' * B') k j ∈ Λ.odd := by
      simp only [Matrix.mul_apply]
      apply Λ.odd.sum_mem
      intro l _
      exact Λ.even_mul_odd _ _ (hA' k l) (hB' l j)
    exact Λ.even_mul_odd _ _ hAinv_even hAB_odd
  have hLΔU_DinvC : ∀ i j, ((((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                             (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
                            (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).D_inv_carrier *
                           (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                             (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
                            (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Cblock) i j ∈ Λ.odd := by
    intro i j
    rw [hLΔUC]
    -- Similar to hLΔ_DinvC: D_inv_carrier * (C' * A') has odd entries
    simp only [Matrix.mul_apply]
    apply Λ.odd.sum_mem
    intro k _
    have hDinv_even : ((((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
        (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
        (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).D_inv_carrier i k) ∈ Λ.even := by
      unfold SuperMatrix.D_inv_carrier
      rw [Λ.even_mem_iff]
      use (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
          (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).D_lifted⁻¹ i k
      rfl
    have hCA_odd : (C' * A') k j ∈ Λ.odd := by
      simp only [Matrix.mul_apply]
      apply Λ.odd.sum_mem
      intro l _
      exact Λ.odd_mul_even _ _ (hC' k l) (hA' l j)
    exact Λ.even_mul_odd _ _ hDinv_even hCA_odd
  -- Use ber_mul_upperTriangular_left to show ber(U*(L*Δ)) = ber(L*Δ)
  -- But we have (L*Δ)*U, not U*(L*Δ). So we need berAlt approach.
  -- The strategy is: ber(L*Δ*U) = berAlt(L*Δ*U) = berAlt(L*Δ) = ber(L*Δ) = ber(Δ)
  -- First, construct the necessary hypotheses for ber_eq_berAlt
  -- For (L*Δ): need hCAinv and hSchurA
  have hLΔ_CAinv : ∀ i j, (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
      (SuperMatrix.diagonal A' D' h0odd hA' hD')).Cblock *
      ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
      (SuperMatrix.diagonal A' D' h0odd hA' hD')).A_inv_carrier) i j ∈ Λ.odd := by
    intro i j
    rw [hLΔC]
    -- (C' * A') * A_inv_carrier = C' * (A' * A_inv_carrier)
    -- A_inv_carrier = matrixEvenToCarrier(A_lifted⁻¹)
    -- A' * A_inv_carrier entries: sum of even * even = even
    -- So (C'*A') * A_inv_carrier = C' * (A' * A_inv_carrier)
    -- C' has odd entries, (A' * A_inv_carrier) should be ~identity in carrier
    simp only [Matrix.mul_apply]
    apply Λ.odd.sum_mem
    intro k _
    have hCA_odd : (C' * A') i k ∈ Λ.odd := by
      simp only [Matrix.mul_apply]
      apply Λ.odd.sum_mem
      intro l _
      exact Λ.odd_mul_even _ _ (hC' i l) (hA' l k)
    have hAinv_even : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
        (SuperMatrix.diagonal A' D' h0odd hA' hD')).A_inv_carrier k j ∈ Λ.even := by
      unfold SuperMatrix.A_inv_carrier
      rw [Λ.even_mem_iff]
      use (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')).A_lifted⁻¹ k j)
      rfl
    exact Λ.odd_mul_even _ _ hCA_odd hAinv_even
  have hLΔ_SchurA_even : ∀ i j, ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
      (SuperMatrix.diagonal A' D' h0odd hA' hD')).schurA_carrier i j ∈ Λ.even := by
    intro i j
    unfold SuperMatrix.schurA_carrier
    rw [hLΔD_eq, hLΔC, hLΔB]
    -- Goal: (D' - (C' * A') * A_inv_carrier * 0) i j ∈ Λ.even
    simp only [Matrix.mul_zero, Matrix.sub_apply, Matrix.zero_apply, sub_zero]
    exact hD' i j
  have hLΔ_SchurA_det : Λ.IsInvertible (Λ.liftEvenMatrix
      ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
      (SuperMatrix.diagonal A' D' h0odd hA' hD')).schurA_carrier
      (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
      (SuperMatrix.diagonal A' D' h0odd hA' hD')).schurA_even hLΔ_CAinv)).det := by
    -- schurA_carrier = D' (since B=0), so det = D'.det which is invertible
    have h_eq : Λ.liftEvenMatrix ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
        (SuperMatrix.diagonal A' D' h0odd hA' hD')).schurA_carrier
        (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
        (SuperMatrix.diagonal A' D' h0odd hA' hD')).schurA_even hLΔ_CAinv) =
        Λ.liftEvenMatrix D' hD' := by
      ext i j
      apply Λ.evenToCarrier_injective
      rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec]
      unfold SuperMatrix.schurA_carrier
      rw [hLΔD_eq, hLΔC, hLΔB]
      simp only [Matrix.mul_zero, Matrix.sub_apply, Matrix.zero_apply, sub_zero]
    rw [h_eq]
    exact _hD'det
  -- Similarly for (L*Δ*U)
  have hLΔU_CAinv : ∀ i j, ((((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
      (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
      (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Cblock *
      (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
      (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
      (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).A_inv_carrier) i j ∈ Λ.odd := by
    intro i j
    rw [hLΔUC]
    simp only [Matrix.mul_apply]
    apply Λ.odd.sum_mem
    intro k _
    have hCA_odd : (C' * A') i k ∈ Λ.odd := by
      simp only [Matrix.mul_apply]
      apply Λ.odd.sum_mem
      intro l _
      exact Λ.odd_mul_even _ _ (hC' i l) (hA' l k)
    have hAinv_even : ((((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
        (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
        (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).A_inv_carrier k j) ∈ Λ.even := by
      unfold SuperMatrix.A_inv_carrier
      rw [Λ.even_mem_iff]
      use ((((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
          (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).A_lifted⁻¹ k j)
      rfl
    exact Λ.odd_mul_even _ _ hCA_odd hAinv_even
  have hLΔU_SchurA_det : Λ.IsInvertible (Λ.liftEvenMatrix
      ((((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
      (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
      (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).schurA_carrier)
      (((((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
      (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
      (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).schurA_even hLΔU_CAinv))).det := by
    -- schurA_carrier = D - C*A_inv*B
    -- For (L*Δ*U): D = C'*A'*B' + D', C = C'*A', A_inv = A'^{-1}, B = A'*B'
    -- So C*A_inv*B = (C'*A')*A'^{-1}*(A'*B') = C'*A'*B' (using A'*A'^{-1} = 1)
    -- Thus schurA = D' + C'*A'*B' - C'*A'*B' = D'
    -- First show schurA_carrier = D'
    have h_schurA_eq : ((((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
        (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
        (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).schurA_carrier) = D' := by
      -- schurA_carrier = Dblock - Cblock * A_inv_carrier * Bblock
      -- For (L*Δ*U): Dblock = C'*A'*B' + D', Cblock = C'*A', Bblock = A'*B'
      -- A_inv_carrier = matrixEvenToCarrier(A_lifted⁻¹) where A_lifted = liftEvenMatrix(Ablock)
      -- Ablock = A', so A_inv_carrier = matrixEvenToCarrier((liftEvenMatrix A')⁻¹)
      -- Thus schurA = (C'*A'*B' + D') - (C'*A') * A_inv_carrier * (A'*B')
      --             = (C'*A'*B' + D') - (C'*A') * (A_inv_carrier * A') * B'
      --             = (C'*A'*B' + D') - (C'*A') * 1 * B'  [since A_inv_carrier * A' = 1]
      --             = D'
      -- First establish A_lifted and its inverse
      have hA_lifted_eq : (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
          (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).A_lifted = Λ.liftEvenMatrix A' hA' := by
        ext i j
        simp only [SuperMatrix.A_lifted]
        apply Λ.evenToCarrier_injective
        rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec]
        exact congrFun (congrFun hLΔUA i) j
      -- Get invertibility for A_lifted
      haveI : Invertible (Λ.liftEvenMatrix A' hA').det := ((Λ.isUnit_iff_body_ne_zero _).mpr hA'det).invertible
      haveI : Invertible (Λ.liftEvenMatrix A' hA') := Matrix.invertibleOfDetInvertible _
      have hAinvA_lifted : (Λ.liftEvenMatrix A' hA')⁻¹ * (Λ.liftEvenMatrix A' hA') = 1 :=
        Matrix.nonsing_inv_mul _ (isUnit_of_invertible _)
      -- matrixEvenToCarrier (liftEvenMatrix A') = A'
      have hA_carrier : matrixEvenToCarrier (Λ.liftEvenMatrix A' hA') = A' := by
        ext i j
        simp only [matrixEvenToCarrier, Matrix.map_apply]
        exact Λ.liftEvenMatrix_spec A' hA' i j
      -- matrixEvenToCarrier(A'_lifted⁻¹) * A' = 1
      have h_Ainv_A_carrier : matrixEvenToCarrier ((Λ.liftEvenMatrix A' hA')⁻¹) * A' = 1 := by
        -- First show that matrixEvenToCarrier preserves multiplication
        have h_mul : matrixEvenToCarrier ((Λ.liftEvenMatrix A' hA')⁻¹) *
            matrixEvenToCarrier (Λ.liftEvenMatrix A' hA') =
            matrixEvenToCarrier ((Λ.liftEvenMatrix A' hA')⁻¹ * (Λ.liftEvenMatrix A' hA')) := by
          ext i j
          simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [← Λ.evenToCarrier.map_mul]
        calc matrixEvenToCarrier ((Λ.liftEvenMatrix A' hA')⁻¹) * A'
            = matrixEvenToCarrier ((Λ.liftEvenMatrix A' hA')⁻¹) *
              matrixEvenToCarrier (Λ.liftEvenMatrix A' hA') := by rw [hA_carrier]
          _ = matrixEvenToCarrier ((Λ.liftEvenMatrix A' hA')⁻¹ * (Λ.liftEvenMatrix A' hA')) := h_mul
          _ = matrixEvenToCarrier 1 := by rw [hAinvA_lifted]
          _ = 1 := by
              ext i j
              simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply]
              split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
      -- Now compute schurA_carrier
      unfold SuperMatrix.schurA_carrier
      rw [hLΔUC, hLΔUB]
      -- Compute Dblock
      have hLΔUD_D : (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
          (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Dblock = (C' * A') * B' + D' := by
        show ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
              (SuperMatrix.diagonal A' D' h0odd hA' hD')).Cblock *
             (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Bblock +
             ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
              (SuperMatrix.diagonal A' D' h0odd hA' hD')).Dblock *
             (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock = (C' * A') * B' + D'
        rw [hLΔC, hLΔD_eq]
        simp only [SuperMatrix.upperTriangular, Matrix.mul_one]
      rw [hLΔUD_D]
      -- Goal: (C' * A') * B' + D' - (C' * A') * A_inv_carrier * (A' * B') = D'
      -- Rewrite A_inv_carrier using hA_lifted_eq
      have hAinv_carrier_eq : (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
          (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
          (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).A_inv_carrier =
          matrixEvenToCarrier ((Λ.liftEvenMatrix A' hA')⁻¹) := by
        unfold SuperMatrix.A_inv_carrier
        congr 1
        rw [hA_lifted_eq]
      rw [hAinv_carrier_eq]
      -- Goal: (C' * A') * B' + D' - (C' * A') * matrixEvenToCarrier (...)⁻¹ * (A' * B') = D'
      -- Use associativity: C' * A' * Ainv * A' * B' = C' * A' * (Ainv * A') * B' = C' * A' * 1 * B'
      have h_assoc : (C' * A') * matrixEvenToCarrier ((Λ.liftEvenMatrix A' hA')⁻¹) * (A' * B') =
          (C' * A') * (matrixEvenToCarrier ((Λ.liftEvenMatrix A' hA')⁻¹) * A') * B' := by
        -- LHS: ((C' * A') * Ainv) * (A' * B')
        -- RHS: ((C' * A') * (Ainv * A')) * B'
        -- Step by step using Matrix.mul_assoc
        have h1 : (C' * A') * matrixEvenToCarrier ((Λ.liftEvenMatrix A' hA')⁻¹) * (A' * B') =
            (C' * A') * (matrixEvenToCarrier ((Λ.liftEvenMatrix A' hA')⁻¹) * (A' * B')) :=
          Matrix.mul_assoc _ _ _
        have h2 : matrixEvenToCarrier ((Λ.liftEvenMatrix A' hA')⁻¹) * (A' * B') =
            (matrixEvenToCarrier ((Λ.liftEvenMatrix A' hA')⁻¹) * A') * B' :=
          (Matrix.mul_assoc _ _ _).symm
        have h3 : (C' * A') * ((matrixEvenToCarrier ((Λ.liftEvenMatrix A' hA')⁻¹) * A') * B') =
            ((C' * A') * (matrixEvenToCarrier ((Λ.liftEvenMatrix A' hA')⁻¹) * A')) * B' :=
          (Matrix.mul_assoc _ _ _).symm
        rw [h1, h2, h3]
      rw [h_assoc, h_Ainv_A_carrier]
      simp only [Matrix.mul_one, add_sub_cancel_left]
    have h_lifted_eq : Λ.liftEvenMatrix
        ((((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
        (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
        (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).schurA_carrier)
        (((((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
        (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
        (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).schurA_even hLΔU_CAinv)) =
        Λ.liftEvenMatrix D' hD' := by
      ext i j
      apply Λ.evenToCarrier_injective
      rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec]
      rw [h_schurA_eq]
    rw [h_lifted_eq]
    exact _hD'det
  -- Now use berAlt_mul_upperTriangular_right to show berAlt((L*Δ)*U) = berAlt(L*Δ)
  have hBerAltU := SuperMatrix.berAlt_mul_upperTriangular_right
    ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
     (SuperMatrix.diagonal A' D' h0odd hA' hD'))
    B' h1 h0even h0odd hB' hLΔA_det hLΔ_CAinv hLΔ_SchurA_det hLΔUA_det hLΔU_CAinv hLΔU_SchurA_det
  -- Use ber_eq_berAlt to convert between ber and berAlt
  have hBerAltLΔ := SuperMatrix.ber_eq_berAlt
    ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
     (SuperMatrix.diagonal A' D' h0odd hA' hD'))
    hLΔA_det hLΔD hLΔ_AinvB hLΔ_DinvC hBDinv_LD hLΔ_CAinv hLΔ_SchurA_det h1 h0even
  have hBerAltLΔU := SuperMatrix.ber_eq_berAlt
    (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
      (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
     (SuperMatrix.upperTriangular B' h1 h0even h0odd hB'))
    hLΔUA_det hLΔUD hLΔU_AinvB hLΔU_DinvC hBDinv_LDU hLΔU_CAinv hLΔU_SchurA_det h1 h0even
  -- Chain: ber(L*Δ*U) = berAlt(L*Δ*U) = berAlt(L*Δ) = ber(L*Δ) = ber(Δ)
  rw [hBerAltLΔU, hBerAltU, ← hBerAltLΔ, hBerLΔ]

/-- LDU factorization: M = L · Δ · U. Requires A invertible (via A_lifted). -/
theorem SuperMatrix.LDU_factorization {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (hA : Λ.IsInvertible M.A_lifted.det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hCAinv : ∀ i j, (M.Cblock * M.A_inv_carrier) i j ∈ Λ.odd)
    (hAinvB : ∀ i j, (M.A_inv_carrier * M.Bblock) i j ∈ Λ.odd)
    (hSchur : ∀ i j, (schurComplementA M hA) i j ∈ Λ.even) :
    M = ((SuperMatrix.lowerTriangular (M.Cblock * M.A_inv_carrier) h1 h0even h0odd hCAinv) *
         (SuperMatrix.diagonal M.Ablock (schurComplementA M hA) h0odd M.Ablock_even hSchur)) *
        (SuperMatrix.upperTriangular (M.A_inv_carrier * M.Bblock) h1 h0even h0odd hAinvB) := by
  -- Get invertibility in evenCarrier
  haveI : Invertible M.A_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hA).invertible
  haveI : Invertible M.A_lifted := Matrix.invertibleOfDetInvertible M.A_lifted
  -- A_lifted⁻¹ * A_lifted = 1 in evenCarrier
  have hAinvA_lifted : M.A_lifted⁻¹ * M.A_lifted = 1 := Matrix.nonsing_inv_mul M.A_lifted (isUnit_of_invertible _)
  have hAAinv_lifted : M.A_lifted * M.A_lifted⁻¹ = 1 := Matrix.mul_nonsing_inv M.A_lifted (isUnit_of_invertible _)
  -- Transfer to carrier: A_inv_carrier * Ablock = 1 and Ablock * A_inv_carrier = 1
  have hA_carrier : matrixEvenToCarrier M.A_lifted = M.Ablock := by
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, SuperMatrix.A_lifted]
    exact Λ.liftEvenMatrix_spec M.Ablock M.Ablock_even i j
  have hAinvA : M.A_inv_carrier * M.Ablock = 1 := by
    have h_mul : matrixEvenToCarrier M.A_lifted⁻¹ * matrixEvenToCarrier M.A_lifted =
        matrixEvenToCarrier (M.A_lifted⁻¹ * M.A_lifted) := by
      ext i j
      simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Λ.evenToCarrier.map_mul]
    calc M.A_inv_carrier * M.Ablock
        = matrixEvenToCarrier M.A_lifted⁻¹ * matrixEvenToCarrier M.A_lifted := by rw [hA_carrier]; rfl
      _ = matrixEvenToCarrier (M.A_lifted⁻¹ * M.A_lifted) := h_mul
      _ = matrixEvenToCarrier 1 := by rw [hAinvA_lifted]
      _ = 1 := by ext i j; simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply];
                   split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
  have hAAinv : M.Ablock * M.A_inv_carrier = 1 := by
    have h_mul : matrixEvenToCarrier M.A_lifted * matrixEvenToCarrier M.A_lifted⁻¹ =
        matrixEvenToCarrier (M.A_lifted * M.A_lifted⁻¹) := by
      ext i j
      simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Λ.evenToCarrier.map_mul]
    calc M.Ablock * M.A_inv_carrier
        = matrixEvenToCarrier M.A_lifted * matrixEvenToCarrier M.A_lifted⁻¹ := by rw [hA_carrier]; rfl
      _ = matrixEvenToCarrier (M.A_lifted * M.A_lifted⁻¹) := h_mul
      _ = matrixEvenToCarrier 1 := by rw [hAAinv_lifted]
      _ = 1 := by ext i j; simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply];
                   split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
  have hA_eq : (((SuperMatrix.lowerTriangular (M.Cblock * M.A_inv_carrier) h1 h0even h0odd hCAinv) *
                (SuperMatrix.diagonal M.Ablock (schurComplementA M hA) h0odd M.Ablock_even hSchur)) *
               (SuperMatrix.upperTriangular (M.A_inv_carrier * M.Bblock) h1 h0even h0odd hAinvB)).Ablock =
              M.Ablock := by
    simp only [SuperMatrix.mul_Ablock, SuperMatrix.lowerTriangular, SuperMatrix.diagonal,
               SuperMatrix.upperTriangular]
    simp only [Matrix.one_mul, add_zero, Matrix.mul_one, Matrix.mul_zero]
  have hB_eq : (((SuperMatrix.lowerTriangular (M.Cblock * M.A_inv_carrier) h1 h0even h0odd hCAinv) *
                (SuperMatrix.diagonal M.Ablock (schurComplementA M hA) h0odd M.Ablock_even hSchur)) *
               (SuperMatrix.upperTriangular (M.A_inv_carrier * M.Bblock) h1 h0even h0odd hAinvB)).Bblock =
              M.Bblock := by
    simp only [SuperMatrix.mul_Bblock, SuperMatrix.mul_Ablock, SuperMatrix.lowerTriangular,
               SuperMatrix.diagonal, SuperMatrix.upperTriangular]
    simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.mul_one, Matrix.mul_zero]
    calc M.Ablock * (M.A_inv_carrier * M.Bblock)
        = (M.Ablock * M.A_inv_carrier) * M.Bblock := by rw [← Matrix.mul_assoc]
      _ = (1 : Matrix _ _ _) * M.Bblock := by rw [hAAinv]
      _ = M.Bblock := by rw [Matrix.one_mul]
  have hC_eq : (((SuperMatrix.lowerTriangular (M.Cblock * M.A_inv_carrier) h1 h0even h0odd hCAinv) *
                (SuperMatrix.diagonal M.Ablock (schurComplementA M hA) h0odd M.Ablock_even hSchur)) *
               (SuperMatrix.upperTriangular (M.A_inv_carrier * M.Bblock) h1 h0even h0odd hAinvB)).Cblock =
              M.Cblock := by
    simp only [SuperMatrix.mul_Cblock, SuperMatrix.mul_Dblock, SuperMatrix.lowerTriangular,
               SuperMatrix.diagonal, SuperMatrix.upperTriangular]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, zero_add]
    calc (M.Cblock * M.A_inv_carrier) * M.Ablock
        = M.Cblock * (M.A_inv_carrier * M.Ablock) := by rw [Matrix.mul_assoc]
      _ = M.Cblock * (1 : Matrix _ _ _) := by rw [hAinvA]
      _ = M.Cblock := by rw [Matrix.mul_one]
  have hD_eq : (((SuperMatrix.lowerTriangular (M.Cblock * M.A_inv_carrier) h1 h0even h0odd hCAinv) *
                (SuperMatrix.diagonal M.Ablock (schurComplementA M hA) h0odd M.Ablock_even hSchur)) *
               (SuperMatrix.upperTriangular (M.A_inv_carrier * M.Bblock) h1 h0even h0odd hAinvB)).Dblock =
              M.Dblock := by
    simp only [SuperMatrix.mul_Dblock, SuperMatrix.mul_Cblock, SuperMatrix.lowerTriangular,
               SuperMatrix.diagonal, SuperMatrix.upperTriangular]
    simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.one_mul, zero_add, add_zero]
    unfold schurComplementA
    -- Goal: (C * A_inv) * A * (A_inv * B) + (D - C * A_inv * B) = D
    -- First simplify: C * A_inv * A = C
    have hCA : M.Cblock * M.A_inv_carrier * M.Ablock = M.Cblock := by
      calc M.Cblock * M.A_inv_carrier * M.Ablock
          = M.Cblock * (M.A_inv_carrier * M.Ablock) := by rw [Matrix.mul_assoc]
        _ = M.Cblock * (1 : Matrix _ _ _) := by rw [hAinvA]
        _ = M.Cblock := by rw [Matrix.mul_one]
    rw [hCA]
    have hAssoc : M.Cblock * (M.A_inv_carrier * M.Bblock) = M.Cblock * M.A_inv_carrier * M.Bblock := by
      rw [← Matrix.mul_assoc]
    rw [hAssoc]
    -- Goal: C * A_inv * B + (D - C * A_inv * B) = D
    -- This simplifies to D by add_sub_cancel
    simp only [add_sub_cancel]
  ext <;> simp only [hA_eq, hB_eq, hC_eq, hD_eq]

/-- UDL factorization: M = U · Δ · L. Requires D invertible (via D_lifted). -/
theorem SuperMatrix.UDL_factorization {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (hD : Λ.IsInvertible M.D_lifted.det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hBDinv : ∀ i j, (M.Bblock * M.D_inv_carrier) i j ∈ Λ.odd)
    (hDinvC : ∀ i j, (M.D_inv_carrier * M.Cblock) i j ∈ Λ.odd)
    (hSchur : ∀ i j, (schurComplementD M hD) i j ∈ Λ.even) :
    M = ((SuperMatrix.upperTriangular (M.Bblock * M.D_inv_carrier) h1 h0even h0odd hBDinv) *
         (SuperMatrix.diagonal (schurComplementD M hD) M.Dblock h0odd hSchur M.Dblock_even)) *
        (SuperMatrix.lowerTriangular (M.D_inv_carrier * M.Cblock) h1 h0even h0odd hDinvC) := by
  -- Get invertibility in evenCarrier
  haveI : Invertible M.D_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hD).invertible
  haveI : Invertible M.D_lifted := Matrix.invertibleOfDetInvertible M.D_lifted
  -- D_lifted⁻¹ * D_lifted = 1 in evenCarrier
  have hDinvD_lifted : M.D_lifted⁻¹ * M.D_lifted = 1 := Matrix.nonsing_inv_mul M.D_lifted (isUnit_of_invertible _)
  have hDDinv_lifted : M.D_lifted * M.D_lifted⁻¹ = 1 := Matrix.mul_nonsing_inv M.D_lifted (isUnit_of_invertible _)
  -- Transfer to carrier
  have hD_carrier : matrixEvenToCarrier M.D_lifted = M.Dblock := by
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, SuperMatrix.D_lifted]
    exact Λ.liftEvenMatrix_spec M.Dblock M.Dblock_even i j
  have hDinvD : M.D_inv_carrier * M.Dblock = 1 := by
    have h_mul : matrixEvenToCarrier M.D_lifted⁻¹ * matrixEvenToCarrier M.D_lifted =
        matrixEvenToCarrier (M.D_lifted⁻¹ * M.D_lifted) := by
      ext i j
      simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Λ.evenToCarrier.map_mul]
    calc M.D_inv_carrier * M.Dblock
        = matrixEvenToCarrier M.D_lifted⁻¹ * matrixEvenToCarrier M.D_lifted := by rw [hD_carrier]; rfl
      _ = matrixEvenToCarrier (M.D_lifted⁻¹ * M.D_lifted) := h_mul
      _ = matrixEvenToCarrier 1 := by rw [hDinvD_lifted]
      _ = 1 := by ext i j; simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply];
                   split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
  have hDDinv : M.Dblock * M.D_inv_carrier = 1 := by
    have h_mul : matrixEvenToCarrier M.D_lifted * matrixEvenToCarrier M.D_lifted⁻¹ =
        matrixEvenToCarrier (M.D_lifted * M.D_lifted⁻¹) := by
      ext i j
      simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Λ.evenToCarrier.map_mul]
    calc M.Dblock * M.D_inv_carrier
        = matrixEvenToCarrier M.D_lifted * matrixEvenToCarrier M.D_lifted⁻¹ := by rw [hD_carrier]; rfl
      _ = matrixEvenToCarrier (M.D_lifted * M.D_lifted⁻¹) := h_mul
      _ = matrixEvenToCarrier 1 := by rw [hDDinv_lifted]
      _ = 1 := by ext i j; simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply];
                   split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
  have hA_eq : (((SuperMatrix.upperTriangular (M.Bblock * M.D_inv_carrier) h1 h0even h0odd hBDinv) *
                (SuperMatrix.diagonal (schurComplementD M hD) M.Dblock h0odd hSchur M.Dblock_even)) *
               (SuperMatrix.lowerTriangular (M.D_inv_carrier * M.Cblock) h1 h0even h0odd hDinvC)).Ablock =
              M.Ablock := by
    simp only [SuperMatrix.mul_Ablock, SuperMatrix.mul_Bblock, SuperMatrix.upperTriangular,
               SuperMatrix.diagonal, SuperMatrix.lowerTriangular]
    simp only [Matrix.one_mul, add_zero, Matrix.mul_one, Matrix.mul_zero, zero_add]
    unfold schurComplementD
    have hBD : M.Bblock * M.D_inv_carrier * M.Dblock = M.Bblock := by
      calc M.Bblock * M.D_inv_carrier * M.Dblock
          = M.Bblock * (M.D_inv_carrier * M.Dblock) := by rw [Matrix.mul_assoc]
        _ = M.Bblock * (1 : Matrix _ _ _) := by rw [hDinvD]
        _ = M.Bblock := by rw [Matrix.mul_one]
    rw [hBD]
    have hAssoc : M.Bblock * (M.D_inv_carrier * M.Cblock) = M.Bblock * M.D_inv_carrier * M.Cblock := by
      rw [← Matrix.mul_assoc]
    rw [hAssoc]
    -- Goal: B * D_inv * C + (A - B * D_inv * C) = A
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply]
    -- x + (y - x) = y, i.e., add_sub_cancel
    abel
  have hB_eq : (((SuperMatrix.upperTriangular (M.Bblock * M.D_inv_carrier) h1 h0even h0odd hBDinv) *
                (SuperMatrix.diagonal (schurComplementD M hD) M.Dblock h0odd hSchur M.Dblock_even)) *
               (SuperMatrix.lowerTriangular (M.D_inv_carrier * M.Cblock) h1 h0even h0odd hDinvC)).Bblock =
              M.Bblock := by
    simp only [SuperMatrix.mul_Bblock, SuperMatrix.mul_Ablock, SuperMatrix.upperTriangular,
               SuperMatrix.diagonal, SuperMatrix.lowerTriangular]
    simp only [Matrix.one_mul, add_zero, Matrix.mul_one, Matrix.mul_zero, zero_add]
    calc M.Bblock * M.D_inv_carrier * M.Dblock
        = M.Bblock * (M.D_inv_carrier * M.Dblock) := by rw [Matrix.mul_assoc]
      _ = M.Bblock * (1 : Matrix _ _ _) := by rw [hDinvD]
      _ = M.Bblock := by rw [Matrix.mul_one]
  have hC_eq : (((SuperMatrix.upperTriangular (M.Bblock * M.D_inv_carrier) h1 h0even h0odd hBDinv) *
                (SuperMatrix.diagonal (schurComplementD M hD) M.Dblock h0odd hSchur M.Dblock_even)) *
               (SuperMatrix.lowerTriangular (M.D_inv_carrier * M.Cblock) h1 h0even h0odd hDinvC)).Cblock =
              M.Cblock := by
    simp only [SuperMatrix.mul_Cblock, SuperMatrix.mul_Dblock, SuperMatrix.upperTriangular,
               SuperMatrix.diagonal, SuperMatrix.lowerTriangular]
    simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.mul_one, Matrix.mul_zero, zero_add]
    calc M.Dblock * (M.D_inv_carrier * M.Cblock)
        = (M.Dblock * M.D_inv_carrier) * M.Cblock := by rw [← Matrix.mul_assoc]
      _ = (1 : Matrix _ _ _) * M.Cblock := by rw [hDDinv]
      _ = M.Cblock := by rw [Matrix.one_mul]
  have hD_eq : (((SuperMatrix.upperTriangular (M.Bblock * M.D_inv_carrier) h1 h0even h0odd hBDinv) *
                (SuperMatrix.diagonal (schurComplementD M hD) M.Dblock h0odd hSchur M.Dblock_even)) *
               (SuperMatrix.lowerTriangular (M.D_inv_carrier * M.Cblock) h1 h0even h0odd hDinvC)).Dblock =
              M.Dblock := by
    simp only [SuperMatrix.mul_Dblock, SuperMatrix.mul_Cblock, SuperMatrix.upperTriangular,
               SuperMatrix.diagonal, SuperMatrix.lowerTriangular]
    simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.mul_one, Matrix.mul_zero, zero_add]
  ext <;> simp only [hA_eq, hB_eq, hC_eq, hD_eq]

end Supermanifolds.Helpers
