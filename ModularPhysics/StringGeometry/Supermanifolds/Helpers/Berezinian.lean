import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import ModularPhysics.StringGeometry.Supermanifolds.Superalgebra
import ModularPhysics.StringGeometry.Supermanifolds.Helpers.SuperMatrix
import ModularPhysics.StringGeometry.Supermanifolds.Helpers.MatrixParity
import ModularPhysics.StringGeometry.Supermanifolds.Helpers.BerezinianHelpers

/-!
# Berezinian (Superdeterminant) - Core Definitions

This file contains the core definitions and basic theorems for the Berezinian (superdeterminant)
of supermatrices over a Grassmann algebra.

## Main definitions

* `SuperMatrix.ber` - The Berezinian Ber(M) = det(A - BD⁻¹C) / det(D)
* `SuperMatrix.berAlt` - Alternative formula Ber(M) = det(A) / det(D - CA⁻¹B)
* `schurComplementD`, `schurComplementA` - Schur complements
* Various factor definitions for LDU/UDL decompositions

## Main results

* `SuperMatrix.ber_eq_berAlt` - The two Berezinian formulas agree
* `SuperMatrix.ber_upperTriangular` - Ber([I B; 0 I]) = 1
* `SuperMatrix.ber_lowerTriangular` - Ber([I 0; C I]) = 1
* `SuperMatrix.ber_diagonal` - Ber([A 0; 0 D]) = det(A)/det(D)
* `SuperMatrix.LDU_factorization` - M = L · Δ · U factorization
* `SuperMatrix.UDL_factorization` - M = U · Δ · L factorization

For multiplicativity theorems, see BerezinianMul.lean.
-/

namespace Supermanifolds.Helpers

open Supermanifolds

/-! ## Berezinian Definition

The Berezinian is computed on evenCarrier (CommRing) where determinants and inverses
are well-defined. Since A and D blocks have even entries, they can be lifted to evenCarrier.
The Schur complement A - BD⁻¹C also has even entries (since BD⁻¹ is odd×even=odd, and
BD⁻¹C is odd×odd=even, so A - BD⁻¹C is even-even=even).

Note: Basic definitions (D_lifted, A_lifted, matrixEvenToCarrier, D_inv_carrier, A_inv_carrier,
schurD_carrier, schurA_carrier, schurD_even, schurA_even, upperTriangular, lowerTriangular,
diagonal, one_mem_even_matrix, matrixEvenToCarrier_one) are in BerezinianDefs.lean.
-/

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
  have hAblock_Ainv : M.Ablock * M.A_inv_carrier = 1 := Ablock_mul_A_inv_carrier M hMA

  have hDblock_Dinv : M.Dblock * M.D_inv_carrier = 1 := Dblock_mul_D_inv_carrier M hMD

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
   one_mem_even_matrix h1 h0even,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   hDinvC,
   one_mem_even_matrix h1 h0even⟩

/-- Upper triangular factor (D-based): U = [I BD⁻¹; 0 I] (uses evenCarrier inverse) -/
noncomputable def upperTriangularFactorD {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (_hD : Λ.IsInvertible M.D_lifted.det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hBDinv : ∀ i j, (M.Bblock * M.D_inv_carrier) i j ∈ Λ.odd) : SuperMatrix Λ n m :=
  ⟨1, M.Bblock * M.D_inv_carrier, 0, 1,
   one_mem_even_matrix h1 h0even,
   hBDinv,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   one_mem_even_matrix h1 h0even⟩

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
   one_mem_even_matrix h1 h0even,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   hCAinv,
   one_mem_even_matrix h1 h0even⟩

/-- Upper triangular factor (A-based): U = [I A⁻¹B; 0 I] (uses evenCarrier inverse) -/
noncomputable def upperTriangularFactorA {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    {n m : ℕ} (M : SuperMatrix Λ n m) (_hA : Λ.IsInvertible M.A_lifted.det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hAinvB : ∀ i j, (M.A_inv_carrier * M.Bblock) i j ∈ Λ.odd) : SuperMatrix Λ n m :=
  ⟨1, M.A_inv_carrier * M.Bblock, 0, 1,
   one_mem_even_matrix h1 h0even,
   hAinvB,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   one_mem_even_matrix h1 h0even⟩

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

-- Note: upperTriangular, lowerTriangular, and diagonal are now in BerezinianDefs.lean

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

/-! ## Matrix Factorizations -/

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
  -- Transfer to carrier: A_inv_carrier * Ablock = 1 and Ablock * A_inv_carrier = 1
  have hAinvA : M.A_inv_carrier * M.Ablock = 1 := A_inv_carrier_mul_Ablock M hA
  have hAAinv : M.Ablock * M.A_inv_carrier = 1 := Ablock_mul_A_inv_carrier M hA
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
  -- Transfer to carrier using helpers
  have hDinvD : M.D_inv_carrier * M.Dblock = 1 := D_inv_carrier_mul_Dblock M hD
  have hDDinv : M.Dblock * M.D_inv_carrier = 1 := Dblock_mul_D_inv_carrier M hD
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
