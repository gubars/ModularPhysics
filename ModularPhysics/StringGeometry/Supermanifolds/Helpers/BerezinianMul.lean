import ModularPhysics.StringGeometry.Supermanifolds.Helpers.Berezinian

set_option maxHeartbeats 400000

/-!
# Berezinian Multiplicativity

This file contains all multiplicativity theorems for the Berezinian (superdeterminant).

## Main results

* `SuperMatrix.berAlt_mul_lowerTriangular_left` - berAlt(L·N) = berAlt(N)
* `SuperMatrix.berAlt_mul_upperTriangular_right` - berAlt(M·U) = berAlt(M)
* `SuperMatrix.ber_mul_upperTriangular_left` - Ber(U·N) = Ber(N)
* `SuperMatrix.ber_mul_lowerTriangular_right` - Ber(M·L) = Ber(M)
* `SuperMatrix.ber_UDL` - Ber(U·Δ·L) = Ber(Δ)
* `SuperMatrix.ber_LDU` - Ber(L·Δ·U) = Ber(Δ)
* `SuperMatrix.ber_mul_A_invertible` - Ber(M·N) = Ber(M)·Ber(N) when M.A invertible
* `SuperMatrix.ber_mul_lowerTriangular_left` - Ber(L·N) = Ber(N)
* `SuperMatrix.ber_mul_diagonal_left` - Ber(Δ·N) = Ber(Δ)·Ber(N)
* `SuperMatrix.ber_mul` - General multiplicativity: Ber(M·N) = Ber(M)·Ber(N)
-/

namespace Supermanifolds.Helpers

open Supermanifolds

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
  have hLNA_lifted_eq : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).A_lifted = N.A_lifted :=
    A_lifted_eq_of_Ablock_eq' _ _ hLNA_eq
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
    have hAAinv : N.Ablock * N.A_inv_carrier = 1 := Ablock_mul_A_inv_carrier N hNA
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
  have h_det_eq : (Λ.liftEvenMatrix (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_carrier
      ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_even hLNCAinv)).det =
      (Λ.liftEvenMatrix N.schurA_carrier (N.schurA_even hNCAinv)).det :=
    liftEvenMatrix_det_eq_of_eq _ _ _ _ hSchurA_eq
  -- Show the inverses are equal using inv_eq_of_val_eq
  have h_inv_eq : Λ.inv (Λ.liftEvenMatrix (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_carrier
      ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).schurA_even hLNCAinv)).det hLNSchurA =
      Λ.inv (Λ.liftEvenMatrix N.schurA_carrier (N.schurA_even hNCAinv)).det hNSchurA :=
    inv_eq_of_val_eq h_det_eq hLNSchurA hNSchurA
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
  have hMUA_lifted_eq : (M * U).A_lifted = M.A_lifted :=
    A_lifted_eq_of_Ablock_eq' _ _ hMUA_eq
  have hA_lifted_det_eq : (M * U).A_lifted.det = M.A_lifted.det := by rw [hMUA_lifted_eq]
  have hA_inv_carrier_eq : (M * U).A_inv_carrier = M.A_inv_carrier :=
    A_inv_carrier_eq_of_A_lifted_eq _ _ hMUA_lifted_eq
  have hSchurA_eq : (M * U).schurA_carrier = M.schurA_carrier := by
    unfold SuperMatrix.schurA_carrier
    simp only [hMUB_eq, hMUC_eq, hMUD_eq, hA_inv_carrier_eq]
    -- Goal: (M.Cblock * B' + M.Dblock) - M.Cblock * M.A_inv_carrier * (M.Ablock * B' + M.Bblock)
    --     = M.Dblock - M.Cblock * M.A_inv_carrier * M.Bblock
    have hAAinv : M.Ablock * M.A_inv_carrier = 1 := Ablock_mul_A_inv_carrier M hMA
    have hAinvA : M.A_inv_carrier * M.Ablock = 1 := A_inv_carrier_mul_Ablock M hMA
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
  have h_det_eq : (Λ.liftEvenMatrix (M * U).schurA_carrier ((M * U).schurA_even hMUCAinv)).det =
      (Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hMCAinv)).det :=
    liftEvenMatrix_det_eq_of_eq _ _ _ _ hSchurA_eq
  have h_inv_eq : Λ.inv (Λ.liftEvenMatrix (M * U).schurA_carrier ((M * U).schurA_even hMUCAinv)).det hMUSchurA =
      Λ.inv (Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hMCAinv)).det hMSchurA :=
    inv_eq_of_val_eq h_det_eq hMUSchurA hMSchurA
  -- Goal: (M * U).A_lifted.det * inv(...) = M.A_lifted.det * inv(...)
  -- Since (M * U) = (M * upperTriangular ...), need to show they match
  show (M * U).A_lifted.det * Λ.inv (Λ.liftEvenMatrix (M * U).schurA_carrier _).det hMUSchurA =
       M.A_lifted.det * Λ.inv (Λ.liftEvenMatrix M.schurA_carrier _).det hMSchurA
  rw [hA_lifted_det_eq, h_inv_eq]

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
  have hD_inv_eq : (Y * L).D_inv_carrier = Y.D_inv_carrier :=
    D_inv_carrier_eq_of_D_lifted_eq _ _ hYLD_lifted_eq
  rw [hD_inv_eq]
  -- Now goal: Y.Ablock - Y.Bblock * Y.D_inv_carrier * L.Cblock = Y.Ablock - Y.Bblock * Y.D_inv_carrier * Y.Cblock
  -- Since L.Cblock is from lower triangular, we need to determine what it is
  -- Actually, L is lower triangular with L.Cblock being the C' parameter
  -- But since Y.Cblock = 0, the result simplifies
  haveI : Invertible Y.D_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hD).invertible
  haveI : Invertible Y.D_lifted := Matrix.invertibleOfDetInvertible Y.D_lifted
  have hYDinv : Y.Dblock * Y.D_inv_carrier = 1 := Dblock_mul_D_inv_carrier Y hD
  -- Goal: Y.Ablock + Y.Bblock * L.Cblock - Y.Bblock * Y.D_inv_carrier * (Y.Dblock * L.Cblock) = Y.Ablock
  -- Simplify: Y.Bblock * Y.D_inv_carrier * (Y.Dblock * L.Cblock) = Y.Bblock * (Y.D_inv_carrier * Y.Dblock) * L.Cblock
  --         = Y.Bblock * 1 * L.Cblock (using D_inv * D = 1... but we have D * D_inv = 1)
  -- Actually we need D_inv * D = 1
  have hDinvD : Y.D_inv_carrier * Y.Dblock = 1 := D_inv_carrier_mul_Dblock Y hD
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
  have hUND_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).Dblock = N.Dblock :=
    upperTriangular_mul_Dblock B' N h1 h0even h0odd hB'
  have hUNC_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).Cblock = N.Cblock :=
    upperTriangular_mul_Cblock B' N h1 h0even h0odd hB'
  have hUNB_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).Bblock =
                 N.Bblock + B' * N.Dblock := upperTriangular_mul_Bblock B' N h1 h0even h0odd hB'
  have hUNA_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).Ablock =
                 N.Ablock + B' * N.Cblock := upperTriangular_mul_Ablock B' N h1 h0even h0odd hB'
  -- (U*N).D_lifted = N.D_lifted since Dblock is the same
  have hUND_lifted_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).D_lifted = N.D_lifted :=
    D_lifted_eq_of_Dblock_eq' _ _ hUND_eq
  have hD_lifted_det_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).D_lifted.det = N.D_lifted.det := by
    rw [hUND_lifted_eq]
  have hD_inv_carrier_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).D_inv_carrier = N.D_inv_carrier :=
    D_inv_carrier_eq_of_D_lifted_eq _ _ hUND_lifted_eq
  -- schurD_carrier = A - B * D_inv_carrier * C
  have hSchurD_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).schurD_carrier = N.schurD_carrier := by
    unfold SuperMatrix.schurD_carrier
    rw [hUNA_eq, hUNB_eq, hUNC_eq, hD_inv_carrier_eq]
    -- Goal: (N.Ablock + B' * N.Cblock) - (N.Bblock + B' * N.Dblock) * N.D_inv_carrier * N.Cblock
    --     = N.Ablock - N.Bblock * N.D_inv_carrier * N.Cblock
    have h_DinvD : N.Dblock * N.D_inv_carrier = 1 := Dblock_mul_D_inv_carrier N hND
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
  have h_det_eq : (Λ.liftEvenMatrix (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).schurD_carrier
      ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).schurD_even hUNBDinv)).det =
      (Λ.liftEvenMatrix N.schurD_carrier (N.schurD_even hNBDinv)).det :=
    liftEvenMatrix_det_eq_of_eq _ _ _ _ hSchurD_eq
  have hND_inv : Λ.IsInvertible N.D_lifted.det := hND
  have h_inv_eq : Λ.inv (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).D_lifted.det hUND =
      Λ.inv N.D_lifted.det hND_inv :=
    inv_eq_of_val_eq hD_lifted_det_eq hUND hND_inv
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
          have hD_inv_carrier_eq : (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_inv_carrier = M.D_inv_carrier :=
            D_inv_carrier_eq_of_Dblock_eq _ _ hMLD_eq
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
  have hMLD_lifted_eq := D_lifted_eq_of_Dblock_eq' _ _ hMLD_eq
  have hD_inv_carrier_eq := D_inv_carrier_eq_of_D_lifted_eq _ _ hMLD_lifted_eq
  -- Setup for inverse calculation
  have h_DinvD : M.D_inv_carrier * M.Dblock = 1 := D_inv_carrier_mul_Dblock M hMD
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
                  Λ.inv M.D_lifted.det hMD :=
    inv_eq_of_val_eq h_det_eq hMLD hMD
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
    rw [A_lifted_eq_of_Ablock_eq _ A' hA' hLΔA]; exact hA'det
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
    rw [A_lifted_eq_of_Ablock_eq _ A' hA' hLΔUA]; exact hA'det
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
        Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD :=
      inv_eq_of_val_eq h_det_eq hLΔD hΔD
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
      have hA_lifted_eq := A_lifted_eq_of_Ablock_eq _ A' hA' hLΔUA
      -- Get invertibility for A_lifted
      haveI : Invertible (Λ.liftEvenMatrix A' hA').det := ((Λ.isUnit_iff_body_ne_zero _).mpr hA'det).invertible
      haveI : Invertible (Λ.liftEvenMatrix A' hA') := Matrix.invertibleOfDetInvertible _
      have hAinvA_lifted : (Λ.liftEvenMatrix A' hA')⁻¹ * (Λ.liftEvenMatrix A' hA') = 1 :=
        Matrix.nonsing_inv_mul _ (isUnit_of_invertible _)
      -- matrixEvenToCarrier (liftEvenMatrix A') = A'
      have hA_carrier := matrixEvenToCarrier_liftEvenMatrix A' hA'
      -- matrixEvenToCarrier(A'_lifted⁻¹) * A' = 1
      have h_Ainv_A_carrier : matrixEvenToCarrier ((Λ.liftEvenMatrix A' hA')⁻¹) * A' = 1 := by
        calc matrixEvenToCarrier ((Λ.liftEvenMatrix A' hA')⁻¹) * A'
            = matrixEvenToCarrier ((Λ.liftEvenMatrix A' hA')⁻¹) *
              matrixEvenToCarrier (Λ.liftEvenMatrix A' hA') := by rw [hA_carrier]
          _ = matrixEvenToCarrier ((Λ.liftEvenMatrix A' hA')⁻¹ * (Λ.liftEvenMatrix A' hA')) :=
              (matrixEvenToCarrier_mul _ _).symm
          _ = matrixEvenToCarrier 1 := by rw [hAinvA_lifted]
          _ = 1 := matrixEvenToCarrier_one
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


/-! ## Multiplicativity when M.A is invertible -/

theorem SuperMatrix.ber_mul_A_invertible {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (M N : SuperMatrix Λ n m)
    (hMA : Λ.IsInvertible M.A_lifted.det)
    (hMD : Λ.IsInvertible M.D_lifted.det)
    (hND : Λ.IsInvertible N.D_lifted.det)
    (hMND : Λ.IsInvertible (M * N).D_lifted.det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hBDinvM : ∀ i j, (M.Bblock * M.D_inv_carrier) i j ∈ Λ.odd)
    (hBDinvN : ∀ i j, (N.Bblock * N.D_inv_carrier) i j ∈ Λ.odd)
    (hBDinvMN : ∀ i j, ((M * N).Bblock * (M * N).D_inv_carrier) i j ∈ Λ.odd)
    (hDinvCN : ∀ i j, (N.D_inv_carrier * N.Cblock) i j ∈ Λ.odd)
    (hCAinvM : ∀ i j, (M.Cblock * M.A_inv_carrier) i j ∈ Λ.odd)
    (hAinvBM : ∀ i j, (M.A_inv_carrier * M.Bblock) i j ∈ Λ.odd)
    (hDinvCM : ∀ i j, (M.D_inv_carrier * M.Cblock) i j ∈ Λ.odd)
    (hSchurM : ∀ i j, (schurComplementA M hMA) i j ∈ Λ.even)
    (hSchurN : ∀ i j, (schurComplementD N hND) i j ∈ Λ.even)
    (hSchurM_det : Λ.IsInvertible (Λ.liftEvenMatrix (schurComplementA M hMA) hSchurM).det) :
    (M * N).ber hMND hBDinvMN = M.ber hMD hBDinvM * N.ber hND hBDinvN := by
  -- Get invertibility in evenCarrier
  haveI : Invertible M.A_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hMA).invertible
  haveI hInvMA : Invertible M.A_lifted := Matrix.invertibleOfDetInvertible M.A_lifted
  haveI : Invertible M.D_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hMD).invertible
  haveI hInvMD : Invertible M.D_lifted := Matrix.invertibleOfDetInvertible M.D_lifted
  haveI : Invertible N.D_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hND).invertible
  haveI hInvND : Invertible N.D_lifted := Matrix.invertibleOfDetInvertible N.D_lifted

  let C_M := M.Cblock * M.A_inv_carrier
  let A_M := M.Ablock
  let D_M := schurComplementA M hMA
  let B_M := M.A_inv_carrier * M.Bblock

  let B_N := N.Bblock * N.D_inv_carrier
  let A_N := schurComplementD N hND
  let D_N := N.Dblock
  let C_N := N.D_inv_carrier * N.Cblock

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

  -- hBDinv proofs for basic matrices (needed for ber calls)
  have hBDinvL : ∀ i j, (L.Bblock * L.D_inv_carrier) i j ∈ Λ.odd :=
    lowerTriangular_BDinv_odd C_M h1 h0even h0odd hCAinvM
  have hBDinvΔ : ∀ i j, (Δ.Bblock * Δ.D_inv_carrier) i j ∈ Λ.odd :=
    diagonal_BDinv_odd A_M D_M h0odd M.Ablock_even hSchurM
  have hBDinvU : ∀ i j, (U.Bblock * U.D_inv_carrier) i j ∈ Λ.odd :=
    upperTriangular_BDinv_odd B_M h1 h0even h0odd hAinvBM
  have hBDinvU' : ∀ i j, (U'.Bblock * U'.D_inv_carrier) i j ∈ Λ.odd :=
    upperTriangular_BDinv_odd B_N h1 h0even h0odd hBDinvN
  have hBDinvΔ' : ∀ i j, (Δ'.Bblock * Δ'.D_inv_carrier) i j ∈ Λ.odd :=
    diagonal_BDinv_odd A_N D_N h0odd hSchurN N.Dblock_even
  have hBDinvL' : ∀ i j, (L'.Bblock * L'.D_inv_carrier) i j ∈ Λ.odd :=
    lowerTriangular_BDinv_odd C_N h1 h0even h0odd hDinvCN

  have hLD : Λ.IsInvertible L.D_lifted.det :=
    lowerTriangular_D_lifted_invertible C_M h1 h0even h0odd hCAinvM
  have hΔD : Λ.IsInvertible Δ.D_lifted.det := by simp only [SuperMatrix.D_lifted]; exact hSchurM_det
  have hUD : Λ.IsInvertible U.D_lifted.det :=
    upperTriangular_D_lifted_invertible B_M h1 h0even h0odd hAinvBM
  have hU'D : Λ.IsInvertible U'.D_lifted.det :=
    upperTriangular_D_lifted_invertible B_N h1 h0even h0odd hBDinvN
  have hΔ'D : Λ.IsInvertible Δ'.D_lifted.det := by simp only [SuperMatrix.D_lifted]; exact hND
  have hL'D : Λ.IsInvertible L'.D_lifted.det :=
    lowerTriangular_D_lifted_invertible C_N h1 h0even h0odd hDinvCN

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
  have hXD : Λ.IsInvertible (L * Δ * U * (U' * Δ')).D_lifted.det := by
    have hD_lifted_eq : (L * Δ * U * (U' * Δ')).D_lifted = (L * Δ * U * (U' * Δ') * L').D_lifted :=
      D_lifted_eq_of_Dblock_eq' _ _ hXL'_D_eq'.symm
    have hMN_D_lifted_eq : (L * Δ * U * (U' * Δ') * L').D_lifted = (M * N).D_lifted :=
      D_lifted_eq_of_Dblock_eq' _ _ (by rw [← hMN_assoc])
    rw [hD_lifted_eq, hMN_D_lifted_eq]; exact hMND
  have hXL'D : Λ.IsInvertible (L * Δ * U * (U' * Δ') * L').D_lifted.det := by
    have hMN_D_lifted_eq : (L * Δ * U * (U' * Δ') * L').D_lifted = (M * N).D_lifted :=
      D_lifted_eq_of_Dblock_eq' _ _ (by rw [← hMN_assoc])
    rw [hMN_D_lifted_eq]; exact hMND

  -- hBDinv for X = L * Δ * U * (U' * Δ')
  -- Since (M * N) = X * L' and (M * N).Bblock * (M * N).D_inv_carrier is odd,
  -- and X * L' has the same B and D blocks as M * N (since M * N = X * L'),
  -- we can use hBDinvMN
  have hBDinvX : ∀ i j, ((L * Δ * U * (U' * Δ')).Bblock * (L * Δ * U * (U' * Δ')).D_inv_carrier) i j ∈ Λ.odd := by
    intro i j
    -- X * L' = M * N, and L' is lower triangular with Bblock = 0, Dblock = 1
    -- So (X * L').Bblock = X.Ablock * 0 + X.Bblock * 1 = X.Bblock
    -- And (X * L').Dblock = X.Cblock * 0 + X.Dblock * 1 = X.Dblock
    have hXL'B_eq : (L * Δ * U * (U' * Δ') * L').Bblock = (L * Δ * U * (U' * Δ')).Bblock := by
      show (L * Δ * U * (U' * Δ')).Ablock * L'.Bblock + (L * Δ * U * (U' * Δ')).Bblock * L'.Dblock =
           (L * Δ * U * (U' * Δ')).Bblock
      have hL'B : L'.Bblock = 0 := rfl
      have hL'D : L'.Dblock = 1 := rfl
      simp only [hL'B, hL'D, Matrix.mul_zero, zero_add, Matrix.mul_one]
    have hXL'D_eq2 : (L * Δ * U * (U' * Δ') * L').Dblock = (L * Δ * U * (U' * Δ')).Dblock := hXL'_D_eq'
    have hMN_B_eq : (M * N).Bblock = (L * Δ * U * (U' * Δ') * L').Bblock := by rw [← hMN_assoc]
    have hMN_D_eq : (M * N).Dblock = (L * Δ * U * (U' * Δ') * L').Dblock := by rw [← hMN_assoc]
    have hX_B_eq : (L * Δ * U * (U' * Δ')).Bblock = (M * N).Bblock := by
      rw [hMN_B_eq, hXL'B_eq]
    have hX_D_eq : (L * Δ * U * (U' * Δ')).Dblock = (M * N).Dblock := by
      rw [hMN_D_eq, hXL'D_eq2]
    have hX_D_inv_carrier_eq : (L * Δ * U * (U' * Δ')).D_inv_carrier = (M * N).D_inv_carrier :=
      D_inv_carrier_eq_of_Dblock_eq _ _ hX_D_eq
    rw [hX_B_eq, hX_D_inv_carrier_eq]
    exact hBDinvMN i j

  have hStrip1 : (M * N).ber hMND hBDinvMN = (L * Δ * U * (U' * Δ')).ber hXD hBDinvX := by
    have hXL'_D_eq : (L * Δ * U * (U' * Δ') * L').Dblock = (L * Δ * U * (U' * Δ')).Dblock := by
      show (L * Δ * U * (U' * Δ')).Cblock * L'.Bblock + (L * Δ * U * (U' * Δ')).Dblock * L'.Dblock =
           (L * Δ * U * (U' * Δ')).Dblock
      have hL'B : L'.Bblock = 0 := rfl
      have hL'D : L'.Dblock = 1 := rfl
      simp only [hL'B, hL'D, Matrix.mul_zero, zero_add, Matrix.mul_one]
    have hMN_blocks : M * N = (L * Δ * U * (U' * Δ')) * L' := hMN_assoc
    have hXL'D_ne : Λ.IsInvertible ((L * Δ * U * (U' * Δ')) * L').D_lifted.det := by
      rw [D_lifted_eq_of_Dblock_eq' _ _ hXL'_D_eq]; exact hXD
    have hStrip' := SuperMatrix.ber_mul_lowerTriangular_right (L * Δ * U * (U' * Δ')) C_N
      h1 h0even h0odd hDinvCN hXD hL'D hXL'D_ne hBDinvX
    -- hStrip' : (X * L').ber hXL'D_ne _ = X.ber hXD hBDinvX
    -- We need: (M * N).ber hMND hBDinvMN = X.ber hXD hBDinvX
    -- Since M * N = X * L', we show (M*N).ber = (X*L').ber by component equality
    simp only [SuperMatrix.ber]
    -- Show schurD_carrier equality: (M*N) and (X*L') have the same Bblock and Dblock
    have hMN_B_eq : (M * N).Bblock = (L * Δ * U * (U' * Δ') * L').Bblock := by rw [← hMN_blocks]
    have hMN_D_eq : (M * N).Dblock = (L * Δ * U * (U' * Δ') * L').Dblock := by rw [← hMN_blocks]
    have hXL'B_eq : (L * Δ * U * (U' * Δ') * L').Bblock = (L * Δ * U * (U' * Δ')).Bblock := by
      show (L * Δ * U * (U' * Δ')).Ablock * L'.Bblock + (L * Δ * U * (U' * Δ')).Bblock * L'.Dblock =
           (L * Δ * U * (U' * Δ')).Bblock
      have hL'B : L'.Bblock = 0 := rfl
      have hL'D : L'.Dblock = 1 := rfl
      simp only [hL'B, hL'D, Matrix.mul_zero, zero_add, Matrix.mul_one]
    have hMN_B_eq' : (M * N).Bblock = (L * Δ * U * (U' * Δ')).Bblock := by
      rw [hMN_B_eq, hXL'B_eq]
    have hMN_D_eq' : (M * N).Dblock = (L * Δ * U * (U' * Δ')).Dblock := by
      rw [hMN_D_eq, hXL'_D_eq]
    have hMN_D_inv_carrier_eq : (M * N).D_inv_carrier = (L * Δ * U * (U' * Δ')).D_inv_carrier :=
      D_inv_carrier_eq_of_Dblock_eq _ _ hMN_D_eq'
    -- schurD_carrier equality
    have hMN_schurD_carrier_eq : (M * N).schurD_carrier = (L * Δ * U * (U' * Δ')).schurD_carrier := by
      unfold SuperMatrix.schurD_carrier
      rw [hMN_B_eq', hMN_D_inv_carrier_eq]
      -- Need to show Ablock and Cblock are the same
      have hMN_A_eq : (M * N).Ablock = (L * Δ * U * (U' * Δ') * L').Ablock := by rw [← hMN_blocks]
      have hMN_C_eq : (M * N).Cblock = (L * Δ * U * (U' * Δ') * L').Cblock := by rw [← hMN_blocks]
      have hXL'A_eq : (L * Δ * U * (U' * Δ') * L').Ablock = (L * Δ * U * (U' * Δ')).Ablock + (L * Δ * U * (U' * Δ')).Bblock * C_N := by
        show (L * Δ * U * (U' * Δ')).Ablock * L'.Ablock + (L * Δ * U * (U' * Δ')).Bblock * L'.Cblock =
             (L * Δ * U * (U' * Δ')).Ablock + (L * Δ * U * (U' * Δ')).Bblock * C_N
        have hL'A : L'.Ablock = 1 := rfl
        have hL'C : L'.Cblock = C_N := rfl
        simp only [hL'A, hL'C, Matrix.mul_one]
      have hXL'C_eq : (L * Δ * U * (U' * Δ') * L').Cblock = (L * Δ * U * (U' * Δ')).Cblock + (L * Δ * U * (U' * Δ')).Dblock * C_N := by
        show (L * Δ * U * (U' * Δ')).Cblock * L'.Ablock + (L * Δ * U * (U' * Δ')).Dblock * L'.Cblock =
             (L * Δ * U * (U' * Δ')).Cblock + (L * Δ * U * (U' * Δ')).Dblock * C_N
        have hL'A : L'.Ablock = 1 := rfl
        have hL'C : L'.Cblock = C_N := rfl
        simp only [hL'A, hL'C, Matrix.mul_one]
      rw [hMN_A_eq, hXL'A_eq, hMN_C_eq, hXL'C_eq]
      -- Now need Ablock - Bblock * D_inv * (Cblock + D*C_N) = A + B*C_N - B*D_inv*(C + D*C_N)
      -- After cancellation, these should be equal
      -- Using X for L * Δ * U * (U' * Δ')
      have hDinvD : (L * Δ * U * (U' * Δ')).D_inv_carrier * (L * Δ * U * (U' * Δ')).Dblock = 1 := by
        haveI : Invertible (L * Δ * U * (U' * Δ')).D_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hXD).invertible
        haveI : Invertible (L * Δ * U * (U' * Δ')).D_lifted := Matrix.invertibleOfDetInvertible _
        have hD_inv_def : (L * Δ * U * (U' * Δ')).D_inv_carrier = matrixEvenToCarrier (L * Δ * U * (U' * Δ')).D_lifted⁻¹ := rfl
        have hD_lifted_carrier := matrixEvenToCarrier_D_lifted (L * Δ * U * (U' * Δ'))
        have hDinvD_lifted : (L * Δ * U * (U' * Δ')).D_lifted⁻¹ * (L * Δ * U * (U' * Δ')).D_lifted = 1 :=
          Matrix.nonsing_inv_mul (L * Δ * U * (U' * Δ')).D_lifted (isUnit_of_invertible _)
        rw [hD_inv_def, ← hD_lifted_carrier, (matrixEvenToCarrier_mul _ _).symm, hDinvD_lifted]
        exact matrixEvenToCarrier_one
      -- Prove the matrix equality directly
      have h_distrib_mat : (L * Δ * U * (U' * Δ')).Bblock * (L * Δ * U * (U' * Δ')).D_inv_carrier *
          ((L * Δ * U * (U' * Δ')).Cblock + (L * Δ * U * (U' * Δ')).Dblock * C_N) =
          (L * Δ * U * (U' * Δ')).Bblock * (L * Δ * U * (U' * Δ')).D_inv_carrier * (L * Δ * U * (U' * Δ')).Cblock +
          (L * Δ * U * (U' * Δ')).Bblock * C_N := by
        rw [Matrix.mul_add]
        congr 1
        calc (L * Δ * U * (U' * Δ')).Bblock * (L * Δ * U * (U' * Δ')).D_inv_carrier *
            ((L * Δ * U * (U' * Δ')).Dblock * C_N)
            = (L * Δ * U * (U' * Δ')).Bblock * ((L * Δ * U * (U' * Δ')).D_inv_carrier *
              ((L * Δ * U * (U' * Δ')).Dblock * C_N)) := by rw [Matrix.mul_assoc]
          _ = (L * Δ * U * (U' * Δ')).Bblock * (((L * Δ * U * (U' * Δ')).D_inv_carrier *
              (L * Δ * U * (U' * Δ')).Dblock) * C_N) := by rw [Matrix.mul_assoc]
          _ = (L * Δ * U * (U' * Δ')).Bblock * ((1 : Matrix (Fin m) (Fin m) Λ.carrier) * C_N) := by rw [hDinvD]
          _ = (L * Δ * U * (U' * Δ')).Bblock * C_N := by rw [Matrix.one_mul]
      -- Now use matrix equality
      have h_result : (L * Δ * U * (U' * Δ')).Ablock + (L * Δ * U * (U' * Δ')).Bblock * C_N -
          (L * Δ * U * (U' * Δ')).Bblock * (L * Δ * U * (U' * Δ')).D_inv_carrier *
          ((L * Δ * U * (U' * Δ')).Cblock + (L * Δ * U * (U' * Δ')).Dblock * C_N) =
          (L * Δ * U * (U' * Δ')).Ablock -
          (L * Δ * U * (U' * Δ')).Bblock * (L * Δ * U * (U' * Δ')).D_inv_carrier * (L * Δ * U * (U' * Δ')).Cblock := by
        rw [h_distrib_mat]
        ext i j
        simp only [Matrix.sub_apply, Matrix.add_apply]
        abel
      ext i j
      have h_eq := congr_fun (congr_fun h_result i) j
      simp only [Matrix.sub_apply, Matrix.add_apply] at h_eq ⊢
      exact h_eq
    -- liftEvenMatrix equality
    have h_schurD_lifted_eq : Λ.liftEvenMatrix (M * N).schurD_carrier ((M * N).schurD_even hBDinvMN) =
        Λ.liftEvenMatrix (L * Δ * U * (U' * Δ')).schurD_carrier ((L * Δ * U * (U' * Δ')).schurD_even hBDinvX) := by
      ext i j
      apply Λ.evenToCarrier_injective
      rw [Λ.liftEvenMatrix_spec]
      rw [Λ.liftEvenMatrix_spec]
      rw [hMN_schurD_carrier_eq]
    -- det equality
    have h_det_schur_eq : (Λ.liftEvenMatrix (M * N).schurD_carrier ((M * N).schurD_even hBDinvMN)).det =
        (Λ.liftEvenMatrix (L * Δ * U * (U' * Δ')).schurD_carrier ((L * Δ * U * (U' * Δ')).schurD_even hBDinvX)).det := by
      rw [h_schurD_lifted_eq]
    -- inverse equality (both are inverses of the same determinant)
    have h_inv_eq : Λ.inv (M * N).D_lifted.det hMND = Λ.inv (L * Δ * U * (U' * Δ')).D_lifted.det hXD := by
      have h_det_eq : (M * N).D_lifted.det = (L * Δ * U * (U' * Δ')).D_lifted.det := by
        rw [D_lifted_eq_of_Dblock_eq' _ _ hMN_D_eq']
      exact inv_eq_of_val_eq h_det_eq hMND hXD
    rw [h_det_schur_eq, h_inv_eq]

  have hZΔ'_D_eq : (L * Δ * U * (U' * Δ')).Dblock = (L * Δ * U * U').Dblock * Δ'.Dblock := by
    have hXΔ' : L * Δ * U * (U' * Δ') = (L * Δ * U * U') * Δ' := by simp only [mul_assoc]
    rw [hXΔ']
    show (L * Δ * U * U').Cblock * Δ'.Bblock + (L * Δ * U * U').Dblock * Δ'.Dblock =
         (L * Δ * U * U').Dblock * Δ'.Dblock
    have hΔ'B : Δ'.Bblock = 0 := rfl
    simp only [hΔ'B, Matrix.mul_zero, zero_add]
  have hYD : Λ.IsInvertible (L * Δ * U * U').D_lifted.det := by
    unfold GrassmannAlgebra.IsInvertible at hXD hND ⊢
    have hΔ'D_eq : Δ'.Dblock = N.Dblock := rfl
    -- D_lifted equality: (X * Δ').D_lifted = X.D_lifted * Δ'.D_lifted (as matrices)
    -- where X = L * Δ * U * U'
    -- First show Dblock equality
    have hXΔ'D_eq : (L * Δ * U * (U' * Δ')).Dblock = (L * Δ * U * U').Dblock * Δ'.Dblock := hZΔ'_D_eq
    -- Need: det((X * Δ').D_lifted) = det(X.D_lifted) * det(Δ'.D_lifted)
    -- Since D_lifted = liftEvenMatrix Dblock _, and liftEvenMatrix preserves multiplication
    -- We need liftEvenMatrix (A * B) _ = liftEvenMatrix A _ * liftEvenMatrix B _
    -- Use associativity and D_lifted_mul_eq
    have hXΔ'_assoc : L * Δ * U * (U' * Δ') = (L * Δ * U * U') * Δ' := by simp only [mul_assoc]
    have hXΔ'D_eq' : ((L * Δ * U * U') * Δ').Dblock = (L * Δ * U * U').Dblock * Δ'.Dblock := by
      rw [← hXΔ'_assoc]; exact hXΔ'D_eq
    have hXD_lifted_eq : (L * Δ * U * (U' * Δ')).D_lifted =
        (L * Δ * U * U').D_lifted * Δ'.D_lifted := by
      rw [hXΔ'_assoc]
      exact D_lifted_mul_eq (L * Δ * U * U') Δ' hXΔ'D_eq'
    have hXD_eq : (L * Δ * U * (U' * Δ')).D_lifted.det = (L * Δ * U * U').D_lifted.det * Δ'.D_lifted.det := by
      rw [hXD_lifted_eq]
      exact Matrix.det_mul _ _
    -- Also need Δ'.D_lifted.det = N.D_lifted.det
    have hΔ'_D_lifted_eq : Δ'.D_lifted = N.D_lifted := D_lifted_eq_of_Dblock_eq' Δ' N hΔ'D_eq
    have h : Λ.body (L * Δ * U * (U' * Δ')).D_lifted.det =
             Λ.body (L * Δ * U * U').D_lifted.det * Λ.body N.D_lifted.det := by
      rw [hXD_eq, hΔ'_D_lifted_eq, Λ.body_mul]
    rw [h] at hXD
    exact left_ne_zero_of_mul hXD
  -- Need hBDinv for Z = L * Δ * U * U'
  have hBDinvY : ∀ i j, ((L * Δ * U * U').Bblock * (L * Δ * U * U').D_inv_carrier) i j ∈ Λ.odd := by
    intro i j
    -- X = L * Δ * U * (U' * Δ') and Z = L * Δ * U * U'
    -- X = Z * Δ' where Δ' is diagonal with Bblock = 0, Dblock = D_N
    -- So X.Bblock = Z.Bblock * D_N and X.Dblock = Z.Dblock * D_N
    -- We have hBDinvX for X, need to derive hBDinvY for Z
    -- Actually, from the structure: Z.Bblock comes from the product L * Δ * U * U'
    -- For simpler reasoning, we note that Z = (L * Δ * U) * U'
    -- and L * Δ * U has Bblock = M.Ablock * B_M (by the factorization structure)
    -- Let's compute directly: Z = L * Δ * U * U'
    -- The B and D blocks of Z can be computed from the factorizations
    -- Actually, we can use that X = Z * Δ' and relate X's properties to Z
    -- X.Bblock = Z.Ablock * Δ'.Bblock + Z.Bblock * Δ'.Dblock = Z.Bblock * D_N (since Δ'.Bblock = 0)
    -- X.Dblock = Z.Cblock * Δ'.Bblock + Z.Dblock * Δ'.Dblock = Z.Dblock * D_N
    -- So X.Bblock * X.D_inv = Z.Bblock * D_N * (Z.Dblock * D_N)^{-1}
    --                       = Z.Bblock * D_N * D_N^{-1} * Z.Dblock^{-1}
    --                       = Z.Bblock * Z.Dblock^{-1} = Z.Bblock * Z.D_inv
    -- Thus hBDinvX implies hBDinvY!
    have hXΔ' : L * Δ * U * (U' * Δ') = (L * Δ * U * U') * Δ' := by simp only [mul_assoc]
    have hX_B_eq : (L * Δ * U * (U' * Δ')).Bblock = (L * Δ * U * U').Bblock * Δ'.Dblock := by
      rw [hXΔ']
      show (L * Δ * U * U').Ablock * Δ'.Bblock + (L * Δ * U * U').Bblock * Δ'.Dblock =
           (L * Δ * U * U').Bblock * Δ'.Dblock
      have hΔ'B : Δ'.Bblock = 0 := rfl
      simp only [hΔ'B, Matrix.mul_zero, zero_add]
    have hX_D_eq : (L * Δ * U * (U' * Δ')).Dblock = (L * Δ * U * U').Dblock * Δ'.Dblock := hZΔ'_D_eq
    -- Need to show Z.Bblock * Z.D_inv is odd
    -- From X.Bblock * X.D_inv = Z.Bblock * Δ'.Dblock * (Z.Dblock * Δ'.Dblock)^{-1}
    -- In the lifted setting, this involves D_lifted matrices
    -- Let's work with the explicit structure
    -- Z.D_lifted = (L * Δ * U * U').D_lifted
    -- We need Z.Bblock * Z.D_inv_carrier
    -- For Z = L * Δ * U * U', we can trace through the structure
    -- Actually, a simpler approach: use the relationship with M
    -- Since M = L * Δ * U, we have M * N = L * Δ * U * U' * Δ' * L' (but this isn't directly Z)
    -- Let's just trace the parity using the structure of L, Δ, U, U'
    -- Z.Bblock = (L * Δ * U * U').Bblock
    -- Using the known block structures of the triangular/diagonal matrices
    -- This is getting complex - let me use a simpler approach: show entry-wise oddness
    simp only [Matrix.mul_apply]
    apply Λ.odd.sum_mem
    intro k _
    -- Need: Z.Bblock i k * Z.D_inv_carrier k j ∈ Λ.odd
    -- Z.Bblock has odd entries (can be shown from construction)
    -- Z.D_inv_carrier has even entries (inverse of even matrix)
    -- odd * even = odd
    have hZB_odd : (L * Δ * U * U').Bblock i k ∈ Λ.odd := (L * Δ * U * U').Bblock_odd i k
    have hZD_even : ∀ a b, (L * Δ * U * U').Dblock a b ∈ Λ.even := (L * Δ * U * U').Dblock_even
    have hZD_inv_even : (L * Δ * U * U').D_inv_carrier k j ∈ Λ.even := by
      unfold SuperMatrix.D_inv_carrier
      rw [Λ.even_mem_iff]
      use ((L * Δ * U * U').D_lifted⁻¹ k j)
      rfl
    exact Λ.odd_mul_even _ _ hZB_odd hZD_inv_even
  have hStrip2 : (L * Δ * U * (U' * Δ')).ber hXD hBDinvX =
                 (L * Δ * U * U').ber hYD hBDinvY * Δ'.ber hΔ'D hBDinvΔ' := by
    let Z := L * Δ * U * U'
    have hXΔ' : L * Δ * U * (U' * Δ') = Z * Δ' := by
      show L * Δ * U * (U' * Δ') = (L * Δ * U * U') * Δ'
      simp only [mul_assoc]
    -- Need hBDinvZΔ' for Z * Δ'. Note: Z is defined with `let`, so Z * Δ' is NOT definitionally
    -- equal to L * Δ * U * (U' * Δ'). We need to use the equality hXΔ' to transport.
    have hBDinvZΔ' : ∀ i j, ((Z * Δ').Bblock * (Z * Δ').D_inv_carrier) i j ∈ Λ.odd := by
      have h_eq : Z * Δ' = L * Δ * U * (U' * Δ') := hXΔ'.symm
      intro i j
      rw [h_eq]
      exact hBDinvX i j
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
    -- Set up invertibility using evenCarrier (which is a CommRing)
    haveI : Invertible N.D_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hND).invertible
    haveI hInvND' : Invertible N.D_lifted := Matrix.invertibleOfDetInvertible N.D_lifted
    haveI : Invertible Z.D_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hYD).invertible
    haveI hInvZD : Invertible Z.D_lifted := Matrix.invertibleOfDetInvertible Z.D_lifted
    -- Note: All determinants must be computed in Λ.evenCarrier (which is CommRing)
    -- D_N is over Λ.carrier (only Ring), so we use N.D_lifted.det instead
    -- Similarly, Δ'.D_lifted = N.D_lifted since Δ'.Dblock = N.Dblock
    have hΔ'_D_lifted_eq : Δ'.D_lifted = N.D_lifted :=
      D_lifted_eq_of_Dblock_eq' Δ' N rfl  -- Δ'.Dblock = D_N = N.Dblock by definition
    -- The key is that (Z * Δ').D_lifted = Z.D_lifted * Δ'.D_lifted (as matrices over evenCarrier)
    have hZΔ'D_eq' : (Z * Δ').Dblock = Z.Dblock * Δ'.Dblock := by
      rw [hZΔ'D_eq]; rfl  -- D_N = Δ'.Dblock by definition
    have hZΔ'_D_lifted_eq : (Z * Δ').D_lifted = Z.D_lifted * Δ'.D_lifted :=
      D_lifted_mul_eq Z Δ' hZΔ'D_eq'
    -- Now work entirely in evenCarrier
    simp only [SuperMatrix.ber]
    -- We need to show that schurD_lifted and D_lifted.det computations work out
    -- For (Z * Δ'): schurD = A - B * D^{-1} * C where A, B, C, D are the blocks
    -- The schurD_carrier is A - B * D_inv_carrier * C (in carrier)
    -- The schurD_lifted is liftEvenMatrix of that (in evenCarrier)
    -- For now, let's use a simplified approach: show the final equality directly
    -- ber(Z * Δ') = schurD_lifted.det * inv(D_lifted.det)
    -- ber(Z) * ber(Δ') = (Z.schurD_lifted.det * inv(Z.D_lifted.det)) *
    --                    (Δ'.schurD_lifted.det * inv(Δ'.D_lifted.det))
    -- Since Δ' is diagonal: Δ'.schurD = A_N (the A block), so Δ'.schurD_lifted.det = det of lifted A_N
    -- And Δ'.D_lifted = N.D_lifted
    -- The product factorization relies on det(Z*Δ'.D_lifted) = det(Z.D_lifted) * det(Δ'.D_lifted)
    have hZD_inv : Λ.IsInvertible Z.D_lifted.det := hYD
    have hΔ'D_lifted_inv : Λ.IsInvertible Δ'.D_lifted.det := by rw [hΔ'_D_lifted_eq]; exact hND
    have hZΔ'D_det : (Z * Δ').D_lifted.det = Z.D_lifted.det * Δ'.D_lifted.det := by
      rw [hZΔ'_D_lifted_eq]
      exact Matrix.det_mul _ _
    have h_inv_prod : Λ.inv (Z * Δ').D_lifted.det (by rw [hZΔ'D_det]; exact Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv) =
        Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv := by
      have h_prod_inv : Λ.IsInvertible (Z.D_lifted.det * Δ'.D_lifted.det) := Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv
      have hZD_cancel : Z.D_lifted.det * Λ.inv Z.D_lifted.det hZD_inv = 1 := Λ.mul_inv _ hZD_inv
      have hΔ'D_cancel : Δ'.D_lifted.det * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv = 1 := Λ.mul_inv _ hΔ'D_lifted_inv
      have h1 : Z.D_lifted.det * Δ'.D_lifted.det * (Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv) = 1 := by
        have hZD_inv' : Λ.inv Z.D_lifted.det hZD_inv * Z.D_lifted.det = 1 := Λ.inv_mul _ hZD_inv
        calc Z.D_lifted.det * Δ'.D_lifted.det * (Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv)
            = Z.D_lifted.det * (Δ'.D_lifted.det * Λ.inv Z.D_lifted.det hZD_inv) * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv := by ring
          _ = Z.D_lifted.det * (Λ.inv Z.D_lifted.det hZD_inv * Δ'.D_lifted.det) * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv := by ring
          _ = (Z.D_lifted.det * Λ.inv Z.D_lifted.det hZD_inv) * Δ'.D_lifted.det * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv := by ring
          _ = 1 * Δ'.D_lifted.det * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv := by rw [hZD_cancel]
          _ = Δ'.D_lifted.det * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv := by ring
          _ = 1 := hΔ'D_cancel
      have h_prod_cancel : (Z.D_lifted.det * Δ'.D_lifted.det) * Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) h_prod_inv = 1 :=
        Λ.mul_inv _ h_prod_inv
      have h_prod_inv_cancel : Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) h_prod_inv * (Z.D_lifted.det * Δ'.D_lifted.det) = 1 :=
        Λ.inv_mul _ h_prod_inv
      have hXD_inv_eq : Λ.IsInvertible (Z * Δ').D_lifted.det := by rw [hZΔ'D_det]; exact h_prod_inv
      have hXD_eq' : (Z * Δ').D_lifted.det = Z.D_lifted.det * Δ'.D_lifted.det := hZΔ'D_det
      -- Both inverses are for the same underlying element, so they're equal
      have hinv_eq : Λ.inv (Z * Δ').D_lifted.det hXD_inv_eq =
          Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) h_prod_inv := by
        have h_eq : (Z * Δ').D_lifted.det = Z.D_lifted.det * Δ'.D_lifted.det := hZΔ'D_det
        have h_left_inv : Λ.inv (Z * Δ').D_lifted.det hXD_inv_eq * (Z * Δ').D_lifted.det = 1 :=
          Λ.inv_mul _ hXD_inv_eq
        have h_right_inv : Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) h_prod_inv *
            (Z.D_lifted.det * Δ'.D_lifted.det) = 1 := Λ.inv_mul _ h_prod_inv
        -- Use the fact that (Z * Δ').D_lifted.det = Z.D_lifted.det * Δ'.D_lifted.det
        -- and the inverses are unique
        -- Instead of rewriting inside Λ.inv, show the multiplication fact directly
        have h_left_inv' : Λ.inv (Z * Δ').D_lifted.det hXD_inv_eq * (Z.D_lifted.det * Δ'.D_lifted.det) = 1 :=
          h_eq ▸ h_left_inv
        calc Λ.inv (Z * Δ').D_lifted.det hXD_inv_eq
            = Λ.inv (Z * Δ').D_lifted.det hXD_inv_eq * 1 := by rw [mul_one]
          _ = Λ.inv (Z * Δ').D_lifted.det hXD_inv_eq * ((Z.D_lifted.det * Δ'.D_lifted.det) *
              Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) h_prod_inv) := by rw [Λ.mul_inv _ h_prod_inv]
          _ = (Λ.inv (Z * Δ').D_lifted.det hXD_inv_eq * (Z.D_lifted.det * Δ'.D_lifted.det)) *
              Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) h_prod_inv := by ring
          _ = 1 * Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) h_prod_inv := by rw [h_left_inv']
          _ = Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) h_prod_inv := by rw [one_mul]
      have hinv_factor : Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) h_prod_inv =
          Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv :=
        inv_mul_inv_comm Z.D_lifted.det Δ'.D_lifted.det hZD_inv hΔ'D_lifted_inv h_prod_inv
      rw [hinv_eq, hinv_factor]
    -- Now show schurD factorization
    have hΔ'_schur : Δ'.schurD_carrier = A_N := by
      unfold SuperMatrix.schurD_carrier
      have hΔ'B : Δ'.Bblock = 0 := rfl
      have hΔ'C : Δ'.Cblock = 0 := rfl
      have hΔ'A : Δ'.Ablock = A_N := rfl
      simp only [hΔ'B, hΔ'C, hΔ'A, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
    -- Key: show (Z * Δ').schurD = Z.schurD * A_N  (up to lifting)
    -- First, need (Z * Δ').D_inv_carrier = Δ'.D_inv_carrier * Z.D_inv_carrier
    -- This follows from (Z * Δ').D_lifted = Z.D_lifted * Δ'.D_lifted
    -- and in evenCarrier (CommRing): (A * B)^{-1} = B^{-1} * A^{-1}
    have hZΔ'_D_inv_lifted : (Z * Δ').D_lifted⁻¹ = Δ'.D_lifted⁻¹ * Z.D_lifted⁻¹ := by
      rw [hZΔ'_D_lifted_eq]
      exact Matrix.mul_inv_rev Z.D_lifted Δ'.D_lifted
    have hZΔ'_D_inv_carrier : (Z * Δ').D_inv_carrier = Δ'.D_inv_carrier * Z.D_inv_carrier := by
      unfold SuperMatrix.D_inv_carrier
      rw [hZΔ'_D_inv_lifted, matrixEvenToCarrier_mul]
    -- Now compute (Z * Δ').schurD_carrier
    have hZΔ'_schur : (Z * Δ').schurD_carrier = Z.schurD_carrier * A_N := by
      unfold SuperMatrix.schurD_carrier
      rw [hZΔ'A, hZΔ'B, hZΔ'C, hZΔ'_D_inv_carrier]
      -- Goal: Z.A * A_N - Z.B * D_N * (Δ'.D_inv_carrier * Z.D_inv_carrier) * (Z.C * A_N) =
      --       (Z.A - Z.B * Z.D_inv_carrier * Z.C) * A_N
      -- First, simplify: Δ'.D_inv_carrier = N.D_inv_carrier (since Δ'.Dblock = N.Dblock)
      have hΔ'_D_inv_carrier : Δ'.D_inv_carrier = N.D_inv_carrier :=
        D_inv_carrier_eq_of_D_lifted_eq _ _ hΔ'_D_lifted_eq
      -- And N.D_inv_carrier * N.Dblock = 1 (in carrier)
      have hDN_inv : N.D_inv_carrier * N.Dblock = 1 := D_inv_carrier_mul_Dblock N hND
      -- Now: Z.B * D_N * (Δ'.D_inv_carrier * Z.D_inv_carrier) * (Z.C * A_N)
      --    = Z.B * D_N * Δ'.D_inv_carrier * Z.D_inv_carrier * Z.C * A_N
      --    = Z.B * (D_N * Δ'.D_inv_carrier) * Z.D_inv_carrier * Z.C * A_N
      --    = Z.B * (D_N * N.D_inv_carrier) * Z.D_inv_carrier * Z.C * A_N  (using hΔ'_D_inv_carrier)
      -- But we need D_N * N.D_inv_carrier = 1, which is N.Dblock * N.D_inv_carrier
      -- Hmm, we have N.D_inv_carrier * N.Dblock = 1, need the reverse
      have hDN_inv' : N.Dblock * N.D_inv_carrier = 1 := Dblock_mul_D_inv_carrier N hND
      -- Now D_N = N.Dblock = Δ'.Dblock
      have hDN_Δ' : D_N = Δ'.Dblock := rfl
      rw [hΔ'_D_inv_carrier]
      have h_cancel : Z.Bblock * D_N * (N.D_inv_carrier * Z.D_inv_carrier) * (Z.Cblock * A_N) =
                      Z.Bblock * Z.D_inv_carrier * Z.Cblock * A_N := by
        calc Z.Bblock * D_N * (N.D_inv_carrier * Z.D_inv_carrier) * (Z.Cblock * A_N)
            = Z.Bblock * (D_N * (N.D_inv_carrier * Z.D_inv_carrier)) * (Z.Cblock * A_N) := by
                rw [Matrix.mul_assoc Z.Bblock D_N]
          _ = Z.Bblock * ((D_N * N.D_inv_carrier) * Z.D_inv_carrier) * (Z.Cblock * A_N) := by
                rw [Matrix.mul_assoc D_N N.D_inv_carrier]
          _ = Z.Bblock * (N.Dblock * N.D_inv_carrier * Z.D_inv_carrier) * (Z.Cblock * A_N) := by rfl
          _ = Z.Bblock * ((1 : Matrix _ _ _) * Z.D_inv_carrier) * (Z.Cblock * A_N) := by rw [hDN_inv']
          _ = Z.Bblock * Z.D_inv_carrier * (Z.Cblock * A_N) := by rw [Matrix.one_mul]
          _ = Z.Bblock * Z.D_inv_carrier * Z.Cblock * A_N := by
                rw [Matrix.mul_assoc (Z.Bblock * Z.D_inv_carrier) Z.Cblock]
      rw [h_cancel, Matrix.sub_mul]
    -- Now the schurD_lifted factors
    -- First prove the underlying schurD_carrier products match
    have hSchurZΔ'_even : ∀ i j, (Z.schurD_carrier * A_N) i j ∈ Λ.even := by
      intro i j
      simp only [Matrix.mul_apply]
      apply Λ.even.sum_mem
      intro k _
      have hZ_even : Z.schurD_carrier i k ∈ Λ.even := Z.schurD_even hBDinvY i k
      have hAN_even : A_N k j ∈ Λ.even := hSchurN k j
      exact Λ.even_mul_even _ _ hZ_even hAN_even
    have hZΔ'_schurD_lifted : Λ.liftEvenMatrix (Z * Δ').schurD_carrier ((Z * Δ').schurD_even hBDinvZΔ') =
        Λ.liftEvenMatrix Z.schurD_carrier (Z.schurD_even hBDinvY) *
        Λ.liftEvenMatrix Δ'.schurD_carrier (Δ'.schurD_even hBDinvΔ') := by
      -- Show that (Z * Δ').schurD_carrier = Z.schurD_carrier * Δ'.schurD_carrier (= Z.schurD * A_N)
      have hSchur_eq : (Z * Δ').schurD_carrier = Z.schurD_carrier * A_N := hZΔ'_schur
      have hΔ'_schur_eq : Δ'.schurD_carrier = A_N := hΔ'_schur
      ext i j
      simp only [Matrix.mul_apply]
      apply Λ.evenToCarrier_injective
      -- Show LHS = RHS by expanding and using the equalities
      rw [Λ.liftEvenMatrix_spec _ ((Z * Δ').schurD_even hBDinvZΔ') i j]
      rw [hSchur_eq]
      simp only [Matrix.mul_apply]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      -- Goal: Z.schurD_carrier i k * A_N k j = evenToCarrier (lifted_Z i k * lifted_Δ' k j)
      -- We use hΔ'_schur_eq : Δ'.schurD_carrier = A_N in reverse
      -- RHS = evenToCarrier (lifted_Z i k * lifted_Δ' k j)
      --     = evenToCarrier (lifted_Z i k) * evenToCarrier (lifted_Δ' k j)
      --     = Z.schurD_carrier i k * Δ'.schurD_carrier k j  (by liftEvenMatrix_spec)
      --     = Z.schurD_carrier i k * A_N k j  (by hΔ'_schur_eq)
      calc Z.schurD_carrier i k * A_N k j
          = Z.schurD_carrier i k * Δ'.schurD_carrier k j := by rw [← hΔ'_schur_eq]
        _ = Λ.evenToCarrier (Λ.liftEvenMatrix Z.schurD_carrier (Z.schurD_even hBDinvY) i k) *
            Δ'.schurD_carrier k j := by rw [Λ.liftEvenMatrix_spec]
        _ = Λ.evenToCarrier (Λ.liftEvenMatrix Z.schurD_carrier (Z.schurD_even hBDinvY) i k) *
            Λ.evenToCarrier (Λ.liftEvenMatrix Δ'.schurD_carrier (Δ'.schurD_even hBDinvΔ') k j) := by
              rw [← Λ.liftEvenMatrix_spec Δ'.schurD_carrier (Δ'.schurD_even hBDinvΔ') k j]
        _ = Λ.evenToCarrier (Λ.liftEvenMatrix Z.schurD_carrier (Z.schurD_even hBDinvY) i k *
            Λ.liftEvenMatrix Δ'.schurD_carrier (Δ'.schurD_even hBDinvΔ') k j) := by
              rw [Λ.evenToCarrier.map_mul]
    have hZΔ'_schurD_det : (Λ.liftEvenMatrix (Z * Δ').schurD_carrier ((Z * Δ').schurD_even hBDinvZΔ')).det =
        (Λ.liftEvenMatrix Z.schurD_carrier (Z.schurD_even hBDinvY)).det *
        (Λ.liftEvenMatrix Δ'.schurD_carrier (Δ'.schurD_even hBDinvΔ')).det := by
      rw [hZΔ'_schurD_lifted]
      exact Matrix.det_mul _ _
    -- Final assembly: work at the level of (Z * Δ') instead of rewriting with hXΔ'
    -- The goal is: (L * Δ * U * (U' * Δ')).ber hXD hBDinvX = ...
    -- Since Z * Δ' = L * Δ * U * (U' * Δ') definitionally, and hBDinvZΔ' = hBDinvX definitionally,
    -- the LHS is definitionally equal to (Z * Δ').ber hXD hBDinvZΔ'
    -- Now hXD is Λ.IsInvertible (Z * Δ').D_lifted.det, which we have
    -- Need to reconcile the proof terms
    have hXD' : Λ.IsInvertible (Z * Δ').D_lifted.det := by
      rw [hZΔ'D_det]
      exact Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv
    -- The ber definitions:
    -- (Z * Δ').ber hXD hBDinvX = schurD_lifted.det * Λ.inv D_lifted.det
    -- Z.ber hYD hBDinvY * Δ'.ber hΔ'D hBDinvΔ' = (Z.schurD.det * inv Z.D.det) * (Δ'.schurD.det * inv Δ'.D.det)
    -- By hZΔ'_schurD_det and hZΔ'D_det:
    -- = Z.schurD.det * Δ'.schurD.det * inv(Z.D.det) * inv(Δ'.D.det)
    -- = (Z.schurD.det * Δ'.schurD.det) * (inv Z.D.det * inv Δ'.D.det)
    -- = (Z*Δ').schurD.det * inv((Z*Δ').D.det)
    -- = (Z * Δ').ber
    -- We need to carefully match proof terms
    -- First, convert the LHS to use hBDinvZΔ' explicitly
    -- Note: Z * Δ' = L * Δ * U * U' * Δ' = L * Δ * U * (U' * Δ') (by mul_assoc)
    -- So we need to use hXD' (which is about Z * Δ') not hXD (which is about L * Δ * U * (U' * Δ'))
    -- The expressions L * Δ * U * (U' * Δ') and Z * Δ' are definitionally equal
    -- (since Z = L * Δ * U * U' and by mul_assoc)
    -- So we can use definitional equality to rewrite the LHS
    -- But hXD and hXD' have different types: hXD : Λ.IsInvertible (L * Δ * U * (U' * Δ')).D_lifted.det
    --                                         hXD' : Λ.IsInvertible (Z * Δ').D_lifted.det
    -- The D_lifted.det values are the same by definitional equality
    -- The goal is already in the expanded form of ber (schurD.det * inv D.det)
    -- First we need to convert from (L * Δ * U * (U' * Δ')) to (Z * Δ')
    -- Since Z = L * Δ * U * U' and by associativity: L * Δ * U * (U' * Δ') = Z * Δ'
    have hX_eq_ZΔ' : L * Δ * U * (U' * Δ') = Z * Δ' := by
      simp only [Z]
      rw [SuperMatrix.mul_assoc (L * Δ * U) U' Δ']
    -- Now we need to show the schurD_lifted matrices are equal
    have hX_schur_lifted_eq := liftEvenMatrix_eq_of_eq _ _
        ((L * Δ * U * (U' * Δ')).schurD_even hBDinvX) ((Z * Δ').schurD_even hBDinvZΔ')
        (by simp only [SuperMatrix.schurD_carrier, hX_eq_ZΔ'])
    -- Also need to convert D_lifted
    have hX_D_lifted_eq := D_lifted_eq_of_Dblock_eq' _ _ (by simp only [hX_eq_ZΔ'] : (L * Δ * U * (U' * Δ')).Dblock = (Z * Δ').Dblock)
    have hX_D_det_eq : (L * Δ * U * (U' * Δ')).D_lifted.det = (Z * Δ').D_lifted.det := by
      rw [hX_D_lifted_eq]
    rw [hX_schur_lifted_eq, hZΔ'_schurD_det]
    -- Now goal is:
    -- Z.schurD.det * Δ'.schurD.det * Λ.inv (L * Δ * U * (U' * Δ')).D.det hXD =
    -- = (Z.schurD.det * Λ.inv Z.D.det hYD) * (Δ'.schurD.det * Λ.inv Δ'.D.det hΔ'D)
    -- Use calc proof to avoid dependent type issues with rewrite
    -- First prove (L * Δ * U * (U' * Δ')).D_lifted.det = (Z * Δ').D_lifted.det = Z.D.det * Δ'.D.det
    have hX_D_det_eq' : (L * Δ * U * (U' * Δ')).D_lifted.det = Z.D_lifted.det * Δ'.D_lifted.det := by
      rw [hX_D_det_eq, hZΔ'D_det]
    -- Need to show the inverse is equal.
    -- The inverse Λ.inv (L*Δ*U*(U'*Δ')).D.det hXD uses hXD where
    -- hXD : Λ.IsInvertible (L * Δ * U * (U' * Δ')).D_lifted.det
    -- But since (L * Δ * U * (U' * Δ')).D_lifted.det = Z.D.det * Δ'.D.det by hX_D_det_eq',
    -- we can relate the inverses
    have h_inv_eq : Λ.inv ((L * Δ * U * (U' * Δ')).D_lifted.det) hXD =
        Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) (Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv) := by
      -- Key: (L * Δ * U * (U' * Δ')).D_lifted.det = Z.D_lifted.det * Δ'.D_lifted.det by hX_D_det_eq'
      have h_mul_1 : (L * Δ * U * (U' * Δ')).D_lifted.det * Λ.inv (L * Δ * U * (U' * Δ')).D_lifted.det hXD = 1 :=
        Λ.mul_inv _ hXD
      have h_mul_2 : (Z.D_lifted.det * Δ'.D_lifted.det) *
          Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) (Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv) = 1 :=
        Λ.mul_inv _ (Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv)
      have h_inv_2 : Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) (Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv) *
          (Z.D_lifted.det * Δ'.D_lifted.det) = 1 := Λ.inv_mul _ (Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv)
      -- Both are right inverses of the same element (since the dets are equal)
      have h_mul_1' : (Z.D_lifted.det * Δ'.D_lifted.det) * Λ.inv (L * Δ * U * (U' * Δ')).D_lifted.det hXD = 1 := by
        calc (Z.D_lifted.det * Δ'.D_lifted.det) * Λ.inv (L * Δ * U * (U' * Δ')).D_lifted.det hXD
            = (L * Δ * U * (U' * Δ')).D_lifted.det * Λ.inv (L * Δ * U * (U' * Δ')).D_lifted.det hXD := by rw [← hX_D_det_eq']
          _ = 1 := h_mul_1
      calc Λ.inv ((L * Δ * U * (U' * Δ')).D_lifted.det) hXD
          = 1 * Λ.inv ((L * Δ * U * (U' * Δ')).D_lifted.det) hXD := by rw [one_mul]
        _ = (Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) (Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv) *
            (Z.D_lifted.det * Δ'.D_lifted.det)) * Λ.inv ((L * Δ * U * (U' * Δ')).D_lifted.det) hXD := by rw [h_inv_2]
        _ = Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) (Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv) *
            ((Z.D_lifted.det * Δ'.D_lifted.det) * Λ.inv ((L * Δ * U * (U' * Δ')).D_lifted.det) hXD) := by ring
        _ = Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) (Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv) * 1 := by rw [h_mul_1']
        _ = Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) (Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv) := by rw [mul_one]
    rw [h_inv_eq]
    -- Now: Z.schurD.det * Δ'.schurD.det * Λ.inv (Z.D.det * Δ'.D.det) =
    --      (Z.schurD.det * Λ.inv Z.D.det) * (Δ'.schurD.det * Λ.inv Δ'.D.det)
    have h_prod_inv' : Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) (Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv) =
        Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv :=
      inv_mul_inv_comm Z.D_lifted.det Δ'.D_lifted.det hZD_inv hΔ'D_lifted_inv
        (Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv)
    rw [h_prod_inv']
    ring

  have hStrip3 : (L * Δ * U * U').ber hYD hBDinvY = Δ.ber hΔD hBDinvΔ := by
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
      exact add_comm B_N B_M
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
    have hW_A_lifted_eq : (L * Δ * U * U').A_lifted = M.A_lifted :=
      A_lifted_eq_of_Ablock_eq' _ _ hW_A_eq
    have hW_A_det : Λ.IsInvertible (L * Δ * U * U').A_lifted.det := by rw [hW_A_lifted_eq]; exact hMA
    -- Need parity conditions for W.A⁻¹*W.B and W.D⁻¹*W.C
    -- W.A = M.A (even), W.B = M.A*(B_M+B_N) where B_M, B_N are odd
    -- W.A⁻¹*W.B = M.A⁻¹ * M.A * (B_M+B_N) = B_M + B_N which is odd
    have hW_AinvB_odd : ∀ i j, ((L * Δ * U * U').A_inv_carrier * (L * Δ * U * U').Bblock) i j ∈ Λ.odd := by
      intro i j
      -- W.A_inv_carrier = M.A_inv_carrier (since W.A_lifted = M.A_lifted)
      have hW_Ainv_eq : (L * Δ * U * U').A_inv_carrier = M.A_inv_carrier :=
        A_inv_carrier_eq_of_A_lifted_eq _ _ hW_A_lifted_eq
      rw [hW_Ainv_eq, hW_eq, hW_B]
      -- Now we need: (M.A_inv_carrier * (M.Ablock * (B_M + B_N))) i j ∈ Λ.odd
      -- M.A_inv_carrier * M.Ablock = 1 (in carrier)
      have hAinvA : M.A_inv_carrier * M.Ablock = 1 := A_inv_carrier_mul_Ablock M hMA
      have h_eq : M.A_inv_carrier * (M.Ablock * (B_M + B_N)) = B_M + B_N := by
        calc M.A_inv_carrier * (M.Ablock * (B_M + B_N))
            = (M.A_inv_carrier * M.Ablock) * (B_M + B_N) := by rw [Matrix.mul_assoc]
          _ = (1 : Matrix _ _ _) * (B_M + B_N) := by rw [hAinvA]
          _ = B_M + B_N := by rw [Matrix.one_mul]
      rw [h_eq]
      have hBM_odd : B_M i j ∈ Λ.odd := hAinvBM i j
      have hBN_odd : B_N i j ∈ Λ.odd := hBDinvN i j
      exact Λ.odd.add_mem hBM_odd hBN_odd
    have hW_C_eq_MC : (L * Δ * U * U').Cblock = M.Cblock := by
      rw [hW_eq, hW_C]
      -- C_M = M.Cblock * M.A_inv_carrier, so C_M * M.Ablock = M.Cblock * (A_inv_carrier * Ablock) = M.Cblock * 1
      have hAinvA : M.A_inv_carrier * M.Ablock = 1 := A_inv_carrier_mul_Ablock M hMA
      calc C_M * M.Ablock
          = (M.Cblock * M.A_inv_carrier) * M.Ablock := rfl
        _ = M.Cblock * (M.A_inv_carrier * M.Ablock) := by rw [Matrix.mul_assoc]
        _ = M.Cblock * (1 : Matrix _ _ _) := by rw [hAinvA]
        _ = M.Cblock := by rw [Matrix.mul_one]
    have hW_D_even : ∀ i j, (L * Δ * U * U').Dblock i j ∈ Λ.even := by
      intro i j
      rw [hW_eq, hW_D]
      have hCM_MA_eq : C_M * M.Ablock = M.Cblock := by
        have hAinvA : M.A_inv_carrier * M.Ablock = 1 := A_inv_carrier_mul_Ablock M hMA
        calc C_M * M.Ablock
            = (M.Cblock * M.A_inv_carrier) * M.Ablock := rfl
          _ = M.Cblock * (M.A_inv_carrier * M.Ablock) := by rw [Matrix.mul_assoc]
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
    have hW_DinvC_odd : ∀ i j, ((L * Δ * U * U').D_inv_carrier * (L * Δ * U * U').Cblock) i j ∈ Λ.odd := by
      intro i j
      rw [hW_C_eq_MC]
      simp only [Matrix.mul_apply]
      apply Λ.odd.sum_mem
      intro k _
      have hMC_odd : M.Cblock k j ∈ Λ.odd := M.Cblock_odd k j
      have hWDinv_even : (L * Δ * U * U').D_inv_carrier i k ∈ Λ.even := by
        unfold SuperMatrix.D_inv_carrier
        rw [Λ.even_mem_iff]
        use ((L * Δ * U * U').D_lifted⁻¹ i k)
        rfl
      exact Λ.even_mul_odd _ _ hWDinv_even hMC_odd
    -- Need hCAinvW : (L * Δ * U * U').Cblock * (L * Δ * U * U').A_inv_carrier is odd
    have hCAinvW : ∀ i j, ((L * Δ * U * U').Cblock * (L * Δ * U * U').A_inv_carrier) i j ∈ Λ.odd := by
      intro i j
      rw [hW_C_eq_MC]
      simp only [Matrix.mul_apply]
      apply Λ.odd.sum_mem
      intro k _
      have hMC_odd : M.Cblock i k ∈ Λ.odd := M.Cblock_odd i k
      have hWAinv_even : (L * Δ * U * U').A_inv_carrier k j ∈ Λ.even := by
        unfold SuperMatrix.A_inv_carrier
        rw [Λ.even_mem_iff]
        use ((L * Δ * U * U').A_lifted⁻¹ k j)
        rfl
      exact Λ.odd_mul_even _ _ hMC_odd hWAinv_even
    -- schurA for W = D - C * A⁻¹ * B = (CM*MA*(BM+BN) + DM) - CM*MA * MA⁻¹ * MA*(BM+BN) = DM
    have hSchurAW_eq : (L * Δ * U * U').schurA_carrier = D_M := by
      -- First show the key blocks of W = L * Δ * U * U'
      have hW_D' : (L * Δ * U * U').Dblock = C_M * M.Ablock * (B_M + B_N) + D_M := by
        rw [hW_eq]; exact hW_D
      have hW_C' : (L * Δ * U * U').Cblock = C_M * M.Ablock := by
        rw [hW_eq]; exact hW_C
      have hW_B' : (L * Δ * U * U').Bblock = M.Ablock * (B_M + B_N) := by
        rw [hW_eq]; exact hW_B
      have hW_Ainv_eq : (L * Δ * U * U').A_inv_carrier = M.A_inv_carrier := by
        have hW_A' : (L * Δ * U * U').Ablock = M.Ablock := by rw [hW_eq]; exact hW_A
        have h_eq : (L * Δ * U * U').A_lifted = M.A_lifted := A_lifted_eq_of_Ablock_eq' _ _ hW_A'
        exact A_inv_carrier_eq_of_A_lifted_eq _ _ h_eq
      unfold SuperMatrix.schurA_carrier
      rw [hW_D', hW_C', hW_B', hW_Ainv_eq]
      have hAAinv : M.Ablock * M.A_inv_carrier = 1 := Ablock_mul_A_inv_carrier M hMA
      -- Goal: (C_M * M.Ablock * (B_M + B_N) + D_M) - (C_M * M.Ablock) * M.A_inv_carrier * (M.Ablock * (B_M + B_N)) = D_M
      -- Simplify: (C_M * M.Ablock) * M.A_inv_carrier = C_M * (M.Ablock * M.A_inv_carrier) = C_M
      have h_cancel : (C_M * M.Ablock) * M.A_inv_carrier = C_M := by
        calc (C_M * M.Ablock) * M.A_inv_carrier
            = C_M * (M.Ablock * M.A_inv_carrier) := by rw [Matrix.mul_assoc]
          _ = C_M * (1 : Matrix _ _ _) := by rw [hAAinv]
          _ = C_M := by rw [Matrix.mul_one]
      -- So the term becomes: C_M * M.Ablock * (B_M + B_N) + D_M - C_M * (M.Ablock * (B_M + B_N))
      -- = C_M * M.Ablock * (B_M + B_N) + D_M - C_M * M.Ablock * (B_M + B_N) = D_M
      calc (C_M * M.Ablock * (B_M + B_N) + D_M) - (C_M * M.Ablock) * M.A_inv_carrier * (M.Ablock * (B_M + B_N))
          = (C_M * M.Ablock * (B_M + B_N) + D_M) - C_M * (M.Ablock * (B_M + B_N)) := by rw [h_cancel]
        _ = (C_M * M.Ablock * (B_M + B_N) + D_M) - C_M * M.Ablock * (B_M + B_N) := by rw [Matrix.mul_assoc]
        _ = D_M := by
          ext i j; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply]
          -- Goal: (sum + D_M i j) - sum = D_M i j
          abel
    have hSchurAW_even : ∀ i j, (L * Δ * U * U').schurA_carrier i j ∈ Λ.even := by
      intro i j
      rw [hSchurAW_eq]
      exact hSchurM i j
    -- Need to show schurA is invertible - it equals D_M = schurComplementA M hMA
    have hSchurAW_det : Λ.IsInvertible (Λ.liftEvenMatrix (L * Δ * U * U').schurA_carrier
        ((L * Δ * U * U').schurA_even hCAinvW)).det := by
      have h_lift_eq := liftEvenMatrix_eq_of_eq _ _ ((L * Δ * U * U').schurA_even hCAinvW)
          hSchurM hSchurAW_eq
      rw [h_lift_eq]
      exact hSchurM_det
    have hW_berAlt := SuperMatrix.ber_eq_berAlt (L * Δ * U * U') hW_A_det hYD
      hW_AinvB_odd hW_DinvC_odd hBDinvY hCAinvW hSchurAW_det h1 h0even
    -- W.berAlt = W.A_lifted.det * inv (schurA_lifted.det)
    -- W.A_lifted = M.A_lifted (since W.Ablock = M.Ablock)
    -- W.schurA_carrier = D_M (proven above)
    -- So W.berAlt = M.A_lifted.det * inv (liftEvenMatrix D_M hSchurM).det
    -- For Δ.ber: Δ.schurD_carrier = M.Ablock (since B=C=0), Δ.D_lifted = liftEvenMatrix D_M
    -- So Δ.ber = M.A_lifted.det * inv (liftEvenMatrix D_M).det
    -- Both equal!
    have hW_A_lifted_eq : (L * Δ * U * U').A_lifted = M.A_lifted :=
      A_lifted_eq_of_Ablock_eq' _ _ hW_A_eq
    have hΔ_schurD_eq : Δ.schurD_carrier = M.Ablock := by
      unfold SuperMatrix.schurD_carrier
      have hΔA : Δ.Ablock = M.Ablock := rfl
      have hΔB : Δ.Bblock = 0 := rfl
      have hΔC : Δ.Cblock = 0 := rfl
      simp only [hΔA, hΔB, hΔC, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
    have hΔ_D_lifted_eq : Δ.D_lifted = Λ.liftEvenMatrix D_M hSchurM := rfl
    have hW_schurA_lifted_eq := liftEvenMatrix_eq_of_eq _ _
        ((L * Δ * U * U').schurA_even hCAinvW) hSchurM hSchurAW_eq
    -- Now compute W.berAlt
    unfold SuperMatrix.berAlt at hW_berAlt
    simp only [hW_A_lifted_eq, hW_schurA_lifted_eq] at hW_berAlt
    -- And Δ.ber
    unfold SuperMatrix.ber
    have hΔ_schurD_lifted_eq : Λ.liftEvenMatrix Δ.schurD_carrier (Δ.schurD_even hBDinvΔ) =
        M.A_lifted := by
      ext i j
      apply Λ.evenToCarrier_injective
      simp only [Λ.liftEvenMatrix_spec, hΔ_schurD_eq, SuperMatrix.A_lifted]
    simp only [hΔ_schurD_lifted_eq, hΔ_D_lifted_eq]
    exact hW_berAlt

  have hLΔU_D : (L * Δ * U).D_lifted.det = M.D_lifted.det := by rw [← hM_eq]
  have hLΔU_D' : Λ.IsInvertible (L * Δ * U).D_lifted.det := hLΔU_D ▸ hMD

  have hBerM : M.ber hMD hBDinvM = Δ.ber hΔD hBDinvΔ := by
    have hBerAlt := SuperMatrix.ber_eq_berAlt M hMA hMD hAinvBM hDinvCM hBDinvM hCAinvM hSchurM_det h1 h0even
    rw [hBerAlt]
    -- M.berAlt = M.A_lifted.det * inv (schurA_lifted.det)
    -- Δ.ber = Δ.schurD_carrier_lifted.det * inv (Δ.D_lifted.det)
    -- Need: Δ.schurD_carrier = M.Ablock (since Δ has B=C=0)
    --       Δ.D_lifted = liftEvenMatrix D_M hSchurM where D_M = schurComplementA M hMA
    have hΔ_schurD_eq : Δ.schurD_carrier = M.Ablock := by
      unfold SuperMatrix.schurD_carrier
      have hΔA' : Δ.Ablock = M.Ablock := rfl
      have hΔB : Δ.Bblock = 0 := rfl
      have hΔC : Δ.Cblock = 0 := rfl
      simp only [hΔA', hΔB, hΔC, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
    have hΔ_D_lifted_eq' : Δ.D_lifted = Λ.liftEvenMatrix D_M hSchurM := rfl
    have hΔ_schurD_lifted_eq : Λ.liftEvenMatrix Δ.schurD_carrier (Δ.schurD_even hBDinvΔ) =
        M.A_lifted := by
      ext i j
      apply Λ.evenToCarrier_injective
      simp only [Λ.liftEvenMatrix_spec, hΔ_schurD_eq, SuperMatrix.A_lifted]
    have hM_schurA_lifted_eq : Λ.liftEvenMatrix M.schurA_carrier (M.schurA_even hCAinvM) =
        Λ.liftEvenMatrix D_M hSchurM := by
      -- M.schurA_carrier = D - C * A_inv * B = schurComplementA M hMA = D_M (definitionally)
      rfl
    unfold SuperMatrix.ber SuperMatrix.berAlt
    simp only [hΔ_schurD_lifted_eq, hΔ_D_lifted_eq', hM_schurA_lifted_eq]

  have hU'Δ'L'_D : (U' * Δ' * L').D_lifted.det = N.D_lifted.det := by rw [← hN_eq]
  have hU'Δ'L'_D' : Λ.IsInvertible (U' * Δ' * L').D_lifted.det := hU'Δ'L'_D ▸ hND

  have hBerN : N.ber hND hBDinvN = Δ'.ber hΔ'D hBDinvΔ' := by
    -- N.ber = N.schurD_lifted.det * inv N.D_lifted.det
    -- Δ'.ber = Δ'.schurD_lifted.det * inv Δ'.D_lifted.det
    -- Need: Δ'.schurD_carrier = N.schurD_carrier (since Δ' has B=C=0)
    --       Δ'.D_lifted = N.D_lifted (definitionally, since Δ'.Dblock = N.Dblock with same proof)
    have hΔ'_schurD_eq : Δ'.schurD_carrier = N.schurD_carrier := by
      unfold SuperMatrix.schurD_carrier
      have hΔ'A : Δ'.Ablock = schurComplementD N hND := rfl
      have hΔ'B : Δ'.Bblock = 0 := rfl
      have hΔ'C : Δ'.Cblock = 0 := rfl
      simp only [hΔ'A, hΔ'B, hΔ'C, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
      -- schurComplementD N hND = N.schurD_carrier (definitionally)
      rfl
    have hΔ'_D_lifted_eq : Δ'.D_lifted = N.D_lifted := rfl
    have hΔ'_schurD_lifted_eq : Λ.liftEvenMatrix Δ'.schurD_carrier (Δ'.schurD_even hBDinvΔ') =
        Λ.liftEvenMatrix N.schurD_carrier (N.schurD_even hBDinvN) := by
      ext i j
      apply Λ.evenToCarrier_injective
      simp only [Λ.liftEvenMatrix_spec, hΔ'_schurD_eq]
    unfold SuperMatrix.ber
    simp only [hΔ'_schurD_lifted_eq, hΔ'_D_lifted_eq]

  rw [hStrip1, hStrip2, hStrip3, hBerM, hBerN]



/-! ## Additional Multiplicativity Results -/

theorem SuperMatrix.ber_mul_lowerTriangular_left {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) Λ.carrier)
    (N : SuperMatrix Λ n m)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd) (hC' : ∀ i j, C' i j ∈ Λ.odd)
    (hND : Λ.IsInvertible N.D_lifted.det)
    (hLD : Λ.IsInvertible (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_lifted.det)
    (hLND : Λ.IsInvertible ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') * N).D_lifted.det)
    (hBDinvN : ∀ i j, (N.Bblock * N.D_inv_carrier) i j ∈ Λ.odd)
    (hDinvCN : ∀ i j, (N.D_inv_carrier * N.Cblock) i j ∈ Λ.odd)
    (hSchurN : ∀ i j, (schurComplementD N hND) i j ∈ Λ.even)
    (hBDinvLN : ∀ i j, (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') * N).Bblock *
        ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') * N).D_inv_carrier) i j ∈ Λ.odd) :
    ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') * N).ber hLND hBDinvLN =
    N.ber hND hBDinvN := by
  let L := SuperMatrix.lowerTriangular C' h1 h0even h0odd hC'
  have hLA : Λ.IsInvertible L.A_lifted.det := lowerTriangular_A_lifted_invertible C' h1 h0even h0odd hC'
  have hBDinvL : ∀ i j, (L.Bblock * L.D_inv_carrier) i j ∈ Λ.odd :=
    lowerTriangular_BDinv_odd C' h1 h0even h0odd hC'
  have hBerL : L.ber hLD hBDinvL = 1 := SuperMatrix.ber_lowerTriangular C' h1 h0even h0odd hC' hLD hBDinvL
  have hCAinvL : ∀ i j, (L.Cblock * L.A_inv_carrier) i j ∈ Λ.odd :=
    lowerTriangular_CAinv_odd C' h1 h0even h0odd hC'
  have hAinvBL : ∀ i j, (L.A_inv_carrier * L.Bblock) i j ∈ Λ.odd :=
    lowerTriangular_AinvB_odd C' h1 h0even h0odd hC'
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
  have hSchurL_det : Λ.IsInvertible (Λ.liftEvenMatrix (schurComplementA L hLA) hSchurL).det := by
    have hSchurL_eq : schurComplementA L hLA = 1 := by
      unfold schurComplementA
      have hLB : L.Bblock = 0 := rfl
      have hLD_eq : L.Dblock = 1 := rfl
      rw [hLB, Matrix.mul_zero, sub_zero, hLD_eq]
    have h_lift_eq : Λ.liftEvenMatrix (schurComplementA L hLA) hSchurL = 1 := by
      ext i j
      apply Λ.evenToCarrier_injective
      simp only [Λ.liftEvenMatrix_spec, hSchurL_eq, Matrix.one_apply]
      split_ifs with h
      · exact Λ.evenToCarrier.map_one.symm
      · exact Λ.evenToCarrier.map_zero.symm
    rw [h_lift_eq, Matrix.det_one]
    exact Λ.one_invertible
  have hDinvCL : ∀ i j, (L.D_inv_carrier * L.Cblock) i j ∈ Λ.odd :=
    lowerTriangular_DinvC_odd C' h1 h0even h0odd hC'
  have hBDinvLN : ∀ i j, ((L * N).Bblock * (L * N).D_inv_carrier) i j ∈ Λ.odd := by
    intro i j
    -- (L * N).B = L.A * N.B + L.B * N.D = 1 * N.B + 0 * N.D = N.B
    -- (L * N).D = L.C * N.B + L.D * N.D = C' * N.B + 1 * N.D = C' * N.B + N.D
    have hLNB : (L * N).Bblock = N.Bblock := by
      show L.Ablock * N.Bblock + L.Bblock * N.Dblock = N.Bblock
      have hLA : L.Ablock = 1 := rfl
      have hLB : L.Bblock = 0 := rfl
      simp only [hLA, hLB, Matrix.one_mul, Matrix.zero_mul, add_zero]
    -- For now, we use that this is a consequence of N's parity conditions
    -- This is a complex computation - we need to show the product has odd entries
    -- For simplicity, assume the user provides this or we derive it
    simp only [Matrix.mul_apply]
    apply Λ.odd.sum_mem
    intro k _
    rw [hLNB]
    have hNB_odd : N.Bblock i k ∈ Λ.odd := N.Bblock_odd i k
    -- (L * N).D_inv_carrier entries are even (inverse of even matrix)
    have hLND_even : ∀ a b, (L * N).Dblock a b ∈ Λ.even := by
      intro a b
      show (L.Cblock * N.Bblock + L.Dblock * N.Dblock) a b ∈ Λ.even
      have hLC : L.Cblock = C' := rfl
      have hLD : L.Dblock = 1 := rfl
      simp only [hLC, hLD, Matrix.add_apply, Matrix.mul_apply, Matrix.one_mul]
      apply Λ.even.add_mem
      · apply Λ.even.sum_mem
        intro c _
        exact Λ.odd_mul_odd _ _ (hC' a c) (N.Bblock_odd c b)
      · -- L.Dblock = 1, so (1 * N.Dblock) a b = N.Dblock a b (already simplified by simp)
        exact N.Dblock_even a b
    have hLNDinv_even : (L * N).D_inv_carrier k j ∈ Λ.even := by
      unfold SuperMatrix.D_inv_carrier
      rw [Λ.even_mem_iff]
      use ((L * N).D_lifted⁻¹ k j)
      rfl
    exact Λ.odd_mul_even _ _ hNB_odd hLNDinv_even
  have hMul := SuperMatrix.ber_mul_A_invertible L N hLA hLD hND hLND h1 h0even h0odd
    hBDinvL hBDinvN hBDinvLN hDinvCN hCAinvL hAinvBL hDinvCL hSchurL hSchurN hSchurL_det
  rw [hMul, hBerL, one_mul]

/-- Ber(Δ * Z) = Ber(Δ) * Ber(Z) for diagonal Δ = [A' 0; 0 D']. -/
theorem SuperMatrix.ber_mul_diagonal_left {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (A' : Matrix (Fin n) (Fin n) Λ.carrier) (D' : Matrix (Fin m) (Fin m) Λ.carrier)
    (Z : SuperMatrix Λ n m)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hA' : ∀ i j, A' i j ∈ Λ.even) (hD' : ∀ i j, D' i j ∈ Λ.even)
    (hD'det : Λ.IsInvertible (Λ.liftEvenMatrix D' hD').det) (hZD : Λ.IsInvertible Z.D_lifted.det)
    (hΔD : Λ.IsInvertible (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det)
    (hΔZD : Λ.IsInvertible ((SuperMatrix.diagonal A' D' h0odd hA' hD') * Z).D_lifted.det)
    (hBDinvZ : ∀ i j, (Z.Bblock * Z.D_inv_carrier) i j ∈ Λ.odd)
    (hBDinvΔZ : ∀ i j, (((SuperMatrix.diagonal A' D' h0odd hA' hD') * Z).Bblock *
                        ((SuperMatrix.diagonal A' D' h0odd hA' hD') * Z).D_inv_carrier) i j ∈ Λ.odd)
    (hBDinvΔ : ∀ i j, ((SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock *
                       (SuperMatrix.diagonal A' D' h0odd hA' hD').D_inv_carrier) i j ∈ Λ.odd) :
    ((SuperMatrix.diagonal A' D' h0odd hA' hD') * Z).ber hΔZD hBDinvΔZ =
    (SuperMatrix.diagonal A' D' h0odd hA' hD').ber hΔD hBDinvΔ * Z.ber hZD hBDinvZ := by
  -- Block equalities for Δ * Z (using show to avoid let-binding issues)
  have hΔZA : (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).Ablock = A' * Z.Ablock := by
    show (SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock * Z.Ablock +
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock * Z.Cblock = A' * Z.Ablock
    simp only [SuperMatrix.diagonal, Matrix.zero_mul, add_zero]
  have hΔZB : (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).Bblock = A' * Z.Bblock := by
    show (SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock * Z.Bblock +
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock * Z.Dblock = A' * Z.Bblock
    simp only [SuperMatrix.diagonal, Matrix.zero_mul, add_zero]
  have hΔZC : (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).Cblock = D' * Z.Cblock := by
    show (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock * Z.Ablock +
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock * Z.Cblock = D' * Z.Cblock
    simp only [SuperMatrix.diagonal, Matrix.zero_mul, zero_add]
  have hΔZD_eq : (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).Dblock = D' * Z.Dblock := by
    show (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock * Z.Bblock +
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock * Z.Dblock = D' * Z.Dblock
    simp only [SuperMatrix.diagonal, Matrix.zero_mul, zero_add]
  -- Diagonal Δ has schurD_carrier = A' (since B=C=0)
  have hΔ_schurD : (SuperMatrix.diagonal A' D' h0odd hA' hD').schurD_carrier = A' := by
    unfold SuperMatrix.schurD_carrier
    simp only [SuperMatrix.diagonal, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
  -- Δ.D_lifted = liftEvenMatrix D' hD'
  have hΔ_D_lifted : (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted = Λ.liftEvenMatrix D' hD' := rfl
  -- ber(Δ) = A'_lifted.det * inv(D'_lifted.det)
  -- Need to work with schurD_lifted for Δ
  have hΔ_schurD_lifted : Λ.liftEvenMatrix (SuperMatrix.diagonal A' D' h0odd hA' hD').schurD_carrier
      ((SuperMatrix.diagonal A' D' h0odd hA' hD').schurD_even hBDinvΔ) = Λ.liftEvenMatrix A' hA' := by
    ext i j
    apply Λ.evenToCarrier_injective
    simp only [Λ.liftEvenMatrix_spec, hΔ_schurD]
  -- The key is to prove equalities at the lifted level
  -- 1. (Δ * Z).D_lifted = Δ.D_lifted * Z.D_lifted
  -- 2. (Δ * Z).schurD_carrier = A' * Z.schurD_carrier
  -- Block equalities
  have hΔZD_eq : (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).Dblock = D' * Z.Dblock := by
    show (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock * Z.Bblock +
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock * Z.Dblock = D' * Z.Dblock
    simp only [SuperMatrix.diagonal, Matrix.zero_mul, zero_add]
  -- D_lifted equality
  have hΔZ_D_lifted_eq : (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).D_lifted =
      (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted * Z.D_lifted := by
    ext i j
    simp only [SuperMatrix.D_lifted, Matrix.mul_apply]
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec _ (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).Dblock_even i j]
    rw [hΔZD_eq]
    simp only [Matrix.mul_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hD'_eq : D' i k = Λ.evenToCarrier (Λ.liftEvenMatrix D' hD' i k) := by
      rw [Λ.liftEvenMatrix_spec]
    have hZD_eq : Z.Dblock k j = Λ.evenToCarrier (Λ.liftEvenMatrix Z.Dblock Z.Dblock_even k j) := by
      rw [Λ.liftEvenMatrix_spec]
    rw [hD'_eq, hZD_eq, ← Λ.evenToCarrier.map_mul]
    congr 1
  -- D_lifted det equality
  have hΔZ_D_det_eq : (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).D_lifted.det =
      (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det * Z.D_lifted.det := by
    rw [hΔZ_D_lifted_eq, Matrix.det_mul]
  -- schurD_carrier equality: (Δ * Z).schurD_carrier = A' * Z.schurD_carrier
  -- First prove the D_inv_carrier relationship
  haveI : Invertible (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det :=
    ((Λ.isUnit_iff_body_ne_zero _).mpr hΔD).invertible
  haveI : Invertible (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted :=
    Matrix.invertibleOfDetInvertible _
  haveI : Invertible Z.D_lifted.det := ((Λ.isUnit_iff_body_ne_zero _).mpr hZD).invertible
  haveI : Invertible Z.D_lifted := Matrix.invertibleOfDetInvertible Z.D_lifted
  have hΔZ_D_inv_lifted : (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).D_lifted⁻¹ =
      Z.D_lifted⁻¹ * (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted⁻¹ := by
    rw [hΔZ_D_lifted_eq, Matrix.mul_inv_rev]
  -- Now prove the schurD_carrier equality
  have hΔZA : (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).Ablock = A' * Z.Ablock := by
    show (SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock * Z.Ablock +
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock * Z.Cblock = A' * Z.Ablock
    simp only [SuperMatrix.diagonal, Matrix.zero_mul, add_zero]
  have hΔZB : (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).Bblock = A' * Z.Bblock := by
    show (SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock * Z.Bblock +
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock * Z.Dblock = A' * Z.Bblock
    simp only [SuperMatrix.diagonal, Matrix.zero_mul, add_zero]
  have hΔZC : (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).Cblock = D' * Z.Cblock := by
    show (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock * Z.Ablock +
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock * Z.Cblock = D' * Z.Cblock
    simp only [SuperMatrix.diagonal, Matrix.zero_mul, zero_add]
  -- (Δ * Z).D_inv_carrier = Z.D_inv_carrier * Δ.D_inv_carrier
  have hΔZ_D_inv_carrier : (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).D_inv_carrier =
      Z.D_inv_carrier * (SuperMatrix.diagonal A' D' h0odd hA' hD').D_inv_carrier := by
    unfold SuperMatrix.D_inv_carrier
    rw [hΔZ_D_inv_lifted, matrixEvenToCarrier_mul]
  -- Δ.D_inv_carrier = matrixEvenToCarrier(liftEvenMatrix D' hD')⁻¹
  have hΔ_D_inv_carrier : (SuperMatrix.diagonal A' D' h0odd hA' hD').D_inv_carrier =
      matrixEvenToCarrier (Λ.liftEvenMatrix D' hD')⁻¹ := rfl
  -- D' * Δ.D_inv_carrier = 1 (in carrier)
  haveI hD'_det_inv : Invertible (Λ.liftEvenMatrix D' hD').det :=
    ((Λ.isUnit_iff_body_ne_zero _).mpr hD'det).invertible
  have hD'_Δinv : D' * (SuperMatrix.diagonal A' D' h0odd hA' hD').D_inv_carrier = 1 := by
    rw [hΔ_D_inv_carrier]
    -- Prove directly via matrix extensionality
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply, Matrix.one_apply]
    -- Goal: ∑ k, D' i k * (D_lifted⁻¹) k j = if i = j then 1 else 0
    -- We use that D' i k = evenToCarrier (D_lifted i k)
    conv_lhs =>
      arg 2
      ext k
      rw [← Λ.liftEvenMatrix_spec D' hD' i k]
      rw [← Λ.evenToCarrier.map_mul]
    rw [← map_sum]
    -- Now goal is: evenToCarrier (∑ k, D_lifted i k * D_lifted⁻¹ k j) = if i = j then 1 else 0
    have h_prod : (∑ k, Λ.liftEvenMatrix D' hD' i k * (Λ.liftEvenMatrix D' hD')⁻¹ k j) =
        (Λ.liftEvenMatrix D' hD' * (Λ.liftEvenMatrix D' hD')⁻¹) i j := rfl
    rw [h_prod, Matrix.mul_nonsing_inv (Λ.liftEvenMatrix D' hD') (isUnit_of_invertible _)]
    simp only [Matrix.one_apply]
    split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
  -- schurD_carrier for Δ * Z
  have hΔZ_schurD : (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).schurD_carrier =
      A' * Z.schurD_carrier := by
    unfold SuperMatrix.schurD_carrier
    rw [hΔZA, hΔZB, hΔZC, hΔZ_D_inv_carrier]
    -- Goal: A' * Z.Ablock - A' * Z.Bblock * (Z.D_inv_carrier * Δ.D_inv_carrier) * (D' * Z.Cblock)
    --     = A' * (Z.Ablock - Z.Bblock * Z.D_inv_carrier * Z.Cblock)
    -- First prove Δ.D_inv_carrier * D' = 1 using extensionality (to avoid dependent type rewrite)
    have hΔinv_D' : (SuperMatrix.diagonal A' D' h0odd hA' hD').D_inv_carrier * D' = 1 := by
      rw [hΔ_D_inv_carrier]
      ext i j
      simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply, Matrix.one_apply]
      conv_lhs =>
        arg 2
        ext k
        rw [← Λ.liftEvenMatrix_spec D' hD' k j]
        rw [← Λ.evenToCarrier.map_mul]
      rw [← map_sum]
      have h_prod : (∑ k, (Λ.liftEvenMatrix D' hD')⁻¹ i k * Λ.liftEvenMatrix D' hD' k j) =
          ((Λ.liftEvenMatrix D' hD')⁻¹ * Λ.liftEvenMatrix D' hD') i j := rfl
      rw [h_prod, Matrix.nonsing_inv_mul (Λ.liftEvenMatrix D' hD') (isUnit_of_invertible _)]
      simp only [Matrix.one_apply]
      split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
    have h_cancel : A' * Z.Bblock * (Z.D_inv_carrier *
        (SuperMatrix.diagonal A' D' h0odd hA' hD').D_inv_carrier) * (D' * Z.Cblock) =
        A' * Z.Bblock * Z.D_inv_carrier * Z.Cblock := by
      calc A' * Z.Bblock * (Z.D_inv_carrier *
          (SuperMatrix.diagonal A' D' h0odd hA' hD').D_inv_carrier) * (D' * Z.Cblock)
          = A' * Z.Bblock * Z.D_inv_carrier *
            ((SuperMatrix.diagonal A' D' h0odd hA' hD').D_inv_carrier * (D' * Z.Cblock)) := by
              simp only [Matrix.mul_assoc]
        _ = A' * Z.Bblock * Z.D_inv_carrier *
            (((SuperMatrix.diagonal A' D' h0odd hA' hD').D_inv_carrier * D') * Z.Cblock) := by
              simp only [Matrix.mul_assoc]
        _ = A' * Z.Bblock * Z.D_inv_carrier * ((1 : Matrix _ _ _) * Z.Cblock) := by
              rw [hΔinv_D']
        _ = A' * Z.Bblock * Z.D_inv_carrier * Z.Cblock := by rw [Matrix.one_mul]
    rw [h_cancel]
    -- Goal: A' * Z.Ablock - A' * Z.Bblock * Z.D_inv_carrier * Z.Cblock = A' * (Z.Ablock - Z.Bblock * Z.D_inv_carrier * Z.Cblock)
    -- First reassociate the LHS
    have h_assoc : A' * Z.Bblock * Z.D_inv_carrier * Z.Cblock =
        A' * (Z.Bblock * Z.D_inv_carrier * Z.Cblock) := by simp only [Matrix.mul_assoc]
    rw [h_assoc, ← Matrix.mul_sub]
  -- Now prove the lifted schurD equality
  have hΔZ_schurD_lifted : Λ.liftEvenMatrix (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).schurD_carrier
      ((SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).schurD_even hBDinvΔZ) =
      Λ.liftEvenMatrix A' hA' * Λ.liftEvenMatrix Z.schurD_carrier (Z.schurD_even hBDinvZ) := by
    ext i j
    apply Λ.evenToCarrier_injective
    rw [Λ.liftEvenMatrix_spec, hΔZ_schurD]
    simp only [Matrix.mul_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hA'_eq : A' i k = Λ.evenToCarrier (Λ.liftEvenMatrix A' hA' i k) := by
      rw [Λ.liftEvenMatrix_spec]
    have hZ_eq : Z.schurD_carrier k j = Λ.evenToCarrier (Λ.liftEvenMatrix Z.schurD_carrier
        (Z.schurD_even hBDinvZ) k j) := by
      rw [Λ.liftEvenMatrix_spec]
    rw [hA'_eq, hZ_eq, ← Λ.evenToCarrier.map_mul]
  -- schurD det equality
  have hΔZ_schurD_det : (Λ.liftEvenMatrix (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).schurD_carrier
      ((SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).schurD_even hBDinvΔZ)).det =
      (Λ.liftEvenMatrix A' hA').det *
      (Λ.liftEvenMatrix Z.schurD_carrier (Z.schurD_even hBDinvZ)).det := by
    rw [hΔZ_schurD_lifted, Matrix.det_mul]
  -- Inverse equality using Λ.inv
  have hΔZ_D_inv_eq : Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).D_lifted.det hΔZD =
      Λ.inv Z.D_lifted.det hZD * Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD := by
    have h_prod : (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).D_lifted.det =
        (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det * Z.D_lifted.det := hΔZ_D_det_eq
    have h_prod_inv : Λ.IsInvertible ((SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det *
        Z.D_lifted.det) := Λ.mul_invertible _ _ hΔD hZD
    -- Both sides are inverses of the same product (up to commutativity in evenCarrier)
    have h_left : (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).D_lifted.det *
        Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).D_lifted.det hΔZD = 1 :=
      Λ.mul_inv _ hΔZD
    have h_right : Z.D_lifted.det * Λ.inv Z.D_lifted.det hZD = 1 := Λ.mul_inv _ hZD
    have h_right2 : (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det *
        Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD = 1 := Λ.mul_inv _ hΔD
    -- In evenCarrier (CommRing), we have commutativity
    have h_prod_right : ((SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det * Z.D_lifted.det) *
        (Λ.inv Z.D_lifted.det hZD *
         Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD) = 1 := by
      calc ((SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det * Z.D_lifted.det) *
          (Λ.inv Z.D_lifted.det hZD *
           Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD)
          = (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det *
            (Z.D_lifted.det * Λ.inv Z.D_lifted.det hZD) *
            Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD := by ring
        _ = (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det * 1 *
            Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD := by rw [h_right]
        _ = (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det *
            Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD := by ring
        _ = 1 := h_right2
    -- Use uniqueness of inverse
    have h_left' : (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det * Z.D_lifted.det *
        Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).D_lifted.det hΔZD = 1 := by
      calc (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det * Z.D_lifted.det *
          Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).D_lifted.det hΔZD
          = (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).D_lifted.det *
            Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).D_lifted.det hΔZD := by
              rw [← h_prod]
        _ = 1 := h_left
    calc Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).D_lifted.det hΔZD
        = 1 * Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).D_lifted.det hΔZD := by ring
      _ = (Λ.inv Z.D_lifted.det hZD * Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD *
           ((SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det * Z.D_lifted.det)) *
          Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).D_lifted.det hΔZD := by
            rw [mul_comm (Λ.inv Z.D_lifted.det hZD * _) _, h_prod_right]
      _ = Λ.inv Z.D_lifted.det hZD * Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD *
          ((SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det * Z.D_lifted.det *
           Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD' * Z).D_lifted.det hΔZD) := by ring
      _ = Λ.inv Z.D_lifted.det hZD *
          Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD * 1 := by rw [h_left']
      _ = Λ.inv Z.D_lifted.det hZD *
          Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD := by ring
  -- Final assembly
  simp only [SuperMatrix.ber]
  rw [hΔZ_schurD_det, hΔ_schurD_lifted, hΔZ_D_inv_eq]
  -- Now goal involves (diagonal ...).D_lifted.det and we need to show it equals liftEvenMatrix D' hD'
  -- Since hΔ_D_lifted : (diagonal ...).D_lifted = liftEvenMatrix D' hD', the dets are equal
  -- But we can't just rewrite because of dependent types in Λ.inv
  -- Instead, use congr_arg to show the dets are equal, and use the fact that Λ.inv is unique
  have hΔ_D_det_eq : (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det =
      (Λ.liftEvenMatrix D' hD').det := by rw [hΔ_D_lifted]
  -- The inverse of equal elements are equal
  have hΔ_inv_eq : Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD =
      Λ.inv (Λ.liftEvenMatrix D' hD').det hD'det := by
    -- Both are inverses of the same element (since hΔ_D_det_eq shows the elements are equal)
    have h1 : (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det *
        Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD = 1 := Λ.mul_inv _ hΔD
    have h2 : (Λ.liftEvenMatrix D' hD').det * Λ.inv (Λ.liftEvenMatrix D' hD').det hD'det = 1 :=
      Λ.mul_inv _ hD'det
    -- Use hΔ_D_det_eq to get that they multiply the same element to 1
    have h_eq : (Λ.liftEvenMatrix D' hD').det *
        Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD = 1 := by
      calc (Λ.liftEvenMatrix D' hD').det *
          Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD
          = (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det *
            Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD := by
              rw [← hΔ_D_det_eq]
        _ = 1 := h1
    -- In a commutative ring, if a * b = 1 and a * c = 1, then b = c
    exact inv_eq_of_val_eq hΔ_D_det_eq hΔD hD'det
  rw [hΔ_inv_eq]
  ring

/-- Full Berezinian multiplicativity: Ber(MN) = Ber(M) * Ber(N). -/
theorem SuperMatrix.ber_mul {k : Type*} [Field k] [CharZero k] {Λ : GrassmannAlgebra k}
    [SuperCommutative Λ.toSuperAlgebra] {n m : ℕ}
    (M N : SuperMatrix Λ n m)
    (hMD : Λ.IsInvertible M.D_lifted.det)
    (hND : Λ.IsInvertible N.D_lifted.det)
    (hMND : Λ.IsInvertible (M * N).D_lifted.det)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (h0even : (0 : Λ.carrier) ∈ Λ.even)
    (h0odd : (0 : Λ.carrier) ∈ Λ.odd)
    (hBDinvM : ∀ i j, (M.Bblock * M.D_inv_carrier) i j ∈ Λ.odd)
    (hBDinvN : ∀ i j, (N.Bblock * N.D_inv_carrier) i j ∈ Λ.odd)
    (hBDinvMN : ∀ i j, ((M * N).Bblock * (M * N).D_inv_carrier) i j ∈ Λ.odd)
    (hDinvCM : ∀ i j, (M.D_inv_carrier * M.Cblock) i j ∈ Λ.odd)
    (hDinvCN : ∀ i j, (N.D_inv_carrier * N.Cblock) i j ∈ Λ.odd)
    (hSchurM : ∀ i j, (schurComplementD M hMD) i j ∈ Λ.even)
    (hSchurN : ∀ i j, (schurComplementD N hND) i j ∈ Λ.even) :
    (M * N).ber hMND hBDinvMN = M.ber hMD hBDinvM * N.ber hND hBDinvN := by
  -- Factor M = U_M * Δ_M * L_M using UDL factorization
  let B_M := M.Bblock * M.D_inv_carrier
  let A_M := schurComplementD M hMD
  let D_M := M.Dblock
  let C_M := M.D_inv_carrier * M.Cblock

  let U_M := SuperMatrix.upperTriangular B_M h1 h0even h0odd hBDinvM
  let Δ_M := SuperMatrix.diagonal A_M D_M h0odd hSchurM M.Dblock_even
  let L_M := SuperMatrix.lowerTriangular C_M h1 h0even h0odd hDinvCM

  -- Factor N = U_N * Δ_N * L_N using UDL factorization
  let B_N := N.Bblock * N.D_inv_carrier
  let A_N := schurComplementD N hND
  let D_N := N.Dblock
  let C_N := N.D_inv_carrier * N.Cblock

  let U_N := SuperMatrix.upperTriangular B_N h1 h0even h0odd hBDinvN
  let Δ_N := SuperMatrix.diagonal A_N D_N h0odd hSchurN N.Dblock_even
  let L_N := SuperMatrix.lowerTriangular C_N h1 h0even h0odd hDinvCN

  have hM_eq : M = (U_M * Δ_M) * L_M := SuperMatrix.UDL_factorization M hMD h1 h0even h0odd
    hBDinvM hDinvCM hSchurM

  have hN_eq : N = (U_N * Δ_N) * L_N := SuperMatrix.UDL_factorization N hND h1 h0even h0odd
    hBDinvN hDinvCN hSchurN

  -- Get det conditions for factored matrices
  have hU_M_D : Λ.IsInvertible U_M.D_lifted.det :=
    upperTriangular_D_lifted_invertible B_M h1 h0even h0odd hBDinvM
  have hΔ_M_D : Λ.IsInvertible Δ_M.D_lifted.det := by simp only [SuperMatrix.D_lifted]; exact hMD
  have hL_M_D : Λ.IsInvertible L_M.D_lifted.det :=
    lowerTriangular_D_lifted_invertible C_M h1 h0even h0odd hDinvCM
  have hU_N_D : Λ.IsInvertible U_N.D_lifted.det :=
    upperTriangular_D_lifted_invertible B_N h1 h0even h0odd hBDinvN
  have hΔ_N_D : Λ.IsInvertible Δ_N.D_lifted.det := by
    have hΔN_lift : Δ_N.D_lifted = Λ.liftEvenMatrix N.Dblock N.Dblock_even := rfl
    rw [hΔN_lift]; exact hND
  have hL_N_D : Λ.IsInvertible L_N.D_lifted.det :=
    lowerTriangular_D_lifted_invertible C_N h1 h0even h0odd hDinvCN

  -- BDinv conditions for diagonal matrices (B=0 so trivially satisfied)
  have hBDinv_Δ_M : ∀ i j, (Δ_M.Bblock * Δ_M.D_inv_carrier) i j ∈ Λ.odd :=
    diagonal_BDinv_odd A_M D_M h0odd hSchurM M.Dblock_even
  have hBDinv_Δ_N : ∀ i j, (Δ_N.Bblock * Δ_N.D_inv_carrier) i j ∈ Λ.odd :=
    diagonal_BDinv_odd A_N D_N h0odd hSchurN N.Dblock_even

  -- Ber(M) = Ber(Δ_M) by UDL stripping
  -- For Δ_M = diagonal(schurComplementD M, M.Dblock), we have:
  -- Δ_M.schurD_carrier = Δ_M.Ablock - Δ_M.Bblock * Δ_M.D_inv_carrier * Δ_M.Cblock
  --                    = schurComplementD M - 0 * _ * 0 = schurComplementD M = M.schurD_carrier
  -- Δ_M.D_lifted = M.D_lifted
  have hΔM_schurD_eq : Δ_M.schurD_carrier = M.schurD_carrier := by
    unfold SuperMatrix.schurD_carrier
    have hΔA : Δ_M.Ablock = schurComplementD M hMD := rfl
    have hΔB : Δ_M.Bblock = 0 := rfl
    have hΔC : Δ_M.Cblock = 0 := rfl
    simp only [hΔA, hΔB, hΔC, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
    unfold schurComplementD
    rfl
  have hΔM_D_lifted_eq : Δ_M.D_lifted = M.D_lifted := rfl
  have hBerM_eq : M.ber hMD hBDinvM = Δ_M.ber hΔ_M_D hBDinv_Δ_M := by
    simp only [SuperMatrix.ber]
    -- Both sides have form: schurD_lifted.det * inv(D_lifted.det)
    -- Show they're equal by showing components are equal
    have h_schurD_det_eq := liftEvenMatrix_det_eq_of_eq _ _ (M.schurD_even hBDinvM)
        (Δ_M.schurD_even hBDinv_Δ_M) hΔM_schurD_eq.symm
    have h_D_inv_eq : Λ.inv M.D_lifted.det hMD = Λ.inv Δ_M.D_lifted.det hΔ_M_D := by
      simp only [hΔM_D_lifted_eq]
    rw [h_schurD_det_eq, h_D_inv_eq]

  -- Ber(N) = Ber(Δ_N) by UDL stripping
  have hΔN_schurD_eq : Δ_N.schurD_carrier = N.schurD_carrier := by
    unfold SuperMatrix.schurD_carrier
    have hΔA : Δ_N.Ablock = schurComplementD N hND := rfl
    have hΔB : Δ_N.Bblock = 0 := rfl
    have hΔC : Δ_N.Cblock = 0 := rfl
    simp only [hΔA, hΔB, hΔC, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
    unfold schurComplementD
    rfl
  have hΔN_D_lifted_eq : Δ_N.D_lifted = N.D_lifted := rfl
  have hBerN_eq : N.ber hND hBDinvN = Δ_N.ber hΔ_N_D hBDinv_Δ_N := by
    simp only [SuperMatrix.ber]
    have h_schurD_det_eq := liftEvenMatrix_det_eq_of_eq _ _ (N.schurD_even hBDinvN)
        (Δ_N.schurD_even hBDinv_Δ_N) hΔN_schurD_eq.symm
    have h_D_inv_eq : Λ.inv N.D_lifted.det hND = Λ.inv Δ_N.D_lifted.det hΔ_N_D := by
      simp only [hΔN_D_lifted_eq]
    rw [h_schurD_det_eq, h_D_inv_eq]

  -- M * N = (U_M * Δ_M * L_M) * (U_N * Δ_N * L_N)
  --       = U_M * Δ_M * (L_M * U_N) * Δ_N * L_N
  -- Now we need to strip off the triangular parts

  -- Since M * N = U_M * Δ_M * L_M * U_N * Δ_N * L_N,
  -- we can use the stripping lemmas iteratively

  -- Let X₅ = M * N
  -- Let X₄ = Δ_M * L_M * U_N * Δ_N * L_N (after stripping U_M from left)
  -- Let X₃ = L_M * U_N * Δ_N * L_N (after applying diagonal mult)
  -- Let X₂ = U_N * Δ_N * L_N (after stripping L_M from left)
  -- Let X₁ = Δ_N * L_N (after stripping U_N from left)
  -- Ber(X₁) = Ber(Δ_N) (after stripping L_N from right)

  let X₅ := M * N
  let X₄ := Δ_M * L_M * U_N * Δ_N * L_N
  let X₃ := L_M * U_N * Δ_N * L_N
  let X₂ := U_N * Δ_N * L_N
  let X₁ := Δ_N * L_N

  -- First, establish that M * N = U_M * X₄
  have hMN_eq_UX₄ : M * N = U_M * X₄ := by
    calc M * N = ((U_M * Δ_M) * L_M) * ((U_N * Δ_N) * L_N) := by rw [hM_eq, hN_eq]
      _ = U_M * Δ_M * L_M * (U_N * Δ_N * L_N) := by simp only [mul_assoc]
      _ = U_M * (Δ_M * L_M * U_N * Δ_N * L_N) := by simp only [mul_assoc]
      _ = U_M * X₄ := rfl

  -- Get det invertibility for intermediate products
  have hX₄_D : Λ.IsInvertible X₄.D_lifted.det := by
    -- X₄ = Δ_M * (L_M * U_N * Δ_N * L_N)
    -- We need to show X₄.D is invertible
    -- Since U_M * X₄ = M * N and U_M.D = I, we have X₄.D = (M*N).D
    have hUX₄_D_eq : (U_M * X₄).Dblock = X₄.Dblock := by
      show U_M.Cblock * X₄.Bblock + U_M.Dblock * X₄.Dblock = X₄.Dblock
      have hUC : U_M.Cblock = 0 := rfl
      have hUD : U_M.Dblock = 1 := rfl
      simp only [hUC, hUD, Matrix.zero_mul, Matrix.one_mul, zero_add]
    -- (M * N).D = (U_M * X₄).D = X₄.D
    have hMN_D_eq : (M * N).Dblock = X₄.Dblock := by
      rw [hMN_eq_UX₄, hUX₄_D_eq]
    -- So (M * N).D_lifted = X₄.D_lifted
    have hMN_D_lifted_eq := D_lifted_eq_of_Dblock_eq' _ _ hMN_D_eq
    rw [← hMN_D_lifted_eq]
    exact hMND

  -- X₂ = N (by UDL factorization and associativity) - needed for hX₂_D and later
  have hX₂_eq_N : X₂ = N := by
    show U_N * Δ_N * L_N = N
    have h : N = (U_N * Δ_N) * L_N := hN_eq
    rw [h, SuperMatrix.mul_assoc]

  have hX₃_D : Λ.IsInvertible X₃.D_lifted.det := by
    -- X₄ = Δ_M * X₃, and Δ_M.D = M.D is invertible
    -- X₄.D = Δ_M.D * X₃.D (since Δ_M.C = 0)
    have hX₄_eq : X₄ = Δ_M * X₃ := by
      show Δ_M * L_M * U_N * Δ_N * L_N = Δ_M * (L_M * U_N * Δ_N * L_N)
      simp only [SuperMatrix.mul_assoc]
    have hΔX₃_D : (Δ_M * X₃).Dblock = Δ_M.Dblock * X₃.Dblock := by
      show Δ_M.Cblock * X₃.Bblock + Δ_M.Dblock * X₃.Dblock = Δ_M.Dblock * X₃.Dblock
      have hΔC : Δ_M.Cblock = 0 := rfl
      simp only [hΔC, Matrix.zero_mul, zero_add]
    -- X₄.D_lifted.det = Δ_M.D_lifted.det * X₃.D_lifted.det
    -- We need to prove this via the Dblock equality
    have hX₄_D_lifted_eq : X₄.D_lifted = (Δ_M * X₃).D_lifted := by
      simp only [hX₄_eq]
    have hΔMX₃_D_lifted_eq : (Δ_M * X₃).D_lifted = Δ_M.D_lifted * X₃.D_lifted :=
      D_lifted_mul_eq Δ_M X₃ hΔX₃_D
    have hdet_eq : X₄.D_lifted.det = Δ_M.D_lifted.det * X₃.D_lifted.det := by
      rw [hX₄_D_lifted_eq, hΔMX₃_D_lifted_eq, Matrix.det_mul]
    unfold GrassmannAlgebra.IsInvertible at hX₄_D hΔ_M_D ⊢
    rw [hdet_eq, Λ.body_mul] at hX₄_D
    exact right_ne_zero_of_mul hX₄_D

  have hX₂_D : Λ.IsInvertible X₂.D_lifted.det := by
    -- X₂ = N (by UDL factorization)
    rw [D_lifted_eq_of_Dblock_eq' _ _ (by simp only [hX₂_eq_N] : X₂.Dblock = N.Dblock)]
    exact hND

  have hX₁_D : Λ.IsInvertible X₁.D_lifted.det := by
    -- X₂ = U_N * X₁, and U_N.D = I
    have hX₂_eq : X₂ = U_N * X₁ := by
      show U_N * Δ_N * L_N = U_N * (Δ_N * L_N)
      simp only [SuperMatrix.mul_assoc]
    have hUX₁_D : (U_N * X₁).Dblock = X₁.Dblock := by
      show U_N.Cblock * X₁.Bblock + U_N.Dblock * X₁.Dblock = X₁.Dblock
      have hUC : U_N.Cblock = 0 := rfl
      have hUD : U_N.Dblock = 1 := rfl
      simp only [hUC, hUD, Matrix.zero_mul, Matrix.one_mul, zero_add]
    -- X₂.D = X₁.D, so X₂.D_lifted = X₁.D_lifted
    have hX₂_D_eq : X₂.Dblock = X₁.Dblock := by rw [hX₂_eq, hUX₁_D]
    rw [← D_lifted_eq_of_Dblock_eq' _ _ hX₂_D_eq]
    exact hX₂_D

  have hX₅_D : Λ.IsInvertible X₅.D_lifted.det := hMND

  -- Define BDinv conditions for intermediate matrices
  -- These need to be defined before the stripping lemmas that use them in their type signatures
  have hBDinvX₄ : ∀ i j, (X₄.Bblock * X₄.D_inv_carrier) i j ∈ Λ.odd := by
      intro i j
      -- X₄.B involves products of odd elements
      -- This follows from the structure of X₄ = Δ_M * L_M * U_N * Δ_N * L_N
      -- For now, we need to verify this holds
      simp only [Matrix.mul_apply]
      apply Λ.odd.sum_mem
      intro k _
      -- X₄.B k j is odd, X₄.D_inv_carrier is even
      have hX₄B_odd : X₄.Bblock i k ∈ Λ.odd := by
        -- X₄ = Δ_M * (L_M * U_N * Δ_N * L_N)
        -- Δ_M.B = 0, so (Δ_M * Y).B = Δ_M.A * Y.B
        -- Y = L_M * U_N * Δ_N * L_N
        -- This is a long computation - the key is that B blocks are odd
        -- For now, accept that structure is preserved
        have hX₄_eq : X₄ = Δ_M * X₃ := by
          show Δ_M * L_M * U_N * Δ_N * L_N = Δ_M * (L_M * U_N * Δ_N * L_N)
          simp only [SuperMatrix.mul_assoc]
        have hΔX₃_B : (Δ_M * X₃).Bblock = Δ_M.Ablock * X₃.Bblock := by
          show Δ_M.Ablock * X₃.Bblock + Δ_M.Bblock * X₃.Dblock = Δ_M.Ablock * X₃.Bblock
          have hΔB : Δ_M.Bblock = 0 := rfl
          simp only [hΔB, Matrix.zero_mul, add_zero]
        rw [hX₄_eq, hΔX₃_B]
        simp only [Matrix.mul_apply]
        apply Λ.odd.sum_mem
        intro l _
        have hΔA_even : Δ_M.Ablock i l ∈ Λ.even := hSchurM i l
        -- X₃.B is odd (from structure of L_M * U_N * ...)
        have hX₃B_odd : X₃.Bblock l k ∈ Λ.odd := by
          -- X₃ = L_M * (U_N * Δ_N * L_N)
          -- L_M.B = 0, so (L_M * Y).B = L_M.A * Y.B + L_M.B * Y.D = Y.B (since L_M.A = I, L_M.B = 0)
          have hX₃_eq : X₃ = L_M * X₂ := by
            show L_M * U_N * Δ_N * L_N = L_M * (U_N * Δ_N * L_N)
            simp only [SuperMatrix.mul_assoc]
          have hLX₂_B : (L_M * X₂).Bblock = X₂.Bblock := by
            show L_M.Ablock * X₂.Bblock + L_M.Bblock * X₂.Dblock = X₂.Bblock
            have hLA : L_M.Ablock = 1 := rfl
            have hLB : L_M.Bblock = 0 := rfl
            simp only [hLA, hLB, Matrix.one_mul, Matrix.zero_mul, add_zero]
          rw [hX₃_eq, hLX₂_B]
          -- X₂ = U_N * Δ_N * L_N = N (use the outer hX₂_eq_N)
          rw [hX₂_eq_N]
          exact N.Bblock_odd l k
        exact Λ.even_mul_odd _ _ hΔA_even hX₃B_odd
      have hX₄Dinv_even : X₄.D_inv_carrier k j ∈ Λ.even := by
        -- X₄.D is even (product of even blocks), so its inverse is even
        have hX₄D_even : ∀ a b, X₄.Dblock a b ∈ Λ.even := by
          intro a b
          -- X₄ = Δ_M * X₃, Δ_M.D = M.D (even), Δ_M.C = 0
          -- (Δ_M * X₃).D = Δ_M.C * X₃.B + Δ_M.D * X₃.D = Δ_M.D * X₃.D
          have hX₄_eq : X₄ = Δ_M * X₃ := by
            show Δ_M * L_M * U_N * Δ_N * L_N = Δ_M * (L_M * U_N * Δ_N * L_N)
            simp only [SuperMatrix.mul_assoc]
          have hΔX₃_D : (Δ_M * X₃).Dblock = Δ_M.Dblock * X₃.Dblock := by
            show Δ_M.Cblock * X₃.Bblock + Δ_M.Dblock * X₃.Dblock = Δ_M.Dblock * X₃.Dblock
            have hΔC : Δ_M.Cblock = 0 := rfl
            simp only [hΔC, Matrix.zero_mul, zero_add]
          rw [hX₄_eq, hΔX₃_D]
          simp only [Matrix.mul_apply]
          apply Λ.even.sum_mem
          intro c _
          have hΔD_even : Δ_M.Dblock a c ∈ Λ.even := M.Dblock_even a c
          -- X₃.D is even
          have hX₃D_even : X₃.Dblock c b ∈ Λ.even := by
            -- X₃ = L_M * X₂
            -- (L_M * X₂).D = L_M.C * X₂.B + L_M.D * X₂.D = C_M * X₂.B + X₂.D
            have hX₃_eq : X₃ = L_M * X₂ := by
              show L_M * U_N * Δ_N * L_N = L_M * (U_N * Δ_N * L_N)
              simp only [SuperMatrix.mul_assoc]
            have hLX₂_D : (L_M * X₂).Dblock c b =
                          (L_M.Cblock * X₂.Bblock + L_M.Dblock * X₂.Dblock) c b := rfl
            rw [hX₃_eq, hLX₂_D]
            simp only [Matrix.add_apply, Matrix.mul_apply]
            apply Λ.even.add_mem
            · apply Λ.even.sum_mem
              intro d _
              have hLC_odd : L_M.Cblock c d ∈ Λ.odd := hDinvCM c d
              -- X₂ = N, so X₂.B is odd
              have hX₂B_odd : X₂.Bblock d b ∈ Λ.odd := by
                rw [hX₂_eq_N]
                exact N.Bblock_odd d b
              exact Λ.odd_mul_odd _ _ hLC_odd hX₂B_odd
            · have hLD : L_M.Dblock = 1 := rfl
              simp only [hLD, Matrix.one_apply]
              -- Goal: ∑ x, (if c = x then 1 else 0) * X₂.Dblock x b ∈ Λ.even
              -- This simplifies to X₂.Dblock c b since only x = c contributes
              have hsum : ∑ x, (if c = x then (1 : Λ.carrier) else 0) * X₂.Dblock x b = X₂.Dblock c b := by
                rw [Finset.sum_eq_single c]
                · simp only [ite_true, one_mul]
                · intro d _ hdc
                  simp only [if_neg (Ne.symm hdc), zero_mul]
                · intro hc
                  exact (hc (Finset.mem_univ c)).elim
              rw [hsum, hX₂_eq_N]
              exact N.Dblock_even c b
          exact Λ.even_mul_even _ _ hΔD_even hX₃D_even
        unfold SuperMatrix.D_inv_carrier
        rw [Λ.even_mem_iff]
        use (X₄.D_lifted⁻¹ k j)
        rfl
      exact Λ.odd_mul_even _ _ hX₄B_odd hX₄Dinv_even

  -- BDinv condition for U_M (B_M * D_inv = B_M * I⁻¹ = B_M, which is odd)
  have hBDinv_U_M : ∀ i j, (U_M.Bblock * U_M.D_inv_carrier) i j ∈ Λ.odd :=
    upperTriangular_BDinv_odd B_M h1 h0even h0odd hBDinvM

  -- Ber(X₅) = Ber(X₄) (strip U_M from left)
  have hStrip_U_M : X₅.ber hX₅_D hBDinvMN = X₄.ber hX₄_D hBDinvX₄ := by
    -- X₅ = M * N = U_M * X₄ by hMN_eq_UX₄
    -- U_M = upperTriangular B_M h1 h0even h0odd hBDinvM
    -- The lemma expects proofs about (upperTriangular ... * X₄), not X₅
    -- We need to cast proofs across the equality hMN_eq_UX₄ : M * N = U_M * X₄
    have hUMX₄_D_inv : Λ.IsInvertible (U_M * X₄).D_lifted.det := by
      have hD_eq : (U_M * X₄).Dblock = X₅.Dblock := by
        show (U_M * X₄).Dblock = (M * N).Dblock; rw [hMN_eq_UX₄]
      rw [D_lifted_eq_of_Dblock_eq' _ _ hD_eq]; exact hX₅_D
    have hUMX₄_BDinv : ∀ i j, ((U_M * X₄).Bblock * (U_M * X₄).D_inv_carrier) i j ∈ Λ.odd := by
      intro i j
      have hB_eq : (U_M * X₄).Bblock = X₅.Bblock := by
        show (U_M * X₄).Bblock = (M * N).Bblock; rw [hMN_eq_UX₄]
      have hDinv_eq := D_inv_carrier_eq_of_Dblock_eq _ _ (by
        show (U_M * X₄).Dblock = (M * N).Dblock; rw [hMN_eq_UX₄] : (U_M * X₄).Dblock = X₅.Dblock)
      rw [hB_eq, hDinv_eq]; exact hBDinvMN i j
    -- Now apply the stripping lemma
    have h := SuperMatrix.ber_mul_upperTriangular_left B_M X₄ h1 h0even h0odd hBDinvM hX₄_D hBDinvX₄ hU_M_D hBDinv_U_M hUMX₄_D_inv hUMX₄_BDinv
    -- h : (U_M * X₄).ber hUMX₄_D_inv hUMX₄_BDinv = X₄.ber hX₄_D hBDinvX₄
    -- We need: X₅.ber hX₅_D hBDinvMN = X₄.ber hX₄_D hBDinvX₄
    -- Show X₅.ber hX₅_D hBDinvMN = (U_M * X₄).ber hUMX₄_D_inv hUMX₄_BDinv
    -- Key: X₅ = M * N = U_M * X₄, so all blocks are equal
    have hX₅_eq : X₅ = U_M * X₄ := hMN_eq_UX₄
    have hber_eq : X₅.ber hX₅_D hBDinvMN = (U_M * X₄).ber hUMX₄_D_inv hUMX₄_BDinv := by
      -- X₅ = M * N = U_M * X₄ by hMN_eq_UX₄
      -- The ber function computes det(schurD_carrier) * inv(D_lifted.det)
      -- Both sides have the same schurD_carrier and D_lifted since M*N = U_M*X₄
      simp only [SuperMatrix.ber]
      -- Show the det and inv parts are equal
      have hSchur_eq : X₅.schurD_carrier = (U_M * X₄).schurD_carrier := by
        unfold SuperMatrix.schurD_carrier
        show (M * N).schurD_carrier = (U_M * X₄).schurD_carrier
        unfold SuperMatrix.schurD_carrier
        rw [hMN_eq_UX₄]
      have hD_lifted_det_eq : X₅.D_lifted.det = (U_M * X₄).D_lifted.det := by
        show (M * N).D_lifted.det = (U_M * X₄).D_lifted.det
        congr 1
        unfold SuperMatrix.D_lifted
        congr 1
        show (M * N).Dblock = (U_M * X₄).Dblock
        rw [hMN_eq_UX₄]
      -- The schurD_carrier are equal, so liftEvenMatrix gives the same matrix
      -- (though with possibly different proof terms - but the matrix values are the same)
      -- Similarly for D_lifted.det
      -- Now use these equalities to show the products are equal
      -- Prove the schurD_carrier entries are even for both
      -- Use schurD_even which requires the hBDinv proof
      have hX₅_schur_even : ∀ i j, X₅.schurD_carrier i j ∈ Λ.even := X₅.schurD_even hBDinvMN
      have hUMX₄_schur_even : ∀ i j, (U_M * X₄).schurD_carrier i j ∈ Λ.even :=
        (U_M * X₄).schurD_even hUMX₄_BDinv
      have h1 := liftEvenMatrix_det_eq_of_eq _ _ hX₅_schur_even hUMX₄_schur_even hSchur_eq
      have h2 : Λ.inv X₅.D_lifted.det hX₅_D = Λ.inv (U_M * X₄).D_lifted.det hUMX₄_D_inv := by
        simp only [D_lifted_eq_of_Dblock_eq' _ _ (by simp only [hX₅_eq] : X₅.Dblock = (U_M * X₄).Dblock)]
      rw [h1, h2]
    rw [hber_eq, h]

  -- X₂ = N (by UDL factorization and associativity)
  have hX₂_eq_N : X₂ = N := by
    show U_N * Δ_N * L_N = N
    have h : N = (U_N * Δ_N) * L_N := hN_eq
    rw [h, SuperMatrix.mul_assoc]

  -- Define BDinv condition for X₃ (needed for hStrip_Δ_M type signature)
  have hBDinvX₃ : ∀ i j, (X₃.Bblock * X₃.D_inv_carrier) i j ∈ Λ.odd := by
    intro i j
    simp only [Matrix.mul_apply]
    apply Λ.odd.sum_mem
    intro k _
    -- X₃.B is odd
    have hX₃B_odd : X₃.Bblock i k ∈ Λ.odd := by
      -- X₃ = L_M * X₂, and (L_M * X₂).B = X₂.B since L_M.A = I, L_M.B = 0
      have hX₃_B_eq : X₃.Bblock = X₂.Bblock := by
        show (L_M * U_N * Δ_N * L_N).Bblock = X₂.Bblock
        have h1 : (L_M * U_N * Δ_N * L_N).Bblock = (L_M * (U_N * Δ_N * L_N)).Bblock := by
          congr 1; simp only [SuperMatrix.mul_assoc]
        rw [h1]
        show L_M.Ablock * X₂.Bblock + L_M.Bblock * X₂.Dblock = X₂.Bblock
        have hLA : L_M.Ablock = 1 := rfl
        have hLB : L_M.Bblock = 0 := rfl
        simp only [hLA, hLB, Matrix.one_mul, Matrix.zero_mul, add_zero]
      rw [hX₃_B_eq, hX₂_eq_N]
      exact N.Bblock_odd i k
    -- X₃.D_inv is even
    have hX₃Dinv_even : X₃.D_inv_carrier k j ∈ Λ.even := by
      unfold SuperMatrix.D_inv_carrier
      rw [Λ.even_mem_iff]
      use (X₃.D_lifted⁻¹ k j)
      rfl
    exact Λ.odd_mul_even _ _ hX₃B_odd hX₃Dinv_even

  -- Ber(X₄) = Ber(Δ_M) * Ber(X₃) (diagonal mult)
  have hStrip_Δ_M : X₄.ber hX₄_D hBDinvX₄ = Δ_M.ber hΔ_M_D hBDinv_Δ_M * X₃.ber hX₃_D hBDinvX₃ := by
    have hX₄_eq : X₄ = Δ_M * X₃ := by
      show Δ_M * L_M * U_N * Δ_N * L_N = Δ_M * (L_M * U_N * Δ_N * L_N)
      simp only [SuperMatrix.mul_assoc]
    -- Need to show X₄.ber hX₄_D hBDinvX₄ = (Δ_M * X₃).ber ... * X₃.ber ...
    -- First show that (Δ_M * X₃).ber equals X₄.ber with appropriate proof transport
    have hBDinvΔX₃ : ∀ i j, ((Δ_M * X₃).Bblock * (Δ_M * X₃).D_inv_carrier) i j ∈ Λ.odd := by
      intro i j
      -- (Δ_M * X₃).B = Δ_M.A * X₃.B (since Δ_M.B = 0)
      have hΔX₃_B : (Δ_M * X₃).Bblock = Δ_M.Ablock * X₃.Bblock := by
        show Δ_M.Ablock * X₃.Bblock + Δ_M.Bblock * X₃.Dblock = Δ_M.Ablock * X₃.Bblock
        have hΔB : Δ_M.Bblock = 0 := rfl
        simp only [hΔB, Matrix.zero_mul, add_zero]
      simp only [Matrix.mul_apply]
      apply Λ.odd.sum_mem
      intro k _
      rw [hΔX₃_B]
      simp only [Matrix.mul_apply]
      -- (Δ_M.A * X₃.B) i k = Σ Δ_M.A i l * X₃.B l k
      -- This is odd (even * odd)
      have hΔAX₃B_odd : (Δ_M.Ablock * X₃.Bblock) i k ∈ Λ.odd := by
        simp only [Matrix.mul_apply]
        apply Λ.odd.sum_mem
        intro l _
        have hΔA_even : Δ_M.Ablock i l ∈ Λ.even := hSchurM i l
        have hX₃B_odd : X₃.Bblock l k ∈ Λ.odd := by
          have hX₃_eq' : X₃ = L_M * X₂ := by
            show L_M * U_N * Δ_N * L_N = L_M * (U_N * Δ_N * L_N)
            simp only [SuperMatrix.mul_assoc]
          have hLX₂_B : (L_M * X₂).Bblock = X₂.Bblock := by
            show L_M.Ablock * X₂.Bblock + L_M.Bblock * X₂.Dblock = X₂.Bblock
            have hLA : L_M.Ablock = 1 := rfl
            have hLB : L_M.Bblock = 0 := rfl
            simp only [hLA, hLB, Matrix.one_mul, Matrix.zero_mul, add_zero]
          rw [hX₃_eq', hLX₂_B, hX₂_eq_N]
          exact N.Bblock_odd l k
        exact Λ.even_mul_odd _ _ hΔA_even hX₃B_odd
      -- (Δ_M * X₃).D_inv is even
      have hΔX₃D_even : ∀ a b, (Δ_M * X₃).Dblock a b ∈ Λ.even := by
        intro a b
        have hΔX₃_D : (Δ_M * X₃).Dblock = Δ_M.Dblock * X₃.Dblock := by
          show Δ_M.Cblock * X₃.Bblock + Δ_M.Dblock * X₃.Dblock = Δ_M.Dblock * X₃.Dblock
          have hΔC : Δ_M.Cblock = 0 := rfl
          simp only [hΔC, Matrix.zero_mul, zero_add]
        rw [hΔX₃_D]
        simp only [Matrix.mul_apply]
        apply Λ.even.sum_mem
        intro c _
        have hΔD_even : Δ_M.Dblock a c ∈ Λ.even := M.Dblock_even a c
        have hX₃D_even : X₃.Dblock c b ∈ Λ.even := by
          have hX₃_eq' : X₃ = L_M * X₂ := by
            show L_M * U_N * Δ_N * L_N = L_M * (U_N * Δ_N * L_N)
            simp only [SuperMatrix.mul_assoc]
          rw [hX₃_eq']
          show (L_M.Cblock * X₂.Bblock + L_M.Dblock * X₂.Dblock) c b ∈ Λ.even
          simp only [Matrix.add_apply, Matrix.mul_apply]
          apply Λ.even.add_mem
          · apply Λ.even.sum_mem
            intro d _
            have hLC_odd : L_M.Cblock c d ∈ Λ.odd := hDinvCM c d
            have hX₂B_odd : X₂.Bblock d b ∈ Λ.odd := by
              rw [hX₂_eq_N]
              exact N.Bblock_odd d b
            exact Λ.odd_mul_odd _ _ hLC_odd hX₂B_odd
          · have hLD : L_M.Dblock = 1 := rfl
            simp only [hLD, Matrix.one_apply]
            -- Goal: ∑ x, (if c = x then 1 else 0) * X₂.Dblock x b ∈ Λ.even
            -- This sum simplifies to X₂.Dblock c b
            have hsum : ∑ x, (if c = x then 1 else 0) * X₂.Dblock x b = X₂.Dblock c b := by
              have heq : ∀ x, (if c = x then (1 : Λ.carrier) else 0) * X₂.Dblock x b =
                         if x = c then X₂.Dblock x b else 0 := by
                intro x
                split_ifs with h1 h2 h2
                · rw [one_mul]
                · exact (h2 h1.symm).elim
                · exact (h1 h2.symm).elim
                · rw [zero_mul]
              simp only [heq]
              rw [Finset.sum_ite_eq']
              simp only [Finset.mem_univ, ↓reduceIte]
            rw [hsum, hX₂_eq_N]
            exact N.Dblock_even c b
        exact Λ.even_mul_even _ _ hΔD_even hX₃D_even
      have hΔX₃Dinv_even : (Δ_M * X₃).D_inv_carrier k j ∈ Λ.even := by
        unfold SuperMatrix.D_inv_carrier
        rw [Λ.even_mem_iff]
        use ((Δ_M * X₃).D_lifted⁻¹ k j)
        rfl
      exact Λ.odd_mul_even _ _ hΔAX₃B_odd hΔX₃Dinv_even
    -- Need to prove (Δ_M * X₃).D_lifted.det = X₄.D_lifted.det to transport hX₄_D
    have hΔX₃_D_eq : (Δ_M * X₃).D_lifted.det = X₄.D_lifted.det := by
      rw [D_lifted_eq_of_Dblock_eq' _ _ (by simp only [← hX₄_eq] : (Δ_M * X₃).Dblock = X₄.Dblock)]
    have hΔX₃_D : Λ.IsInvertible (Δ_M * X₃).D_lifted.det := hΔX₃_D_eq ▸ hX₄_D
    -- Also need proof that (Λ.liftEvenMatrix D_M M.Dblock_even).det is invertible
    -- D_M = M.Dblock, so liftEvenMatrix D_M M.Dblock_even = M.D_lifted (definitionally)
    have hDM_det : Λ.IsInvertible (Λ.liftEvenMatrix D_M M.Dblock_even).det := hMD
    -- ber_mul_diagonal_left gives us (Δ_M * X₃).ber = Δ_M.ber * X₃.ber
    -- We need X₄.ber = Δ_M.ber * X₃.ber, so first convert using hX₄_eq
    have hber_ΔX₃ : (Δ_M * X₃).ber hΔX₃_D hBDinvΔX₃ = Δ_M.ber hΔ_M_D hBDinv_Δ_M * X₃.ber hX₃_D hBDinvX₃ :=
      SuperMatrix.ber_mul_diagonal_left A_M D_M X₃ h0odd hSchurM M.Dblock_even hDM_det hX₃_D hΔ_M_D hΔX₃_D hBDinvX₃ hBDinvΔX₃ hBDinv_Δ_M
    -- Now show X₄.ber hX₄_D hBDinvX₄ = (Δ_M * X₃).ber hΔX₃_D hBDinvΔX₃
    have hber_X₄_eq : X₄.ber hX₄_D hBDinvX₄ = (Δ_M * X₃).ber hΔX₃_D hBDinvΔX₃ := by
      simp only [SuperMatrix.ber]
      have hSchur_eq : X₄.schurD_carrier = (Δ_M * X₃).schurD_carrier := by
        unfold SuperMatrix.schurD_carrier; rw [hX₄_eq]
      have hD_lifted_eq := D_lifted_eq_of_Dblock_eq' X₄ (Δ_M * X₃) (by simp only [hX₄_eq])
      have h1 := liftEvenMatrix_det_eq_of_eq _ _ (X₄.schurD_even hBDinvX₄)
                  ((Δ_M * X₃).schurD_even hBDinvΔX₃) hSchur_eq
      have h2 : Λ.inv X₄.D_lifted.det hX₄_D = Λ.inv (Δ_M * X₃).D_lifted.det hΔX₃_D := by
        simp only [hD_lifted_eq]
      rw [h1, h2]
    rw [hber_X₄_eq, hber_ΔX₃]

  -- Ber(X₃) = Ber(X₂) (strip L_M from left)
  have hBDinvX₂ : ∀ i j, (X₂.Bblock * X₂.D_inv_carrier) i j ∈ Λ.odd := by
    intro i j; rw [hX₂_eq_N]; exact hBDinvN i j
  have hStrip_L_M : X₃.ber hX₃_D hBDinvX₃ = X₂.ber hX₂_D hBDinvX₂ := by
    have hX₃_eq' : X₃ = L_M * X₂ := by
      show L_M * U_N * Δ_N * L_N = L_M * (U_N * Δ_N * L_N)
      simp only [SuperMatrix.mul_assoc]
    have hDinvCX₂ : ∀ i j, (X₂.D_inv_carrier * X₂.Cblock) i j ∈ Λ.odd := by
      intro i j; rw [hX₂_eq_N]; exact hDinvCN i j
    -- For schurComplementD, we need to handle dependent type - X₂ = N but hX₂_D ≠ hND
    have hSchurX₂ : ∀ i j, (schurComplementD X₂ hX₂_D) i j ∈ Λ.even := by
      intro i j
      -- schurComplementD X₂ hX₂_D = X₂.A - X₂.B * X₂.D_inv_carrier * X₂.C
      -- Since X₂ = N (as matrices), the schur complement values are equal
      unfold schurComplementD SuperMatrix.D_inv_carrier
      simp only [Matrix.sub_apply, Matrix.mul_apply]
      apply Λ.even.sub_mem
      · have hX₂A_eq : X₂.Ablock = N.Ablock := by rw [hX₂_eq_N]
        rw [hX₂A_eq]; exact N.Ablock_even i j
      · apply Λ.even.sum_mem; intro k _
        have hX₂B_eq : X₂.Bblock = N.Bblock := by rw [hX₂_eq_N]
        have hX₂C_eq : X₂.Cblock = N.Cblock := by rw [hX₂_eq_N]
        have hX₂Dinv : ∀ a b, Λ.evenToCarrier (X₂.D_lifted⁻¹ a b) ∈ Λ.even := fun a b => by
          rw [Λ.even_mem_iff]; exact ⟨X₂.D_lifted⁻¹ a b, rfl⟩
        rw [hX₂B_eq, hX₂C_eq]
        -- (∑ l, N.B i l * evenToCarrier (X₂.D_lifted⁻¹ l k)) * N.C k j
        -- = (odd sum) * odd = even
        have hsum_odd : (∑ l, N.Bblock i l * Λ.evenToCarrier (X₂.D_lifted⁻¹ l k)) ∈ Λ.odd := by
          apply Λ.odd.sum_mem; intro l _
          exact Λ.odd_mul_even _ _ (N.Bblock_odd i l) (hX₂Dinv l k)
        exact Λ.odd_mul_odd _ _ hsum_odd (N.Cblock_odd k j)
    -- Need to show (L_M * X₂).ber = X₂.ber, then connect to X₃.ber
    have hLX₂_D : Λ.IsInvertible (L_M * X₂).D_lifted.det := by
      rw [D_lifted_eq_of_Dblock_eq' _ _ (by rw [← hX₃_eq'])]; exact hX₃_D
    have hBDinvLX₂ : ∀ i j, ((L_M * X₂).Bblock * (L_M * X₂).D_inv_carrier) i j ∈ Λ.odd := by
      intro i j
      have heq : (L_M * X₂).Bblock = X₃.Bblock := by rw [← hX₃_eq']
      have heqD : (L_M * X₂).D_inv_carrier = X₃.D_inv_carrier :=
        D_inv_carrier_eq_of_Dblock_eq _ _ (by rw [← hX₃_eq'])
      rw [heq, heqD]; exact hBDinvX₃ i j
    -- Signature: ber_mul_lowerTriangular_left C' N h1 h0even h0odd hC' hND hLD hLND hBDinvN hDinvCN hSchurN hBDinvLN
    have h := SuperMatrix.ber_mul_lowerTriangular_left C_M X₂ h1 h0even h0odd hDinvCM hX₂_D hL_M_D hLX₂_D hBDinvX₂ hDinvCX₂ hSchurX₂ hBDinvLX₂
    -- h : (L_M * X₂).ber hLX₂_D hBDinvLX₂ = X₂.ber hX₂_D hBDinvX₂
    -- Need: X₃.ber hX₃_D hBDinvX₃ = X₂.ber hX₂_D hBDinvX₂
    -- So need: X₃.ber hX₃_D hBDinvX₃ = (L_M * X₂).ber hLX₂_D hBDinvLX₂
    have hX₃_eq_LX₂ : X₃.ber hX₃_D hBDinvX₃ = (L_M * X₂).ber hLX₂_D hBDinvLX₂ := by
      simp only [SuperMatrix.ber]
      have hSchur_eq : X₃.schurD_carrier = (L_M * X₂).schurD_carrier := by
        unfold SuperMatrix.schurD_carrier; rw [hX₃_eq']
      have hD_lifted_eq : X₃.D_lifted = (L_M * X₂).D_lifted :=
        D_lifted_eq_of_Dblock_eq' _ _ (by rw [hX₃_eq'])
      have hX₃_schur_even : ∀ i j, X₃.schurD_carrier i j ∈ Λ.even := X₃.schurD_even hBDinvX₃
      have hLX₂_schur_even : ∀ i j, (L_M * X₂).schurD_carrier i j ∈ Λ.even :=
        (L_M * X₂).schurD_even hBDinvLX₂
      have h1' : (Λ.liftEvenMatrix X₃.schurD_carrier hX₃_schur_even).det =
                (Λ.liftEvenMatrix (L_M * X₂).schurD_carrier hLX₂_schur_even).det :=
        liftEvenMatrix_det_eq_of_eq _ _ _ _ hSchur_eq
      have h2' : Λ.inv X₃.D_lifted.det hX₃_D = Λ.inv (L_M * X₂).D_lifted.det hLX₂_D := by
        simp only [hD_lifted_eq]
      rw [h1', h2']
    rw [hX₃_eq_LX₂, h]

  -- Ber(X₂) = Ber(X₁) (strip U_N from left)
  have hBDinvX₁ : ∀ i j, (X₁.Bblock * X₁.D_inv_carrier) i j ∈ Λ.odd := by
    intro i j
    -- X₁ = Δ_N * L_N
    -- X₁.B = Δ_N.A * L_N.B + Δ_N.B * L_N.D = 0 (Δ_N.B = 0, L_N.B = 0)
    have hX₁_B : X₁.Bblock = 0 := by
      show (Δ_N * L_N).Bblock = 0
      have hΔNB : Δ_N.Bblock = 0 := rfl
      have hLNB : L_N.Bblock = 0 := rfl
      simp only [SuperMatrix.mul_Bblock, hΔNB, hLNB, Matrix.zero_mul, Matrix.mul_zero, add_zero]
    simp only [hX₁_B, Matrix.zero_mul]
    exact h0odd
  -- Define hBDinv_U_N (similar to hBDinv_U_M)
  have hBDinv_U_N : ∀ i j, (U_N.Bblock * U_N.D_inv_carrier) i j ∈ Λ.odd :=
    upperTriangular_BDinv_odd B_N h1 h0even h0odd hBDinvN

  have hStrip_U_N : X₂.ber hX₂_D hBDinvX₂ = X₁.ber hX₁_D hBDinvX₁ := by
    have hX₂_eq' : X₂ = U_N * X₁ := by
      show U_N * Δ_N * L_N = U_N * (Δ_N * L_N)
      simp only [SuperMatrix.mul_assoc]
    -- Similar pattern: show (U_N * X₁).ber = X₁.ber, then connect to X₂.ber
    have hUNX₁_D : Λ.IsInvertible (U_N * X₁).D_lifted.det := by
      rw [D_lifted_eq_of_Dblock_eq' _ _ (by rw [← hX₂_eq'])]; exact hX₂_D
    have hBDinvUNX₁ : ∀ i j, ((U_N * X₁).Bblock * (U_N * X₁).D_inv_carrier) i j ∈ Λ.odd := by
      intro i j
      have heq : (U_N * X₁).Bblock = X₂.Bblock := by rw [← hX₂_eq']
      have heqD : (U_N * X₁).D_inv_carrier = X₂.D_inv_carrier :=
        D_inv_carrier_eq_of_Dblock_eq _ _ (by rw [← hX₂_eq'])
      rw [heq, heqD]; exact hBDinvX₂ i j
    -- Signature: ber_mul_upperTriangular_left B' N h1 h0even h0odd hB' hND hNBDinv hUD hUBDinv hUND hUNBDinv
    have h := SuperMatrix.ber_mul_upperTriangular_left B_N X₁ h1 h0even h0odd hBDinvN hX₁_D hBDinvX₁ hU_N_D hBDinv_U_N hUNX₁_D hBDinvUNX₁
    -- h : (U_N * X₁).ber hUNX₁_D hBDinvUNX₁ = X₁.ber hX₁_D hBDinvX₁
    have hX₂_eq_UNX₁ : X₂.ber hX₂_D hBDinvX₂ = (U_N * X₁).ber hUNX₁_D hBDinvUNX₁ := by
      simp only [SuperMatrix.ber]
      have hSchur_eq : X₂.schurD_carrier = (U_N * X₁).schurD_carrier := by
        unfold SuperMatrix.schurD_carrier; rw [hX₂_eq']
      have hD_lifted_eq : X₂.D_lifted = (U_N * X₁).D_lifted :=
        D_lifted_eq_of_Dblock_eq' _ _ (by rw [hX₂_eq'])
      have hX₂_schur_even : ∀ i j, X₂.schurD_carrier i j ∈ Λ.even := X₂.schurD_even hBDinvX₂
      have hUNX₁_schur_even : ∀ i j, (U_N * X₁).schurD_carrier i j ∈ Λ.even :=
        (U_N * X₁).schurD_even hBDinvUNX₁
      have h1' : (Λ.liftEvenMatrix X₂.schurD_carrier hX₂_schur_even).det =
                (Λ.liftEvenMatrix (U_N * X₁).schurD_carrier hUNX₁_schur_even).det :=
        liftEvenMatrix_det_eq_of_eq _ _ _ _ hSchur_eq
      have h2' : Λ.inv X₂.D_lifted.det hX₂_D = Λ.inv (U_N * X₁).D_lifted.det hUNX₁_D := by
        simp only [hD_lifted_eq]
      rw [h1', h2']
    rw [hX₂_eq_UNX₁, h]

  -- Ber(X₁) = Ber(Δ_N) (strip L_N from right)
  have hX₁_ber : X₁.ber hX₁_D hBDinvX₁ = Δ_N.ber hΔ_N_D hBDinv_Δ_N := by
    show (Δ_N * L_N).ber hX₁_D hBDinvX₁ = Δ_N.ber hΔ_N_D hBDinv_Δ_N
    -- ber_mul_lowerTriangular_right: (M * L).ber hMLD _ = M.ber hMD hBDinv
    -- The second argument of (M*L).ber is auto-generated in the theorem
    exact SuperMatrix.ber_mul_lowerTriangular_right Δ_N C_N h1 h0even h0odd hDinvCN
          hΔ_N_D hL_N_D hX₁_D hBDinv_Δ_N

  calc (M * N).ber hMND hBDinvMN
      = X₅.ber hX₅_D hBDinvMN := by rfl
    _ = X₄.ber hX₄_D hBDinvX₄ := hStrip_U_M
    _ = Δ_M.ber hΔ_M_D hBDinv_Δ_M * X₃.ber hX₃_D hBDinvX₃ := hStrip_Δ_M
    _ = Δ_M.ber hΔ_M_D hBDinv_Δ_M * X₂.ber hX₂_D hBDinvX₂ := by rw [hStrip_L_M]
    _ = Δ_M.ber hΔ_M_D hBDinv_Δ_M * X₁.ber hX₁_D hBDinvX₁ := by rw [hStrip_U_N]
    _ = Δ_M.ber hΔ_M_D hBDinv_Δ_M * Δ_N.ber hΔ_N_D hBDinv_Δ_N := by rw [hX₁_ber]
    _ = M.ber hMD hBDinvM * N.ber hND hBDinvN := by rw [← hBerM_eq, ← hBerN_eq]


end Supermanifolds.Helpers
