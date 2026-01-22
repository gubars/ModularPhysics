import ModularPhysics.StringGeometry.Supermanifolds.Helpers.BerezinianBasics

set_option maxHeartbeats 400000

/-!
# Berezinian Multiplicativity - Case A Invertible

This file contains the Berezinian multiplicativity theorem for the case when M.A is invertible,
building on the basic definitions and lemmas from BerezinianBasics.lean.

## Main result

* `SuperMatrix.ber_mul_A_invertible` - Proves Ber(M*N) = Ber(M) * Ber(N) when M.A is invertible.
-/

namespace Supermanifolds.Helpers

open Supermanifolds

/-- Berezinian multiplicativity when M.A is invertible. -/
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
  have hBDinvL : ∀ i j, (L.Bblock * L.D_inv_carrier) i j ∈ Λ.odd := by
    intro i j
    have hLB : L.Bblock = 0 := rfl
    rw [hLB, Matrix.zero_mul]
    exact h0odd
  have hBDinvΔ : ∀ i j, (Δ.Bblock * Δ.D_inv_carrier) i j ∈ Λ.odd := by
    intro i j
    have hΔB : Δ.Bblock = 0 := rfl
    rw [hΔB, Matrix.zero_mul]
    exact h0odd
  have hBDinvU : ∀ i j, (U.Bblock * U.D_inv_carrier) i j ∈ Λ.odd := by
    intro i j
    have hUB : U.Bblock = B_M := rfl
    have hUD_eq : U.Dblock = 1 := rfl
    have h1_even : ∀ a b, (1 : Matrix (Fin m) (Fin m) Λ.carrier) a b ∈ Λ.even := fun a b => by
      simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]
    have hU_D_lifted_eq : U.D_lifted = Λ.liftEvenMatrix 1 h1_even := by
      simp only [SuperMatrix.D_lifted]
      congr 1
    have hU_D_inv_carrier_eq : U.D_inv_carrier = 1 := by
      simp only [SuperMatrix.D_inv_carrier, hU_D_lifted_eq]
      rw [Λ.liftEvenMatrix_one h1_even, inv_one, matrixEvenToCarrier]
      ext a b
      simp only [Matrix.map_apply, Matrix.one_apply]
      split_ifs with h
      · exact Λ.evenToCarrier.map_one
      · exact Λ.evenToCarrier.map_zero
    rw [hUB, hU_D_inv_carrier_eq, Matrix.mul_one]
    exact hAinvBM i j
  have hBDinvU' : ∀ i j, (U'.Bblock * U'.D_inv_carrier) i j ∈ Λ.odd := by
    intro i j
    have hU'B : U'.Bblock = B_N := rfl
    have hU'D_eq : U'.Dblock = 1 := rfl
    have h1_even : ∀ a b, (1 : Matrix (Fin m) (Fin m) Λ.carrier) a b ∈ Λ.even := fun a b => by
      simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]
    have hU'_D_lifted_eq : U'.D_lifted = Λ.liftEvenMatrix 1 h1_even := by
      simp only [SuperMatrix.D_lifted]
      congr 1
    have hU'_D_inv_carrier_eq : U'.D_inv_carrier = 1 := by
      simp only [SuperMatrix.D_inv_carrier, hU'_D_lifted_eq]
      rw [Λ.liftEvenMatrix_one h1_even, inv_one, matrixEvenToCarrier]
      ext a b
      simp only [Matrix.map_apply, Matrix.one_apply]
      split_ifs with h
      · exact Λ.evenToCarrier.map_one
      · exact Λ.evenToCarrier.map_zero
    rw [hU'B, hU'_D_inv_carrier_eq, Matrix.mul_one]
    exact hBDinvN i j
  have hBDinvΔ' : ∀ i j, (Δ'.Bblock * Δ'.D_inv_carrier) i j ∈ Λ.odd := by
    intro i j
    have hΔ'B : Δ'.Bblock = 0 := rfl
    rw [hΔ'B, Matrix.zero_mul]
    exact h0odd
  have hBDinvL' : ∀ i j, (L'.Bblock * L'.D_inv_carrier) i j ∈ Λ.odd := by
    intro i j
    have hL'B : L'.Bblock = 0 := rfl
    rw [hL'B, Matrix.zero_mul]
    exact h0odd

  have hLD : Λ.IsInvertible L.D_lifted.det := by
    have h1_even : ∀ i j, (1 : Matrix (Fin m) (Fin m) Λ.carrier) i j ∈ Λ.even := fun i j => by
      simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]
    have h_det_one : (Λ.liftEvenMatrix (1 : Matrix (Fin m) (Fin m) Λ.carrier) h1_even).det = 1 := by
      rw [Λ.liftEvenMatrix_one h1_even, Matrix.det_one]
    have hL_D_lifted_eq : L.D_lifted = Λ.liftEvenMatrix 1 h1_even := by
      simp only [SuperMatrix.D_lifted]
      congr 1
    rw [hL_D_lifted_eq, h_det_one]
    exact Λ.one_invertible
  have hΔD : Λ.IsInvertible Δ.D_lifted.det := by
    simp only [SuperMatrix.D_lifted]
    exact hSchurM_det
  have hUD : Λ.IsInvertible U.D_lifted.det := by
    have h1_even : ∀ i j, (1 : Matrix (Fin m) (Fin m) Λ.carrier) i j ∈ Λ.even := fun i j => by
      simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]
    have h_det_one : (Λ.liftEvenMatrix 1 h1_even).det = 1 := by
      rw [Λ.liftEvenMatrix_one h1_even, Matrix.det_one]
    have hU_D_eq : U.Dblock = 1 := rfl
    have hU_D_lifted_eq : U.D_lifted = Λ.liftEvenMatrix 1 h1_even := by
      simp only [SuperMatrix.D_lifted]
      congr 1
    rw [hU_D_lifted_eq, h_det_one]
    exact Λ.one_invertible
  have hU'D : Λ.IsInvertible U'.D_lifted.det := by
    have h1_even : ∀ i j, (1 : Matrix (Fin m) (Fin m) Λ.carrier) i j ∈ Λ.even := fun i j => by
      simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]
    have h_det_one : (Λ.liftEvenMatrix 1 h1_even).det = 1 := by
      rw [Λ.liftEvenMatrix_one h1_even, Matrix.det_one]
    have hU'_D_lifted_eq : U'.D_lifted = Λ.liftEvenMatrix 1 h1_even := by
      simp only [SuperMatrix.D_lifted]
      congr 1
    rw [hU'_D_lifted_eq, h_det_one]
    exact Λ.one_invertible
  have hΔ'D : Λ.IsInvertible Δ'.D_lifted.det := by
    simp only [SuperMatrix.D_lifted]
    exact hND
  have hL'D : Λ.IsInvertible L'.D_lifted.det := by
    have h1_even : ∀ i j, (1 : Matrix (Fin m) (Fin m) Λ.carrier) i j ∈ Λ.even := fun i j => by
      simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]
    have h_det_one : (Λ.liftEvenMatrix 1 h1_even).det = 1 := by
      rw [Λ.liftEvenMatrix_one h1_even, Matrix.det_one]
    have hL'_D_lifted_eq : L'.D_lifted = Λ.liftEvenMatrix 1 h1_even := by
      simp only [SuperMatrix.D_lifted]
      congr 1
    rw [hL'_D_lifted_eq, h_det_one]
    exact Λ.one_invertible

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
    have hD_lifted_eq : (L * Δ * U * (U' * Δ')).D_lifted = (L * Δ * U * (U' * Δ') * L').D_lifted := by
      ext i j; apply Λ.evenToCarrier_injective
      simp only [SuperMatrix.D_lifted, Λ.liftEvenMatrix_spec, hXL'_D_eq']
    have hMN_D_lifted_eq : (L * Δ * U * (U' * Δ') * L').D_lifted = (M * N).D_lifted := by
      ext i j; apply Λ.evenToCarrier_injective
      simp only [SuperMatrix.D_lifted, Λ.liftEvenMatrix_spec, ← hMN_assoc]
    rw [hD_lifted_eq, hMN_D_lifted_eq]
    exact hMND
  have hXL'D : Λ.IsInvertible (L * Δ * U * (U' * Δ') * L').D_lifted.det := by
    have hMN_D_lifted_eq : (L * Δ * U * (U' * Δ') * L').D_lifted = (M * N).D_lifted := by
      ext i j; apply Λ.evenToCarrier_injective
      simp only [SuperMatrix.D_lifted, Λ.liftEvenMatrix_spec, ← hMN_assoc]
    rw [hMN_D_lifted_eq]
    exact hMND

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
    have hX_D_lifted_eq : (L * Δ * U * (U' * Δ')).D_lifted = (M * N).D_lifted := by
      ext i j; apply Λ.evenToCarrier_injective
      simp only [SuperMatrix.D_lifted, Λ.liftEvenMatrix_spec, hX_D_eq]
    have hX_D_inv_carrier_eq : (L * Δ * U * (U' * Δ')).D_inv_carrier = (M * N).D_inv_carrier := by
      simp only [SuperMatrix.D_inv_carrier]
      rw [hX_D_lifted_eq]
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
      have hD_lifted_eq : ((L * Δ * U * (U' * Δ')) * L').D_lifted = (L * Δ * U * (U' * Δ')).D_lifted := by
        ext i j; apply Λ.evenToCarrier_injective
        simp only [SuperMatrix.D_lifted, Λ.liftEvenMatrix_spec, hXL'_D_eq]
      rw [hD_lifted_eq]; exact hXD
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
    -- D_lifted equality
    have hMN_D_lifted_eq : (M * N).D_lifted = (L * Δ * U * (U' * Δ')).D_lifted := by
      ext i j
      simp only [SuperMatrix.D_lifted]
      apply Λ.evenToCarrier_injective
      rw [Λ.liftEvenMatrix_spec _ (M * N).Dblock_even i j]
      rw [Λ.liftEvenMatrix_spec _ (L * Δ * U * (U' * Δ')).Dblock_even i j]
      rw [hMN_D_eq']
    -- D_inv_carrier equality
    have hMN_D_inv_carrier_eq : (M * N).D_inv_carrier = (L * Δ * U * (U' * Δ')).D_inv_carrier := by
      unfold SuperMatrix.D_inv_carrier
      rw [hMN_D_lifted_eq]
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
        have hD_lifted_carrier : matrixEvenToCarrier (L * Δ * U * (U' * Δ')).D_lifted = (L * Δ * U * (U' * Δ')).Dblock := by
          ext i j
          simp only [matrixEvenToCarrier, Matrix.map_apply, SuperMatrix.D_lifted]
          exact Λ.liftEvenMatrix_spec (L * Δ * U * (U' * Δ')).Dblock (L * Δ * U * (U' * Δ')).Dblock_even i j
        have hDinvD_lifted : (L * Δ * U * (U' * Δ')).D_lifted⁻¹ * (L * Δ * U * (U' * Δ')).D_lifted = 1 :=
          Matrix.nonsing_inv_mul (L * Δ * U * (U' * Δ')).D_lifted (isUnit_of_invertible _)
        rw [hD_inv_def, ← hD_lifted_carrier]
        have hD_inv_D : matrixEvenToCarrier (L * Δ * U * (U' * Δ')).D_lifted⁻¹ * matrixEvenToCarrier (L * Δ * U * (U' * Δ')).D_lifted =
            matrixEvenToCarrier ((L * Δ * U * (U' * Δ')).D_lifted⁻¹ * (L * Δ * U * (U' * Δ')).D_lifted) := by
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
        rw [hMN_D_lifted_eq]
      have h_mul_MN : (M * N).D_lifted.det * Λ.inv (M * N).D_lifted.det hMND = 1 := Λ.mul_inv _ hMND
      have h_mul_X : (L * Δ * U * (U' * Δ')).D_lifted.det * Λ.inv (L * Δ * U * (U' * Δ')).D_lifted.det hXD = 1 := Λ.mul_inv _ hXD
      have h_inv_MN : Λ.inv (M * N).D_lifted.det hMND * (M * N).D_lifted.det = 1 := Λ.inv_mul _ hMND
      have h_inv_X : Λ.inv (L * Δ * U * (U' * Δ')).D_lifted.det hXD * (L * Δ * U * (U' * Δ')).D_lifted.det = 1 := Λ.inv_mul _ hXD
      -- Use h_det_eq to rewrite h_mul_X: X.det * inv_X = 1 becomes (M*N).det * inv_X = 1
      have h_mul_X' : (M * N).D_lifted.det * Λ.inv (L * Δ * U * (U' * Δ')).D_lifted.det hXD = 1 := by
        calc (M * N).D_lifted.det * Λ.inv (L * Δ * U * (U' * Δ')).D_lifted.det hXD
            = (L * Δ * U * (U' * Δ')).D_lifted.det * Λ.inv (L * Δ * U * (U' * Δ')).D_lifted.det hXD := by
                rw [h_det_eq]
          _ = 1 := h_mul_X
      -- Now both inv_MN and inv_X are right inverses of (M*N).det, so they're equal
      calc Λ.inv (M * N).D_lifted.det hMND
          = 1 * Λ.inv (M * N).D_lifted.det hMND := by rw [one_mul]
        _ = (Λ.inv (L * Δ * U * (U' * Δ')).D_lifted.det hXD * (M * N).D_lifted.det) *
            Λ.inv (M * N).D_lifted.det hMND := by
              have h_inv_X' : Λ.inv (L * Δ * U * (U' * Δ')).D_lifted.det hXD * (M * N).D_lifted.det = 1 := by
                calc Λ.inv (L * Δ * U * (U' * Δ')).D_lifted.det hXD * (M * N).D_lifted.det
                    = Λ.inv (L * Δ * U * (U' * Δ')).D_lifted.det hXD * (L * Δ * U * (U' * Δ')).D_lifted.det := by
                        rw [h_det_eq]
                  _ = 1 := h_inv_X
              rw [h_inv_X']
        _ = Λ.inv (L * Δ * U * (U' * Δ')).D_lifted.det hXD *
            ((M * N).D_lifted.det * Λ.inv (M * N).D_lifted.det hMND) := by ring
        _ = Λ.inv (L * Δ * U * (U' * Δ')).D_lifted.det hXD * 1 := by rw [h_mul_MN]
        _ = Λ.inv (L * Δ * U * (U' * Δ')).D_lifted.det hXD := by rw [mul_one]
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
    have hXD_lifted_eq : (L * Δ * U * (U' * Δ')).D_lifted =
        (L * Δ * U * U').D_lifted * Δ'.D_lifted := by
      ext i j
      simp only [SuperMatrix.D_lifted, Matrix.mul_apply]
      apply Λ.evenToCarrier_injective
      rw [Λ.liftEvenMatrix_spec _ (L * Δ * U * (U' * Δ')).Dblock_even i j]
      rw [hXΔ'D_eq]
      simp only [Matrix.mul_apply]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      -- Goal: (L * Δ * U * U').Dblock i k * Δ'.Dblock k j = Λ.evenToCarrier (... i k * ... k j)
      have hLHS : (L * Δ * U * U').Dblock i k * Δ'.Dblock k j =
          Λ.evenToCarrier (Λ.liftEvenMatrix (L * Δ * U * U').Dblock (L * Δ * U * U').Dblock_even i k) *
          Λ.evenToCarrier (Λ.liftEvenMatrix Δ'.Dblock Δ'.Dblock_even k j) := by
        rw [Λ.liftEvenMatrix_spec _ (L * Δ * U * U').Dblock_even i k]
        rw [Λ.liftEvenMatrix_spec _ Δ'.Dblock_even k j]
      rw [hLHS, ← Λ.evenToCarrier.map_mul]
    have hXD_eq : (L * Δ * U * (U' * Δ')).D_lifted.det = (L * Δ * U * U').D_lifted.det * Δ'.D_lifted.det := by
      rw [hXD_lifted_eq]
      exact Matrix.det_mul _ _
    -- Also need Δ'.D_lifted.det = N.D_lifted.det
    have hΔ'_D_lifted_eq : Δ'.D_lifted = N.D_lifted := by
      ext i j
      simp only [SuperMatrix.D_lifted]
      apply Λ.evenToCarrier_injective
      rw [Λ.liftEvenMatrix_spec _ Δ'.Dblock_even i j]
      rw [Λ.liftEvenMatrix_spec _ N.Dblock_even i j]
      rfl  -- Δ'.Dblock = N.Dblock by definition
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
    have hΔ'_D_lifted_eq : Δ'.D_lifted = N.D_lifted := by
      ext i j
      simp only [SuperMatrix.D_lifted]
      apply Λ.evenToCarrier_injective
      rw [Λ.liftEvenMatrix_spec _ Δ'.Dblock_even i j]
      rw [Λ.liftEvenMatrix_spec _ N.Dblock_even i j]
      rfl  -- Δ'.Dblock = N.Dblock by definition
    -- The key is that (Z * Δ').D_lifted = Z.D_lifted * Δ'.D_lifted (as matrices over evenCarrier)
    have hZΔ'_D_lifted_eq : (Z * Δ').D_lifted = Z.D_lifted * Δ'.D_lifted := by
      ext i j
      simp only [SuperMatrix.D_lifted, Matrix.mul_apply]
      apply Λ.evenToCarrier_injective
      rw [Λ.liftEvenMatrix_spec _ (Z * Δ').Dblock_even i j]
      rw [hZΔ'D_eq]
      simp only [Matrix.mul_apply]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hDN_eq_Δ' : D_N k j = Δ'.Dblock k j := rfl
      have hLHS : Z.Dblock i k * Δ'.Dblock k j =
          Λ.evenToCarrier (Λ.liftEvenMatrix Z.Dblock Z.Dblock_even i k) *
          Λ.evenToCarrier (Λ.liftEvenMatrix Δ'.Dblock Δ'.Dblock_even k j) := by
        rw [Λ.liftEvenMatrix_spec _ Z.Dblock_even i k]
        rw [Λ.liftEvenMatrix_spec _ Δ'.Dblock_even k j]
      rw [hDN_eq_Δ', hLHS, ← Λ.evenToCarrier.map_mul]
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
          Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv := by
        have h_left_inv : Λ.inv Z.D_lifted.det hZD_inv * Z.D_lifted.det = 1 := Λ.inv_mul _ hZD_inv
        have h_right_inv : Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv * Δ'.D_lifted.det = 1 :=
          Λ.inv_mul _ hΔ'D_lifted_inv
        have h_prod_left : (Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv) *
            (Z.D_lifted.det * Δ'.D_lifted.det) = 1 := by
          calc (Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv) *
              (Z.D_lifted.det * Δ'.D_lifted.det)
              = Λ.inv Z.D_lifted.det hZD_inv * (Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv * Z.D_lifted.det) *
                Δ'.D_lifted.det := by ring
            _ = Λ.inv Z.D_lifted.det hZD_inv * (Z.D_lifted.det * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv) *
                Δ'.D_lifted.det := by ring
            _ = (Λ.inv Z.D_lifted.det hZD_inv * Z.D_lifted.det) *
                (Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv * Δ'.D_lifted.det) := by ring
            _ = 1 * 1 := by rw [h_left_inv, h_right_inv]
            _ = 1 := by ring
        -- Use the fact that h_prod_left shows the product is a left inverse
        have h_prod_right : (Z.D_lifted.det * Δ'.D_lifted.det) *
            (Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv) = 1 := by
          have hZD_cancel : Z.D_lifted.det * Λ.inv Z.D_lifted.det hZD_inv = 1 := Λ.mul_inv _ hZD_inv
          have hΔ'D_cancel : Δ'.D_lifted.det * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv = 1 := Λ.mul_inv _ hΔ'D_lifted_inv
          calc (Z.D_lifted.det * Δ'.D_lifted.det) *
              (Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv)
              = (Z.D_lifted.det * Λ.inv Z.D_lifted.det hZD_inv) *
                (Δ'.D_lifted.det * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv) := by ring
            _ = 1 * 1 := by rw [hZD_cancel, hΔ'D_cancel]
            _ = 1 := by ring
        calc Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) h_prod_inv
            = Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) h_prod_inv * 1 := by rw [mul_one]
          _ = Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) h_prod_inv *
              ((Z.D_lifted.det * Δ'.D_lifted.det) *
               (Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv)) := by
                rw [h_prod_right]
          _ = (Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) h_prod_inv *
              (Z.D_lifted.det * Δ'.D_lifted.det)) *
              (Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv) := by ring
          _ = 1 * (Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv) := by
                rw [Λ.inv_mul _ h_prod_inv]
          _ = Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv := by rw [one_mul]
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
      rw [hZΔ'_D_inv_lifted]
      ext i j
      simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Λ.evenToCarrier.map_mul]
    -- Now compute (Z * Δ').schurD_carrier
    have hZΔ'_schur : (Z * Δ').schurD_carrier = Z.schurD_carrier * A_N := by
      unfold SuperMatrix.schurD_carrier
      rw [hZΔ'A, hZΔ'B, hZΔ'C, hZΔ'_D_inv_carrier]
      -- Goal: Z.A * A_N - Z.B * D_N * (Δ'.D_inv_carrier * Z.D_inv_carrier) * (Z.C * A_N) =
      --       (Z.A - Z.B * Z.D_inv_carrier * Z.C) * A_N
      -- First, simplify: Δ'.D_inv_carrier = N.D_inv_carrier (since Δ'.Dblock = N.Dblock)
      have hΔ'_D_inv_carrier : Δ'.D_inv_carrier = N.D_inv_carrier := by
        unfold SuperMatrix.D_inv_carrier
        rw [hΔ'_D_lifted_eq]
      -- And N.D_inv_carrier * N.Dblock = 1 (in carrier)
      haveI : Invertible N.D_lifted := Matrix.invertibleOfDetInvertible N.D_lifted
      have hDN_inv : N.D_inv_carrier * N.Dblock = 1 := by
        have hD_inv_def : N.D_inv_carrier = matrixEvenToCarrier N.D_lifted⁻¹ := rfl
        have hD_lifted_carrier : matrixEvenToCarrier N.D_lifted = N.Dblock := by
          ext i j
          simp only [matrixEvenToCarrier, Matrix.map_apply, SuperMatrix.D_lifted]
          exact Λ.liftEvenMatrix_spec N.Dblock N.Dblock_even i j
        have hDinvD_lifted : N.D_lifted⁻¹ * N.D_lifted = 1 := Matrix.nonsing_inv_mul N.D_lifted (isUnit_of_invertible _)
        rw [hD_inv_def, ← hD_lifted_carrier]
        have hD_inv_D : matrixEvenToCarrier N.D_lifted⁻¹ * matrixEvenToCarrier N.D_lifted =
            matrixEvenToCarrier (N.D_lifted⁻¹ * N.D_lifted) := by
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
      -- Now: Z.B * D_N * (Δ'.D_inv_carrier * Z.D_inv_carrier) * (Z.C * A_N)
      --    = Z.B * D_N * Δ'.D_inv_carrier * Z.D_inv_carrier * Z.C * A_N
      --    = Z.B * (D_N * Δ'.D_inv_carrier) * Z.D_inv_carrier * Z.C * A_N
      --    = Z.B * (D_N * N.D_inv_carrier) * Z.D_inv_carrier * Z.C * A_N  (using hΔ'_D_inv_carrier)
      -- But we need D_N * N.D_inv_carrier = 1, which is N.Dblock * N.D_inv_carrier
      -- Hmm, we have N.D_inv_carrier * N.Dblock = 1, need the reverse
      have hDN_inv' : N.Dblock * N.D_inv_carrier = 1 := by
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
    have hX_schur_lifted_eq : Λ.liftEvenMatrix (L * Δ * U * (U' * Δ')).schurD_carrier
        ((L * Δ * U * (U' * Δ')).schurD_even hBDinvX) =
        Λ.liftEvenMatrix (Z * Δ').schurD_carrier ((Z * Δ').schurD_even hBDinvZΔ') := by
      ext i j
      apply Λ.evenToCarrier_injective
      simp only [Λ.liftEvenMatrix_spec]
      have h_carrier_eq : (L * Δ * U * (U' * Δ')).schurD_carrier = (Z * Δ').schurD_carrier := by
        simp only [SuperMatrix.schurD_carrier, hX_eq_ZΔ']
      exact congrFun (congrFun h_carrier_eq i) j
    -- Also need to convert D_lifted
    have hX_D_lifted_eq : (L * Δ * U * (U' * Δ')).D_lifted = (Z * Δ').D_lifted := by
      ext i j
      apply Λ.evenToCarrier_injective
      simp only [SuperMatrix.D_lifted, Λ.liftEvenMatrix_spec]
      have h_dblock_eq : (L * Δ * U * (U' * Δ')).Dblock = (Z * Δ').Dblock := by
        simp only [hX_eq_ZΔ']
      exact congrFun (congrFun h_dblock_eq i) j
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
        Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv := by
      have h1 : Z.D_lifted.det * Δ'.D_lifted.det * (Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv) = 1 := by
        have hZD_cancel : Z.D_lifted.det * Λ.inv Z.D_lifted.det hZD_inv = 1 := Λ.mul_inv _ hZD_inv
        have hΔ'D_cancel : Δ'.D_lifted.det * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv = 1 := Λ.mul_inv _ hΔ'D_lifted_inv
        calc Z.D_lifted.det * Δ'.D_lifted.det * (Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv)
            = (Z.D_lifted.det * Λ.inv Z.D_lifted.det hZD_inv) * Δ'.D_lifted.det * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv := by ring
          _ = 1 * Δ'.D_lifted.det * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv := by rw [hZD_cancel]
          _ = Δ'.D_lifted.det * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv := by ring
          _ = 1 := hΔ'D_cancel
      have h_inv_prod_2 : Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) (Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv) *
          (Z.D_lifted.det * Δ'.D_lifted.det) = 1 := Λ.inv_mul _ (Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv)
      calc Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) (Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv)
          = 1 * Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) (Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv) := by rw [one_mul]
        _ = ((Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv) * (Z.D_lifted.det * Δ'.D_lifted.det)) *
            Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) (Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv) := by
              have hinv : (Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv) *
                  (Z.D_lifted.det * Δ'.D_lifted.det) = 1 := by
                calc (Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv) *
                    (Z.D_lifted.det * Δ'.D_lifted.det)
                    = Λ.inv Z.D_lifted.det hZD_inv * (Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv * Z.D_lifted.det) *
                      Δ'.D_lifted.det := by ring
                  _ = Λ.inv Z.D_lifted.det hZD_inv * (Z.D_lifted.det * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv) *
                      Δ'.D_lifted.det := by ring
                  _ = (Λ.inv Z.D_lifted.det hZD_inv * Z.D_lifted.det) *
                      (Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv * Δ'.D_lifted.det) := by ring
                  _ = 1 * (Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv * Δ'.D_lifted.det) := by rw [Λ.inv_mul _ hZD_inv]
                  _ = Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv * Δ'.D_lifted.det := by rw [one_mul]
                  _ = 1 := Λ.inv_mul _ hΔ'D_lifted_inv
              rw [hinv]
        _ = (Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv) *
            ((Z.D_lifted.det * Δ'.D_lifted.det) *
             Λ.inv (Z.D_lifted.det * Δ'.D_lifted.det) (Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv)) := by ring
        _ = (Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv) * 1 := by
              rw [Λ.mul_inv _ (Λ.mul_invertible _ _ hZD_inv hΔ'D_lifted_inv)]
        _ = Λ.inv Z.D_lifted.det hZD_inv * Λ.inv Δ'.D_lifted.det hΔ'D_lifted_inv := by rw [mul_one]
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
    have hW_A_lifted_eq : (L * Δ * U * U').A_lifted = M.A_lifted := by
      ext i j
      apply Λ.evenToCarrier_injective
      simp only [SuperMatrix.A_lifted, Λ.liftEvenMatrix_spec]
      exact congrFun (congrFun hW_A_eq i) j
    have hW_A_det : Λ.IsInvertible (L * Δ * U * U').A_lifted.det := by rw [hW_A_lifted_eq]; exact hMA
    -- Need parity conditions for W.A⁻¹*W.B and W.D⁻¹*W.C
    -- W.A = M.A (even), W.B = M.A*(B_M+B_N) where B_M, B_N are odd
    -- W.A⁻¹*W.B = M.A⁻¹ * M.A * (B_M+B_N) = B_M + B_N which is odd
    have hW_AinvB_odd : ∀ i j, ((L * Δ * U * U').A_inv_carrier * (L * Δ * U * U').Bblock) i j ∈ Λ.odd := by
      intro i j
      -- W.A_inv_carrier = M.A_inv_carrier (since W.A_lifted = M.A_lifted)
      have hW_Ainv_eq : (L * Δ * U * U').A_inv_carrier = M.A_inv_carrier := by
        simp only [SuperMatrix.A_inv_carrier, hW_A_lifted_eq]
      rw [hW_Ainv_eq, hW_eq, hW_B]
      -- Now we need: (M.A_inv_carrier * (M.Ablock * (B_M + B_N))) i j ∈ Λ.odd
      -- M.A_inv_carrier * M.Ablock = 1 (in carrier)
      have hAinvA : M.A_inv_carrier * M.Ablock = 1 := by
        -- A_inv_carrier * Ablock = matrixEvenToCarrier(A_lifted⁻¹) * matrixEvenToCarrier(A_lifted)
        -- = matrixEvenToCarrier(A_lifted⁻¹ * A_lifted) = matrixEvenToCarrier(1) = 1
        have h1 : M.A_lifted⁻¹ * M.A_lifted = 1 := Matrix.nonsing_inv_mul M.A_lifted (isUnit_of_invertible _)
        calc M.A_inv_carrier * M.Ablock
            = matrixEvenToCarrier M.A_lifted⁻¹ * M.Ablock := rfl
          _ = matrixEvenToCarrier M.A_lifted⁻¹ * matrixEvenToCarrier M.A_lifted := by
              congr 1
              ext i j
              simp only [SuperMatrix.A_lifted, matrixEvenToCarrier, Matrix.map_apply, Λ.liftEvenMatrix_spec]
          _ = matrixEvenToCarrier (M.A_lifted⁻¹ * M.A_lifted) := by
              ext i j
              simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
              rw [map_sum]
              congr 1
              ext k
              rw [Λ.evenToCarrier.map_mul]
          _ = matrixEvenToCarrier 1 := by rw [h1]
          _ = 1 := by
              ext i j
              simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply]
              split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
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
      have hAinvA : M.A_inv_carrier * M.Ablock = 1 := by
        have h1 : M.A_lifted⁻¹ * M.A_lifted = 1 := Matrix.nonsing_inv_mul M.A_lifted (isUnit_of_invertible _)
        calc M.A_inv_carrier * M.Ablock
            = matrixEvenToCarrier M.A_lifted⁻¹ * M.Ablock := rfl
          _ = matrixEvenToCarrier M.A_lifted⁻¹ * matrixEvenToCarrier M.A_lifted := by
              congr 1
              ext i j
              simp only [SuperMatrix.A_lifted, matrixEvenToCarrier, Matrix.map_apply, Λ.liftEvenMatrix_spec]
          _ = matrixEvenToCarrier (M.A_lifted⁻¹ * M.A_lifted) := by
              ext i j
              simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
              rw [map_sum]
              congr 1
              ext k
              rw [Λ.evenToCarrier.map_mul]
          _ = matrixEvenToCarrier 1 := by rw [h1]
          _ = 1 := by
              ext i j
              simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply]
              split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
      calc C_M * M.Ablock
          = (M.Cblock * M.A_inv_carrier) * M.Ablock := rfl
        _ = M.Cblock * (M.A_inv_carrier * M.Ablock) := by rw [Matrix.mul_assoc]
        _ = M.Cblock * (1 : Matrix _ _ _) := by rw [hAinvA]
        _ = M.Cblock := by rw [Matrix.mul_one]
    have hW_D_even : ∀ i j, (L * Δ * U * U').Dblock i j ∈ Λ.even := by
      intro i j
      rw [hW_eq, hW_D]
      have hCM_MA_eq : C_M * M.Ablock = M.Cblock := by
        have hAinvA : M.A_inv_carrier * M.Ablock = 1 := by
          have h1 : M.A_lifted⁻¹ * M.A_lifted = 1 := Matrix.nonsing_inv_mul M.A_lifted (isUnit_of_invertible _)
          calc M.A_inv_carrier * M.Ablock
              = matrixEvenToCarrier M.A_lifted⁻¹ * M.Ablock := rfl
            _ = matrixEvenToCarrier M.A_lifted⁻¹ * matrixEvenToCarrier M.A_lifted := by
                congr 1
                ext i' j'
                simp only [SuperMatrix.A_lifted, matrixEvenToCarrier, Matrix.map_apply, Λ.liftEvenMatrix_spec]
            _ = matrixEvenToCarrier (M.A_lifted⁻¹ * M.A_lifted) := by
                ext i' j'
                simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
                rw [map_sum]
                congr 1
                ext k'
                rw [Λ.evenToCarrier.map_mul]
            _ = matrixEvenToCarrier 1 := by rw [h1]
            _ = 1 := by
                ext i' j'
                simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply]
                split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
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
        have h_eq : (L * Δ * U * U').A_lifted = M.A_lifted := by
          ext i j
          apply Λ.evenToCarrier_injective
          simp only [SuperMatrix.A_lifted, Λ.liftEvenMatrix_spec]
          exact congrFun (congrFun hW_A' i) j
        simp only [SuperMatrix.A_inv_carrier, h_eq]
      unfold SuperMatrix.schurA_carrier
      rw [hW_D', hW_C', hW_B', hW_Ainv_eq]
      have hAAinv : M.Ablock * M.A_inv_carrier = 1 := by
        have h1 : M.A_lifted * M.A_lifted⁻¹ = 1 := Matrix.mul_nonsing_inv M.A_lifted (isUnit_of_invertible _)
        calc M.Ablock * M.A_inv_carrier
            = matrixEvenToCarrier M.A_lifted * matrixEvenToCarrier M.A_lifted⁻¹ := by
              congr 1
              ext i j
              simp only [SuperMatrix.A_lifted, matrixEvenToCarrier, Matrix.map_apply, Λ.liftEvenMatrix_spec]
          _ = matrixEvenToCarrier (M.A_lifted * M.A_lifted⁻¹) := by
              ext i j
              simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
              rw [map_sum]
              congr 1
              ext k
              rw [Λ.evenToCarrier.map_mul]
          _ = matrixEvenToCarrier 1 := by rw [h1]
          _ = 1 := by
              ext i j
              simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply]
              split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
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
      have h_lift_eq : Λ.liftEvenMatrix (L * Δ * U * U').schurA_carrier
          ((L * Δ * U * U').schurA_even hCAinvW) =
          Λ.liftEvenMatrix D_M hSchurM := by
        ext i j
        apply Λ.evenToCarrier_injective
        simp only [Λ.liftEvenMatrix_spec]
        exact congrFun (congrFun hSchurAW_eq i) j
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
    have hW_A_lifted_eq : (L * Δ * U * U').A_lifted = M.A_lifted := by
      ext i j
      apply Λ.evenToCarrier_injective
      simp only [SuperMatrix.A_lifted, Λ.liftEvenMatrix_spec]
      exact congrFun (congrFun hW_A_eq i) j
    have hΔ_schurD_eq : Δ.schurD_carrier = M.Ablock := by
      unfold SuperMatrix.schurD_carrier
      have hΔA : Δ.Ablock = M.Ablock := rfl
      have hΔB : Δ.Bblock = 0 := rfl
      have hΔC : Δ.Cblock = 0 := rfl
      simp only [hΔA, hΔB, hΔC, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
    have hΔ_D_lifted_eq : Δ.D_lifted = Λ.liftEvenMatrix D_M hSchurM := rfl
    have hW_schurA_lifted_eq : Λ.liftEvenMatrix (L * Δ * U * U').schurA_carrier
        ((L * Δ * U * U').schurA_even hCAinvW) = Λ.liftEvenMatrix D_M hSchurM := by
      ext i j
      apply Λ.evenToCarrier_injective
      simp only [Λ.liftEvenMatrix_spec]
      exact congrFun (congrFun hSchurAW_eq i) j
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


end Supermanifolds.Helpers
