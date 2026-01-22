import ModularPhysics.StringGeometry.Supermanifolds.Helpers.BerezinianMulA

set_option maxHeartbeats 400000

/-!
# Berezinian Multiplicativity Theorems - Additional Results

This file contains additional multiplicativity theorems for the Berezinian, building on
the basic definitions from BerezinianBasics.lean and the M.A-invertible case from
BerezinianMulA.lean.

## Main results

* `SuperMatrix.ber_mul_lowerTriangular_left` - Ber(L * N) = Ber(N) for lower triangular L
* `SuperMatrix.ber_mul_upperTriangular_right` - Ber(M * U) = Ber(M) for upper triangular U
* `SuperMatrix.ber_mul_diagonal_left` - Multiplicativity for diagonal left factor

-/

namespace Supermanifolds.Helpers

open Supermanifolds

/-- Ber(L * N) = Ber(N) for lower triangular L = [I 0; C' I]. -/
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
  have hLA : Λ.IsInvertible L.A_lifted.det := by
    show Λ.IsInvertible (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').A_lifted.det
    simp only [SuperMatrix.lowerTriangular, SuperMatrix.A_lifted]
    have h1_even : ∀ i j, (1 : Matrix (Fin n) (Fin n) Λ.carrier) i j ∈ Λ.even := fun i j => by
      simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]
    rw [Λ.liftEvenMatrix_one h1_even, Matrix.det_one]
    exact Λ.one_invertible
  have hBDinvL : ∀ i j, (L.Bblock * L.D_inv_carrier) i j ∈ Λ.odd := by
    intro i j
    show ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock *
          (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_inv_carrier) i j ∈ Λ.odd
    simp only [SuperMatrix.lowerTriangular]
    rw [Matrix.zero_mul]
    exact h0odd
  have hBerL : L.ber hLD hBDinvL = 1 := SuperMatrix.ber_lowerTriangular C' h1 h0even h0odd hC' hLD hBDinvL
  have hCAinvL : ∀ i j, (L.Cblock * L.A_inv_carrier) i j ∈ Λ.odd := by
    intro i j
    show ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock *
          (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').A_inv_carrier) i j ∈ Λ.odd
    simp only [SuperMatrix.lowerTriangular, SuperMatrix.A_inv_carrier, SuperMatrix.A_lifted]
    have h1_even : ∀ i j, (1 : Matrix (Fin n) (Fin n) Λ.carrier) i j ∈ Λ.even := fun i j => by
      simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]
    have hLift1 : Λ.liftEvenMatrix (1 : Matrix (Fin n) (Fin n) Λ.carrier) h1_even = 1 :=
      Λ.liftEvenMatrix_one h1_even
    simp only [hLift1, inv_one, matrixEvenToCarrier]
    have h_map_one : (1 : Matrix (Fin n) (Fin n) Λ.evenCarrier).map Λ.evenToCarrier = 1 := by
      ext a b
      simp only [Matrix.map_apply, Matrix.one_apply]
      split_ifs with h
      · exact Λ.evenToCarrier.map_one
      · exact Λ.evenToCarrier.map_zero
    rw [h_map_one, Matrix.mul_one]
    exact hC' i j
  have hAinvBL : ∀ i j, (L.A_inv_carrier * L.Bblock) i j ∈ Λ.odd := by
    intro i j
    show ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').A_inv_carrier *
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
  have hSchurL_det : Λ.IsInvertible (Λ.liftEvenMatrix (schurComplementA L hLA) hSchurL).det := by
    have h1_even : ∀ i j, (1 : Matrix (Fin m) (Fin m) Λ.carrier) i j ∈ Λ.even := fun i j => by
      simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]
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
  have hDinvCL : ∀ i j, (L.D_inv_carrier * L.Cblock) i j ∈ Λ.odd := by
    intro i j
    show ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').D_inv_carrier *
          (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock) i j ∈ Λ.odd
    simp only [SuperMatrix.lowerTriangular, SuperMatrix.D_inv_carrier, SuperMatrix.D_lifted]
    have h1_even : ∀ i j, (1 : Matrix (Fin m) (Fin m) Λ.carrier) i j ∈ Λ.even := fun i j => by
      simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]
    have hLift1 : Λ.liftEvenMatrix (1 : Matrix (Fin m) (Fin m) Λ.carrier) h1_even = 1 :=
      Λ.liftEvenMatrix_one h1_even
    simp only [hLift1, inv_one, matrixEvenToCarrier]
    have h_map_one : (1 : Matrix (Fin m) (Fin m) Λ.evenCarrier).map Λ.evenToCarrier = 1 := by
      ext a b
      simp only [Matrix.map_apply, Matrix.one_apply]
      split_ifs with h
      · exact Λ.evenToCarrier.map_one
      · exact Λ.evenToCarrier.map_zero
    rw [h_map_one, Matrix.one_mul]
    exact hC' i j
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
    rw [hΔZ_D_inv_lifted]
    ext i j
    simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.mul_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Λ.evenToCarrier.map_mul]
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
    calc Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD
        = 1 * Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD := by ring
      _ = (Λ.inv (Λ.liftEvenMatrix D' hD').det hD'det * (Λ.liftEvenMatrix D' hD').det) *
          Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD := by
            rw [Λ.inv_mul _ hD'det]
      _ = Λ.inv (Λ.liftEvenMatrix D' hD').det hD'det *
          ((Λ.liftEvenMatrix D' hD').det *
           Λ.inv (SuperMatrix.diagonal A' D' h0odd hA' hD').D_lifted.det hΔD) := by ring
      _ = Λ.inv (Λ.liftEvenMatrix D' hD').det hD'det * 1 := by rw [h_eq]
      _ = Λ.inv (Λ.liftEvenMatrix D' hD').det hD'det := by ring
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
  have hU_M_D : Λ.IsInvertible U_M.D_lifted.det := by
    have h1_even : ∀ i j, (1 : Matrix (Fin m) (Fin m) Λ.carrier) i j ∈ Λ.even := fun i j => by
      simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]
    -- U_M.Dblock = 1 by definition of upperTriangular, so U_M.D_lifted = liftEvenMatrix 1 _
    have hUM_lift : U_M.D_lifted = Λ.liftEvenMatrix 1 h1_even := rfl
    rw [hUM_lift, Λ.liftEvenMatrix_one h1_even, Matrix.det_one]
    exact Λ.one_invertible

  have hΔ_M_D : Λ.IsInvertible Δ_M.D_lifted.det := by
    simp only [SuperMatrix.D_lifted]
    exact hMD

  have hL_M_D : Λ.IsInvertible L_M.D_lifted.det := by
    have h1_even : ∀ i j, (1 : Matrix (Fin m) (Fin m) Λ.carrier) i j ∈ Λ.even := fun i j => by
      simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]
    have hLM_lift : L_M.D_lifted = Λ.liftEvenMatrix 1 h1_even := rfl
    rw [hLM_lift, Λ.liftEvenMatrix_one h1_even, Matrix.det_one]
    exact Λ.one_invertible

  have hU_N_D : Λ.IsInvertible U_N.D_lifted.det := by
    have h1_even : ∀ i j, (1 : Matrix (Fin m) (Fin m) Λ.carrier) i j ∈ Λ.even := fun i j => by
      simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]
    have hUN_lift : U_N.D_lifted = Λ.liftEvenMatrix 1 h1_even := rfl
    rw [hUN_lift, Λ.liftEvenMatrix_one h1_even, Matrix.det_one]
    exact Λ.one_invertible

  have hΔ_N_D : Λ.IsInvertible Δ_N.D_lifted.det := by
    have hΔN_lift : Δ_N.D_lifted = Λ.liftEvenMatrix N.Dblock N.Dblock_even := rfl
    rw [hΔN_lift]
    exact hND

  have hL_N_D : Λ.IsInvertible L_N.D_lifted.det := by
    have h1_even : ∀ i j, (1 : Matrix (Fin m) (Fin m) Λ.carrier) i j ∈ Λ.even := fun i j => by
      simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]
    have hLN_lift : L_N.D_lifted = Λ.liftEvenMatrix 1 h1_even := rfl
    rw [hLN_lift, Λ.liftEvenMatrix_one h1_even, Matrix.det_one]
    exact Λ.one_invertible

  -- BDinv conditions for diagonal matrices (B=0 so trivially satisfied)
  have hBDinv_Δ_M : ∀ i j, (Δ_M.Bblock * Δ_M.D_inv_carrier) i j ∈ Λ.odd := fun i j => by
    have hΔB : Δ_M.Bblock = 0 := rfl
    simp only [hΔB, Matrix.zero_mul]
    exact h0odd
  have hBDinv_Δ_N : ∀ i j, (Δ_N.Bblock * Δ_N.D_inv_carrier) i j ∈ Λ.odd := fun i j => by
    have hΔB : Δ_N.Bblock = 0 := rfl
    simp only [hΔB, Matrix.zero_mul]
    exact h0odd

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
    have h_schurD_det_eq : (Λ.liftEvenMatrix M.schurD_carrier (M.schurD_even hBDinvM)).det =
        (Λ.liftEvenMatrix Δ_M.schurD_carrier (Δ_M.schurD_even hBDinv_Δ_M)).det := by
      congr 1
      ext i j
      apply Λ.evenToCarrier_injective
      simp only [Λ.liftEvenMatrix_spec, hΔM_schurD_eq]
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
    have h_schurD_det_eq : (Λ.liftEvenMatrix N.schurD_carrier (N.schurD_even hBDinvN)).det =
        (Λ.liftEvenMatrix Δ_N.schurD_carrier (Δ_N.schurD_even hBDinv_Δ_N)).det := by
      congr 1
      ext i j
      apply Λ.evenToCarrier_injective
      simp only [Λ.liftEvenMatrix_spec, hΔN_schurD_eq]
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
    have hMN_D_lifted_eq : (M * N).D_lifted = X₄.D_lifted := by
      ext i j
      apply Λ.evenToCarrier_injective
      simp only [SuperMatrix.D_lifted, Λ.liftEvenMatrix_spec]
      rw [hMN_D_eq]
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
    have hΔMX₃_D_lifted_eq : (Δ_M * X₃).D_lifted = Δ_M.D_lifted * X₃.D_lifted := by
      ext i j
      apply Λ.evenToCarrier_injective
      -- LHS: evenToCarrier ((Δ_M * X₃).D_lifted i j) = (Δ_M * X₃).Dblock i j = (Δ_M.D * X₃.D) i j
      -- RHS: evenToCarrier ((Δ_M.D_lifted * X₃.D_lifted) i j) = Σ evenToCarrier(Δ_M.D_lifted i k * X₃.D_lifted k j)
      simp only [SuperMatrix.D_lifted]
      rw [Λ.liftEvenMatrix_spec, hΔX₃_D, Matrix.mul_apply, Matrix.mul_apply, map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Λ.evenToCarrier.map_mul, Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec]
    have hdet_eq : X₄.D_lifted.det = Δ_M.D_lifted.det * X₃.D_lifted.det := by
      rw [hX₄_D_lifted_eq, hΔMX₃_D_lifted_eq, Matrix.det_mul]
    unfold GrassmannAlgebra.IsInvertible at hX₄_D hΔ_M_D ⊢
    rw [hdet_eq, Λ.body_mul] at hX₄_D
    exact right_ne_zero_of_mul hX₄_D

  have hX₂_D : Λ.IsInvertible X₂.D_lifted.det := by
    -- X₂ = N (by UDL factorization)
    have hX₂_D_lifted_eq : X₂.D_lifted = N.D_lifted := by
      ext i j
      apply Λ.evenToCarrier_injective
      simp only [SuperMatrix.D_lifted, Λ.liftEvenMatrix_spec]
      rw [hX₂_eq_N]
    rw [hX₂_D_lifted_eq]
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
    have hX₂X₁_D_lifted : X₂.D_lifted = X₁.D_lifted := by
      ext i j
      apply Λ.evenToCarrier_injective
      simp only [SuperMatrix.D_lifted, Λ.liftEvenMatrix_spec]
      rw [hX₂_D_eq]
    rw [← hX₂X₁_D_lifted]
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
  have hBDinv_U_M : ∀ i j, (U_M.Bblock * U_M.D_inv_carrier) i j ∈ Λ.odd := by
    intro i j
    have hUB : U_M.Bblock = B_M := rfl
    have hUD : U_M.Dblock = 1 := rfl
    -- U_M.D_lifted = liftEvenMatrix 1 _, so U_M.D_lifted⁻¹ = 1
    -- U_M.D_inv_carrier = matrixEvenToCarrier(1) = 1
    have h1_even : ∀ a b, (1 : Matrix (Fin m) (Fin m) Λ.carrier) a b ∈ Λ.even := fun a b => by
      simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]
    have hUM_Dinv : U_M.D_inv_carrier = 1 := by
      -- U_M.D_lifted = liftEvenMatrix 1 h1_even by definition of upperTriangular
      have hUM_lift : U_M.D_lifted = Λ.liftEvenMatrix 1 h1_even := rfl
      unfold SuperMatrix.D_inv_carrier
      rw [hUM_lift, Λ.liftEvenMatrix_one h1_even, inv_one]
      ext a b
      simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply]
      split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
    rw [hUB, hUM_Dinv, Matrix.mul_one]
    exact hBDinvM i j

  -- Ber(X₅) = Ber(X₄) (strip U_M from left)
  have hStrip_U_M : X₅.ber hX₅_D hBDinvMN = X₄.ber hX₄_D hBDinvX₄ := by
    -- X₅ = M * N = U_M * X₄ by hMN_eq_UX₄
    -- U_M = upperTriangular B_M h1 h0even h0odd hBDinvM
    -- The lemma expects proofs about (upperTriangular ... * X₄), not X₅
    -- We need to cast proofs across the equality hMN_eq_UX₄ : M * N = U_M * X₄
    have hUMX₄_D_inv : Λ.IsInvertible (U_M * X₄).D_lifted.det := by
      have h : (U_M * X₄).D_lifted = X₅.D_lifted := by
        ext i j
        apply Λ.evenToCarrier_injective
        simp only [SuperMatrix.D_lifted]
        rw [Λ.liftEvenMatrix_spec, Λ.liftEvenMatrix_spec]
        show (U_M * X₄).Dblock i j = (M * N).Dblock i j
        rw [hMN_eq_UX₄]
      rw [h]; exact hX₅_D
    have hUMX₄_BDinv : ∀ i j, ((U_M * X₄).Bblock * (U_M * X₄).D_inv_carrier) i j ∈ Λ.odd := by
      intro i j
      have hB_eq : (U_M * X₄).Bblock = X₅.Bblock := by
        show (U_M * X₄).Bblock = (M * N).Bblock; rw [hMN_eq_UX₄]
      have hDinv_eq : (U_M * X₄).D_inv_carrier = X₅.D_inv_carrier := by
        unfold SuperMatrix.D_inv_carrier SuperMatrix.D_lifted
        have hD_eq : (U_M * X₄).Dblock = X₅.Dblock := by
          show (U_M * X₄).Dblock = (M * N).Dblock; rw [hMN_eq_UX₄]
        -- Goal: matrixEvenToCarrier (liftEvenMatrix (U_M * X₄).Dblock ...)⁻¹ =
        --       matrixEvenToCarrier (liftEvenMatrix X₅.Dblock ...)⁻¹
        -- Since Dblock are equal, the liftEvenMatrix results are equal (up to proof term)
        have hD_lifted_eq : Λ.liftEvenMatrix (U_M * X₄).Dblock (U_M * X₄).Dblock_even =
                            Λ.liftEvenMatrix X₅.Dblock X₅.Dblock_even := by
          ext i j
          apply Λ.evenToCarrier_injective
          simp only [Λ.liftEvenMatrix_spec, hD_eq]
        simp only [hD_lifted_eq]
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
      have h1 : (Λ.liftEvenMatrix X₅.schurD_carrier hX₅_schur_even).det =
                (Λ.liftEvenMatrix (U_M * X₄).schurD_carrier hUMX₄_schur_even).det := by
        congr 1
        ext i j
        apply Λ.evenToCarrier_injective
        simp only [Λ.liftEvenMatrix_spec, hSchur_eq]
      have h2 : Λ.inv X₅.D_lifted.det hX₅_D = Λ.inv (U_M * X₄).D_lifted.det hUMX₄_D_inv := by
        -- Both compute the multiplicative inverse of the same element
        -- The D_lifted matrices are equal since X₅ = U_M * X₄
        have hD_lifted_eq : X₅.D_lifted = (U_M * X₄).D_lifted := by
          ext i j
          apply Λ.evenToCarrier_injective
          simp only [SuperMatrix.D_lifted, Λ.liftEvenMatrix_spec]
          show X₅.Dblock i j = (U_M * X₄).Dblock i j
          rw [hX₅_eq]
        -- Since the matrices are definitionally equal after simplification,
        -- so are their determinants, and Λ.inv is proof-irrelevant
        simp only [hD_lifted_eq]
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
      congr 1
      ext i j
      apply Λ.evenToCarrier_injective
      simp only [SuperMatrix.D_lifted, Λ.liftEvenMatrix_spec]
      show (Δ_M * X₃).Dblock i j = X₄.Dblock i j
      rw [← hX₄_eq]
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
      have hD_lifted_eq : X₄.D_lifted = (Δ_M * X₃).D_lifted := by
        ext i j
        apply Λ.evenToCarrier_injective
        simp only [SuperMatrix.D_lifted, Λ.liftEvenMatrix_spec]
        rw [hX₄_eq]
      have hX₄_schur_even : ∀ i j, X₄.schurD_carrier i j ∈ Λ.even := X₄.schurD_even hBDinvX₄
      have hΔX₃_schur_even : ∀ i j, (Δ_M * X₃).schurD_carrier i j ∈ Λ.even :=
        (Δ_M * X₃).schurD_even hBDinvΔX₃
      have h1 : (Λ.liftEvenMatrix X₄.schurD_carrier hX₄_schur_even).det =
                (Λ.liftEvenMatrix (Δ_M * X₃).schurD_carrier hΔX₃_schur_even).det := by
        congr 1
        ext i j
        apply Λ.evenToCarrier_injective
        simp only [Λ.liftEvenMatrix_spec, hSchur_eq]
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
      have heq : (L_M * X₂).D_lifted.det = X₃.D_lifted.det := by
        congr 1; ext i j; apply Λ.evenToCarrier_injective
        simp only [SuperMatrix.D_lifted, Λ.liftEvenMatrix_spec]
        rw [← hX₃_eq']
      rw [heq]; exact hX₃_D
    have hBDinvLX₂ : ∀ i j, ((L_M * X₂).Bblock * (L_M * X₂).D_inv_carrier) i j ∈ Λ.odd := by
      intro i j
      have heq : (L_M * X₂).Bblock = X₃.Bblock := by rw [← hX₃_eq']
      have heqD : (L_M * X₂).D_inv_carrier = X₃.D_inv_carrier := by
        ext a b; unfold SuperMatrix.D_inv_carrier; rw [← hX₃_eq']
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
      have hD_lifted_eq : X₃.D_lifted = (L_M * X₂).D_lifted := by
        ext i j; apply Λ.evenToCarrier_injective
        simp only [SuperMatrix.D_lifted, Λ.liftEvenMatrix_spec, hX₃_eq']
      have hX₃_schur_even : ∀ i j, X₃.schurD_carrier i j ∈ Λ.even := X₃.schurD_even hBDinvX₃
      have hLX₂_schur_even : ∀ i j, (L_M * X₂).schurD_carrier i j ∈ Λ.even :=
        (L_M * X₂).schurD_even hBDinvLX₂
      have h1' : (Λ.liftEvenMatrix X₃.schurD_carrier hX₃_schur_even).det =
                (Λ.liftEvenMatrix (L_M * X₂).schurD_carrier hLX₂_schur_even).det := by
        congr 1; ext i j; apply Λ.evenToCarrier_injective
        simp only [Λ.liftEvenMatrix_spec, hSchur_eq]
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
  have hBDinv_U_N : ∀ i j, (U_N.Bblock * U_N.D_inv_carrier) i j ∈ Λ.odd := by
    intro i j
    have hUB : U_N.Bblock = B_N := rfl
    -- U_N.D_inv_carrier = 1 (since U_N.D = 1, so D_lifted = 1, so D_lifted⁻¹ = 1)
    have h1_even : ∀ a b, (1 : Matrix (Fin m) (Fin m) Λ.carrier) a b ∈ Λ.even := fun a b => by
      simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]
    have hUN_Dinv : U_N.D_inv_carrier = 1 := by
      -- U_N.D_lifted = liftEvenMatrix 1 h1_even by definition of upperTriangular
      have hUN_lift : U_N.D_lifted = Λ.liftEvenMatrix 1 h1_even := rfl
      unfold SuperMatrix.D_inv_carrier
      rw [hUN_lift, Λ.liftEvenMatrix_one h1_even, inv_one]
      ext a b
      simp only [matrixEvenToCarrier, Matrix.map_apply, Matrix.one_apply]
      split_ifs <;> simp [Λ.evenToCarrier.map_one, Λ.evenToCarrier.map_zero]
    rw [hUB, hUN_Dinv, Matrix.mul_one]
    exact hBDinvN i j

  have hStrip_U_N : X₂.ber hX₂_D hBDinvX₂ = X₁.ber hX₁_D hBDinvX₁ := by
    have hX₂_eq' : X₂ = U_N * X₁ := by
      show U_N * Δ_N * L_N = U_N * (Δ_N * L_N)
      simp only [SuperMatrix.mul_assoc]
    -- Similar pattern: show (U_N * X₁).ber = X₁.ber, then connect to X₂.ber
    have hUNX₁_D : Λ.IsInvertible (U_N * X₁).D_lifted.det := by
      have heq : (U_N * X₁).D_lifted.det = X₂.D_lifted.det := by
        congr 1; ext i j; apply Λ.evenToCarrier_injective
        simp only [SuperMatrix.D_lifted, Λ.liftEvenMatrix_spec]
        rw [← hX₂_eq']
      rw [heq]; exact hX₂_D
    have hBDinvUNX₁ : ∀ i j, ((U_N * X₁).Bblock * (U_N * X₁).D_inv_carrier) i j ∈ Λ.odd := by
      intro i j
      have heq : (U_N * X₁).Bblock = X₂.Bblock := by rw [← hX₂_eq']
      have heqD : (U_N * X₁).D_inv_carrier = X₂.D_inv_carrier := by
        ext a b; unfold SuperMatrix.D_inv_carrier; rw [← hX₂_eq']
      rw [heq, heqD]; exact hBDinvX₂ i j
    -- Signature: ber_mul_upperTriangular_left B' N h1 h0even h0odd hB' hND hNBDinv hUD hUBDinv hUND hUNBDinv
    have h := SuperMatrix.ber_mul_upperTriangular_left B_N X₁ h1 h0even h0odd hBDinvN hX₁_D hBDinvX₁ hU_N_D hBDinv_U_N hUNX₁_D hBDinvUNX₁
    -- h : (U_N * X₁).ber hUNX₁_D hBDinvUNX₁ = X₁.ber hX₁_D hBDinvX₁
    have hX₂_eq_UNX₁ : X₂.ber hX₂_D hBDinvX₂ = (U_N * X₁).ber hUNX₁_D hBDinvUNX₁ := by
      simp only [SuperMatrix.ber]
      have hSchur_eq : X₂.schurD_carrier = (U_N * X₁).schurD_carrier := by
        unfold SuperMatrix.schurD_carrier; rw [hX₂_eq']
      have hD_lifted_eq : X₂.D_lifted = (U_N * X₁).D_lifted := by
        ext i j; apply Λ.evenToCarrier_injective
        simp only [SuperMatrix.D_lifted, Λ.liftEvenMatrix_spec, hX₂_eq']
      have hX₂_schur_even : ∀ i j, X₂.schurD_carrier i j ∈ Λ.even := X₂.schurD_even hBDinvX₂
      have hUNX₁_schur_even : ∀ i j, (U_N * X₁).schurD_carrier i j ∈ Λ.even :=
        (U_N * X₁).schurD_even hBDinvUNX₁
      have h1' : (Λ.liftEvenMatrix X₂.schurD_carrier hX₂_schur_even).det =
                (Λ.liftEvenMatrix (U_N * X₁).schurD_carrier hUNX₁_schur_even).det := by
        congr 1; ext i j; apply Λ.evenToCarrier_injective
        simp only [Λ.liftEvenMatrix_spec, hSchur_eq]
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
