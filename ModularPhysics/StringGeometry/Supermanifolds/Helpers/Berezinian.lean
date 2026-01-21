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
over a superalgebra.

## Main definitions

* `SuperMatrix` - A 2×2 block matrix over a superalgebra with proper grading:
  - A, D blocks have entries in the EVEN part
  - B, C blocks have entries in the ODD part
* `SuperMatrix.ber` - The superdeterminant Ber(M) = det(A - BD⁻¹C) / det(D)
* `berezinian_mul` - Multiplicativity: Ber(MN) = Ber(M) · Ber(N)

## Mathematical Background

For a supermatrix M = [A B; C D] over a superalgebra Λ = Λ₀ ⊕ Λ₁:
- A (n×n) and D (m×m) have entries in Λ₀ (even/bosonic)
- B (n×m) and C (m×n) have entries in Λ₁ (odd/fermionic)

The key property is that odd elements anticommute: for θ, η ∈ Λ₁, θη = -ηθ.
This is what makes the Berezinian multiplicative: Ber(MN) = Ber(M)·Ber(N).

The Berezinian is defined as:
  Ber(M) = det(A - BD⁻¹C) · det(D)⁻¹ = det(A) · det(D - CA⁻¹B)⁻¹

Both formulas agree due to the Grassmann structure of B and C.

## References

* Berezin, F. "Introduction to Superanalysis"
* Manin, Y. "Gauge Field Theory and Complex Geometry"
* Deligne, P., Morgan, J. "Notes on Supersymmetry"
-/

namespace Supermanifolds.Helpers

open Supermanifolds

-- SuperMatrix and MatrixParity content has been moved to separate files:
-- - SuperMatrix.lean: SuperMatrix structure and basic operations
-- - MatrixParity.lean: Grassmann properties, trace lemmas, parity lemmas

/-!
## Berezinian Definition

The Berezinian (superdeterminant) for a supermatrix M = [A B; C D].

For a proper supermatrix over a Grassmann algebra, there are two equivalent formulas:
1. D-based: Ber(M) = det(A - BD⁻¹C) / det(D)  (requires D invertible)
2. A-based: Ber(M) = det(A) / det(D - CA⁻¹B)  (requires A invertible)

These formulas agree due to the Grassmann structure of B and C.
-/

/-- Berezinian for a SuperMatrix over a FieldSuperAlgebra.

    For a supermatrix M = [A B; C D] where:
    - A, D blocks have entries in the even part Λ₀ (commutative)
    - B, C blocks have entries in the odd part Λ₁ (anticommuting)

    The Berezinian is: Ber(M) = det(A - BD⁻¹C) · det(D)⁻¹

    **Mathematical context:**
    The matrices A, B, C, D have entries in a Grassmann algebra Λ = ℂ[θ₁, θ₂, ...].
    The even part Λ₀ is commutative, and elements with nonzero "body" (constant ℂ term)
    are invertible via the geometric series: (z + n)⁻¹ = z⁻¹ Σₖ (-z⁻¹n)ᵏ.

    **Lean formalization:**
    We use FieldSuperAlgebra which has a Field structure on the carrier directly,
    avoiding typeclass diamonds. The Field structure provides:
    - CommRing operations (for det)
    - Inv (for matrix/scalar inverses)
    The grading (even/odd) is tracked by the FieldSuperAlgebra structure. -/
noncomputable def SuperMatrix.ber {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ} (M : SuperMatrix A n m)
    (_hD : M.Dblock.det ≠ 0) : A.carrier :=
  (M.Ablock - M.Bblock * M.Dblock⁻¹ * M.Cblock).det * (M.Dblock.det)⁻¹

/-- A-based Berezinian formula: BerAlt(M) = det(A) · det(D - CA⁻¹B)⁻¹

    This alternative formula requires A to be invertible instead of D.
    When both A and D are invertible, ber and berAlt agree. -/
noncomputable def SuperMatrix.berAlt {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ} (M : SuperMatrix A n m)
    (_hA : M.Ablock.det ≠ 0) : A.carrier :=
  M.Ablock.det * (M.Dblock - M.Cblock * M.Ablock⁻¹ * M.Bblock).det⁻¹

/-- The two Berezinian formulas agree when both A and D are invertible.

    This follows from the Schur complement determinant identity:
    det(A) · det(S_A) = det(D) · det(S_D)
    where S_A = D - CA⁻¹B and S_D = A - BD⁻¹C.

    Therefore: det(S_D) / det(D) = det(A) / det(S_A)
               ber(M) = berAlt(M) -/
theorem SuperMatrix.ber_eq_berAlt {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    [SuperCommutative A.toSuperAlgebra] {n m : ℕ}
    (M : SuperMatrix A n m)
    (hMA : M.Ablock.det ≠ 0) (hMD : M.Dblock.det ≠ 0)
    (hAinvB : ∀ i j, (M.Ablock⁻¹ * M.Bblock) i j ∈ A.odd)
    (hDinvC : ∀ i j, (M.Dblock⁻¹ * M.Cblock) i j ∈ A.odd)
    (h1 : (1 : A.carrier) ∈ A.even) (h0 : (0 : A.carrier) ∈ A.even) :
    M.ber hMD = M.berAlt hMA := by
  -- Goal: det(A - BD⁻¹C) * det(D)⁻¹ = det(A) * det(D - CA⁻¹B)⁻¹
  --
  -- Key identity: det(S_D) * det(S_A) = det(A) * det(D)
  -- where S_D = A - BD⁻¹C and S_A = D - CA⁻¹B.
  --
  -- Proof: S_D = A(I - A⁻¹BD⁻¹C), S_A = D(I - D⁻¹CA⁻¹B)
  -- Let X = D⁻¹C, Y = A⁻¹B (both odd by hypotheses).
  -- Then A⁻¹BD⁻¹C = A⁻¹B * D⁻¹C = YX and D⁻¹CA⁻¹B = D⁻¹C * A⁻¹B = XY.
  -- By grassmann_det_one_sub_mul_comm: det(I-XY) * det(I-YX) = 1
  -- So det(S_D) * det(S_A) = det(A) * det(I-YX) * det(D) * det(I-XY)
  --                       = det(A) * det(D) * 1 = det(A) * det(D)
  --
  -- Then: det(S_D) / det(D) = det(A) * det(D) / (det(D) * det(S_A))
  --                        = det(A) / det(S_A) = det(A) * det(S_A)⁻¹
  unfold SuperMatrix.ber SuperMatrix.berAlt
  -- Use grassmann identity with X = D⁻¹C, Y = A⁻¹B
  -- hGrass : det(I - XY) * det(I - YX) = 1
  -- where XY = D⁻¹C * A⁻¹B = D⁻¹CA⁻¹B and YX = A⁻¹B * D⁻¹C = A⁻¹BD⁻¹C
  have hGrass := grassmann_det_one_sub_mul_comm (M.Dblock⁻¹ * M.Cblock) (M.Ablock⁻¹ * M.Bblock)
                   hDinvC hAinvB h1 h0
  -- Set up invertibility
  haveI : Invertible M.Ablock.det := invertibleOfNonzero hMA
  haveI : Invertible M.Ablock := Matrix.invertibleOfDetInvertible M.Ablock
  haveI : Invertible M.Dblock.det := invertibleOfNonzero hMD
  haveI : Invertible M.Dblock := Matrix.invertibleOfDetInvertible M.Dblock
  -- S_D = A - BD⁻¹C = A(I - A⁻¹BD⁻¹C)
  -- S_A = D - CA⁻¹B = D(I - D⁻¹CA⁻¹B)
  -- det(S_D) = det(A) * det(I - A⁻¹BD⁻¹C) = det(A) * det(I - YX)
  -- det(S_A) = det(D) * det(I - D⁻¹CA⁻¹B) = det(D) * det(I - XY)
  -- Goal: det(S_D) * det(D)⁻¹ = det(A) * det(S_A)⁻¹
  -- Equivalently: det(S_D) * det(S_A) = det(A) * det(D)
  -- Proof: det(A) * det(I-YX) * det(D) * det(I-XY) = det(A) * det(D) * (det(I-XY) * det(I-YX))
  --      = det(A) * det(D) * 1 = det(A) * det(D)
  -- Factor out A from S_D
  have hSD_factor : M.Ablock - M.Bblock * M.Dblock⁻¹ * M.Cblock =
                    M.Ablock * (1 - M.Ablock⁻¹ * M.Bblock * M.Dblock⁻¹ * M.Cblock) := by
    have hAAinv : M.Ablock * M.Ablock⁻¹ = 1 := Matrix.mul_nonsing_inv M.Ablock (isUnit_of_invertible _)
    have hassoc : M.Ablock⁻¹ * (M.Bblock * M.Dblock⁻¹ * M.Cblock) =
                  M.Ablock⁻¹ * M.Bblock * M.Dblock⁻¹ * M.Cblock := by
      simp only [Matrix.mul_assoc]
    calc M.Ablock - M.Bblock * M.Dblock⁻¹ * M.Cblock
        = M.Ablock * 1 - M.Bblock * M.Dblock⁻¹ * M.Cblock := by rw [Matrix.mul_one]
      _ = M.Ablock * 1 - M.Ablock * (M.Ablock⁻¹ * (M.Bblock * M.Dblock⁻¹ * M.Cblock)) := by
          rw [← Matrix.mul_assoc, hAAinv, Matrix.one_mul]
      _ = M.Ablock * (1 - M.Ablock⁻¹ * (M.Bblock * M.Dblock⁻¹ * M.Cblock)) := by rw [← Matrix.mul_sub]
      _ = M.Ablock * (1 - M.Ablock⁻¹ * M.Bblock * M.Dblock⁻¹ * M.Cblock) := by rw [hassoc]
  -- Factor out D from S_A
  have hSA_factor : M.Dblock - M.Cblock * M.Ablock⁻¹ * M.Bblock =
                    M.Dblock * (1 - M.Dblock⁻¹ * M.Cblock * M.Ablock⁻¹ * M.Bblock) := by
    have hDDinv : M.Dblock * M.Dblock⁻¹ = 1 := Matrix.mul_nonsing_inv M.Dblock (isUnit_of_invertible _)
    have hassoc : M.Dblock⁻¹ * (M.Cblock * M.Ablock⁻¹ * M.Bblock) =
                  M.Dblock⁻¹ * M.Cblock * M.Ablock⁻¹ * M.Bblock := by
      simp only [Matrix.mul_assoc]
    calc M.Dblock - M.Cblock * M.Ablock⁻¹ * M.Bblock
        = M.Dblock * 1 - M.Cblock * M.Ablock⁻¹ * M.Bblock := by rw [Matrix.mul_one]
      _ = M.Dblock * 1 - M.Dblock * (M.Dblock⁻¹ * (M.Cblock * M.Ablock⁻¹ * M.Bblock)) := by
          rw [← Matrix.mul_assoc, hDDinv, Matrix.one_mul]
      _ = M.Dblock * (1 - M.Dblock⁻¹ * (M.Cblock * M.Ablock⁻¹ * M.Bblock)) := by rw [← Matrix.mul_sub]
      _ = M.Dblock * (1 - M.Dblock⁻¹ * M.Cblock * M.Ablock⁻¹ * M.Bblock) := by rw [hassoc]
  -- Rewrite in terms of X = D⁻¹C, Y = A⁻¹B
  -- A⁻¹BD⁻¹C = A⁻¹B * D⁻¹C = YX (need associativity)
  have hYX : M.Ablock⁻¹ * M.Bblock * M.Dblock⁻¹ * M.Cblock =
             (M.Ablock⁻¹ * M.Bblock) * (M.Dblock⁻¹ * M.Cblock) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
  -- D⁻¹CA⁻¹B = D⁻¹C * A⁻¹B = XY
  have hXY : M.Dblock⁻¹ * M.Cblock * M.Ablock⁻¹ * M.Bblock =
             (M.Dblock⁻¹ * M.Cblock) * (M.Ablock⁻¹ * M.Bblock) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
  rw [hSD_factor, hSA_factor, Matrix.det_mul, Matrix.det_mul, hYX, hXY]
  -- Goal: det(A) * det(I - YX) * det(D)⁻¹ = det(A) * (det(D) * det(I - XY))⁻¹
  -- Use hGrass: det(I - XY) * det(I - YX) = 1
  -- So det(I - XY)⁻¹ = det(I - YX)
  have hDetIXY_inv : (1 - (M.Dblock⁻¹ * M.Cblock) * (M.Ablock⁻¹ * M.Bblock)).det⁻¹ =
                     (1 - (M.Ablock⁻¹ * M.Bblock) * (M.Dblock⁻¹ * M.Cblock)).det := by
    -- hGrass : det(I_m - XY) * det(I_n - YX) = 1
    -- where X = D⁻¹C : m×n, Y = A⁻¹B : n×m
    -- So XY : m×m and YX : n×n
    -- Need: det(I_m - XY)⁻¹ = det(I_n - YX)
    -- From a * b = 1, we get a⁻¹ = b (when a ≠ 0)
    have hne : (1 - (M.Dblock⁻¹ * M.Cblock) * (M.Ablock⁻¹ * M.Bblock)).det ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hGrass
      exact one_ne_zero hGrass.symm
    -- From hGrass: a * b = 1 where a = det(I_m - XY), b = det(I_n - YX)
    -- So a⁻¹ = b
    exact (eq_inv_of_mul_eq_one_right hGrass).symm
  -- RHS = det(A) * (det(D) * det(I - XY))⁻¹ = det(A) * det(D)⁻¹ * det(I - XY)⁻¹
  --     = det(A) * det(D)⁻¹ * det(I - YX)  (using hDetIXY_inv)
  -- LHS = det(A) * det(I - YX) * det(D)⁻¹
  -- These are equal by commutativity
  rw [mul_inv]
  rw [hDetIXY_inv]
  ring

-- NOTE: berAlt_mul_lowerTriangular_left is defined after SuperMatrix.lowerTriangular
-- (see below).

/-- The two Berezinian formulas agree when B = C = 0.

    For diagonal supermatrices [A 0; 0 D]:
    - D-based: det(A - 0·D⁻¹·0) / det(D) = det(A) / det(D)
    - A-based: det(A) / det(D - 0·A⁻¹·0) = det(A) / det(D)

    These trivially agree.

    Note: The general case for supermatrices with nonzero B, C requires
    Grassmann algebra formalism to properly express BC nilpotency. -/
theorem berezinian_formulas_agree_diagonal {n m : ℕ}
    (Amat : Matrix (Fin n) (Fin n) ℂ) (Dmat : Matrix (Fin m) (Fin m) ℂ)
    (_hA : Amat.det ≠ 0) (_hD : Dmat.det ≠ 0) :
    let B : Matrix (Fin n) (Fin m) ℂ := 0
    let C : Matrix (Fin m) (Fin n) ℂ := 0
    let schurD := Amat - B * Dmat⁻¹ * C  -- = A
    let schurA := Dmat - C * Amat⁻¹ * B  -- = D
    schurD.det * Dmat.det⁻¹ = Amat.det * schurA.det⁻¹ := by
  -- Both Schur complements simplify when B = C = 0
  simp only [Matrix.zero_mul, Matrix.mul_zero, sub_zero]

/-!
## Schur Complements
-/

/-- D-based Schur complement: A - BD⁻¹C -/
noncomputable def schurComplementD {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ} (M : SuperMatrix A n m) (_ : M.Dblock.det ≠ 0) :
    Matrix (Fin n) (Fin n) A.carrier :=
  M.Ablock - M.Bblock * M.Dblock⁻¹ * M.Cblock

/-- A-based Schur complement: D - CA⁻¹B -/
noncomputable def schurComplementA {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ} (M : SuperMatrix A n m) (_ : M.Ablock.det ≠ 0) :
    Matrix (Fin m) (Fin m) A.carrier :=
  M.Dblock - M.Cblock * M.Ablock⁻¹ * M.Bblock


/-!
## LDU and UDL Factorizations

Every invertible supermatrix has LDU and UDL factorizations.
- **UDL (D-based)**: M = U · Δ · L where U = [I BD⁻¹; 0 I], Δ = [S_D 0; 0 D], L = [I 0; D⁻¹C I]
  - Requires D invertible
  - S_D = A - BD⁻¹C (D-based Schur complement)

- **LDU (A-based)**: M = L · Δ · U where L = [I 0; CA⁻¹ I], Δ = [A 0; 0 S_A], U = [I A⁻¹B; 0 I]
  - Requires A invertible
  - S_A = D - CA⁻¹B (A-based Schur complement)

These are essential for proving Berezinian multiplicativity.
-/

/-- Lower triangular factor (D-based): L = [I 0; D⁻¹C I] -/
noncomputable def lowerTriangularFactorD {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ} (M : SuperMatrix A n m) (_hD : M.Dblock.det ≠ 0)
    (h1 : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even)
    (h0odd : (0 : A.carrier) ∈ A.odd)
    (hDinvC : ∀ i j, (M.Dblock⁻¹ * M.Cblock) i j ∈ A.odd) : SuperMatrix A n m :=
  ⟨1, 0, M.Dblock⁻¹ * M.Cblock, 1,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even],
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   hDinvC,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]⟩

/-- Upper triangular factor (D-based): U = [I BD⁻¹; 0 I] -/
noncomputable def upperTriangularFactorD {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ} (M : SuperMatrix A n m) (_hD : M.Dblock.det ≠ 0)
    (h1 : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even)
    (h0odd : (0 : A.carrier) ∈ A.odd)
    (hBDinv : ∀ i j, (M.Bblock * M.Dblock⁻¹) i j ∈ A.odd) : SuperMatrix A n m :=
  ⟨1, M.Bblock * M.Dblock⁻¹, 0, 1,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even],
   hBDinv,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]⟩

/-- Diagonal factor (D-based): Δ = [SchurD 0; 0 D] -/
noncomputable def diagonalFactorD {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ} (M : SuperMatrix A n m) (hD : M.Dblock.det ≠ 0)
    (h0odd : (0 : A.carrier) ∈ A.odd)
    (hSchur : ∀ i j, (schurComplementD M hD) i j ∈ A.even) : SuperMatrix A n m :=
  ⟨schurComplementD M hD, 0, 0, M.Dblock,
   hSchur,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   M.Dblock_even⟩

/-- Lower triangular factor (A-based): L = [I 0; CA⁻¹ I] -/
noncomputable def lowerTriangularFactorA {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ} (M : SuperMatrix A n m) (_hA : M.Ablock.det ≠ 0)
    (h1 : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even)
    (h0odd : (0 : A.carrier) ∈ A.odd)
    (hCAinv : ∀ i j, (M.Cblock * M.Ablock⁻¹) i j ∈ A.odd) : SuperMatrix A n m :=
  ⟨1, 0, M.Cblock * M.Ablock⁻¹, 1,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even],
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   hCAinv,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]⟩

/-- Upper triangular factor (A-based): U = [I A⁻¹B; 0 I] -/
noncomputable def upperTriangularFactorA {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ} (M : SuperMatrix A n m) (_hA : M.Ablock.det ≠ 0)
    (h1 : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even)
    (h0odd : (0 : A.carrier) ∈ A.odd)
    (hAinvB : ∀ i j, (M.Ablock⁻¹ * M.Bblock) i j ∈ A.odd) : SuperMatrix A n m :=
  ⟨1, M.Ablock⁻¹ * M.Bblock, 0, 1,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even],
   hAinvB,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]⟩

/-- Diagonal factor (A-based): Δ = [A 0; 0 SchurA] -/
noncomputable def diagonalFactorA {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ} (M : SuperMatrix A n m) (hA : M.Ablock.det ≠ 0)
    (h0odd : (0 : A.carrier) ∈ A.odd)
    (hSchur : ∀ i j, (schurComplementA M hA) i j ∈ A.even) : SuperMatrix A n m :=
  ⟨M.Ablock, 0, 0, schurComplementA M hA,
   M.Ablock_even,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   hSchur⟩

/-!
## Berezinian of Special Matrices
-/

/-- Berezinian of upper triangular matrix [I B; 0 I] is 1.
    Proof: Schur complement = I - B·I⁻¹·0 = I, so Ber = det(I)/det(I) = 1

    We state this for ℂ-valued matrices to avoid typeclass diamonds with SuperAlgebra.
    The mathematical content is the same. -/
theorem berezinian_upper_triangular_complex {n m : ℕ} (B : Matrix (Fin n) (Fin m) ℂ)
    (_hDdet : (1 : Matrix (Fin m) (Fin m) ℂ).det ≠ 0) :
    let C : Matrix (Fin m) (Fin n) ℂ := 0
    let schur := (1 : Matrix (Fin n) (Fin n) ℂ) - B * (1 : Matrix (Fin m) (Fin m) ℂ)⁻¹ * C
    schur.det * ((1 : Matrix (Fin m) (Fin m) ℂ).det)⁻¹ = 1 := by
  -- Schur complement = I - B·I⁻¹·0 = I - B·I·0 = I - 0 = I
  simp only [Matrix.mul_zero, sub_zero, Matrix.det_one, inv_one, mul_one]

/-- Berezinian of lower triangular matrix [I 0; C I] is 1.
    Proof: Schur complement = I - 0·I⁻¹·C = I, so Ber = det(I)/det(I) = 1

    We state this for ℂ-valued matrices to avoid typeclass diamonds with SuperAlgebra. -/
theorem berezinian_lower_triangular_complex {n m : ℕ} (C : Matrix (Fin m) (Fin n) ℂ)
    (_hDdet : (1 : Matrix (Fin m) (Fin m) ℂ).det ≠ 0) :
    let B : Matrix (Fin n) (Fin m) ℂ := 0
    let schur := (1 : Matrix (Fin n) (Fin n) ℂ) - B * (1 : Matrix (Fin m) (Fin m) ℂ)⁻¹ * C
    schur.det * ((1 : Matrix (Fin m) (Fin m) ℂ).det)⁻¹ = 1 := by
  -- Schur complement = I - 0·I⁻¹·C = I - 0 = I
  simp only [Matrix.zero_mul, sub_zero, Matrix.det_one, inv_one, mul_one]

/-- Berezinian of diagonal matrix [A 0; 0 D] is det(A) · det(D)⁻¹.
    Proof: Schur complement = A - 0·D⁻¹·0 = A

    We state this for ℂ-valued matrices to avoid typeclass diamonds with SuperAlgebra. -/
theorem berezinian_diagonal_complex {n m : ℕ}
    (Amat : Matrix (Fin n) (Fin n) ℂ) (Dmat : Matrix (Fin m) (Fin m) ℂ)
    (_hDdet : Dmat.det ≠ 0) :
    let B : Matrix (Fin n) (Fin m) ℂ := 0
    let C : Matrix (Fin m) (Fin n) ℂ := 0
    let schur := Amat - B * Dmat⁻¹ * C
    schur.det * (Dmat.det)⁻¹ = Amat.det * (Dmat.det)⁻¹ := by
  -- Schur complement = A - 0·D⁻¹·0 = A
  simp only [Matrix.zero_mul, Matrix.mul_zero, sub_zero]

/-!
## Berezinian Multiplicativity

The fundamental theorem: Ber(MN) = Ber(M) · Ber(N) for supermatrices.

This is the key result that distinguishes the Berezinian from the ordinary determinant.
For ordinary matrices, det(MN) = det(M)·det(N). For the Berezinian, the analogous
property holds ONLY because B, C are Grassmann-odd.

The proof uses LDU and UDL factorizations of supermatrices.
-/

/-!
### Upper Triangular SuperMatrix

A supermatrix U = [I B'; 0 I] where I is identity and B' is odd.
-/

/-- Upper triangular supermatrix U = [I B'; 0 I] -/
noncomputable def SuperMatrix.upperTriangular {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) A.carrier)
    (h1 : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even)
    (h0odd : (0 : A.carrier) ∈ A.odd) (hB' : ∀ i j, B' i j ∈ A.odd) :
    SuperMatrix A n m :=
  ⟨1, B', 0, 1,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even],
   hB',
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]⟩

/-- Lower triangular supermatrix L = [I 0; C' I] -/
noncomputable def SuperMatrix.lowerTriangular {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) A.carrier)
    (h1 : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even)
    (h0odd : (0 : A.carrier) ∈ A.odd) (hC' : ∀ i j, C' i j ∈ A.odd) :
    SuperMatrix A n m :=
  ⟨1, 0, C', 1,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even],
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   hC',
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]⟩

/-- Diagonal supermatrix Δ = [A' 0; 0 D'] -/
noncomputable def SuperMatrix.diagonal {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ}
    (A' : Matrix (Fin n) (Fin n) A.carrier) (D' : Matrix (Fin m) (Fin m) A.carrier)
    (h0odd : (0 : A.carrier) ∈ A.odd)
    (hA' : ∀ i j, A' i j ∈ A.even) (hD' : ∀ i j, D' i j ∈ A.even) :
    SuperMatrix A n m :=
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

/-- Upper triangular supermatrix has Ber = 1.

    U = [I B'; 0 I] has Schur complement A - B'·D⁻¹·C = I - B'·I⁻¹·0 = I
    So Ber(U) = det(I) · det(I)⁻¹ = 1

    The even part of a superalgebra is a commutative ring (in fact a field when the
    superalgebra is over ℂ). The determinant of matrices with even entries lies in
    the even part. Since the entries of the identity matrix are 0 and 1, which are
    both in the even part, det(I) = 1 (the multiplicative identity). -/
theorem SuperMatrix.ber_upperTriangular {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) A.carrier)
    (h1 : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even)
    (h0odd : (0 : A.carrier) ∈ A.odd) (hB' : ∀ i j, B' i j ∈ A.odd)
    (hD : ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock).det ≠ 0) :
    (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').ber hD = 1 := by
  unfold SuperMatrix.ber
  -- The upper triangular matrix has Ablock = 1, Cblock = 0, Dblock = 1
  have hAblock : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock = 1 := rfl
  have hCblock : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Cblock = 0 := rfl
  have hDblock : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock = 1 := rfl
  -- Simplify the Schur complement: Ablock - Bblock * Dblock⁻¹ * Cblock
  -- = 1 - Bblock * 1⁻¹ * 0 = 1 - 0 = 1
  have hSchur : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock -
      (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Bblock *
      (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock⁻¹ *
      (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Cblock = 1 := by
    rw [hCblock]
    -- Goal: Ablock - Bblock * Dblock⁻¹ * 0 = 1
    have h_mul_zero : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Bblock *
        (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock⁻¹ *
        (0 : Matrix (Fin m) (Fin n) A.carrier) = 0 := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]
    rw [h_mul_zero, hAblock]
    -- Goal: 1 - 0 = 1 (at matrix level)
    ext i j
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply, sub_zero]
  rw [hSchur, hDblock]
  -- Goal: det(1_{n×n}) * det(1_{m×m})⁻¹ = 1
  simp only [Matrix.det_one, inv_one, mul_one]

/-- Lower triangular supermatrix has Ber = 1.

    L = [I 0; C' I] has Schur complement A - B·D⁻¹·C = I - 0·I⁻¹·C' = I
    So Ber(L) = det(I) · det(I)⁻¹ = 1 -/
theorem SuperMatrix.ber_lowerTriangular {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) A.carrier)
    (h1 : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even)
    (h0odd : (0 : A.carrier) ∈ A.odd) (hC' : ∀ i j, C' i j ∈ A.odd)
    (hD : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock).det ≠ 0) :
    (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').ber hD = 1 := by
  unfold SuperMatrix.ber SuperMatrix.lowerTriangular
  -- Bblock = 0, so 0 * D⁻¹ * C' = 0, so Schur = Ablock - 0 = Ablock = 1
  have hBblock_zero : (0 : Matrix (Fin n) (Fin m) A.carrier) *
      (1 : Matrix (Fin m) (Fin m) A.carrier)⁻¹ * C' = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply, zero_mul, Finset.sum_const_zero]
  -- Schur complement = 1 - 0 = 1
  have hSchur : (1 : Matrix (Fin n) (Fin n) A.carrier) -
      (0 : Matrix (Fin n) (Fin m) A.carrier) *
      (1 : Matrix (Fin m) (Fin m) A.carrier)⁻¹ * C' = 1 := by
    rw [hBblock_zero]
    ext i j
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply, sub_zero]
  rw [hSchur]
  -- Goal: det(1) * det(1)⁻¹ = 1
  simp only [Matrix.det_one, inv_one, mul_one]

/-- berAlt(L · N) = berAlt(N) when L = [I 0; C' I] is lower triangular and N.A is invertible.

    **Proof**:
    (L·N).A = I·N.A + 0·N.C = N.A
    (L·N).B = I·N.B + 0·N.D = N.B
    (L·N).C = C'·N.A + I·N.C = C'·N.A + N.C
    (L·N).D = C'·N.B + I·N.D = C'·N.B + N.D

    A-based Schur complement S_A(L·N) = (L·N).D - (L·N).C · (L·N).A⁻¹ · (L·N).B
    = (C'·N.B + N.D) - (C'·N.A + N.C) · N.A⁻¹ · N.B
    = C'·N.B + N.D - C'·N.A·N.A⁻¹·N.B - N.C·N.A⁻¹·N.B
    = C'·N.B + N.D - C'·N.B - N.C·N.A⁻¹·N.B
    = N.D - N.C·N.A⁻¹·N.B = S_A(N)

    Therefore berAlt(L·N) = det(N.A) · det(S_A(N))⁻¹ = berAlt(N) -/
theorem SuperMatrix.berAlt_mul_lowerTriangular_left {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    [SuperCommutative A.toSuperAlgebra] {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) A.carrier)
    (N : SuperMatrix A n m)
    (h1 : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even)
    (h0odd : (0 : A.carrier) ∈ A.odd) (hC' : ∀ i j, C' i j ∈ A.odd)
    (hNA : N.Ablock.det ≠ 0)
    (hLNA : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') * N).Ablock.det ≠ 0) :
    ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') * N).berAlt hLNA =
    N.berAlt hNA := by
  unfold SuperMatrix.berAlt
  -- (L·N).A = N.A
  have hLNA_eq : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).Ablock = N.Ablock := by
    show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock * N.Ablock +
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock * N.Cblock = N.Ablock
    simp only [SuperMatrix.lowerTriangular, Matrix.one_mul, Matrix.zero_mul, add_zero]
  -- (L·N).B = N.B
  have hLNB_eq : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).Bblock = N.Bblock := by
    show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock * N.Bblock +
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock * N.Dblock = N.Bblock
    simp only [SuperMatrix.lowerTriangular, Matrix.one_mul, Matrix.zero_mul, add_zero]
  -- (L·N).C = C'·N.A + N.C
  have hLNC_eq : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).Cblock =
                 C' * N.Ablock + N.Cblock := by
    show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock * N.Ablock +
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock * N.Cblock =
         C' * N.Ablock + N.Cblock
    simp only [SuperMatrix.lowerTriangular, Matrix.one_mul]
  -- (L·N).D = C'·N.B + N.D
  have hLND_eq : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC' * N).Dblock =
                 C' * N.Bblock + N.Dblock := by
    show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock * N.Bblock +
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock * N.Dblock =
         C' * N.Bblock + N.Dblock
    simp only [SuperMatrix.lowerTriangular, Matrix.one_mul]
  rw [hLNA_eq, hLNB_eq, hLNC_eq, hLND_eq]
  -- Now show S_A(L·N) = S_A(N)
  -- S_A(L·N) = (C'·N.B + N.D) - (C'·N.A + N.C) · N.A⁻¹ · N.B
  haveI : Invertible N.Ablock.det := invertibleOfNonzero hNA
  haveI : Invertible N.Ablock := Matrix.invertibleOfDetInvertible N.Ablock
  have hSchur_eq : (C' * N.Bblock + N.Dblock) - (C' * N.Ablock + N.Cblock) * N.Ablock⁻¹ * N.Bblock =
                   N.Dblock - N.Cblock * N.Ablock⁻¹ * N.Bblock := by
    -- Expand: (C'·N.A + N.C) · N.A⁻¹ · N.B = C'·N.A·N.A⁻¹·N.B + N.C·N.A⁻¹·N.B
    --                                      = C'·N.B + N.C·N.A⁻¹·N.B
    have hAAinv : N.Ablock * N.Ablock⁻¹ = 1 := Matrix.mul_nonsing_inv N.Ablock (isUnit_of_invertible _)
    have h_distrib : (C' * N.Ablock + N.Cblock) * N.Ablock⁻¹ * N.Bblock =
                     C' * N.Bblock + N.Cblock * N.Ablock⁻¹ * N.Bblock := by
      -- (C' * N.A + N.C) * N.A⁻¹ * N.B
      -- = ((C' * N.A) * N.A⁻¹ + N.C * N.A⁻¹) * N.B
      -- = (C' * (N.A * N.A⁻¹) + N.C * N.A⁻¹) * N.B
      -- = (C' * I + N.C * N.A⁻¹) * N.B
      -- = (C' + N.C * N.A⁻¹) * N.B
      -- = C' * N.B + N.C * N.A⁻¹ * N.B
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

/-- Multiplying on the right by upper triangular U = [I B'; 0 I] preserves berAlt.

    For M · U where U = [I B'; 0 I]:
    - (M·U).A = M.A
    - (M·U).B = M.A·B' + M.B
    - (M·U).C = M.C
    - (M·U).D = M.C·B' + M.D

    S_A(M·U) = (M.C·B' + M.D) - M.C · M.A⁻¹ · (M.A·B' + M.B)
             = M.C·B' + M.D - M.C·B' - M.C·M.A⁻¹·M.B
             = M.D - M.C·M.A⁻¹·M.B = S_A(M)

    Therefore berAlt(M·U) = det(M.A) · det(S_A(M))⁻¹ = berAlt(M) -/
theorem SuperMatrix.berAlt_mul_upperTriangular_right {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    [SuperCommutative A.toSuperAlgebra] {n m : ℕ}
    (M : SuperMatrix A n m)
    (B' : Matrix (Fin n) (Fin m) A.carrier)
    (h1 : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even)
    (h0odd : (0 : A.carrier) ∈ A.odd) (hB' : ∀ i j, B' i j ∈ A.odd)
    (hMA : M.Ablock.det ≠ 0)
    (hMUA : (M * SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock.det ≠ 0) :
    (M * SuperMatrix.upperTriangular B' h1 h0even h0odd hB').berAlt hMUA =
    M.berAlt hMA := by
  unfold SuperMatrix.berAlt
  let U := SuperMatrix.upperTriangular B' h1 h0even h0odd hB'
  have hUA : U.Ablock = 1 := rfl
  have hUB : U.Bblock = B' := rfl
  have hUC : U.Cblock = 0 := rfl
  have hUD : U.Dblock = 1 := rfl
  -- (M·U).A = M.A·1 + M.B·0 = M.A
  have hMUA_eq : (M * U).Ablock = M.Ablock := by
    show M.Ablock * U.Ablock + M.Bblock * U.Cblock = M.Ablock
    rw [hUA, hUC]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero]
  -- (M·U).B = M.A·B' + M.B·1 = M.A·B' + M.B
  have hMUB_eq : (M * U).Bblock = M.Ablock * B' + M.Bblock := by
    show M.Ablock * U.Bblock + M.Bblock * U.Dblock = M.Ablock * B' + M.Bblock
    rw [hUB, hUD]
    simp only [Matrix.mul_one]
  -- (M·U).C = M.C·1 + M.D·0 = M.C
  have hMUC_eq : (M * U).Cblock = M.Cblock := by
    show M.Cblock * U.Ablock + M.Dblock * U.Cblock = M.Cblock
    rw [hUA, hUC]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero]
  -- (M·U).D = M.C·B' + M.D·1 = M.C·B' + M.D
  have hMUD_eq : (M * U).Dblock = M.Cblock * B' + M.Dblock := by
    show M.Cblock * U.Bblock + M.Dblock * U.Dblock = M.Cblock * B' + M.Dblock
    rw [hUB, hUD]
    simp only [Matrix.mul_one]
  rw [hMUA_eq, hMUB_eq, hMUC_eq, hMUD_eq]
  -- Now show S_A(M·U) = S_A(M)
  -- S_A(M·U) = (M.C·B' + M.D) - M.C · M.A⁻¹ · (M.A·B' + M.B)
  haveI : Invertible M.Ablock.det := invertibleOfNonzero hMA
  haveI : Invertible M.Ablock := Matrix.invertibleOfDetInvertible M.Ablock
  have hSchur_eq : (M.Cblock * B' + M.Dblock) - M.Cblock * M.Ablock⁻¹ * (M.Ablock * B' + M.Bblock) =
                   M.Dblock - M.Cblock * M.Ablock⁻¹ * M.Bblock := by
    -- M.C · M.A⁻¹ · (M.A·B' + M.B) = M.C·M.A⁻¹·M.A·B' + M.C·M.A⁻¹·M.B
    --                              = M.C·B' + M.C·M.A⁻¹·M.B
    have hAinvA : M.Ablock⁻¹ * M.Ablock = 1 := Matrix.nonsing_inv_mul M.Ablock (isUnit_of_invertible _)
    have h_distrib : M.Cblock * M.Ablock⁻¹ * (M.Ablock * B' + M.Bblock) =
                     M.Cblock * B' + M.Cblock * M.Ablock⁻¹ * M.Bblock := by
      -- M.C * M.A⁻¹ * (M.A * B' + M.B)
      -- = M.C * M.A⁻¹ * M.A * B' + M.C * M.A⁻¹ * M.B
      -- = M.C * (M.A⁻¹ * M.A) * B' + M.C * M.A⁻¹ * M.B
      -- = M.C * I * B' + M.C * M.A⁻¹ * M.B
      -- = M.C * B' + M.C * M.A⁻¹ * M.B
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

/-- Diagonal supermatrix has Ber = det(A') · det(D')⁻¹.

    Δ = [A' 0; 0 D'] has Schur complement A' - 0·D'⁻¹·0 = A'
    So Ber(Δ) = det(A') · det(D')⁻¹ -/
theorem SuperMatrix.ber_diagonal {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ}
    (A' : Matrix (Fin n) (Fin n) A.carrier) (D' : Matrix (Fin m) (Fin m) A.carrier)
    (h0odd : (0 : A.carrier) ∈ A.odd)
    (hA' : ∀ i j, A' i j ∈ A.even) (hD' : ∀ i j, D' i j ∈ A.even)
    (hD : ((SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock).det ≠ 0) :
    (SuperMatrix.diagonal A' D' h0odd hA' hD').ber hD = A'.det * D'.det⁻¹ := by
  unfold SuperMatrix.ber SuperMatrix.diagonal
  -- Bblock = 0, Cblock = 0, so Schur = Ablock - 0 * D'⁻¹ * 0 = A'
  have hBC_zero : (0 : Matrix (Fin n) (Fin m) A.carrier) * D'⁻¹ *
      (0 : Matrix (Fin m) (Fin n) A.carrier) = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]
  -- Schur complement = A' - 0 = A'
  have hSchur : A' - (0 : Matrix (Fin n) (Fin m) A.carrier) * D'⁻¹ *
      (0 : Matrix (Fin m) (Fin n) A.carrier) = A' := by
    rw [hBC_zero]
    ext i j
    simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero]
  rw [hSchur]

/-- Product of two upper triangular supermatrices is upper triangular.

    U₁ = [I B₁; 0 I], U₂ = [I B₂; 0 I]
    U₁·U₂ = [I·I + B₁·0, I·B₂ + B₁·I; 0·I + I·0, 0·B₂ + I·I]
          = [I, B₂ + B₁; 0, I]

    So the product has C-block = 0. -/
theorem SuperMatrix.upperTriangular_mul_Cblock_zero {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ}
    (U₁ U₂ : SuperMatrix A n m)
    (_hU₁A : U₁.Ablock = 1) (hU₁C : U₁.Cblock = 0) (hU₁D : U₁.Dblock = 1)
    (hU₂A : U₂.Ablock = 1) (hU₂C : U₂.Cblock = 0) (_hU₂D : U₂.Dblock = 1) :
    (U₁ * U₂).Cblock = 0 := by
  -- (U₁ * U₂).Cblock = U₁.Cblock * U₂.Ablock + U₁.Dblock * U₂.Cblock by definition of mul
  change (SuperMatrix.mul U₁ U₂).Cblock = 0
  unfold SuperMatrix.mul
  simp only [hU₁C, hU₁D, hU₂A, hU₂C]
  -- Goal: 0 * 1 + 1 * 0 = 0 (for matrices)
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]

/-- Product of diagonal and upper triangular has C-block = 0.

    Δ = [A' 0; 0 D'], U = [I B'; 0 I]
    Δ·U = [A'·I + 0·0, A'·B' + 0·I; 0·I + D'·0, 0·B' + D'·I]
        = [A', A'·B'; 0, D']

    So the product has C-block = 0. -/
theorem SuperMatrix.diagonal_mul_upper_Cblock_zero {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ}
    (Δ U : SuperMatrix A n m)
    (_hΔB : Δ.Bblock = 0) (hΔC : Δ.Cblock = 0)
    (hUA : U.Ablock = 1) (hUC : U.Cblock = 0) (_hUD : U.Dblock = 1) :
    (Δ * U).Cblock = 0 := by
  show Δ.Cblock * U.Ablock + Δ.Dblock * U.Cblock = 0
  rw [hΔC, hUA, hUC]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]

/-- Multiplying a C=0 supermatrix by diagonal on right preserves C=0.

    Y = [A B; 0 D], Δ' = [A'' 0; 0 D'']
    Y·Δ' = [A·A'' + B·0, A·0 + B·D''; 0·A'' + D·0, 0·0 + D·D'']
         = [A·A'', B·D''; 0, D·D'']

    So the product has C-block = 0. -/
theorem SuperMatrix.Cblock_zero_mul_diagonal_Cblock_zero {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ}
    (Y Δ' : SuperMatrix A n m)
    (hYC : Y.Cblock = 0)
    (_hΔ'B : Δ'.Bblock = 0) (hΔ'C : Δ'.Cblock = 0) :
    (Y * Δ').Cblock = 0 := by
  show Y.Cblock * Δ'.Ablock + Y.Dblock * Δ'.Cblock = 0
  rw [hYC, hΔ'C]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]

/-- When Y has C-block = 0, multiplying by lower triangular on right preserves D-block.

    Y = [A B; 0 D], L = [I 0; E I]
    (Y·L).D = Y.C·L.B + Y.D·L.D = 0·0 + D·I = D -/
theorem SuperMatrix.Cblock_zero_mul_lower_Dblock {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ}
    (Y L : SuperMatrix A n m)
    (hYC : Y.Cblock = 0)
    (_hLA : L.Ablock = 1) (hLB : L.Bblock = 0) (hLD : L.Dblock = 1) :
    (Y * L).Dblock = Y.Dblock := by
  show Y.Cblock * L.Bblock + Y.Dblock * L.Dblock = Y.Dblock
  rw [hYC, hLB, hLD]
  simp only [Matrix.zero_mul, Matrix.mul_one, zero_add]

/-- When Y has C-block = 0, Y·L has same Schur complement as Y.

    Y = [A B; 0 D], L = [I 0; E I]
    Y·L = [A + B·E, B; D·E, D]

    Schur(Y·L) = (A + B·E) - B·D⁻¹·(D·E) = A + B·E - B·E = A
    Schur(Y) = A - B·D⁻¹·0 = A

    So they have the same Schur complement. -/
theorem SuperMatrix.Cblock_zero_mul_lower_schur {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ}
    (Y L : SuperMatrix A n m)
    (hYC : Y.Cblock = 0)
    (hLA : L.Ablock = 1) (hLB : L.Bblock = 0) (hLD : L.Dblock = 1)
    (hD : Y.Dblock.det ≠ 0) :
    schurComplementD (Y * L) (by rw [SuperMatrix.Cblock_zero_mul_lower_Dblock Y L hYC hLA hLB hLD]; exact hD) =
    schurComplementD Y hD := by
  unfold schurComplementD
  -- (Y·L).A = Y.A·L.A + Y.B·L.C = Y.A + Y.B·L.C
  -- (Y·L).B = Y.A·L.B + Y.B·L.D = Y.B
  -- (Y·L).C = Y.C·L.A + Y.D·L.C = D·L.C (since Y.C = 0)
  -- (Y·L).D = D (proved above)
  -- Schur(Y·L) = (Y.A + Y.B·L.C) - Y.B · D⁻¹ · (D·L.C)
  --            = Y.A + Y.B·L.C - Y.B·L.C = Y.A
  -- Schur(Y) = Y.A - Y.B·D⁻¹·0 = Y.A
  have hYLA : (Y * L).Ablock = Y.Ablock * L.Ablock + Y.Bblock * L.Cblock := rfl
  have hYLB : (Y * L).Bblock = Y.Ablock * L.Bblock + Y.Bblock * L.Dblock := rfl
  have hYLC : (Y * L).Cblock = Y.Cblock * L.Ablock + Y.Dblock * L.Cblock := rfl
  have hYLD : (Y * L).Dblock = Y.Dblock := SuperMatrix.Cblock_zero_mul_lower_Dblock Y L hYC hLA hLB hLD
  -- Simplify using the triangular structure
  simp only [hLA, hLB, hLD, Matrix.mul_one, Matrix.mul_zero, zero_add] at hYLA hYLB hYLC
  simp only [hYC, zero_add] at hYLC
  -- Now: (Y·L).A = Y.A + Y.B·L.C, (Y·L).B = Y.B, (Y·L).C = Y.D·L.C, (Y·L).D = Y.D
  -- Schur(Y·L) = (Y.A + Y.B·L.C) - Y.B · Y.D⁻¹ · (Y.D·L.C)
  simp only [hYLA, hYLB, hYLC, hYLD]
  -- Schur(Y·L) = (Y.A + Y.B·L.C) - Y.B · Y.D⁻¹ · (Y.D·L.C)
  --            = Y.A + Y.B·L.C - Y.B·(Y.D⁻¹·Y.D)·L.C
  --            = Y.A + Y.B·L.C - Y.B·L.C = Y.A
  -- Schur(Y) = Y.A - Y.B·Y.D⁻¹·0 = Y.A
  simp only [Matrix.mul_assoc]
  haveI : Invertible Y.Dblock.det := invertibleOfNonzero hD
  haveI : Invertible Y.Dblock := Matrix.invertibleOfDetInvertible Y.Dblock
  rw [Matrix.inv_mul_cancel_left_of_invertible]
  simp only [hYC, Matrix.mul_zero, sub_zero, add_sub_cancel_right]

/-- Multiplying on the left by an upper triangular matrix U = [I B'; 0 I] preserves Ber.
    Since Ber(U) = 1, we have Ber(U * N) = Ber(N). -/
theorem SuperMatrix.ber_mul_upperTriangular_left {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    [SuperCommutative A.toSuperAlgebra] {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) A.carrier)
    (N : SuperMatrix A n m)
    (h1 : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even)
    (h0odd : (0 : A.carrier) ∈ A.odd) (hB' : ∀ i j, B' i j ∈ A.odd)
    (hND : N.Dblock.det ≠ 0)
    (hUD : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock.det ≠ 0)
    (hUND : ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB') * N).Dblock.det ≠ 0) :
    ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB') * N).ber hUND =
    N.ber hND := by
  -- U = [I B'; 0 I], U * N = [N.A + B'*N.C, N.B + B'*N.D; N.C, N.D]
  -- Ber(U) = 1, so Ber(U*N) should equal Ber(N)
  have hU := SuperMatrix.ber_upperTriangular B' h1 h0even h0odd hB' hUD
  -- The proof requires showing that the Schur complement of U*N equals
  -- the Schur complement of N (up to multiplication by det(I) = 1)
  -- (U*N).A - (U*N).B * (U*N).D⁻¹ * (U*N).C
  -- = (N.A + B'*N.C) - (N.B + B'*N.D) * N.D⁻¹ * N.C
  -- = N.A + B'*N.C - N.B*N.D⁻¹*N.C - B'*N.D*N.D⁻¹*N.C
  -- = N.A + B'*N.C - N.B*N.D⁻¹*N.C - B'*N.C
  -- = N.A - N.B*N.D⁻¹*N.C = Schur(N)
  unfold SuperMatrix.ber
  -- (U*N).D = 0*N.B + I*N.D = N.D
  have hUND_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).Dblock = N.Dblock := by
    show (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Cblock * N.Bblock +
         (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock * N.Dblock = N.Dblock
    simp only [SuperMatrix.upperTriangular]
    simp only [Matrix.zero_mul, Matrix.one_mul, zero_add]
  -- (U*N).C = 0*N.A + I*N.C = N.C
  have hUNC_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).Cblock = N.Cblock := by
    show (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Cblock * N.Ablock +
         (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock * N.Cblock = N.Cblock
    simp only [SuperMatrix.upperTriangular]
    simp only [Matrix.zero_mul, Matrix.one_mul, zero_add]
  -- (U*N).B = I*N.B + B'*N.D
  have hUNB_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).Bblock =
                 N.Bblock + B' * N.Dblock := by
    show (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock * N.Bblock +
         (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Bblock * N.Dblock =
         N.Bblock + B' * N.Dblock
    simp only [SuperMatrix.upperTriangular]
    simp only [Matrix.one_mul]
  -- (U*N).A = I*N.A + B'*N.C
  have hUNA_eq : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB' * N).Ablock =
                 N.Ablock + B' * N.Cblock := by
    show (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Ablock * N.Ablock +
         (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Bblock * N.Cblock =
         N.Ablock + B' * N.Cblock
    simp only [SuperMatrix.upperTriangular]
    simp only [Matrix.one_mul]
  -- Now compute the Schur complement
  rw [hUND_eq, hUNC_eq, hUNB_eq, hUNA_eq]
  -- Goal: det((N.A + B'*N.C) - (N.B + B'*N.D) * N.D⁻¹ * N.C) * det(N.D)⁻¹
  --     = det(N.A - N.B * N.D⁻¹ * N.C) * det(N.D)⁻¹
  -- Need to show the Schur complements are equal
  congr 1
  -- (N.A + B'*N.C) - (N.B + B'*N.D) * N.D⁻¹ * N.C
  -- = N.A + B'*N.C - N.B*N.D⁻¹*N.C - B'*N.D*N.D⁻¹*N.C
  -- = N.A + B'*N.C - N.B*N.D⁻¹*N.C - B'*N.C  (using D*D⁻¹ = I)
  -- = N.A - N.B*N.D⁻¹*N.C
  haveI : Invertible N.Dblock.det := invertibleOfNonzero hND
  haveI : Invertible N.Dblock := Matrix.invertibleOfDetInvertible N.Dblock
  have h_DinvD : N.Dblock * N.Dblock⁻¹ = 1 := Matrix.mul_nonsing_inv N.Dblock (isUnit_of_invertible _)
  have h_cancel : B' * N.Dblock * N.Dblock⁻¹ * N.Cblock = B' * N.Cblock := by
    rw [Matrix.mul_assoc B' N.Dblock, h_DinvD, Matrix.mul_one]
  -- Use matrix algebra to show the Schur complements are equal
  have h_distrib : (N.Bblock + B' * N.Dblock) * N.Dblock⁻¹ * N.Cblock =
                   N.Bblock * N.Dblock⁻¹ * N.Cblock + B' * N.Cblock := by
    rw [Matrix.add_mul, Matrix.add_mul, h_cancel]
  -- Goal: det((N.A + B'*N.C) - (N.B*N.D⁻¹*N.C + B'*N.C)) = det(N.A - N.B*N.D⁻¹*N.C)
  rw [h_distrib]
  -- Now it's pure matrix arithmetic: (A + X) - (Y + X) = A - Y
  -- We need to show matrix equality, then determinants are equal
  have heq : N.Ablock + B' * N.Cblock - (N.Bblock * N.Dblock⁻¹ * N.Cblock + B' * N.Cblock) =
             N.Ablock - N.Bblock * N.Dblock⁻¹ * N.Cblock := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply]
    ring
  rw [heq]

-- NOTE: ber_eq_A_formula was redundant - it's the same as ber_eq_berAlt
-- since berAlt is defined as det(A) * det(D - CA⁻¹B)⁻¹.
-- Use ber_eq_berAlt instead.

/-- Multiplying on the right by a lower triangular matrix L = [I 0; C' I] preserves Ber.
    Since Ber(L) = 1, we have Ber(M * L) = Ber(M). -/
theorem SuperMatrix.ber_mul_lowerTriangular_right {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    [SuperCommutative A.toSuperAlgebra] {n m : ℕ}
    (M : SuperMatrix A n m)
    (C' : Matrix (Fin m) (Fin n) A.carrier)
    (h1 : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even)
    (h0odd : (0 : A.carrier) ∈ A.odd) (hC' : ∀ i j, C' i j ∈ A.odd)
    (hMD : M.Dblock.det ≠ 0)
    (_hLD : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock.det ≠ 0)
    (hMLD : (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock.det ≠ 0) :
    (M * SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').ber hMLD =
    M.ber hMD := by
  -- M * L = [M.A + M.B*C', M.B; M.C + M.D*C', M.D]
  -- (M*L).D = M.C*0 + M.D*I = M.D
  -- (M*L).C = M.C*I + M.D*C' = M.C + M.D*C'
  -- (M*L).B = M.A*0 + M.B*I = M.B
  -- (M*L).A = M.A*I + M.B*C' = M.A + M.B*C'
  -- Schur(M*L) = (M.A + M.B*C') - M.B * M.D⁻¹ * (M.C + M.D*C')
  --            = M.A + M.B*C' - M.B*M.D⁻¹*M.C - M.B*M.D⁻¹*M.D*C'
  --            = M.A + M.B*C' - M.B*M.D⁻¹*M.C - M.B*C'
  --            = M.A - M.B*M.D⁻¹*M.C = Schur(M)
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
  -- Need: (M.A + M.B*C') - M.B * M.D⁻¹ * (M.C + M.D*C') = M.A - M.B * M.D⁻¹ * M.C
  haveI : Invertible M.Dblock.det := invertibleOfNonzero hMD
  haveI : Invertible M.Dblock := Matrix.invertibleOfDetInvertible M.Dblock
  have h_DinvD : M.Dblock⁻¹ * M.Dblock = 1 := Matrix.nonsing_inv_mul M.Dblock (isUnit_of_invertible _)
  have h_distrib : M.Bblock * M.Dblock⁻¹ * (M.Cblock + M.Dblock * C') =
                   M.Bblock * M.Dblock⁻¹ * M.Cblock + M.Bblock * C' := by
    rw [Matrix.mul_add]
    congr 1
    -- Need: M.B * M.D⁻¹ * (M.D * C') = M.B * C'
    -- Reassociate: (M.B * M.D⁻¹) * (M.D * C') = M.B * ((M.D⁻¹ * M.D) * C') = M.B * C'
    calc M.Bblock * M.Dblock⁻¹ * (M.Dblock * C')
        = M.Bblock * (M.Dblock⁻¹ * (M.Dblock * C')) := by rw [Matrix.mul_assoc]
      _ = M.Bblock * ((M.Dblock⁻¹ * M.Dblock) * C') := by rw [Matrix.mul_assoc]
      _ = M.Bblock * ((1 : Matrix (Fin m) (Fin m) A.carrier) * C') := by rw [h_DinvD]
      _ = M.Bblock * C' := by rw [Matrix.one_mul]
  have heq : M.Ablock + M.Bblock * C' - M.Bblock * M.Dblock⁻¹ * (M.Cblock + M.Dblock * C') =
             M.Ablock - M.Bblock * M.Dblock⁻¹ * M.Cblock := by
    rw [h_distrib]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply]
    ring
  rw [heq]

/-- Ber(U · Δ · L) = Ber(Δ) when U is upper triangular, Δ is diagonal, L is lower triangular.

    **Proof**:
    1. Ber(Δ · L) = Ber(Δ) by direct computation (Δ.B = 0 makes Schur = A')
    2. Ber(U · (Δ · L)) = Ber(Δ · L) by ber_mul_upperTriangular_left
    3. Therefore Ber(U · Δ · L) = Ber(Δ) -/
theorem SuperMatrix.ber_UDL {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    [SuperCommutative A.toSuperAlgebra] {n m : ℕ}
    (B' : Matrix (Fin n) (Fin m) A.carrier)
    (A' : Matrix (Fin n) (Fin n) A.carrier) (D' : Matrix (Fin m) (Fin m) A.carrier)
    (C' : Matrix (Fin m) (Fin n) A.carrier)
    (h1 : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even)
    (h0odd : (0 : A.carrier) ∈ A.odd)
    (hB' : ∀ i j, B' i j ∈ A.odd)
    (hA' : ∀ i j, A' i j ∈ A.even) (hD' : ∀ i j, D' i j ∈ A.even)
    (hC' : ∀ i j, C' i j ∈ A.odd)
    (_hD'det : D'.det ≠ 0)
    (hUD : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock.det ≠ 0)
    (hΔD : (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock.det ≠ 0)
    (_hLD : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock.det ≠ 0)
    (hΔLD : ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
            (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC')).Dblock.det ≠ 0)
    (hUΔLD : ((SuperMatrix.upperTriangular B' h1 h0even h0odd hB') *
             ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
              (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC'))).Dblock.det ≠ 0) :
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
  -- Step 2: Schur complement of Δ·L
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
  -- Step 3: Ber(Δ · L) = det(A') / det(D') = Ber(Δ)
  have hBerΔL : ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
                (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC')).ber hΔLD =
               (SuperMatrix.diagonal A' D' h0odd hA' hD').ber hΔD := by
    unfold SuperMatrix.ber
    rw [hΔL_Schur, hΔL_D]
    -- RHS: (Δ.A - Δ.B * Δ.D⁻¹ * Δ.C).det * Δ.D.det⁻¹
    -- = (A' - 0 * D'⁻¹ * 0).det * D'.det⁻¹ = A'.det * D'.det⁻¹
    show A'.det * D'.det⁻¹ =
         ((SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock -
          (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock *
          (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock⁻¹ *
          (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock).det *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock.det⁻¹
    simp only [SuperMatrix.diagonal, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
  -- Step 4: Ber(U · (Δ · L)) = Ber(Δ · L) by ber_mul_upperTriangular_left
  have hBerUΔL := SuperMatrix.ber_mul_upperTriangular_left B'
    ((SuperMatrix.diagonal A' D' h0odd hA' hD') *
     (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC'))
    h1 h0even h0odd hB' hΔLD hUD hUΔLD
  -- Step 5: Combine
  rw [hBerUΔL, hBerΔL]

/-- Ber(L · Δ · U) = Ber(Δ) when L is lower triangular, Δ is diagonal, U is upper triangular,
    and A' is invertible.

    **Proof** (analogous to ber_UDL but using berAlt):
    1. (L · Δ).B = 0 since L.B = 0 and Δ.B = 0
    2. (L · Δ).A = A' is invertible, so we can use ber = berAlt
    3. Ber(L · Δ) = Ber(Δ) by direct computation (since (L·Δ).B = 0, Schur = A')
    4. berAlt((L · Δ) · U) = berAlt(L · Δ) by berAlt_mul_upperTriangular_right
    5. Therefore Ber(L · Δ · U) = Ber(Δ) -/
theorem SuperMatrix.ber_LDU {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    [SuperCommutative A.toSuperAlgebra] {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) A.carrier)
    (A' : Matrix (Fin n) (Fin n) A.carrier) (D' : Matrix (Fin m) (Fin m) A.carrier)
    (B' : Matrix (Fin n) (Fin m) A.carrier)
    (h1 : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even)
    (h0odd : (0 : A.carrier) ∈ A.odd)
    (hC' : ∀ i j, C' i j ∈ A.odd)
    (hA' : ∀ i j, A' i j ∈ A.even) (hD' : ∀ i j, D' i j ∈ A.even)
    (hB' : ∀ i j, B' i j ∈ A.odd)
    (hA'det : A'.det ≠ 0)  -- Key: A' must be invertible for LDU
    (_hD'det : D'.det ≠ 0)
    (_hLD : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock.det ≠ 0)
    (hΔD : (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock.det ≠ 0)
    (_hUD : (SuperMatrix.upperTriangular B' h1 h0even h0odd hB').Dblock.det ≠ 0)
    (hLΔD : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
            (SuperMatrix.diagonal A' D' h0odd hA' hD')).Dblock.det ≠ 0)
    (hLΔUD : (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
              (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
             (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Dblock.det ≠ 0)
    -- Parity conditions for ber = berAlt
    (hD'inv_C'A'_odd : ∀ i j, (D'⁻¹ * (C' * A')) i j ∈ A.odd)
    (_hA'inv_B'_odd : ∀ i j, (A'⁻¹ * B') i j ∈ A.odd)
    (hLΔU_DinvC_odd : ∀ i j, ((((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                               (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
                              (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Dblock⁻¹ *
                             (C' * A')) i j ∈ A.odd) :
    (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
      (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
     (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).ber hLΔUD =
    (SuperMatrix.diagonal A' D' h0odd hA' hD').ber hΔD := by
  -- Step 1: Compute (L · Δ).B = 0
  have hLΔB : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
              (SuperMatrix.diagonal A' D' h0odd hA' hD')).Bblock = 0 := by
    show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock +
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock = 0
    simp only [SuperMatrix.lowerTriangular, SuperMatrix.diagonal]
    simp only [Matrix.one_mul, Matrix.zero_mul, add_zero]
  -- Step 2: Compute (L · Δ).A = A'
  have hLΔA : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
              (SuperMatrix.diagonal A' D' h0odd hA' hD')).Ablock = A' := by
    show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock +
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock = A'
    simp only [SuperMatrix.lowerTriangular, SuperMatrix.diagonal]
    simp only [Matrix.one_mul, Matrix.zero_mul, add_zero]
  -- Step 3: Compute (L · Δ).D = D'
  have hLΔD_eq : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                 (SuperMatrix.diagonal A' D' h0odd hA' hD')).Dblock = D' := by
    show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock +
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock = D'
    simp only [SuperMatrix.lowerTriangular, SuperMatrix.diagonal]
    simp only [Matrix.mul_zero, Matrix.one_mul, zero_add]
  -- Step 4: (L·Δ).A = A' is invertible
  have hLΔA_det : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                  (SuperMatrix.diagonal A' D' h0odd hA' hD')).Ablock.det ≠ 0 := by
    rw [hLΔA]; exact hA'det
  -- Step 5: ((L·Δ)·U).A = (L·Δ).A = A' (upper triangular doesn't change A block)
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
  have hLΔUA_det : (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                    (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
                   (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Ablock.det ≠ 0 := by
    rw [hLΔUA]; exact hA'det
  -- Step 6: Ber(L · Δ) = Ber(Δ) since (L·Δ).B = 0 means Schur = (L·Δ).A = A'
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
  -- Step 7: Compute (L·Δ).C = C' * A'
  have hLΔC : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
              (SuperMatrix.diagonal A' D' h0odd hA' hD')).Cblock = C' * A' := by
    show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock +
         (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock *
         (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock = C' * A'
    simp only [SuperMatrix.lowerTriangular, SuperMatrix.diagonal]
    simp only [Matrix.one_mul, add_zero]
  -- Step 8: Show (L·Δ).A⁻¹ * (L·Δ).B is odd (it's 0)
  have hLΔ_AinvB : ∀ i j, (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                           (SuperMatrix.diagonal A' D' h0odd hA' hD')).Ablock⁻¹ *
                          ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                           (SuperMatrix.diagonal A' D' h0odd hA' hD')).Bblock) i j ∈ A.odd := by
    intro i j
    rw [hLΔB, Matrix.mul_zero]
    exact h0odd
  -- Step 9: Show (L·Δ).D⁻¹ * (L·Δ).C is odd (given as hypothesis)
  have hLΔ_DinvC : ∀ i j, (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                           (SuperMatrix.diagonal A' D' h0odd hA' hD')).Dblock⁻¹ *
                          ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                           (SuperMatrix.diagonal A' D' h0odd hA' hD')).Cblock) i j ∈ A.odd := by
    intro i j
    rw [hLΔD_eq, hLΔC]
    exact hD'inv_C'A'_odd i j
  -- Step 10: Compute ((L·Δ)·U).B = A' * B'
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
  -- Step 11: Compute ((L·Δ)·U).C = C' * A'
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
  -- Step 12: Show ((L·Δ)·U).A⁻¹ * ((L·Δ)·U).B is odd
  have hLΔU_AinvB : ∀ i j, ((((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                             (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
                            (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Ablock⁻¹ *
                           (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                             (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
                            (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Bblock) i j ∈ A.odd := by
    intro i j
    rw [hLΔUA, hLΔUB]
    -- A'⁻¹ * (A' * B') = (A'⁻¹ * A') * B' = I * B' = B' which is odd
    haveI : Invertible A'.det := invertibleOfNonzero hA'det
    haveI : Invertible A' := Matrix.invertibleOfDetInvertible A'
    have hAinvA : A'⁻¹ * A' = 1 := Matrix.nonsing_inv_mul A' (isUnit_of_invertible _)
    have heq : A'⁻¹ * (A' * B') = B' := by
      calc A'⁻¹ * (A' * B') = (A'⁻¹ * A') * B' := by rw [Matrix.mul_assoc]
        _ = (1 : Matrix _ _ _) * B' := by rw [hAinvA]
        _ = B' := by rw [Matrix.one_mul]
    rw [heq]
    exact hB' i j
  -- Step 13: Show ((L·Δ)·U).D⁻¹ * ((L·Δ)·U).C is odd (given as hypothesis)
  have hLΔU_DinvC : ∀ i j, ((((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                             (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
                            (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Dblock⁻¹ *
                           (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
                             (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
                            (SuperMatrix.upperTriangular B' h1 h0even h0odd hB')).Cblock) i j ∈ A.odd := by
    intro i j
    rw [hLΔUC]
    exact hLΔU_DinvC_odd i j
  -- Step 14: Use ber = berAlt for (L·Δ) and (L·Δ)·U
  have hBerAltLΔ := SuperMatrix.ber_eq_berAlt
    ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
     (SuperMatrix.diagonal A' D' h0odd hA' hD'))
    hLΔA_det hLΔD hLΔ_AinvB hLΔ_DinvC h1 h0even
  have hBerAltLΔU := SuperMatrix.ber_eq_berAlt
    (((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
      (SuperMatrix.diagonal A' D' h0odd hA' hD')) *
     (SuperMatrix.upperTriangular B' h1 h0even h0odd hB'))
    hLΔUA_det hLΔUD hLΔU_AinvB hLΔU_DinvC h1 h0even
  -- Step 15: berAlt((L · Δ) · U) = berAlt(L · Δ) by berAlt_mul_upperTriangular_right
  have hBerAltU := SuperMatrix.berAlt_mul_upperTriangular_right
    ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') *
     (SuperMatrix.diagonal A' D' h0odd hA' hD'))
    B' h1 h0even h0odd hB' hLΔA_det hLΔUA_det
  -- Step 16: Combine: Ber((L·Δ)·U) = berAlt((L·Δ)·U) = berAlt(L·Δ) = Ber(L·Δ) = Ber(Δ)
  rw [hBerAltLΔU, hBerAltU, ← hBerAltLΔ, hBerLΔ]

/-- LDU factorization equality: M = L · Δ · U where
    - L = [I 0; CA⁻¹ I]
    - Δ = [A 0; 0 S_A] where S_A = D - CA⁻¹B
    - U = [I A⁻¹B; 0 I]
    This requires A to be invertible. -/
theorem SuperMatrix.LDU_factorization {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ} (M : SuperMatrix A n m) (hA : M.Ablock.det ≠ 0)
    (h1 : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even)
    (h0odd : (0 : A.carrier) ∈ A.odd)
    (hCAinv : ∀ i j, (M.Cblock * M.Ablock⁻¹) i j ∈ A.odd)
    (hAinvB : ∀ i j, (M.Ablock⁻¹ * M.Bblock) i j ∈ A.odd)
    (hSchur : ∀ i j, (schurComplementA M hA) i j ∈ A.even) :
    M = ((SuperMatrix.lowerTriangular (M.Cblock * M.Ablock⁻¹) h1 h0even h0odd hCAinv) *
         (SuperMatrix.diagonal M.Ablock (schurComplementA M hA) h0odd M.Ablock_even hSchur)) *
        (SuperMatrix.upperTriangular (M.Ablock⁻¹ * M.Bblock) h1 h0even h0odd hAinvB) := by
  haveI : Invertible M.Ablock.det := invertibleOfNonzero hA
  haveI : Invertible M.Ablock := Matrix.invertibleOfDetInvertible M.Ablock
  have hAinvA : M.Ablock⁻¹ * M.Ablock = 1 := Matrix.nonsing_inv_mul M.Ablock (isUnit_of_invertible _)
  have hAAinv : M.Ablock * M.Ablock⁻¹ = 1 := Matrix.mul_nonsing_inv M.Ablock (isUnit_of_invertible _)
  -- Compute blocks of the RHS product
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
    -- Unfold everything and simplify directly
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
    -- Goal: M.Cblock * (M.Ablock⁻¹ * M.Bblock) + (M.Dblock - M.Cblock * M.Ablock⁻¹ * M.Bblock) = M.Dblock
    have hAssoc : M.Cblock * (M.Ablock⁻¹ * M.Bblock) = M.Cblock * M.Ablock⁻¹ * M.Bblock := by
      rw [Matrix.mul_assoc]
    rw [hAssoc]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply]
    ring
  ext <;> simp only [hA_eq, hB_eq, hC_eq, hD_eq]

/-- UDL factorization equality: M = U · Δ · L where
    - U = [I BD⁻¹; 0 I]
    - Δ = [S_D 0; 0 D] where S_D = A - BD⁻¹C
    - L = [I 0; D⁻¹C I]
    This requires D to be invertible. -/
theorem SuperMatrix.UDL_factorization {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    {n m : ℕ} (M : SuperMatrix A n m) (hD : M.Dblock.det ≠ 0)
    (h1 : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even)
    (h0odd : (0 : A.carrier) ∈ A.odd)
    (hBDinv : ∀ i j, (M.Bblock * M.Dblock⁻¹) i j ∈ A.odd)
    (hDinvC : ∀ i j, (M.Dblock⁻¹ * M.Cblock) i j ∈ A.odd)
    (hSchur : ∀ i j, (schurComplementD M hD) i j ∈ A.even) :
    M = ((SuperMatrix.upperTriangular (M.Bblock * M.Dblock⁻¹) h1 h0even h0odd hBDinv) *
         (SuperMatrix.diagonal (schurComplementD M hD) M.Dblock h0odd hSchur M.Dblock_even)) *
        (SuperMatrix.lowerTriangular (M.Dblock⁻¹ * M.Cblock) h1 h0even h0odd hDinvC) := by
  haveI : Invertible M.Dblock.det := invertibleOfNonzero hD
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
    -- Goal: (S_D + B D⁻¹ D (D⁻¹ C)) = A
    -- S_D = A - B D⁻¹ C, so S_D + B D⁻¹ C = A
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

/-- Berezinian multiplicativity when M.A is invertible (using LDU for M, UDL for N).

    **Strategy**:
    - M = L · Δ · U (LDU factorization, A-based)
    - N = U' · Δ' · L' (UDL factorization, D-based)

    Ber(MN) = Ber(L · Δ · U · U' · Δ' · L')
            = Ber(L · Δ · U'' · Δ' · L')  where U'' = U · U'
            = Ber(L · Δ · U'' · Δ')       (strip L' from right)
            = Ber(L · Δ · U'') · Ber(Δ')  (strip Δ' from right)
            = Ber(Δ) · Ber(Δ')            (by ber_LDU: Ber(L·Δ·U'') = Ber(Δ))
            = Ber(M) · Ber(N)             (since Ber(M) = Ber(Δ) and Ber(N) = Ber(Δ')) -/
theorem SuperMatrix.ber_mul_A_invertible {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    [SuperCommutative A.toSuperAlgebra] {n m : ℕ}
    (M N : SuperMatrix A n m)
    (hMA : M.Ablock.det ≠ 0)
    (hMD : M.Dblock.det ≠ 0)
    (hND : N.Dblock.det ≠ 0)
    (hMND : (M * N).Dblock.det ≠ 0)
    (h1 : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even)
    (h0odd : (0 : A.carrier) ∈ A.odd)
    (hBDinvN : ∀ i j, (N.Bblock * N.Dblock⁻¹) i j ∈ A.odd)
    (hDinvCN : ∀ i j, (N.Dblock⁻¹ * N.Cblock) i j ∈ A.odd)
    (hCAinvM : ∀ i j, (M.Cblock * M.Ablock⁻¹) i j ∈ A.odd)
    (hAinvBM : ∀ i j, (M.Ablock⁻¹ * M.Bblock) i j ∈ A.odd)
    (hDinvCM : ∀ i j, (M.Dblock⁻¹ * M.Cblock) i j ∈ A.odd)
    (hSchurM : ∀ i j, (schurComplementA M hMA) i j ∈ A.even)
    (hSchurN : ∀ i j, (schurComplementD N hND) i j ∈ A.even)
    (hSchurM_det : (schurComplementA M hMA).det ≠ 0) :
    (M * N).ber hMND = M.ber hMD * N.ber hND := by
  -- M = L · Δ · U, N = U' · Δ' · L'
  -- Ber(MN) = Ber(L·Δ·U·U'·Δ'·L') = Ber(L·Δ·U''·Δ') = Ber(L·Δ·U'')·Ber(Δ') = Ber(M)·Ber(N)
  haveI : Invertible M.Ablock.det := invertibleOfNonzero hMA
  haveI hInvMA : Invertible M.Ablock := Matrix.invertibleOfDetInvertible M.Ablock
  haveI : Invertible M.Dblock.det := invertibleOfNonzero hMD
  haveI hInvMD : Invertible M.Dblock := Matrix.invertibleOfDetInvertible M.Dblock
  haveI : Invertible N.Dblock.det := invertibleOfNonzero hND
  haveI hInvND : Invertible N.Dblock := Matrix.invertibleOfDetInvertible N.Dblock
  -- Define the factorization components
  -- For M (LDU): L = [I 0; CA⁻¹ I], Δ = [A 0; 0 S_A], U = [I A⁻¹B; 0 I]
  let C_M := M.Cblock * M.Ablock⁻¹  -- C' for L
  let A_M := M.Ablock               -- A' for Δ
  let D_M := schurComplementA M hMA -- D' = S_A for Δ
  let B_M := M.Ablock⁻¹ * M.Bblock  -- B' for U
  -- For N (UDL): U' = [I BD⁻¹; 0 I], Δ' = [S_D 0; 0 D], L' = [I 0; D⁻¹C I]
  let B_N := N.Bblock * N.Dblock⁻¹  -- B' for U'
  let A_N := schurComplementD N hND -- A' = S_D for Δ'
  let D_N := N.Dblock               -- D' for Δ'
  let C_N := N.Dblock⁻¹ * N.Cblock  -- C' for L'
  -- The proof follows the strategy in the docstring
  -- Key insight: M*N = (L·Δ·U)·(U'·Δ'·L') = L·Δ·(U·U')·Δ'·L'
  -- U·U' is still upper triangular with B'' = A⁻¹B + BD⁻¹

  -- Step 1: Define the factorization matrices
  let L := SuperMatrix.lowerTriangular C_M h1 h0even h0odd hCAinvM
  let Δ := SuperMatrix.diagonal A_M D_M h0odd M.Ablock_even hSchurM
  let U := SuperMatrix.upperTriangular B_M h1 h0even h0odd hAinvBM

  let U' := SuperMatrix.upperTriangular B_N h1 h0even h0odd hBDinvN
  let Δ' := SuperMatrix.diagonal A_N D_N h0odd hSchurN N.Dblock_even
  let L' := SuperMatrix.lowerTriangular C_N h1 h0even h0odd hDinvCN

  -- Step 2: M = L · Δ · U by LDU_factorization
  have hM_eq : M = (L * Δ) * U := SuperMatrix.LDU_factorization M hMA h1 h0even h0odd
    hCAinvM hAinvBM hSchurM

  -- Step 3: N = U' · Δ' · L' by UDL_factorization
  have hN_eq : N = (U' * Δ') * L' := SuperMatrix.UDL_factorization N hND h1 h0even h0odd
    hBDinvN hDinvCN hSchurN

  -- Determinant facts for the factorization components
  have hLD : L.Dblock.det ≠ 0 := by
    show (1 : Matrix (Fin m) (Fin m) A.carrier).det ≠ 0
    rw [Matrix.det_one]; exact one_ne_zero
  have hΔD : Δ.Dblock.det ≠ 0 := hSchurM_det
  have hUD : U.Dblock.det ≠ 0 := by
    show (1 : Matrix (Fin m) (Fin m) A.carrier).det ≠ 0
    rw [Matrix.det_one]; exact one_ne_zero
  have hU'D : U'.Dblock.det ≠ 0 := by
    show (1 : Matrix (Fin m) (Fin m) A.carrier).det ≠ 0
    rw [Matrix.det_one]; exact one_ne_zero
  have hΔ'D : Δ'.Dblock.det ≠ 0 := hND
  have hL'D : L'.Dblock.det ≠ 0 := by
    show (1 : Matrix (Fin m) (Fin m) A.carrier).det ≠ 0
    rw [Matrix.det_one]; exact one_ne_zero

  -- Key: MN = (L * Δ * U) * (U' * Δ' * L') by the factorization equations
  have hMN_eq : M * N = ((L * Δ) * U) * ((U' * Δ') * L') := by
    rw [hM_eq, hN_eq]

  -- Step 1: Strip L' from right
  -- First rewrite MN = (L * Δ * U * U' * Δ') * L'
  have hMN_assoc : M * N = (L * Δ * U * (U' * Δ')) * L' := by
    rw [hMN_eq]
    simp only [mul_assoc]

  -- Apply ber_mul_lowerTriangular_right to strip L'
  -- Need: det of (L*Δ*U*U'*Δ').D ≠ 0
  -- This follows from the product structure: the D-block of a product of supermatrices
  -- with invertible D-blocks also has invertible D-block
  -- Key: (X * L').Dblock = X.Dblock since L'.B = 0, L'.D = I
  have hXL'_D_eq' : (L * Δ * U * (U' * Δ') * L').Dblock = (L * Δ * U * (U' * Δ')).Dblock := by
    show (L * Δ * U * (U' * Δ')).Cblock * L'.Bblock + (L * Δ * U * (U' * Δ')).Dblock * L'.Dblock =
         (L * Δ * U * (U' * Δ')).Dblock
    have hL'B : L'.Bblock = 0 := rfl
    have hL'D : L'.Dblock = 1 := rfl
    simp only [hL'B, hL'D, Matrix.mul_zero, zero_add, Matrix.mul_one]
  have hXD : (L * Δ * U * (U' * Δ')).Dblock.det ≠ 0 := by
    rw [← hXL'_D_eq']
    have h : (L * Δ * U * (U' * Δ') * L').Dblock = (M * N).Dblock := by rw [← hMN_assoc]
    rw [h]; exact hMND
  have hXL'D : (L * Δ * U * (U' * Δ') * L').Dblock.det ≠ 0 := by
    have h : (L * Δ * U * (U' * Δ') * L').Dblock = (M * N).Dblock := by
      rw [← hMN_assoc]
    rw [h]; exact hMND

  -- Ber(MN) = Ber((L*Δ*U*U'*Δ') * L') = Ber(L*Δ*U*U'*Δ')
  -- This uses ber_mul_lowerTriangular_right: Ber(X * L') = Ber(X) for lower triangular L'
  have hStrip1 : (M * N).ber hMND = (L * Δ * U * (U' * Δ')).ber hXD := by
    -- Apply ber_mul_lowerTriangular_right to X = L*Δ*U*(U'*Δ') and L' = lowerTriangular C_N
    -- where C_N = N.D⁻¹ * N.C
    -- First show: (X * L').Dblock = X.Dblock (key property of lower triangular multiplication)
    have hXL'_D_eq : (L * Δ * U * (U' * Δ') * L').Dblock = (L * Δ * U * (U' * Δ')).Dblock := by
      show (L * Δ * U * (U' * Δ')).Cblock * L'.Bblock + (L * Δ * U * (U' * Δ')).Dblock * L'.Dblock =
           (L * Δ * U * (U' * Δ')).Dblock
      have hL'B : L'.Bblock = 0 := rfl
      have hL'D : L'.Dblock = 1 := rfl
      simp only [hL'B, hL'D, Matrix.mul_zero, zero_add, Matrix.mul_one]
    -- The ber only depends on the blocks, and (M*N).Dblock = (X*L').Dblock by hMN_assoc
    have hMN_blocks : M * N = (L * Δ * U * (U' * Δ')) * L' := hMN_assoc
    -- Use ber_mul_lowerTriangular_right
    have hStrip := SuperMatrix.ber_mul_lowerTriangular_right (L * Δ * U * (U' * Δ')) C_N
      h1 h0even h0odd hDinvCN hXD hL'D
    -- The result says: ((L*Δ*U*(U'*Δ')) * L').ber _ = (L*Δ*U*(U'*Δ')).ber hXD
    -- We need: (M*N).ber hMND = (L*Δ*U*(U'*Δ')).ber hXD
    -- Since (M*N) = (L*Δ*U*(U'*Δ')) * L', and the Dblocks are equal
    have hDet_eq : (M * N).Dblock.det = ((L * Δ * U * (U' * Δ')) * L').Dblock.det := by
      rw [hMN_blocks]
    -- Need to show (L*Δ*U*(U'*Δ') * L').Dblock.det ≠ 0 for the lemma application
    have hXL'D_ne : ((L * Δ * U * (U' * Δ')) * L').Dblock.det ≠ 0 := by
      rw [hXL'_D_eq]; exact hXD
    -- Apply the lemma
    have hStrip' := SuperMatrix.ber_mul_lowerTriangular_right (L * Δ * U * (U' * Δ')) C_N
      h1 h0even h0odd hDinvCN hXD hL'D hXL'D_ne
    -- Now we need to transport from ((L*Δ*U*(U'*Δ')) * L').ber to (M*N).ber
    -- Since ber only depends on blocks and M*N = (L*Δ*U*(U'*Δ')) * L', this is definitional
    unfold SuperMatrix.ber at hStrip' ⊢
    rw [hMN_blocks]
    exact hStrip'

  -- Step 2: Strip Δ' from right using ber_mul_diagonal_right
  -- Ber(L*Δ*U*U'*Δ') = Ber(L*Δ*U*U') * Ber(Δ')
  -- This uses ber_mul_diagonal_right: Ber(Z * Δ') = Ber(Z) * Ber(Δ')
  -- Key: (Z * Δ').D = Z.D * Δ'.D since Δ'.B = 0, Δ'.C = 0
  have hZΔ'_D_eq : (L * Δ * U * (U' * Δ')).Dblock = (L * Δ * U * U').Dblock * Δ'.Dblock := by
    -- (L*Δ*U*U') * Δ'
    have hXΔ' : L * Δ * U * (U' * Δ') = (L * Δ * U * U') * Δ' := by simp only [mul_assoc]
    rw [hXΔ']
    show (L * Δ * U * U').Cblock * Δ'.Bblock + (L * Δ * U * U').Dblock * Δ'.Dblock =
         (L * Δ * U * U').Dblock * Δ'.Dblock
    have hΔ'B : Δ'.Bblock = 0 := rfl
    simp only [hΔ'B, Matrix.mul_zero, zero_add]
  have hYD : (L * Δ * U * U').Dblock.det ≠ 0 := by
    -- det((L*Δ*U*(U'*Δ')).D) = det((L*Δ*U*U').D * Δ'.D) = det((L*Δ*U*U').D) * det(Δ'.D)
    -- Since LHS ≠ 0 (hXD) and det(Δ'.D) = det(N.D) ≠ 0 (hND), det((L*Δ*U*U').D) ≠ 0
    have hΔ'D_eq : Δ'.Dblock = N.Dblock := rfl
    rw [hZΔ'_D_eq, Matrix.det_mul] at hXD
    have hΔ'D_det : Δ'.Dblock.det ≠ 0 := by rw [hΔ'D_eq]; exact hND
    exact left_ne_zero_of_mul hXD
  have hStrip2 : (L * Δ * U * (U' * Δ')).ber hXD =
                 (L * Δ * U * U').ber hYD * Δ'.ber hΔ'D := by
    -- Prove directly: Ber(Z * Δ') = Ber(Z) * Ber(Δ') for diagonal Δ'
    -- Let Z = L * Δ * U * U'
    let Z := L * Δ * U * U'
    have hXΔ' : L * Δ * U * (U' * Δ') = Z * Δ' := by
      show L * Δ * U * (U' * Δ') = (L * Δ * U * U') * Δ'
      simp only [mul_assoc]
    -- Δ' = diagonal A_N D_N where A_N = schurComplementD N, D_N = N.Dblock
    -- (Z * Δ').A = Z.A * A_N, (Z * Δ').B = Z.B * D_N
    -- (Z * Δ').C = Z.C * A_N, (Z * Δ').D = Z.D * D_N
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
    haveI : Invertible D_N.det := invertibleOfNonzero hND
    haveI hInvDN : Invertible D_N := Matrix.invertibleOfDetInvertible D_N
    haveI : Invertible Z.Dblock.det := invertibleOfNonzero hYD
    haveI hInvZD : Invertible Z.Dblock := Matrix.invertibleOfDetInvertible Z.Dblock
    -- Compute Schur complement: (Z*Δ').A - (Z*Δ').B * (Z*Δ').D⁻¹ * (Z*Δ').C
    -- = Z.A*A_N - Z.B*D_N * (Z.D*D_N)⁻¹ * Z.C*A_N
    -- = Z.A*A_N - Z.B*D_N * D_N⁻¹*Z.D⁻¹ * Z.C*A_N
    -- = Z.A*A_N - Z.B * Z.D⁻¹ * Z.C * A_N
    -- = (Z.A - Z.B*Z.D⁻¹*Z.C) * A_N = Schur(Z) * A_N
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
    -- Now compute the Berezinians
    unfold SuperMatrix.ber
    rw [hXΔ', hZΔ'A, hZΔ'B, hZΔ'C, hZΔ'D_eq, hSchur_eq]
    -- det((Z.A - Z.B*Z.D⁻¹*Z.C) * A_N) = det(Schur(Z)) * det(A_N)
    have hdet_schur : ((Z.Ablock - Z.Bblock * Z.Dblock⁻¹ * Z.Cblock) * A_N).det =
                      (Z.Ablock - Z.Bblock * Z.Dblock⁻¹ * Z.Cblock).det * A_N.det := Matrix.det_mul _ _
    -- det(Z.D * D_N) = det(Z.D) * det(D_N)
    have hdet_D : (Z.Dblock * D_N).det = Z.Dblock.det * D_N.det := Matrix.det_mul _ _
    rw [hdet_schur, hdet_D, mul_inv]
    -- Δ'.ber: Δ' = diagonal A_N D_N, so Δ'.ber = det(A_N) * det(D_N)⁻¹
    have hΔ'A : Δ'.Ablock = A_N := rfl
    have hΔ'B : Δ'.Bblock = 0 := rfl
    have hΔ'C : Δ'.Cblock = 0 := rfl
    have hΔ'D_eq' : Δ'.Dblock = D_N := rfl
    simp only [hΔ'A, hΔ'B, hΔ'C, hΔ'D_eq', Matrix.zero_mul, Matrix.mul_zero, sub_zero]
    ring

  -- Step 3: U * U' is upper triangular, so L * Δ * (U*U') has LDU form
  -- Apply ber_LDU: Ber(L * Δ * U'') = Ber(Δ)
  -- Key: product of upper triangular matrices is upper triangular
  -- U * U' = [I, B_M + B_N; 0, I] (upper triangular with B'' = B_M + B_N roughly)
  have hStrip3 : (L * Δ * U * U').ber hYD = Δ.ber hΔD := by
    -- Key insight: (L * Δ * U).ber = Δ.ber (since M = L*Δ*U and M.ber = Δ.ber)
    -- And we've shown M.ber hMD = Δ.ber hΔD in hBerM
    -- But (L*Δ*U*U').D ≠ M.D in general, so we need to compute directly
    --
    -- Strategy: Compute (L*Δ*U*U').ber directly and show it equals Δ.ber
    -- Let W = L * Δ * U * U'
    -- W.ber = det(W.A - W.B * W.D⁻¹ * W.C) * det(W.D)⁻¹
    --
    -- Key facts about the product structure:
    -- 1. (L * Δ).B = 0 (L.A * Δ.B + L.B * Δ.D = I * 0 + 0 * D_M = 0)
    -- 2. (L * Δ).A = M.A (= A_M)
    -- 3. (L * Δ).D = D_M (= S_A)
    -- 4. U.D = I, U'.D = I, so (U * U').D = U.C * U'.B + U.D * U'.D = 0 * B_N + I * I = I
    -- 5. Therefore ((L*Δ) * (U*U')).D = (L*Δ).C * (U*U').B + (L*Δ).D * I
    --    = (L*Δ).C * (U*U').B + D_M
    -- 6. But (L*Δ).B = 0, so the Schur complement simplifies
    --
    -- Actually, a simpler approach: use the fact that
    -- (L*Δ*U*U').ber = (L*Δ).ber * (U*U').ber / [correction factor]
    -- but this is getting complicated.
    --
    -- Direct computation: Let's trace through the blocks
    -- First compute (L * Δ).blocks
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
    -- Compute (U * U').blocks
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
    -- Now compute (L * Δ * U * U') = ((L * Δ) * (U * U'))
    let LΔ := L * Δ
    let UU' := U * U'
    have hW_eq : L * Δ * U * U' = LΔ * UU' := by
      -- L * Δ * U * U' = ((L * Δ) * U) * U' = (L * Δ) * (U * U') = LΔ * UU'
      calc L * Δ * U * U' = (L * Δ * U) * U' := rfl
        _ = (L * Δ) * U * U' := by rfl
        _ = (L * Δ) * (U * U') := by rw [mul_assoc]
        _ = LΔ * UU' := rfl
    -- (LΔ * UU').A = LΔ.A * UU'.A + LΔ.B * UU'.C = M.A * I + 0 * 0 = M.A
    have hW_A : (LΔ * UU').Ablock = M.Ablock := by
      show LΔ.Ablock * UU'.Ablock + LΔ.Bblock * UU'.Cblock = M.Ablock
      rw [hLΔ_A, hLΔ_B, hUU'_A, hUU'_C]
      simp only [Matrix.mul_one, Matrix.zero_mul, add_zero]
    -- (LΔ * UU').B = LΔ.A * UU'.B + LΔ.B * UU'.D = M.A * (B_M + B_N) + 0 * I = M.A * (B_M + B_N)
    have hW_B : (LΔ * UU').Bblock = M.Ablock * (B_M + B_N) := by
      show LΔ.Ablock * UU'.Bblock + LΔ.Bblock * UU'.Dblock = M.Ablock * (B_M + B_N)
      rw [hLΔ_A, hLΔ_B, hUU'_B, hUU'_D]
      simp only [Matrix.zero_mul, add_zero]
    -- (LΔ * UU').C = LΔ.C * UU'.A + LΔ.D * UU'.C = C_M*M.A * I + D_M * 0 = C_M * M.A
    have hW_C : (LΔ * UU').Cblock = C_M * M.Ablock := by
      show LΔ.Cblock * UU'.Ablock + LΔ.Dblock * UU'.Cblock = C_M * M.Ablock
      rw [hLΔ_C, hLΔ_D, hUU'_A, hUU'_C]
      simp only [Matrix.mul_one, Matrix.mul_zero, add_zero]
    -- (LΔ * UU').D = LΔ.C * UU'.B + LΔ.D * UU'.D = C_M*M.A * (B_M+B_N) + D_M * I
    --              = C_M * M.A * (B_M + B_N) + D_M
    have hW_D : (LΔ * UU').Dblock = C_M * M.Ablock * (B_M + B_N) + D_M := by
      show LΔ.Cblock * UU'.Bblock + LΔ.Dblock * UU'.Dblock = C_M * M.Ablock * (B_M + B_N) + D_M
      rw [hLΔ_C, hLΔ_D, hUU'_B, hUU'_D]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    -- Now compute the Schur complement of W = LΔ * UU':
    -- W.A - W.B * W.D⁻¹ * W.C
    -- = M.A - M.A*(B_M+B_N) * (C_M*M.A*(B_M+B_N) + D_M)⁻¹ * C_M*M.A
    -- This is complicated. Let's use a different approach.
    --
    -- Key insight: The Berezinian is det(A - B D⁻¹ C) / det(D)
    -- For W = LΔ * UU':
    -- - W.B = M.A * (B_M + B_N) where B_M, B_N are odd matrices
    -- - W.C = C_M * M.A where C_M is an odd matrix
    -- - The product B D⁻¹ C involves odd * (something) * odd = even (potentially nilpotent)
    --
    -- Actually, the cleanest approach uses that W = M * U' where M = L*Δ*U
    -- And M.ber = Δ.ber (already proven in hBerM after adjusting for proof term)
    -- The question is whether (M * U').ber = M.ber
    --
    -- For upper triangular U' = [I, B_N; 0, I]:
    -- (M * U').D = M.C * U'.B + M.D * I = M.C * B_N + M.D
    -- (M * U').C = M.C * I + M.D * 0 = M.C
    -- (M * U').B = M.A * B_N + M.B * I = M.A * B_N + M.B
    -- (M * U').A = M.A * I + M.B * 0 = M.A
    --
    -- Schur(M*U') = (M*U').A - (M*U').B * (M*U').D⁻¹ * (M*U').C
    --            = M.A - (M.A*B_N + M.B) * (M.C*B_N + M.D)⁻¹ * M.C
    --
    -- This still involves inverting M.C*B_N + M.D. Since M.C and B_N are odd,
    -- M.C*B_N is a sum of products of odd elements, hence nilpotent (in Grassmann sense).
    -- So (M.C*B_N + M.D)⁻¹ exists and can be expanded as geometric series.
    --
    -- The full calculation is involved. For now, let's note that the structure
    -- should give us the same Berezinian, and use the algebraic identity.
    --
    -- Alternative: Note that L*Δ*U*U' = (L*Δ*U)*U' = M*U'
    -- Use ber_mul_upperTriangular_right (if it existed) or prove directly.
    --
    -- Direct proof strategy: Use that (X*Y).ber = X.ber * Y.ber when one is triangular
    -- Specifically: Ber(M * U') should equal Ber(M) since Ber(U') = 1
    --
    -- Ber(U') = det(U'.A - U'.B * U'.D⁻¹ * U'.C) * det(U'.D)⁻¹
    --         = det(I - B_N * I⁻¹ * 0) * det(I)⁻¹ = det(I) * 1 = 1
    --
    -- And the multiplicativity gives Ber(M*U') = Ber(M) * Ber(U') = Ber(M) * 1 = Ber(M)
    -- But wait, this is circular - we're trying to prove multiplicativity!
    --
    -- Let me try a more direct approach using the structure.
    --
    -- Since M = L*Δ*U, we have M*U' = L*Δ*U*U' = L*Δ*(U*U')
    -- where U*U' is upper triangular with B'' = B_M + B_N
    -- So L*Δ*(U*U') is still in LDU form, hence Ber = Ber(Δ)
    --
    -- By ber_LDU applied to L, Δ, U*U':
    -- Ber(L*Δ*(U*U')) = Ber(Δ)
    --
    -- The issue is that ber_LDU needs specific hypotheses. Let me check if we can apply it.
    -- Actually, we already have hBerM which shows M.ber = Δ.ber
    -- And L*Δ*U*U' = M*U' where M.ber = Δ.ber
    --
    -- The key insight is: W = L*Δ*(U*U') has the same LDU structure (with U replaced by U*U')
    -- and by the same argument as hBerM, W.ber = Δ.ber
    --
    -- Let me apply the same strategy: W.ber = W.berAlt = det(W.A) / det(SchurA(W))
    -- where SchurA(W) = W.D - W.C * W.A⁻¹ * W.B
    --
    -- W.A = M.A (invertible by hMA)
    -- SchurA(W) = W.D - W.C * W.A⁻¹ * W.B
    --           = (C_M*M.A*(B_M+B_N) + D_M) - (C_M*M.A) * M.A⁻¹ * (M.A*(B_M+B_N))
    --           = C_M*M.A*(B_M+B_N) + D_M - C_M * (B_M+B_N)  (since M.A⁻¹*M.A = I)
    --           = ... wait, C_M*M.A != C_M
    --
    -- Let me recalculate: C_M = M.C * M.A⁻¹
    -- So W.C = C_M * M.A = M.C * M.A⁻¹ * M.A = M.C
    -- And W.C * W.A⁻¹ = M.C * M.A⁻¹
    -- W.C * W.A⁻¹ * W.B = M.C * M.A⁻¹ * M.A * (B_M + B_N) = M.C * (B_M + B_N)
    --                   = M.C * (M.A⁻¹*M.B + B_N) = M.C*M.A⁻¹*M.B + M.C*B_N
    --
    -- W.D = C_M * M.A * (B_M + B_N) + D_M
    --     = M.C * M.A⁻¹ * M.A * (M.A⁻¹*M.B + B_N) + D_M
    --     = M.C * (M.A⁻¹*M.B + B_N) + D_M
    --     = M.C * M.A⁻¹ * M.B + M.C * B_N + D_M
    --
    -- SchurA(W) = W.D - W.C * W.A⁻¹ * W.B
    --           = (M.C*M.A⁻¹*M.B + M.C*B_N + D_M) - (M.C*M.A⁻¹*M.B + M.C*B_N)
    --           = D_M = schurComplementA M = Δ.D
    --
    -- So W.berAlt = det(W.A) / det(SchurA(W)) = det(M.A) / det(D_M) = Δ.berAlt
    -- And Δ.ber = det(Δ.A - 0) / det(Δ.D) = det(M.A) / det(D_M) = Δ.berAlt
    --
    -- Therefore W.ber = W.berAlt = Δ.berAlt = Δ.ber!
    --
    -- Let me implement this:
    -- First need to show W.ber = W.berAlt using ber_eq_berAlt
    -- This requires: W.A⁻¹*W.B and W.D⁻¹*W.C are odd
    have hW_A_eq : (L * Δ * U * U').Ablock = M.Ablock := by rw [hW_eq]; exact hW_A
    have hW_A_det : (L * Δ * U * U').Ablock.det ≠ 0 := by rw [hW_A_eq]; exact hMA
    -- Need parity conditions for W.A⁻¹*W.B and W.D⁻¹*W.C
    -- W.A = M.A (even), W.B = M.A*(B_M+B_N) where B_M, B_N are odd
    -- W.A⁻¹*W.B = M.A⁻¹ * M.A * (B_M+B_N) = B_M + B_N which is odd
    have hW_AinvB_odd : ∀ i j, ((L * Δ * U * U').Ablock⁻¹ * (L * Δ * U * U').Bblock) i j ∈ A.odd := by
      intro i j
      rw [hW_eq, hW_A, hW_B]
      -- M.A⁻¹ * (M.A * (B_M + B_N)) = (M.A⁻¹ * M.A) * (B_M + B_N) = I * (B_M + B_N) = B_M + B_N
      have hAinvA : M.Ablock⁻¹ * M.Ablock = 1 := Matrix.nonsing_inv_mul M.Ablock (isUnit_of_invertible _)
      have h_eq : M.Ablock⁻¹ * (M.Ablock * (B_M + B_N)) = B_M + B_N := by
        calc M.Ablock⁻¹ * (M.Ablock * (B_M + B_N))
            = (M.Ablock⁻¹ * M.Ablock) * (B_M + B_N) := by rw [Matrix.mul_assoc]
          _ = (1 : Matrix _ _ _) * (B_M + B_N) := by rw [hAinvA]
          _ = B_M + B_N := by rw [Matrix.one_mul]
      rw [h_eq]
      -- B_M + B_N is odd (sum of odd matrices is odd)
      have hBM_odd : B_M i j ∈ A.odd := hAinvBM i j
      have hBN_odd : B_N i j ∈ A.odd := hBDinvN i j
      exact A.odd.add_mem hBM_odd hBN_odd
    -- W.D⁻¹*W.C: W.C = M.C (odd), W.D involves odd terms so W.D⁻¹ is more complex
    -- But SchurA(W) = D_M (shown above), so we can use berAlt directly
    -- Let's compute W.berAlt and show it equals Δ.ber
    -- W.berAlt = det(W.A) * det(schurComplementA W)⁻¹
    -- We've shown schurComplementA W = D_M (need to verify this formally)
    --
    -- Strategy: Use ber_eq_berAlt to convert W.ber to W.berAlt, then show W.berAlt = Δ.ber
    --
    -- Key calculation (schurComplementA(W) = D_M):
    -- W.A = M.A, W.D = C_M*M.A*(B_M+B_N) + D_M, W.C = C_M*M.A = M.C, W.B = M.A*(B_M+B_N)
    -- schurComplementA(W) = W.D - W.C*W.A⁻¹*W.B
    --   = C_M*M.A*(B_M+B_N) + D_M - M.C*M.A⁻¹*M.A*(B_M+B_N)
    --   = C_M*M.A*(B_M+B_N) + D_M - M.C*(B_M+B_N)
    --   = (C_M*M.A - M.C)*(B_M+B_N) + D_M
    --   = (M.C*M.A⁻¹*M.A - M.C)*(B_M+B_N) + D_M  (since C_M = M.C*M.A⁻¹)
    --   = (M.C - M.C)*(B_M+B_N) + D_M = D_M
    --
    -- So W.berAlt = det(W.A)/det(schurComplementA W) = det(M.A)/det(D_M) = Δ.ber
    -- First show W.C = M.Cblock (which has odd entries)
    have hW_C_eq_MC : (L * Δ * U * U').Cblock = M.Cblock := by
      rw [hW_eq, hW_C]
      -- C_M * M.A = (M.C * M.A⁻¹) * M.A = M.C
      have hAinvA : M.Ablock⁻¹ * M.Ablock = 1 := Matrix.nonsing_inv_mul M.Ablock (isUnit_of_invertible _)
      calc C_M * M.Ablock
          = (M.Cblock * M.Ablock⁻¹) * M.Ablock := rfl
        _ = M.Cblock * (M.Ablock⁻¹ * M.Ablock) := by rw [Matrix.mul_assoc]
        _ = M.Cblock * (1 : Matrix _ _ _) := by rw [hAinvA]
        _ = M.Cblock := by rw [Matrix.mul_one]
    -- Show W.D has even entries
    -- W.D = C_M * M.A * (B_M + B_N) + D_M = M.C * (B_M + B_N) + D_M
    -- M.C has odd entries, B_M + B_N has odd entries, so M.C * (B_M + B_N) is even (odd * odd = even)
    -- D_M has even entries (hSchurM), so W.D = even + even = even
    have hW_D_even : ∀ i j, (L * Δ * U * U').Dblock i j ∈ A.even := by
      intro i j
      rw [hW_eq, hW_D]
      -- C_M * M.A * (B_M + B_N) + D_M = M.C * (B_M + B_N) + D_M
      -- First: C_M * M.A = M.C (shown in hW_C_eq_MC calculation)
      have hCM_MA_eq : C_M * M.Ablock = M.Cblock := by
        have hAinvA : M.Ablock⁻¹ * M.Ablock = 1 := Matrix.nonsing_inv_mul M.Ablock (isUnit_of_invertible _)
        calc C_M * M.Ablock
            = (M.Cblock * M.Ablock⁻¹) * M.Ablock := rfl
          _ = M.Cblock * (M.Ablock⁻¹ * M.Ablock) := by rw [Matrix.mul_assoc]
          _ = M.Cblock * (1 : Matrix _ _ _) := by rw [hAinvA]
          _ = M.Cblock := by rw [Matrix.mul_one]
      -- Rewrite the D entry
      simp only [Matrix.add_apply]
      -- (C_M * M.A * (B_M + B_N)) i j + D_M i j
      -- = (M.C * (B_M + B_N)) i j + D_M i j  (using hCM_MA_eq)
      have hProd_even : (C_M * M.Ablock * (B_M + B_N)) i j ∈ A.even := by
        -- C_M * M.A * (B_M + B_N) = M.C * (B_M + B_N)
        have h_eq : C_M * M.Ablock * (B_M + B_N) = M.Cblock * (B_M + B_N) := by
          rw [hCM_MA_eq]
        rw [h_eq]
        -- M.C (i, k) * (B_M + B_N) (k, j) is odd * odd = even for each k
        -- Then sum of even is even
        simp only [Matrix.mul_apply]
        apply A.even.sum_mem
        intro k _
        have hMC_odd : M.Cblock i k ∈ A.odd := M.Cblock_odd i k
        have hBsum_odd : (B_M + B_N) k j ∈ A.odd := by
          simp only [Matrix.add_apply]
          exact A.odd.add_mem (hAinvBM k j) (hBDinvN k j)
        exact A.odd_mul_odd _ _ hMC_odd hBsum_odd
      have hDM_even : D_M i j ∈ A.even := hSchurM i j
      exact A.even.add_mem hProd_even hDM_even
    -- Now show W.D⁻¹ * W.C has odd entries
    -- Key: W.D has even entries, W.D⁻¹ also has even entries (inverse preserves parity in even subalgebra)
    -- W.C = M.C has odd entries
    -- even matrix * odd matrix = odd matrix (entry-wise: even * odd = odd)
    have hW_DinvC_odd : ∀ i j, ((L * Δ * U * U').Dblock⁻¹ * (L * Δ * U * U').Cblock) i j ∈ A.odd := by
      intro i j
      rw [hW_C_eq_MC]
      -- W.D⁻¹ * M.C
      -- Since W.D has even entries, W.D⁻¹ has even entries
      -- (inverse of even matrix is even in Grassmann algebra, since adjugate formula
      -- only involves products and sums of entries)
      -- M.C has odd entries
      -- (W.D⁻¹)_ik * M.C_kj is even * odd = odd, sum of odd is odd
      simp only [Matrix.mul_apply]
      apply A.odd.sum_mem
      intro k _
      -- W.D⁻¹ i k ∈ A.even (inverse of even matrix has even entries)
      -- M.C k j ∈ A.odd
      have hMC_odd : M.Cblock k j ∈ A.odd := M.Cblock_odd k j
      -- For the even entry of W.D⁻¹, we use that det is a polynomial in even entries (hence even)
      -- and adjugate entries are polynomials in even entries (hence even)
      -- So (det)⁻¹ * adjugate = inverse has even entries
      -- This is a fundamental property of Grassmann algebras that we assume here
      have hWDinv_even : (L * Δ * U * U').Dblock⁻¹ i k ∈ A.even := by
        -- The inverse of a matrix with even entries has even entries
        -- This follows from matrix_inv_even: M⁻¹ = (det M)⁻¹ • adjugate M
        -- where det M ∈ even, adjugate entries ∈ even, and (det M)⁻¹ ∈ even
        exact matrix_inv_even (L * Δ * U * U').Dblock hW_D_even hYD h1 h0even i k
      exact A.even_mul_odd _ _ hWDinv_even hMC_odd
    have hW_berAlt := SuperMatrix.ber_eq_berAlt (L * Δ * U * U') hW_A_det hYD
      hW_AinvB_odd hW_DinvC_odd h1 h0even
    -- Now show W.berAlt = Δ.ber
    -- W.berAlt = det(W.A) * det(schurComplementA W)⁻¹
    -- We showed schurComplementA W = D_M
    -- So W.berAlt = det(M.A) * det(D_M)⁻¹ = Δ.ber
    rw [hW_berAlt]
    unfold SuperMatrix.berAlt
    -- Goal: det(W.A) * det(W.D - W.C*W.A⁻¹*W.B)⁻¹ = det(Δ.A - 0) * det(Δ.D)⁻¹
    rw [hW_eq, hW_A, hW_B, hW_C, hW_D]
    -- The goal after unfold berAlt and rewrites is:
    -- det(M.A) * det(C_M*M.A*(B_M+B_N) + D_M - (C_M*M.A)*M.A⁻¹*(M.A*(B_M+B_N)))⁻¹ = Δ.ber hΔD
    -- Note: W.C = C_M * M.A, so W.C * W.A⁻¹ = (C_M * M.A) * M.A⁻¹ = C_M * (M.A * M.A⁻¹) = C_M
    -- So the Schur complement simplifies to:
    -- W.D - W.C * W.A⁻¹ * W.B = C_M*M.A*(B_M+B_N) + D_M - C_M * (M.A*(B_M+B_N))
    --                        = C_M*M.A*(B_M+B_N) + D_M - C_M*M.A*(B_M+B_N) = D_M
    have hAAinv : M.Ablock * M.Ablock⁻¹ = 1 := Matrix.mul_nonsing_inv M.Ablock (isUnit_of_invertible _)
    have hSchurA_W : C_M * M.Ablock * (B_M + B_N) + D_M - C_M * M.Ablock * M.Ablock⁻¹ * (M.Ablock * (B_M + B_N)) = D_M := by
      -- C_M * M.A * M.A⁻¹ = C_M * (M.A * M.A⁻¹) = C_M * I = C_M
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
    -- Goal: det(M.A) * det(D_M)⁻¹ = Δ.ber hΔD
    -- Unfold Δ.ber to compare
    unfold SuperMatrix.ber
    -- Now: det(M.A) * det(D_M)⁻¹ = det(Δ.A - Δ.B*Δ.D⁻¹*Δ.C) * det(Δ.D)⁻¹
    have hΔA : Δ.Ablock = M.Ablock := rfl
    have hΔB : Δ.Bblock = 0 := rfl
    have hΔC : Δ.Cblock = 0 := rfl
    have hΔD_eq : Δ.Dblock = D_M := rfl
    simp only [hΔA, hΔB, hΔC, hΔD_eq, Matrix.zero_mul, Matrix.mul_zero, sub_zero]

  -- Step 4: Ber(Δ) = Ber(M) and Ber(Δ') = Ber(N)
  -- M.Dblock = (L*Δ*U).Dblock since M = L*Δ*U
  have hLΔU_D : (L * Δ * U).Dblock.det = M.Dblock.det := by rw [← hM_eq]
  have hLΔU_D' : (L * Δ * U).Dblock.det ≠ 0 := hLΔU_D ▸ hMD

  have hBerM : M.ber hMD = Δ.ber hΔD := by
    -- Strategy: M.ber = M.berAlt by ber_eq_berAlt, and Δ.ber = M.berAlt
    -- First show M.ber = M.berAlt
    have hBerAlt := SuperMatrix.ber_eq_berAlt M hMA hMD hAinvBM hDinvCM h1 h0even
    -- M.berAlt = det(M.A) * det(S_A)⁻¹
    -- Δ.ber = det(Δ.A - Δ.B Δ.D⁻¹ Δ.C) * det(Δ.D)⁻¹
    -- Since Δ.B = 0, this is det(Δ.A) * det(Δ.D)⁻¹ = det(M.A) * det(S_A)⁻¹ = M.berAlt
    rw [hBerAlt]
    unfold SuperMatrix.ber SuperMatrix.berAlt
    have hΔA : Δ.Ablock = M.Ablock := rfl
    have hΔB : Δ.Bblock = 0 := rfl
    have hΔC : Δ.Cblock = 0 := rfl
    have hΔD_eq : Δ.Dblock = schurComplementA M hMA := rfl
    simp only [hΔA, hΔB, hΔC, hΔD_eq, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
    -- Goal: M.Ablock.det * (M.Dblock - M.Cblock * M.Ablock⁻¹ * M.Bblock).det⁻¹ =
    --       M.Ablock.det * (schurComplementA M hMA).det⁻¹
    -- schurComplementA M hMA = M.Dblock - M.Cblock * M.Ablock⁻¹ * M.Bblock by definition
    rfl

  -- N.Dblock = (U'*Δ'*L').Dblock since N = U'*Δ'*L'
  have hU'Δ'L'_D : (U' * Δ' * L').Dblock.det = N.Dblock.det := by rw [← hN_eq]
  have hU'Δ'L'_D' : (U' * Δ' * L').Dblock.det ≠ 0 := hU'Δ'L'_D ▸ hND

  have hBerN : N.ber hND = Δ'.ber hΔ'D := by
    -- N.ber = det(N.A - N.B N.D⁻¹ N.C) * det(N.D)⁻¹ = det(schurComplementD N) * det(N.D)⁻¹
    -- Δ'.ber = det(Δ'.A - 0) * det(Δ'.D)⁻¹ = det(schurComplementD N) * det(N.D)⁻¹
    unfold SuperMatrix.ber
    have hΔ'A : Δ'.Ablock = schurComplementD N hND := rfl
    have hΔ'B : Δ'.Bblock = 0 := rfl
    have hΔ'C : Δ'.Cblock = 0 := rfl
    have hΔ'D_eq : Δ'.Dblock = N.Dblock := rfl
    simp only [hΔ'A, hΔ'B, hΔ'C, hΔ'D_eq, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
    -- Goal: det(N.A - N.B N.D⁻¹ N.C) * det(N.D)⁻¹ = det(schurComplementD N) * det(N.D)⁻¹
    -- schurComplementD N hND = N.A - N.B * N.D⁻¹ * N.C by definition
    rfl

  -- Combine: Ber(MN) = Ber(Δ) * Ber(Δ') = Ber(M) * Ber(N)
  rw [hStrip1, hStrip2, hStrip3, hBerM, hBerN]

/-- Multiplying on the left by a lower triangular matrix L = [I 0; C' I] preserves Ber.

    **Proof**: Apply ber_mul_A_invertible with M = L.
    Since L.A = I is invertible and Ber(L) = 1:
    Ber(L * N) = Ber(L) * Ber(N) = 1 * Ber(N) = Ber(N)

    Note: This does NOT require N.A to be invertible! -/
theorem SuperMatrix.ber_mul_lowerTriangular_left {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    [SuperCommutative A.toSuperAlgebra] {n m : ℕ}
    (C' : Matrix (Fin m) (Fin n) A.carrier)
    (N : SuperMatrix A n m)
    (h1 : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even)
    (h0odd : (0 : A.carrier) ∈ A.odd) (hC' : ∀ i j, C' i j ∈ A.odd)
    (hND : N.Dblock.det ≠ 0)
    (hLD : (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock.det ≠ 0)
    (hLND : ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') * N).Dblock.det ≠ 0)
    (hBDinvN : ∀ i j, (N.Bblock * N.Dblock⁻¹) i j ∈ A.odd)
    (hDinvCN : ∀ i j, (N.Dblock⁻¹ * N.Cblock) i j ∈ A.odd)
    (hSchurN : ∀ i j, (schurComplementD N hND) i j ∈ A.even) :
    ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC') * N).ber hLND =
    N.ber hND := by
  -- Apply ber_mul_A_invertible with M = L
  -- L.A = I, which is invertible (det(I) = 1 ≠ 0)
  -- Ber(L) = 1 (from ber_lowerTriangular)
  -- So Ber(L * N) = Ber(L) * Ber(N) = 1 * Ber(N) = Ber(N)
  let L := SuperMatrix.lowerTriangular C' h1 h0even h0odd hC'
  have hLA : L.Ablock.det ≠ 0 := by
    show (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock.det ≠ 0
    simp only [SuperMatrix.lowerTriangular]
    rw [Matrix.det_one]
    exact one_ne_zero
  -- Ber(L) = 1
  have hBerL : L.ber hLD = 1 := SuperMatrix.ber_lowerTriangular C' h1 h0even h0odd hC' hLD
  -- For ber_mul_A_invertible with M = L, we need:
  -- hCAinvM: (L.C * L.A⁻¹) i j ∈ A.odd, i.e., (C' * I⁻¹) = C' which is odd
  -- hAinvBM: (L.A⁻¹ * L.B) i j ∈ A.odd, i.e., (I⁻¹ * 0) = 0 which is in odd
  have hCAinvL : ∀ i j, (L.Cblock * L.Ablock⁻¹) i j ∈ A.odd := by
    intro i j
    show ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock *
          (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock⁻¹) i j ∈ A.odd
    simp only [SuperMatrix.lowerTriangular]
    rw [inv_one, Matrix.mul_one]
    exact hC' i j
  have hAinvBL : ∀ i j, (L.Ablock⁻¹ * L.Bblock) i j ∈ A.odd := by
    intro i j
    show ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Ablock⁻¹ *
          (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Bblock) i j ∈ A.odd
    simp only [SuperMatrix.lowerTriangular]
    rw [Matrix.mul_zero]
    exact h0odd
  -- Schur complement of L: schurComplementA(L) = L.D - L.C * L.A⁻¹ * L.B = I - C' * I⁻¹ * 0 = I
  have hSchurL : ∀ i j, (schurComplementA L hLA) i j ∈ A.even := by
    intro i j
    unfold schurComplementA
    -- L.Dblock = I, L.Bblock = 0, so L.D - L.C * L.A⁻¹ * L.B = I - anything * 0 = I
    have hLB : L.Bblock = 0 := rfl
    have hLD_eq : L.Dblock = 1 := rfl
    rw [hLB, Matrix.mul_zero, sub_zero, hLD_eq]
    simp only [Matrix.one_apply]
    split_ifs
    · exact h1
    · exact h0even
  -- Schur complement determinant: det(schurComplementA L) = det(I) = 1 ≠ 0
  have hSchurL_det : (schurComplementA L hLA).det ≠ 0 := by
    unfold schurComplementA
    have hLB : L.Bblock = 0 := rfl
    have hLD_eq : L.Dblock = 1 := rfl
    rw [hLB, Matrix.mul_zero, sub_zero, hLD_eq]
    rw [Matrix.det_one]
    exact one_ne_zero
  -- L.Dblock⁻¹ * L.Cblock = I⁻¹ * C' = C' which is odd
  have hDinvCL : ∀ i j, (L.Dblock⁻¹ * L.Cblock) i j ∈ A.odd := by
    intro i j
    show ((SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Dblock⁻¹ *
          (SuperMatrix.lowerTriangular C' h1 h0even h0odd hC').Cblock) i j ∈ A.odd
    simp only [SuperMatrix.lowerTriangular]
    rw [inv_one, Matrix.one_mul]
    exact hC' i j
  -- Apply ber_mul_A_invertible
  have hMul := SuperMatrix.ber_mul_A_invertible L N hLA hLD hND hLND h1 h0even h0odd
    hBDinvN hDinvCN hCAinvL hAinvBL hDinvCL hSchurL hSchurN hSchurL_det
  rw [hMul, hBerL, one_mul]

/-- Berezinian multiplicativity for diagonal matrix on the left.

    When Δ = [A' 0; 0 D'] is a diagonal supermatrix, we have:
    Ber(Δ · Z) = Ber(Δ) · Ber(Z)

    This is because:
    - (Δ · Z).A = A' · Z.A
    - (Δ · Z).B = A' · Z.B
    - (Δ · Z).C = D' · Z.C
    - (Δ · Z).D = D' · Z.D

    The Berezinian of Δ·Z is:
    det((A'·Z.A) - (A'·Z.B) · (D'·Z.D)⁻¹ · (D'·Z.C)) / det(D'·Z.D)
    = det(A' · (Z.A - Z.B · Z.D⁻¹ · Z.C)) / det(D' · Z.D)
    = det(A') · det(Z.A - Z.B · Z.D⁻¹ · Z.C) / (det(D') · det(Z.D))
    = (det(A')/det(D')) · (det(Z.A - Z.B·Z.D⁻¹·Z.C)/det(Z.D))
    = Ber(Δ) · Ber(Z) -/
theorem SuperMatrix.ber_mul_diagonal_left {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    [SuperCommutative A.toSuperAlgebra] {n m : ℕ}
    (A' : Matrix (Fin n) (Fin n) A.carrier) (D' : Matrix (Fin m) (Fin m) A.carrier)
    (Z : SuperMatrix A n m)
    (h0odd : (0 : A.carrier) ∈ A.odd)
    (hA' : ∀ i j, A' i j ∈ A.even) (hD' : ∀ i j, D' i j ∈ A.even)
    (hD'det : D'.det ≠ 0) (hZD : Z.Dblock.det ≠ 0)
    (hΔD : (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock.det ≠ 0)
    (hΔZD : ((SuperMatrix.diagonal A' D' h0odd hA' hD') * Z).Dblock.det ≠ 0) :
    ((SuperMatrix.diagonal A' D' h0odd hA' hD') * Z).ber hΔZD =
    (SuperMatrix.diagonal A' D' h0odd hA' hD').ber hΔD * Z.ber hZD := by
  unfold SuperMatrix.ber
  -- Δ = [A' 0; 0 D'], Z = [Z.A Z.B; Z.C Z.D]
  -- Δ·Z = [A'·Z.A + 0·Z.C, A'·Z.B + 0·Z.D; 0·Z.A + D'·Z.C, 0·Z.B + D'·Z.D]
  --     = [A'·Z.A, A'·Z.B; D'·Z.C, D'·Z.D]
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
  -- Goal: det(A'·Z.A - A'·Z.B · (D'·Z.D)⁻¹ · D'·Z.C) · det(D'·Z.D)⁻¹
  --     = (det(A') · det(D')⁻¹) · (det(Z.A - Z.B·Z.D⁻¹·Z.C) · det(Z.D)⁻¹)

  -- Simplify the Schur complement of Δ·Z
  -- A'·Z.A - A'·Z.B · (D'·Z.D)⁻¹ · D'·Z.C
  -- = A'·Z.A - A'·Z.B · Z.D⁻¹·D'⁻¹ · D'·Z.C  (using (D'·Z.D)⁻¹ = Z.D⁻¹·D'⁻¹)
  -- = A'·Z.A - A'·Z.B · Z.D⁻¹ · Z.C           (D'⁻¹·D' = I)
  -- = A' · (Z.A - Z.B·Z.D⁻¹·Z.C)
  haveI : Invertible D'.det := invertibleOfNonzero hD'det
  haveI : Invertible D' := Matrix.invertibleOfDetInvertible D'
  haveI : Invertible Z.Dblock.det := invertibleOfNonzero hZD
  haveI : Invertible Z.Dblock := Matrix.invertibleOfDetInvertible Z.Dblock

  -- (D' * Z.D)⁻¹ = Z.D⁻¹ * D'⁻¹ for invertible matrices
  have h_inv : (D' * Z.Dblock)⁻¹ = Z.Dblock⁻¹ * D'⁻¹ := by
    rw [Matrix.mul_inv_rev]
  -- det(D' * Z.D) = det(D') * det(Z.D)
  have h_det : (D' * Z.Dblock).det = D'.det * Z.Dblock.det := by
    rw [Matrix.det_mul]
  -- Schur complement simplification
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
  -- det(A' · X) = det(A') · det(X)
  have h_det_schur : (A' * (Z.Ablock - Z.Bblock * Z.Dblock⁻¹ * Z.Cblock)).det =
                     A'.det * (Z.Ablock - Z.Bblock * Z.Dblock⁻¹ * Z.Cblock).det := by
    rw [Matrix.det_mul]
  rw [h_det_schur, h_det]
  -- Goal: det(A') · det(Z.A - Z.B·Z.D⁻¹·Z.C) · (det(D') · det(Z.D))⁻¹
  --     = det(A') · det(D')⁻¹ · (det(Z.A - Z.B·Z.D⁻¹·Z.C) · det(Z.D)⁻¹)
  rw [mul_inv]
  -- Simplify the diagonal matrix blocks on the RHS
  -- (diagonal A' D' h0odd hA' hD').Ablock = A'
  -- (diagonal A' D' h0odd hA' hD').Bblock = 0
  -- (diagonal A' D' h0odd hA' hD').Cblock = 0
  -- (diagonal A' D' h0odd hA' hD').Dblock = D'
  have hΔA : (SuperMatrix.diagonal A' D' h0odd hA' hD').Ablock = A' := rfl
  have hΔB : (SuperMatrix.diagonal A' D' h0odd hA' hD').Bblock = 0 := rfl
  have hΔC : (SuperMatrix.diagonal A' D' h0odd hA' hD').Cblock = 0 := rfl
  have hΔD : (SuperMatrix.diagonal A' D' h0odd hA' hD').Dblock = D' := rfl
  simp only [hΔA, hΔB, hΔC, hΔD, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
  ring

/-- Berezinian multiplicativity for diagonal matrix on the right.

    When Δ' = [A'' 0; 0 D''] is a diagonal supermatrix, we have:
    Ber(Z · Δ') = Ber(Z) · Ber(Δ')

    This is because:
    - (Z · Δ').A = Z.A · A''
    - (Z · Δ').B = Z.B · D''
    - (Z · Δ').C = Z.C · A''
    - (Z · Δ').D = Z.D · D''

    The Schur complement is:
    Z.A·A'' - Z.B·D'' · (Z.D·D'')⁻¹ · Z.C·A''
    = Z.A·A'' - Z.B · D''·D''⁻¹ · Z.D⁻¹ · Z.C · A''
    = Z.A·A'' - Z.B · Z.D⁻¹ · Z.C · A''
    = (Z.A - Z.B·Z.D⁻¹·Z.C) · A''
    = Schur(Z) · A''

    So Ber(Z·Δ') = det(Schur(Z)·A'') / det(Z.D·D'')
                = det(Schur(Z))·det(A'') / (det(Z.D)·det(D''))
                = Ber(Z) · Ber(Δ') -/
theorem SuperMatrix.ber_mul_diagonal_right {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    [SuperCommutative A.toSuperAlgebra] {n m : ℕ}
    (Z : SuperMatrix A n m)
    (A'' : Matrix (Fin n) (Fin n) A.carrier) (D'' : Matrix (Fin m) (Fin m) A.carrier)
    (h0odd : (0 : A.carrier) ∈ A.odd)
    (hA'' : ∀ i j, A'' i j ∈ A.even) (hD'' : ∀ i j, D'' i j ∈ A.even)
    (hD''det : D''.det ≠ 0) (hZD : Z.Dblock.det ≠ 0)
    (hΔD : (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Dblock.det ≠ 0)
    (hZΔD : (Z * (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'')).Dblock.det ≠ 0) :
    (Z * (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'')).ber hZΔD =
    Z.ber hZD * (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').ber hΔD := by
  unfold SuperMatrix.ber
  -- Z · Δ' = [Z.A·A'', Z.B·D''; Z.C·A'', Z.D·D'']
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
  -- Set up invertibility
  haveI : Invertible D''.det := invertibleOfNonzero hD''det
  haveI : Invertible D'' := Matrix.invertibleOfDetInvertible D''
  haveI : Invertible Z.Dblock.det := invertibleOfNonzero hZD
  haveI : Invertible Z.Dblock := Matrix.invertibleOfDetInvertible Z.Dblock
  -- (Z.D * D'')⁻¹ = D''⁻¹ * Z.D⁻¹
  have h_inv : (Z.Dblock * D'')⁻¹ = D''⁻¹ * Z.Dblock⁻¹ := by
    rw [Matrix.mul_inv_rev]
  -- det(Z.D * D'') = det(Z.D) * det(D'')
  have h_det : (Z.Dblock * D'').det = Z.Dblock.det * D''.det := by
    rw [Matrix.det_mul]
  -- Schur complement simplification
  -- Z.A·A'' - Z.B·D'' · (Z.D·D'')⁻¹ · Z.C·A''
  -- = Z.A·A'' - Z.B·D'' · D''⁻¹·Z.D⁻¹ · Z.C·A''
  -- = Z.A·A'' - Z.B · Z.D⁻¹ · Z.C · A''
  -- = (Z.A - Z.B·Z.D⁻¹·Z.C) · A''
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
  rw [mul_inv]
  -- Simplify diagonal matrix blocks on the RHS
  have hΔA : (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Ablock = A'' := rfl
  have hΔB : (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Bblock = 0 := rfl
  have hΔC : (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Cblock = 0 := rfl
  have hΔD : (SuperMatrix.diagonal A'' D'' h0odd hA'' hD'').Dblock = D'' := rfl
  simp only [hΔA, hΔB, hΔC, hΔD, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
  ring

/-- Berezinian multiplicativity: Ber(MN) = Ber(M) · Ber(N) for SuperMatrices.

    This is the fundamental theorem of the Berezinian.

    **Proof strategy** using UDL factorization for both M and N:
    - UDL for M (D-based): M = U · Δ · L
    - UDL for N (D-based): N = U' · Δ' · L'
    - MN = U · Δ · L · U' · Δ' · L'
    - Apply stripping lemmas -/
theorem SuperMatrix.ber_mul {R : Type*} [CommRing R] {A : FieldSuperAlgebra R}
    [SuperCommutative A.toSuperAlgebra] {n m : ℕ}
    (M N : SuperMatrix A n m)
    (hMD : M.Dblock.det ≠ 0)
    (hND : N.Dblock.det ≠ 0)
    (hMND : (M * N).Dblock.det ≠ 0)
    (h1 : (1 : A.carrier) ∈ A.even) (h0even : (0 : A.carrier) ∈ A.even)
    (h0odd : (0 : A.carrier) ∈ A.odd)
    (hBDinvM : ∀ i j, (M.Bblock * M.Dblock⁻¹) i j ∈ A.odd)
    (hDinvCM : ∀ i j, (M.Dblock⁻¹ * M.Cblock) i j ∈ A.odd)
    (hBDinvN : ∀ i j, (N.Bblock * N.Dblock⁻¹) i j ∈ A.odd)
    (hDinvCN : ∀ i j, (N.Dblock⁻¹ * N.Cblock) i j ∈ A.odd)
    (hSchurM : ∀ i j, (schurComplementD M hMD) i j ∈ A.even)
    (hSchurN : ∀ i j, (schurComplementD N hND) i j ∈ A.even) :
    (M * N).ber hMND = M.ber hMD * N.ber hND := by
  -- UDL factorizations:
  -- M = U_M · Δ_M · L_M where Δ_M = diag(S_D^M, D_M)
  -- N = U_N · Δ_N · L_N where Δ_N = diag(S_D^N, D_N)
  --
  -- MN = U_M · Δ_M · L_M · U_N · Δ_N · L_N
  --
  -- Stripping strategy:
  -- 1. Strip U_M from left: Ber(U_M · X) = Ber(X)
  -- 2. Strip L_N from right: Ber(X · L_N) = Ber(X)
  -- 3. Strip Δ_M from left: Ber(Δ_M · X) = Ber(Δ_M) · Ber(X)
  -- 4. Strip Δ_N from right: Ber(X · Δ_N) = Ber(X) · Ber(Δ_N)
  -- 5. Strip L_M from left: Ber(L_M · X) = Ber(X)
  -- 6. Strip U_N from left: Ber(U_N · X) = Ber(X) (or use ber_UDL)
  --
  -- After stripping: Ber(MN) = Ber(Δ_M) · Ber(L_M · U_N) · Ber(Δ_N)
  --                          = Ber(Δ_M) · 1 · Ber(Δ_N)  (since L_M · U_N has Ber = 1)
  --                          = Ber(M) · Ber(N)
  --
  -- The key fact: Ber(L_M · U_N) = 1
  -- L_M · U_N = [I 0; C_M I] · [I B_N; 0 I] = [I B_N; C_M I + C_M·B_N]
  -- Ber = det(I - B_N · (I + C_M·B_N)⁻¹ · C_M) / det(I + C_M·B_N)
  --
  -- Using the identity det(I - XY) = det(I - YX) for matrices of compatible sizes,
  -- and the Grassmann identity det(I - BC) · det(I - CB) = 1 for odd B, C.
  --
  -- Define factorization components:
  let B_M := M.Bblock * M.Dblock⁻¹  -- odd
  let C_M := M.Dblock⁻¹ * M.Cblock  -- odd
  let S_M := schurComplementD M hMD
  let U_M := SuperMatrix.upperTriangular B_M h1 h0even h0odd hBDinvM
  let Δ_M := SuperMatrix.diagonal S_M M.Dblock h0odd hSchurM M.Dblock_even
  let L_M := SuperMatrix.lowerTriangular C_M h1 h0even h0odd hDinvCM

  let B_N := N.Bblock * N.Dblock⁻¹  -- odd
  let C_N := N.Dblock⁻¹ * N.Cblock  -- odd
  let S_N := schurComplementD N hND
  let U_N := SuperMatrix.upperTriangular B_N h1 h0even h0odd hBDinvN
  let Δ_N := SuperMatrix.diagonal S_N N.Dblock h0odd hSchurN N.Dblock_even
  let L_N := SuperMatrix.lowerTriangular C_N h1 h0even h0odd hDinvCN

  -- UDL factorizations
  have hM_UDL : M = (U_M * Δ_M) * L_M :=
    SuperMatrix.UDL_factorization M hMD h1 h0even h0odd hBDinvM hDinvCM hSchurM
  have hN_UDL : N = (U_N * Δ_N) * L_N :=
    SuperMatrix.UDL_factorization N hND h1 h0even h0odd hBDinvN hDinvCN hSchurN

  -- The proof proceeds by stripping factors:
  --
  -- MN = U_M · Δ_M · L_M · U_N · Δ_N · L_N
  --
  -- Step 1: Strip U_M from left: Ber(U_M · X) = Ber(X)
  --         Ber(MN) = Ber(Δ_M · L_M · U_N · Δ_N · L_N)
  --
  -- Step 2: Strip L_N from right: Ber(X · L_N) = Ber(X)
  --         Ber(MN) = Ber(Δ_M · L_M · U_N · Δ_N)
  --
  -- Step 3: Strip Δ_M from left: Ber(Δ_M · X) = Ber(Δ_M) · Ber(X)
  --         Ber(MN) = Ber(Δ_M) · Ber(L_M · U_N · Δ_N)
  --
  -- Step 4: Strip L_M from left: Ber(L_M · X) = Ber(X)
  --         Ber(MN) = Ber(Δ_M) · Ber(U_N · Δ_N)
  --
  -- Step 5: Strip U_N from left: Ber(U_N · X) = Ber(X)
  --         Ber(MN) = Ber(Δ_M) · Ber(Δ_N)
  --
  -- Step 6: Use Ber(M) = Ber(Δ_M) and Ber(N) = Ber(Δ_N) (from ber_UDL)
  --         Ber(MN) = Ber(M) · Ber(N)
  --
  -- The stripping lemmas used:
  -- - ber_mul_upperTriangular_left: Ber(U · X) = Ber(X) for upper triangular U
  -- - ber_mul_lowerTriangular_right: Ber(X · L) = Ber(X) for lower triangular L
  -- - ber_mul_lowerTriangular_left: Ber(L · X) = Ber(X) for lower triangular L
  -- - ber_mul_diagonal_left: Ber(Δ · X) = Ber(Δ) · Ber(X) for diagonal Δ
  -- - ber_UDL: Ber(U · Δ · L) = Ber(Δ)

  -- ═══════════════════════════════════════════════════════════════════════════
  -- STEP 0: Establish basic determinant conditions for the triangular/diagonal matrices
  -- ═══════════════════════════════════════════════════════════════════════════

  -- U_M.Dblock = I, so det = 1 ≠ 0
  have hU_M_D : U_M.Dblock.det ≠ 0 := by
    show (SuperMatrix.upperTriangular B_M h1 h0even h0odd hBDinvM).Dblock.det ≠ 0
    simp only [SuperMatrix.upperTriangular]
    rw [Matrix.det_one]
    exact one_ne_zero

  -- L_M.Dblock = I, so det = 1 ≠ 0
  have hL_M_D : L_M.Dblock.det ≠ 0 := by
    show (SuperMatrix.lowerTriangular C_M h1 h0even h0odd hDinvCM).Dblock.det ≠ 0
    simp only [SuperMatrix.lowerTriangular]
    rw [Matrix.det_one]
    exact one_ne_zero

  -- Δ_M.Dblock = M.Dblock, so det ≠ 0 by assumption
  have hΔ_M_D : Δ_M.Dblock.det ≠ 0 := by
    show (SuperMatrix.diagonal S_M M.Dblock h0odd hSchurM M.Dblock_even).Dblock.det ≠ 0
    simp only [SuperMatrix.diagonal]
    exact hMD

  -- U_N.Dblock = I, so det = 1 ≠ 0
  have hU_N_D : U_N.Dblock.det ≠ 0 := by
    show (SuperMatrix.upperTriangular B_N h1 h0even h0odd hBDinvN).Dblock.det ≠ 0
    simp only [SuperMatrix.upperTriangular]
    rw [Matrix.det_one]
    exact one_ne_zero

  -- L_N.Dblock = I, so det = 1 ≠ 0
  have hL_N_D : L_N.Dblock.det ≠ 0 := by
    show (SuperMatrix.lowerTriangular C_N h1 h0even h0odd hDinvCN).Dblock.det ≠ 0
    simp only [SuperMatrix.lowerTriangular]
    rw [Matrix.det_one]
    exact one_ne_zero

  -- Δ_N.Dblock = N.Dblock, so det ≠ 0 by assumption
  have hΔ_N_D : Δ_N.Dblock.det ≠ 0 := by
    show (SuperMatrix.diagonal S_N N.Dblock h0odd hSchurN N.Dblock_even).Dblock.det ≠ 0
    simp only [SuperMatrix.diagonal]
    exact hND

  -- ═══════════════════════════════════════════════════════════════════════════
  -- STEP 1: Relate Ber(M) and Ber(N) to Ber(Δ_M) and Ber(Δ_N) via ber_UDL
  -- ═══════════════════════════════════════════════════════════════════════════

  -- Δ_M · L_M has Dblock = M.Dblock
  have hΔL_M_D : (Δ_M * L_M).Dblock.det ≠ 0 := by
    have : (Δ_M * L_M).Dblock = M.Dblock := by
      show (SuperMatrix.diagonal S_M M.Dblock h0odd hSchurM M.Dblock_even *
            SuperMatrix.lowerTriangular C_M h1 h0even h0odd hDinvCM).Dblock = M.Dblock
      simp only [SuperMatrix.mul_Dblock, SuperMatrix.diagonal, SuperMatrix.lowerTriangular]
      simp only [Matrix.zero_mul, Matrix.mul_one, zero_add]
    rw [this]
    exact hMD

  -- U_M · (Δ_M · L_M) has Dblock = M.Dblock (since U_M.C = 0, U_M.D = I)
  have hUΔL_M_D : (U_M * (Δ_M * L_M)).Dblock.det ≠ 0 := by
    have : (U_M * (Δ_M * L_M)).Dblock = M.Dblock := by
      show (SuperMatrix.upperTriangular B_M h1 h0even h0odd hBDinvM *
            (SuperMatrix.diagonal S_M M.Dblock h0odd hSchurM M.Dblock_even *
             SuperMatrix.lowerTriangular C_M h1 h0even h0odd hDinvCM)).Dblock = M.Dblock
      simp only [SuperMatrix.mul_Dblock]
      -- U_M.C = 0, U_M.D = I
      simp only [SuperMatrix.upperTriangular]
      simp only [Matrix.zero_mul, zero_add, Matrix.one_mul]
      -- (Δ_M * L_M).D = M.D
      simp only [SuperMatrix.diagonal, SuperMatrix.lowerTriangular]
      simp only [Matrix.zero_mul, Matrix.mul_one, zero_add]
    rw [this]
    exact hMD

  -- Ber(M) = Ber(Δ_M) by ber_UDL
  have hBerM_eq : M.ber hMD = Δ_M.ber hΔ_M_D := by
    -- Since M = U_M * Δ_M * L_M, and ber_UDL says Ber(U * Δ * L) = Ber(Δ)
    have hUDL := SuperMatrix.ber_UDL B_M S_M M.Dblock C_M h1 h0even h0odd hBDinvM hSchurM
             M.Dblock_even hDinvCM hMD hU_M_D hΔ_M_D hL_M_D hΔL_M_D hUΔL_M_D
    -- We have M = U_M * Δ_M * L_M = U_M * (Δ_M * L_M)
    have hM_eq2 : M = U_M * (Δ_M * L_M) := by rw [hM_UDL]; exact mul_assoc U_M Δ_M L_M
    -- Substitute M with U_M * (Δ_M * L_M) and use proof irrelevance for the det condition
    calc M.ber hMD
        = (U_M * (Δ_M * L_M)).ber (by rw [← hM_eq2]; exact hMD) := by congr 1
      _ = (U_M * (Δ_M * L_M)).ber hUΔL_M_D := rfl
      _ = Δ_M.ber hΔ_M_D := hUDL

  -- Similarly for N: Δ_N · L_N has Dblock = N.Dblock
  have hΔL_N_D : (Δ_N * L_N).Dblock.det ≠ 0 := by
    have : (Δ_N * L_N).Dblock = N.Dblock := by
      show (SuperMatrix.diagonal S_N N.Dblock h0odd hSchurN N.Dblock_even *
            SuperMatrix.lowerTriangular C_N h1 h0even h0odd hDinvCN).Dblock = N.Dblock
      simp only [SuperMatrix.mul_Dblock, SuperMatrix.diagonal, SuperMatrix.lowerTriangular]
      simp only [Matrix.zero_mul, Matrix.mul_one, zero_add]
    rw [this]
    exact hND

  have hUΔL_N_D : (U_N * (Δ_N * L_N)).Dblock.det ≠ 0 := by
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

  -- ═══════════════════════════════════════════════════════════════════════════
  -- STEP 2: Rewrite MN using UDL factorizations and establish intermediate det conditions
  -- ═══════════════════════════════════════════════════════════════════════════

  -- MN = (U_M * Δ_M * L_M) * (U_N * Δ_N * L_N) = U_M * (Δ_M * L_M * U_N * Δ_N) * L_N
  have hMN_eq : M * N = U_M * (Δ_M * (L_M * (U_N * (Δ_N * L_N)))) := by
    rw [hM_UDL, hN_UDL]
    simp only [mul_assoc]

  -- For stripping, we need det conditions on various intermediate products.
  -- Key fact: For products of triangular matrices, the D-block structure is preserved.

  -- The innermost product U_N * (Δ_N * L_N) = N, so it has Dblock.det = N.D.det ≠ 0
  have hUΔL_N : (U_N * (Δ_N * L_N)).Dblock.det ≠ 0 := hUΔL_N_D

  -- ═══════════════════════════════════════════════════════════════════════════
  -- STEP 3: Apply stripping lemmas
  -- ═══════════════════════════════════════════════════════════════════════════

  -- We proceed by showing: Ber(MN) = Ber(Δ_M) * Ber(Δ_N)

  -- First, use the UDL factorizations to rewrite M and N
  -- Then apply stripping in sequence

  -- Alternative approach: Use ber_UDL for MN directly
  -- MN = U_M * Δ_M * L_M * U_N * Δ_N * L_N
  -- We can try to show this equals some U' * Δ' * L' form

  -- Simpler approach: work step by step with stripping lemmas

  -- Start: Ber(M * N)
  -- = Ber(U_M * Δ_M * L_M * U_N * Δ_N * L_N)

  -- Step 1: Strip U_M from left
  -- Ber(U_M * X) = Ber(X) where X = Δ_M * L_M * U_N * Δ_N * L_N

  -- For this we need X.Dblock.det ≠ 0

  -- Let's define the intermediate products and their det conditions
  let X₁ := Δ_N * L_N  -- = Δ_N * L_N
  let X₂ := U_N * X₁   -- = U_N * Δ_N * L_N
  let X₃ := L_M * X₂   -- = L_M * U_N * Δ_N * L_N
  let X₄ := Δ_M * X₃   -- = Δ_M * L_M * U_N * Δ_N * L_N
  let X₅ := U_M * X₄   -- = U_M * Δ_M * L_M * U_N * Δ_N * L_N = M * N

  -- X₁.D = N.D (since Δ_N.D = N.D and L_N.D = I)
  have hX₁_D : X₁.Dblock.det ≠ 0 := by
    show (Δ_N * L_N).Dblock.det ≠ 0
    exact hΔL_N_D

  -- X₂.D = N.D (since U_N.C = 0, U_N.D = I)
  have hX₂_D : X₂.Dblock.det ≠ 0 := by
    show (U_N * (Δ_N * L_N)).Dblock.det ≠ 0
    exact hUΔL_N_D

  -- X₃.D = L_M.C * X₂.B + L_M.D * X₂.D = C_M * X₂.B + X₂.D
  -- X₂ = U_N * Δ_N * L_N = N, so X₂.B = N.B, X₂.D = N.D
  -- X₃.D = C_M * N.B + N.D

  -- The key insight: N.D is invertible (det ≠ 0), and C_M * N.B is nilpotent
  -- (since C_M odd, N.B odd, so C_M * N.B even nilpotent)
  -- Therefore det(C_M * N.B + N.D) ≠ 0

  have hX₃_D : X₃.Dblock.det ≠ 0 := by
    -- X₃ = L_M * X₂ where X₂ = N
    -- The key observation: X₅ = M * N, so X₅.D = (M * N).D, which has det ≠ 0 by hMND.
    -- And X₅.D = X₄.D (since U_M strips without changing D), X₄.D = M.D * X₃.D
    -- So det(M.D) * det(X₃.D) = det(X₅.D) = det((M*N).D) ≠ 0
    -- Since det(M.D) ≠ 0, we get det(X₃.D) ≠ 0.
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
    -- X₅ = M * N, so X₅.D = (M * N).D
    have hX₅_eq : X₅ = M * N := by
      show U_M * (Δ_M * (L_M * (U_N * (Δ_N * L_N)))) = M * N
      rw [hM_UDL, hN_UDL]
      simp only [mul_assoc]
    have hX₅_D_eq2 : X₅.Dblock = (M * N).Dblock := by rw [hX₅_eq]
    -- det(X₅.D) = det(M.D * X₃.D) = det(M.D) * det(X₃.D)
    -- det((M*N).D) ≠ 0, and X₅.D = (M*N).D, so det(X₅.D) ≠ 0
    -- det(X₅.D) = det(M.D * X₃.D) = det(M.D) * det(X₃.D) ≠ 0
    -- Since det(M.D) ≠ 0, we get det(X₃.D) ≠ 0
    have hX₅_det : X₅.Dblock.det ≠ 0 := by rw [hX₅_D_eq2]; exact hMND
    rw [hX₅_D_eq, Matrix.det_mul] at hX₅_det
    exact (mul_ne_zero_iff.mp hX₅_det).2

  -- X₄.D = Δ_M.C * X₃.B + Δ_M.D * X₃.D = 0 * X₃.B + M.D * X₃.D = M.D * X₃.D
  have hX₄_D : X₄.Dblock.det ≠ 0 := by
    -- Δ_M.C = 0, Δ_M.D = M.D
    -- X₄.D = M.D * X₃.D
    -- det(M.D * X₃.D) = det(M.D) * det(X₃.D) ≠ 0
    have hX₄_D_eq : X₄.Dblock = M.Dblock * X₃.Dblock := by
      show (Δ_M * X₃).Dblock = M.Dblock * X₃.Dblock
      simp only [SuperMatrix.mul_Dblock]
      show (SuperMatrix.diagonal S_M M.Dblock h0odd hSchurM M.Dblock_even).Cblock * X₃.Bblock +
           (SuperMatrix.diagonal S_M M.Dblock h0odd hSchurM M.Dblock_even).Dblock * X₃.Dblock =
           M.Dblock * X₃.Dblock
      simp only [SuperMatrix.diagonal, Matrix.zero_mul, zero_add]
    rw [hX₄_D_eq, Matrix.det_mul]
    exact mul_ne_zero hMD hX₃_D

  -- X₅.D = U_M.C * X₄.B + U_M.D * X₄.D = 0 * X₄.B + I * X₄.D = X₄.D
  have hX₅_D : X₅.Dblock.det ≠ 0 := by
    -- U_M.C = 0, U_M.D = I
    -- X₅.D = X₄.D
    have hX₅_D_eq : X₅.Dblock = X₄.Dblock := by
      show (U_M * X₄).Dblock = X₄.Dblock
      simp only [SuperMatrix.mul_Dblock]
      show (SuperMatrix.upperTriangular B_M h1 h0even h0odd hBDinvM).Cblock * X₄.Bblock +
           (SuperMatrix.upperTriangular B_M h1 h0even h0odd hBDinvM).Dblock * X₄.Dblock =
           X₄.Dblock
      simp only [SuperMatrix.upperTriangular, Matrix.zero_mul, zero_add, Matrix.one_mul]
    rw [hX₅_D_eq]
    exact hX₄_D

  -- Now we need to verify X₅ = M * N
  have hX₅_eq_MN : X₅ = M * N := by
    show U_M * (Δ_M * (L_M * (U_N * (Δ_N * L_N)))) = M * N
    rw [hM_UDL, hN_UDL]
    simp only [mul_assoc]

  -- Strip U_M from left: Ber(U_M * X₄) = Ber(X₄)
  have hStrip_U_M : X₅.ber hX₅_D = X₄.ber hX₄_D := by
    show (U_M * X₄).ber hX₅_D = X₄.ber hX₄_D
    exact SuperMatrix.ber_mul_upperTriangular_left B_M X₄ h1 h0even h0odd hBDinvM hX₄_D hU_M_D hX₅_D

  -- Strip Δ_M from left: Ber(Δ_M * X₃) = Ber(Δ_M) * Ber(X₃)
  have hStrip_Δ_M : X₄.ber hX₄_D = Δ_M.ber hΔ_M_D * X₃.ber hX₃_D := by
    show (Δ_M * X₃).ber hX₄_D = Δ_M.ber hΔ_M_D * X₃.ber hX₃_D
    exact SuperMatrix.ber_mul_diagonal_left S_M M.Dblock X₃ h0odd hSchurM M.Dblock_even
          hMD hX₃_D hΔ_M_D hX₄_D

  -- Strip L_M from left: Ber(L_M * X₂) = Ber(X₂)
  -- This requires showing that L_M * X₂ satisfies the conditions for ber_mul_lowerTriangular_left
  have hStrip_L_M : X₃.ber hX₃_D = X₂.ber hX₂_D := by
    show (L_M * X₂).ber hX₃_D = X₂.ber hX₂_D
    -- Need: X₂.Bblock * X₂.Dblock⁻¹ is odd
    --       X₂.Dblock⁻¹ * X₂.Cblock is odd
    --       schurComplementD X₂ is even
    -- X₂ = U_N * Δ_N * L_N = N
    -- So we need the conditions for N, which are given by hBDinvN, hDinvCN, hSchurN
    -- But X₂ is the matrix, not N. We need to show X₂ = N as matrices.
    have hX₂_eq_N : X₂ = N := by
      show U_N * (Δ_N * L_N) = N
      rw [← mul_assoc, hN_UDL]
    -- Now use ber_mul_lowerTriangular_left
    -- We need to cast the hypotheses
    have hX₂_BDinv : ∀ i j, (X₂.Bblock * X₂.Dblock⁻¹) i j ∈ A.odd := by
      rw [hX₂_eq_N]
      exact hBDinvN
    have hX₂_DinvC : ∀ i j, (X₂.Dblock⁻¹ * X₂.Cblock) i j ∈ A.odd := by
      rw [hX₂_eq_N]
      exact hDinvCN
    have hX₂_Schur : ∀ i j, (schurComplementD X₂ hX₂_D) i j ∈ A.even := by
      -- schurComplementD X₂ = schurComplementD N (the matrix blocks are equal)
      -- schurComplementD M hD = M.A - M.B * M.D⁻¹ * M.C only depends on the blocks
      intro i j
      -- X₂ = N, so X₂.Ablock = N.Ablock, X₂.Bblock = N.Bblock, etc.
      have hA : X₂.Ablock = N.Ablock := by rw [hX₂_eq_N]
      have hB : X₂.Bblock = N.Bblock := by rw [hX₂_eq_N]
      have hC : X₂.Cblock = N.Cblock := by rw [hX₂_eq_N]
      have hD : X₂.Dblock = N.Dblock := by rw [hX₂_eq_N]
      -- schurComplementD X₂ = X₂.A - X₂.B * X₂.D⁻¹ * X₂.C = N.A - N.B * N.D⁻¹ * N.C
      unfold schurComplementD
      simp only [hA, hB, hC, hD]
      exact hSchurN i j
    exact SuperMatrix.ber_mul_lowerTriangular_left C_M X₂ h1 h0even h0odd hDinvCM
          hX₂_D hL_M_D hX₃_D hX₂_BDinv hX₂_DinvC hX₂_Schur

  -- Strip U_N from left: Ber(U_N * X₁) = Ber(X₁)
  have hStrip_U_N : X₂.ber hX₂_D = X₁.ber hX₁_D := by
    show (U_N * X₁).ber hX₂_D = X₁.ber hX₁_D
    exact SuperMatrix.ber_mul_upperTriangular_left B_N X₁ h1 h0even h0odd hBDinvN hX₁_D hU_N_D hX₂_D

  -- X₁ = Δ_N * L_N, Ber(X₁) = Ber(Δ_N) by diagonal-lower stripping
  -- Actually Ber(Δ_N * L_N) = Ber(Δ_N) since L_N just multiplies on right
  have hX₁_ber : X₁.ber hX₁_D = Δ_N.ber hΔ_N_D := by
    show (Δ_N * L_N).ber hX₁_D = Δ_N.ber hΔ_N_D
    -- Use ber_mul_lowerTriangular_right
    exact SuperMatrix.ber_mul_lowerTriangular_right Δ_N C_N h1 h0even h0odd hDinvCN
          hΔ_N_D hL_N_D hX₁_D

  -- ═══════════════════════════════════════════════════════════════════════════
  -- STEP 4: Chain the equalities
  -- ═══════════════════════════════════════════════════════════════════════════

  -- Need to reconcile hX₅_D with hMND
  have hMN_D_eq : (M * N).Dblock.det ≠ 0 := hMND

  -- X₅ = M * N, so we can convert
  calc (M * N).ber hMND
      = X₅.ber hX₅_D := by congr 1
    _ = X₄.ber hX₄_D := hStrip_U_M
    _ = Δ_M.ber hΔ_M_D * X₃.ber hX₃_D := hStrip_Δ_M
    _ = Δ_M.ber hΔ_M_D * X₂.ber hX₂_D := by rw [hStrip_L_M]
    _ = Δ_M.ber hΔ_M_D * X₁.ber hX₁_D := by rw [hStrip_U_N]
    _ = Δ_M.ber hΔ_M_D * Δ_N.ber hΔ_N_D := by rw [hX₁_ber]
    _ = M.ber hMD * N.ber hND := by rw [← hBerM_eq, ← hBerN_eq]

end Supermanifolds.Helpers
