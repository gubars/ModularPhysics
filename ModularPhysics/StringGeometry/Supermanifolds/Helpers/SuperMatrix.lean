import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import ModularPhysics.StringGeometry.Supermanifolds.Superalgebra

/-!
# SuperMatrix Definition and Basic Operations

This file defines the supermatrix structure and its basic operations.

## Main definitions

* `SuperMatrix` - A 2×2 block matrix over a superalgebra with proper grading:
  - A, D blocks have entries in the EVEN part
  - B, C blocks have entries in the ODD part
* `SuperMatrix.mul` - Multiplication of supermatrices
* `SuperMatrix.id` - Identity supermatrix

## Mathematical Background

For a supermatrix M = [A B; C D] over a superalgebra Λ = Λ₀ ⊕ Λ₁:
- A (n×n) and D (m×m) have entries in Λ₀ (even/bosonic)
- B (n×m) and C (m×n) have entries in Λ₁ (odd/fermionic)

The key property is that odd elements anticommute: for θ, η ∈ Λ₁, θη = -ηθ.
-/

namespace Supermanifolds.Helpers

open Supermanifolds

/-- A supermatrix over a FieldSuperAlgebra A with proper ℤ/2-grading.

    For M = [A B; C D]:
    - A, D blocks have entries in A.even (bosonic/commuting)
    - B, C blocks have entries in A.odd (fermionic/anticommuting)

    The odd entries anticommute: for θ, η ∈ A.odd, θη = -ηθ.
    This is essential for Berezinian multiplicativity.

    We use FieldSuperAlgebra (where the carrier IS a field) instead of SuperAlgebra
    with a separate [Field A.carrier] hypothesis to avoid typeclass diamonds. -/
structure SuperMatrix {R : Type*} [CommRing R] (A : FieldSuperAlgebra R) (n m : ℕ) where
  /-- Even-even block (n×n) with entries in A.even -/
  Ablock : Matrix (Fin n) (Fin n) A.carrier
  /-- Even-odd block (n×m) with entries in A.odd -/
  Bblock : Matrix (Fin n) (Fin m) A.carrier
  /-- Odd-even block (m×n) with entries in A.odd -/
  Cblock : Matrix (Fin m) (Fin n) A.carrier
  /-- Odd-odd block (m×m) with entries in A.even -/
  Dblock : Matrix (Fin m) (Fin m) A.carrier
  /-- A block has even entries -/
  Ablock_even : ∀ i j, Ablock i j ∈ A.even
  /-- B block has odd entries -/
  Bblock_odd : ∀ i j, Bblock i j ∈ A.odd
  /-- C block has odd entries -/
  Cblock_odd : ∀ i j, Cblock i j ∈ A.odd
  /-- D block has even entries -/
  Dblock_even : ∀ i j, Dblock i j ∈ A.even

namespace SuperMatrix

variable {R : Type*} [CommRing R] {A : FieldSuperAlgebra R} {n m : ℕ}

/-- Extensionality for SuperMatrix -/
@[ext]
theorem ext {M N : SuperMatrix A n m}
    (hA : M.Ablock = N.Ablock) (hB : M.Bblock = N.Bblock)
    (hC : M.Cblock = N.Cblock) (hD : M.Dblock = N.Dblock) : M = N := by
  cases M; cases N
  simp only [mk.injEq]
  exact ⟨hA, hB, hC, hD⟩

/-- Convert to a full matrix over A.carrier -/
def toMatrix (M : SuperMatrix A n m) : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) A.carrier :=
  Matrix.fromBlocks M.Ablock M.Bblock M.Cblock M.Dblock

/-- The identity supermatrix (requires 1 ∈ A.even and 0 ∈ A.even ∩ A.odd) -/
noncomputable def id (h1 : (1 : A.carrier) ∈ A.even)
    (h0even : (0 : A.carrier) ∈ A.even) (h0odd : (0 : A.carrier) ∈ A.odd) :
    SuperMatrix A n m :=
  ⟨1, 0, 0, 1,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even],
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   fun _ _ => by simp only [Matrix.zero_apply]; exact h0odd,
   fun i j => by simp only [Matrix.one_apply]; split_ifs <;> [exact h1; exact h0even]⟩

/-- Multiplication of supermatrices preserves the grading structure.

    For M = [A₁ B₁; C₁ D₁] and N = [A₂ B₂; C₂ D₂]:
    MN = [A₁A₂ + B₁C₂,  A₁B₂ + B₁D₂;
          C₁A₂ + D₁C₂,  C₁B₂ + D₁D₂]

    The grading works out because:
    - A₁A₂: even × even = even ✓
    - B₁C₂: odd × odd = even ✓  (so A₁A₂ + B₁C₂ ∈ even)
    - A₁B₂: even × odd = odd ✓
    - B₁D₂: odd × even = odd ✓  (so A₁B₂ + B₁D₂ ∈ odd)
    - C₁A₂: odd × even = odd ✓
    - D₁C₂: even × odd = odd ✓  (so C₁A₂ + D₁C₂ ∈ odd)
    - C₁B₂: odd × odd = even ✓
    - D₁D₂: even × even = even ✓  (so C₁B₂ + D₁D₂ ∈ even) -/
noncomputable def mul (M N : SuperMatrix A n m) : SuperMatrix A n m :=
  ⟨M.Ablock * N.Ablock + M.Bblock * N.Cblock,
   M.Ablock * N.Bblock + M.Bblock * N.Dblock,
   M.Cblock * N.Ablock + M.Dblock * N.Cblock,
   M.Cblock * N.Bblock + M.Dblock * N.Dblock,
   -- (MN).A ∈ even: A₁A₂ ∈ even (even×even), B₁C₂ ∈ even (odd×odd)
   fun i j => by
     simp only [Matrix.add_apply, Matrix.mul_apply]
     -- Sum of (even×even) + (odd×odd) terms, both in A.even
     apply A.even.add_mem
     · -- A₁A₂ term: sum of products of even elements
       apply A.even.sum_mem
       intro k _
       exact A.even_mul_even _ _ (M.Ablock_even i k) (N.Ablock_even k j)
     · -- B₁C₂ term: sum of products of odd elements
       apply A.even.sum_mem
       intro k _
       exact A.odd_mul_odd _ _ (M.Bblock_odd i k) (N.Cblock_odd k j),
   -- (MN).B ∈ odd: A₁B₂ ∈ odd (even×odd), B₁D₂ ∈ odd (odd×even)
   fun i j => by
     simp only [Matrix.add_apply, Matrix.mul_apply]
     apply A.odd.add_mem
     · apply A.odd.sum_mem
       intro k _
       exact A.even_mul_odd _ _ (M.Ablock_even i k) (N.Bblock_odd k j)
     · apply A.odd.sum_mem
       intro k _
       exact A.odd_mul_even _ _ (M.Bblock_odd i k) (N.Dblock_even k j),
   -- (MN).C ∈ odd: C₁A₂ ∈ odd (odd×even), D₁C₂ ∈ odd (even×odd)
   fun i j => by
     simp only [Matrix.add_apply, Matrix.mul_apply]
     apply A.odd.add_mem
     · apply A.odd.sum_mem
       intro k _
       exact A.odd_mul_even _ _ (M.Cblock_odd i k) (N.Ablock_even k j)
     · apply A.odd.sum_mem
       intro k _
       exact A.even_mul_odd _ _ (M.Dblock_even i k) (N.Cblock_odd k j),
   -- (MN).D ∈ even: C₁B₂ ∈ even (odd×odd), D₁D₂ ∈ even (even×even)
   fun i j => by
     simp only [Matrix.add_apply, Matrix.mul_apply]
     apply A.even.add_mem
     · apply A.even.sum_mem
       intro k _
       exact A.odd_mul_odd _ _ (M.Cblock_odd i k) (N.Bblock_odd k j)
     · apply A.even.sum_mem
       intro k _
       exact A.even_mul_even _ _ (M.Dblock_even i k) (N.Dblock_even k j)⟩

noncomputable instance : Mul (SuperMatrix A n m) := ⟨mul⟩

-- Simp lemmas for block access in products
@[simp] theorem mul_Ablock (M N : SuperMatrix A n m) :
    (M * N).Ablock = M.Ablock * N.Ablock + M.Bblock * N.Cblock := rfl
@[simp] theorem mul_Bblock (M N : SuperMatrix A n m) :
    (M * N).Bblock = M.Ablock * N.Bblock + M.Bblock * N.Dblock := rfl
@[simp] theorem mul_Cblock (M N : SuperMatrix A n m) :
    (M * N).Cblock = M.Cblock * N.Ablock + M.Dblock * N.Cblock := rfl
@[simp] theorem mul_Dblock (M N : SuperMatrix A n m) :
    (M * N).Dblock = M.Cblock * N.Bblock + M.Dblock * N.Dblock := rfl

/-- SuperMatrix multiplication is associative.
    Follows from matrix multiplication associativity: (AB)C = A(BC). -/
theorem mul_assoc (M N P : SuperMatrix A n m) : (M * N) * P = M * (N * P) := by
  -- Show block-by-block equality using matrix associativity lemmas
  have hA : ((M * N) * P).Ablock = (M * (N * P)).Ablock := by
    show (M.Ablock * N.Ablock + M.Bblock * N.Cblock) * P.Ablock +
         (M.Ablock * N.Bblock + M.Bblock * N.Dblock) * P.Cblock =
         M.Ablock * (N.Ablock * P.Ablock + N.Bblock * P.Cblock) +
         M.Bblock * (N.Cblock * P.Ablock + N.Dblock * P.Cblock)
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    simp only [Matrix.mul_assoc]
    abel
  have hB : ((M * N) * P).Bblock = (M * (N * P)).Bblock := by
    show (M.Ablock * N.Ablock + M.Bblock * N.Cblock) * P.Bblock +
         (M.Ablock * N.Bblock + M.Bblock * N.Dblock) * P.Dblock =
         M.Ablock * (N.Ablock * P.Bblock + N.Bblock * P.Dblock) +
         M.Bblock * (N.Cblock * P.Bblock + N.Dblock * P.Dblock)
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    simp only [Matrix.mul_assoc]
    abel
  have hC : ((M * N) * P).Cblock = (M * (N * P)).Cblock := by
    show (M.Cblock * N.Ablock + M.Dblock * N.Cblock) * P.Ablock +
         (M.Cblock * N.Bblock + M.Dblock * N.Dblock) * P.Cblock =
         M.Cblock * (N.Ablock * P.Ablock + N.Bblock * P.Cblock) +
         M.Dblock * (N.Cblock * P.Ablock + N.Dblock * P.Cblock)
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    simp only [Matrix.mul_assoc]
    abel
  have hD : ((M * N) * P).Dblock = (M * (N * P)).Dblock := by
    show (M.Cblock * N.Ablock + M.Dblock * N.Cblock) * P.Bblock +
         (M.Cblock * N.Bblock + M.Dblock * N.Dblock) * P.Dblock =
         M.Cblock * (N.Ablock * P.Bblock + N.Bblock * P.Dblock) +
         M.Dblock * (N.Cblock * P.Bblock + N.Dblock * P.Dblock)
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    simp only [Matrix.mul_assoc]
    abel
  exact ext hA hB hC hD

/-- Multiplication corresponds to matrix multiplication -/
theorem toMatrix_mul (M N : SuperMatrix A n m) :
    (M * N).toMatrix = M.toMatrix * N.toMatrix := by
  unfold toMatrix
  conv_rhs => rw [Matrix.fromBlocks_multiply]
  simp only [HMul.hMul, Mul.mul, mul]

end SuperMatrix

end Supermanifolds.Helpers
