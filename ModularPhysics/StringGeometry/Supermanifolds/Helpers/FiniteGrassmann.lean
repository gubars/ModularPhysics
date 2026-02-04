/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.
-/
import ModularPhysics.StringGeometry.Supermanifolds.Superalgebra
import ModularPhysics.StringGeometry.Supermanifolds.Supermanifolds
import ModularPhysics.StringGeometry.Supermanifolds.SuperJacobian
import ModularPhysics.StringGeometry.Supermanifolds.Helpers.SuperMatrix

/-!
# Finite-Dimensional Grassmann Algebra and Super Jacobian Connection

This file defines the finite-dimensional Grassmann algebra Λ_q with q generators over ℝ,
and provides the infrastructure to connect `SuperJacobian p q` to `SuperMatrix`.

## Mathematical Background

The Grassmann algebra with q generators θ₁, ..., θ_q over ℝ is:
  Λ_q = ∧^*(ℝ^q) = ⊕_{k=0}^q ∧^k(ℝ^q)

As a vector space, dim(Λ_q) = 2^q with basis {θ^I : I ⊆ {1,...,q}}.

The ℤ/2-grading:
- Λ_q^even = span{θ^I : |I| even} - commutative subalgebra
- Λ_q^odd = span{θ^I : |I| odd} - anticommuting subspace

## Structure

For the super Jacobian of a coordinate transformation on ℝ^{p|q}:
1. Entries are in `SuperDomainFunction p q` = C^∞(ℝ^p) ⊗ Λ_q
2. At each point x₀ ∈ ℝ^p, evaluation gives a `SuperMatrix (finiteGrassmannAlgebra q) p q`
3. The Berezinian is computed via `SuperMatrix.ber`

## Main Definitions

* `FiniteGrassmannCarrier q` - The carrier type Λ_q represented as `Finset (Fin q) → ℝ`
* `finiteGrassmannAlgebra q` - The `GrassmannAlgebra ℝ` instance for Λ_q
* `SuperDomainFunction.evalAt` - Evaluate at a point to get a Grassmann element
* `SuperJacobian.toSuperMatrixAt` - Convert to SuperMatrix at a point

## References

* Berezin, F.A. "Introduction to Superanalysis"
* Witten, E. "Notes On Supermanifolds And Integration" (arXiv:1209.2199)
-/

noncomputable section

namespace Supermanifolds.Helpers

open Supermanifolds

/-!
## Carrier Type for Finite Grassmann Algebra

Elements of Λ_q are represented as functions `Finset (Fin q) → ℝ`.
The coefficient at I represents the θ^I component.
-/

/-- The carrier type for the finite Grassmann algebra Λ_q with q generators.
    Elements are functions I ↦ coefficient of θ^I.

    Note: We use `def` instead of `abbrev` to prevent Lean from picking up
    the pointwise multiplication instance from `Pi.instMul`. -/
def FiniteGrassmannCarrier (q : ℕ) := Finset (Fin q) → ℝ

namespace FiniteGrassmannCarrier

variable {q : ℕ}

/-- Evaluate a FiniteGrassmannCarrier at an index set -/
@[reducible]
def eval (f : FiniteGrassmannCarrier q) (I : Finset (Fin q)) : ℝ := f I

/-- Allow function application syntax for evaluation -/
instance : CoeFun (FiniteGrassmannCarrier q) (fun _ => Finset (Fin q) → ℝ) := ⟨id⟩

/-! ### Ring Structure -/

instance : Zero (FiniteGrassmannCarrier q) := ⟨fun _ => 0⟩
instance : One (FiniteGrassmannCarrier q) := ⟨fun I => if I = ∅ then 1 else 0⟩
instance : Add (FiniteGrassmannCarrier q) := ⟨fun f g I => f I + g I⟩
instance : Neg (FiniteGrassmannCarrier q) := ⟨fun f I => -(f I)⟩
instance instSMulReal : SMul ℝ (FiniteGrassmannCarrier q) := ⟨fun c f I => c * f I⟩

@[simp] lemma zero_apply (I : Finset (Fin q)) : (0 : FiniteGrassmannCarrier q) I = 0 := rfl
@[simp] lemma one_apply (I : Finset (Fin q)) : (1 : FiniteGrassmannCarrier q) I = if I = ∅ then 1 else 0 := rfl
@[simp] lemma add_apply (f g : FiniteGrassmannCarrier q) (I : Finset (Fin q)) : (f + g) I = f I + g I := rfl
@[simp] lemma neg_apply (f : FiniteGrassmannCarrier q) (I : Finset (Fin q)) : (-f) I = -(f I) := rfl
@[simp] lemma smul_apply (c : ℝ) (f : FiniteGrassmannCarrier q) (I : Finset (Fin q)) : (c • f) I = c * f I := rfl

/-- AddCommGroup structure on FiniteGrassmannCarrier -/
instance : AddCommGroup (FiniteGrassmannCarrier q) where
  add_assoc := fun _ _ _ => funext fun _ => add_assoc _ _ _
  zero_add := fun _ => funext fun _ => zero_add _
  add_zero := fun _ => funext fun _ => add_zero _
  nsmul := fun n f I => n * f I
  nsmul_zero := fun _ => funext fun _ => by simp
  nsmul_succ := fun n f => funext fun I => by
    -- Goal: (n+1) * f I = (n * f) I + f I
    change (↑(n + 1) : ℝ) * f I = (↑n : ℝ) * f I + f I
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  neg_add_cancel := fun _ => funext fun _ => neg_add_cancel _
  add_comm := fun _ _ => funext fun _ => add_comm _ _
  zsmul := fun n f I => n * f I
  zsmul_zero' := fun _ => funext fun _ => by simp
  zsmul_succ' := fun n f => funext fun I => by
    -- Goal: (n.succ : ℤ) * f I = (n : ℤ) * f I + f I
    change (↑(Int.ofNat (n + 1)) : ℝ) * f I = (↑(Int.ofNat n) : ℝ) * f I + f I
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  zsmul_neg' := fun n f => funext fun I => by
    -- Goal: (Int.negSucc n) * f I = -((n+1) * f I)
    change (↑(Int.negSucc n) : ℝ) * f I = -((↑(Int.ofNat (n + 1)) : ℝ) * f I)
    simp only [Int.cast_negSucc, Int.ofNat_eq_natCast, Int.cast_natCast, neg_mul]

/-- The reorder sign for Grassmann multiplication.
    sign(I, J) = (-1)^{# inversions to merge I and J} if I ∩ J = ∅, else 0. -/
def reorderSign (I J : Finset (Fin q)) : ℤ :=
  if I ∩ J = ∅ then
    (-1 : ℤ) ^ ((I ×ˢ J).filter (fun (p : Fin q × Fin q) => p.2 < p.1)).card
  else 0

/-! ### Helper lemmas for reorderSign -/

/-- reorderSign with empty first set is 1 -/
@[simp]
theorem reorderSign_empty_left (J : Finset (Fin q)) : reorderSign ∅ J = 1 := by
  unfold reorderSign
  simp only [Finset.empty_inter, ↓reduceIte]
  have h : (∅ ×ˢ J).filter (fun p => p.2 < p.1) = ∅ := by
    ext x
    constructor
    · intro hx
      simp only [Finset.mem_filter, Finset.mem_product] at hx
      exact absurd hx.1.1 (Finset.notMem_empty _)
    · intro hx
      exact absurd hx (Finset.notMem_empty _)
  rw [h, Finset.card_empty, pow_zero]

/-- reorderSign with empty second set is 1 -/
@[simp]
theorem reorderSign_empty_right (I : Finset (Fin q)) : reorderSign I ∅ = 1 := by
  unfold reorderSign
  simp only [Finset.inter_empty, ↓reduceIte]
  have h : (I ×ˢ ∅).filter (fun p => p.2 < p.1) = ∅ := by
    ext x
    constructor
    · intro hx
      simp only [Finset.mem_filter, Finset.mem_product] at hx
      exact absurd hx.1.2 (Finset.notMem_empty _)
    · intro hx
      exact absurd hx (Finset.notMem_empty _)
  rw [h, Finset.card_empty, pow_zero]

/-- reorderSign of disjoint sets is ±1 -/
theorem reorderSign_ne_zero_of_disjoint {I J : Finset (Fin q)} (h : I ∩ J = ∅) :
    reorderSign I J ≠ 0 := by
  unfold reorderSign
  simp only [h, ↓reduceIte]
  exact pow_ne_zero _ (by decide : (-1 : ℤ) ≠ 0)

/-- reorderSign is 0 when sets overlap -/
theorem reorderSign_eq_zero_of_overlap {I J : Finset (Fin q)} (h : I ∩ J ≠ ∅) :
    reorderSign I J = 0 := by
  unfold reorderSign
  simp only [h, ↓reduceIte]

/-- Union with empty is identity -/
theorem union_empty_eq (I : Finset (Fin q)) : I ∪ ∅ = I := Finset.union_empty I

/-- Empty union is identity -/
theorem empty_union_eq (J : Finset (Fin q)) : ∅ ∪ J = J := Finset.empty_union J

/-- (-1)^a = (-1)^b when a % 2 = b % 2 -/
theorem neg_one_pow_eq_of_mod_eq {a b : ℕ} (h : a % 2 = b % 2) : (-1 : ℤ) ^ a = (-1 : ℤ) ^ b := by
  have ha := Nat.mod_two_eq_zero_or_one a
  have hb := Nat.mod_two_eq_zero_or_one b
  cases ha with
  | inl ha =>
    have hb' : b % 2 = 0 := by rw [← h, ha]
    have ha_even : Even a := Nat.even_iff.mpr ha
    have hb_even : Even b := Nat.even_iff.mpr hb'
    rw [ha_even.neg_one_pow, hb_even.neg_one_pow]
  | inr ha =>
    have hb' : b % 2 = 1 := by rw [← h, ha]
    have ha_odd : Odd a := Nat.odd_iff.mpr ha
    have hb_odd : Odd b := Nat.odd_iff.mpr hb'
    rw [ha_odd.neg_one_pow, hb_odd.neg_one_pow]

/-- Helper: inversion count for union with first set -/
theorem inversions_union_left (I J L : Finset (Fin q)) :
    ((I ∪ J) ×ˢ L).filter (fun p => p.2 < p.1) =
    ((I ×ˢ L).filter (fun p => p.2 < p.1)) ∪ ((J ×ˢ L).filter (fun p => p.2 < p.1)) := by
  ext ⟨x, l⟩
  constructor
  · intro hx
    simp only [Finset.mem_filter, Finset.mem_product] at hx
    obtain ⟨⟨hxIJ, hlL⟩, hlt⟩ := hx
    rw [Finset.mem_union] at hxIJ
    rw [Finset.mem_union]
    rcases hxIJ with hxI | hxJ
    · left; simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hxI, hlL⟩, hlt⟩
    · right; simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hxJ, hlL⟩, hlt⟩
  · intro hx
    rw [Finset.mem_union] at hx
    simp only [Finset.mem_filter, Finset.mem_product] at hx ⊢
    rcases hx with ⟨⟨hxI, hlL⟩, hlt⟩ | ⟨⟨hxJ, hlL⟩, hlt⟩
    · exact ⟨⟨Finset.mem_union_left J hxI, hlL⟩, hlt⟩
    · exact ⟨⟨Finset.mem_union_right I hxJ, hlL⟩, hlt⟩

/-- Helper: inversion count for union with second set -/
theorem inversions_union_right (I J L : Finset (Fin q)) :
    (I ×ˢ (J ∪ L)).filter (fun p => p.2 < p.1) =
    ((I ×ˢ J).filter (fun p => p.2 < p.1)) ∪ ((I ×ˢ L).filter (fun p => p.2 < p.1)) := by
  ext ⟨i, x⟩
  constructor
  · intro hx
    simp only [Finset.mem_filter, Finset.mem_product] at hx
    obtain ⟨⟨hiI, hxJL⟩, hlt⟩ := hx
    rw [Finset.mem_union] at hxJL
    rw [Finset.mem_union]
    rcases hxJL with hxJ | hxL
    · left; simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hiI, hxJ⟩, hlt⟩
    · right; simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hiI, hxL⟩, hlt⟩
  · intro hx
    rw [Finset.mem_union] at hx
    simp only [Finset.mem_filter, Finset.mem_product] at hx ⊢
    rcases hx with ⟨⟨hiI, hxJ⟩, hlt⟩ | ⟨⟨hiI, hxL⟩, hlt⟩
    · exact ⟨⟨hiI, Finset.mem_union_left L hxJ⟩, hlt⟩
    · exact ⟨⟨hiI, Finset.mem_union_right J hxL⟩, hlt⟩

/-- The cocycle property: sign(I∪J, L) · sign(I, J) = sign(I, J∪L) · sign(J, L)
    for pairwise disjoint I, J, L -/
theorem reorderSign_assoc {I J L : Finset (Fin q)}
    (hIJ : I ∩ J = ∅) (hIL : I ∩ L = ∅) (hJL : J ∩ L = ∅) :
    reorderSign (I ∪ J) L * reorderSign I J = reorderSign I (J ∪ L) * reorderSign J L := by
  -- Both sides equal (-1)^(n_{I,J}^{<} + n_{I,L}^{<} + n_{J,L}^{<})
  unfold reorderSign
  -- Check disjointness conditions
  have h_IUJ_L : (I ∪ J) ∩ L = ∅ := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_inter] at hx
      obtain ⟨hIJ_mem, hL⟩ := hx
      rw [Finset.mem_union] at hIJ_mem
      rcases hIJ_mem with hI | hJ
      · have hmem : x ∈ I ∩ L := Finset.mem_inter.mpr ⟨hI, hL⟩
        rw [hIL] at hmem; exact hmem
      · have hmem : x ∈ J ∩ L := Finset.mem_inter.mpr ⟨hJ, hL⟩
        rw [hJL] at hmem; exact hmem
    · intro hx; exact absurd hx (Finset.notMem_empty x)
  have h_I_JUL : I ∩ (J ∪ L) = ∅ := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_inter] at hx
      obtain ⟨hI, hJL_mem⟩ := hx
      rw [Finset.mem_union] at hJL_mem
      rcases hJL_mem with hJ | hL
      · have hmem : x ∈ I ∩ J := Finset.mem_inter.mpr ⟨hI, hJ⟩
        rw [hIJ] at hmem; exact hmem
      · have hmem : x ∈ I ∩ L := Finset.mem_inter.mpr ⟨hI, hL⟩
        rw [hIL] at hmem; exact hmem
    · intro hx; exact absurd hx (Finset.notMem_empty x)
  simp only [hIJ, hJL, h_IUJ_L, h_I_JUL, ↓reduceIte]
  -- Now both sides are products of (-1)^(card of inversion sets)
  -- LHS = (-1)^|inv(I∪J, L)| * (-1)^|inv(I, J)|
  -- RHS = (-1)^|inv(I, J∪L)| * (-1)^|inv(J, L)|
  -- Using pow_add: (-1)^a * (-1)^b = (-1)^(a+b)
  rw [← pow_add, ← pow_add]
  -- Need: |inv(I∪J, L)| + |inv(I, J)| = |inv(I, J∪L)| + |inv(J, L)|
  -- inv(I∪J, L) = inv(I, L) ∪ inv(J, L) (disjoint)
  -- inv(I, J∪L) = inv(I, J) ∪ inv(I, L) (disjoint)
  -- So: |inv(I,L)| + |inv(J,L)| + |inv(I,J)| = |inv(I,J)| + |inv(I,L)| + |inv(J,L)|
  -- which is trivially equal
  congr 1
  -- Helper sets
  let invIJ := ((I ×ˢ J).filter (fun p => p.2 < p.1))
  let invIL := ((I ×ˢ L).filter (fun p => p.2 < p.1))
  let invJL := ((J ×ˢ L).filter (fun p => p.2 < p.1))
  -- Show inv(I∪J, L) = invIL ∪ invJL
  have hLHS_union : ((I ∪ J) ×ˢ L).filter (fun p => p.2 < p.1) = invIL ∪ invJL :=
    inversions_union_left I J L
  -- Show inv(I, J∪L) = invIJ ∪ invIL
  have hRHS_union : (I ×ˢ (J ∪ L)).filter (fun p => p.2 < p.1) = invIJ ∪ invIL :=
    inversions_union_right I J L
  -- The unions are disjoint (since I ∩ J = ∅ and I ∩ L = ∅ and J ∩ L = ∅)
  have hIL_JL_disjoint : Disjoint invIL invJL := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext ⟨x, l⟩
    constructor
    · intro hx
      rw [Finset.mem_inter] at hx
      obtain ⟨hxIL, hxJL⟩ := hx
      rw [Finset.mem_filter, Finset.mem_product] at hxIL hxJL
      obtain ⟨⟨hxI, _⟩, _⟩ := hxIL
      obtain ⟨⟨hxJ, _⟩, _⟩ := hxJL
      have hmem : x ∈ I ∩ J := Finset.mem_inter.mpr ⟨hxI, hxJ⟩
      rw [hIJ] at hmem
      exact absurd hmem (Finset.notMem_empty _)
    · intro hx; exact absurd hx (Finset.notMem_empty _)
  have hIJ_IL_disjoint : Disjoint invIJ invIL := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext ⟨i, x⟩
    constructor
    · intro hx
      rw [Finset.mem_inter] at hx
      obtain ⟨hxIJ, hxIL⟩ := hx
      rw [Finset.mem_filter, Finset.mem_product] at hxIJ hxIL
      obtain ⟨⟨_, hxJ⟩, _⟩ := hxIJ
      obtain ⟨⟨_, hxL⟩, _⟩ := hxIL
      have hmem : x ∈ J ∩ L := Finset.mem_inter.mpr ⟨hxJ, hxL⟩
      rw [hJL] at hmem
      exact absurd hmem (Finset.notMem_empty _)
    · intro hx; exact absurd hx (Finset.notMem_empty _)
  -- Now compute cardinalities
  rw [hLHS_union, hRHS_union]
  rw [Finset.card_union_of_disjoint hIL_JL_disjoint,
      Finset.card_union_of_disjoint hIJ_IL_disjoint]
  ring

/-- When both |I| and |J| are even, sign(I,J) = sign(J,I) -/
theorem reorderSign_swap_even {I J : Finset (Fin q)} (h : I ∩ J = ∅)
    (hI : I.card % 2 = 0) (_hJ : J.card % 2 = 0) :
    reorderSign J I = reorderSign I J := by
  unfold reorderSign
  have hJI : J ∩ I = ∅ := by rw [Finset.inter_comm]; exact h
  simp only [h, hJI, ↓reduceIte]
  -- Let n1 = #{(i,j) ∈ I×J : j < i}, n2 = #{(j,i) ∈ J×I : i < j}
  let n1 := ((I ×ˢ J).filter (fun p => p.2 < p.1)).card
  let n2 := ((J ×ˢ I).filter (fun p => p.2 < p.1)).card
  -- n2 = #{(i,j) ∈ I×J : i < j} by swapping coordinates
  have hn2_eq : n2 = ((I ×ˢ J).filter (fun p => p.1 < p.2)).card := by
    apply Finset.card_bij (fun ⟨j, i⟩ _ => (i, j))
    · intro ⟨j, i⟩ hmem
      simp only [Finset.mem_filter, Finset.mem_product] at hmem ⊢
      exact ⟨⟨hmem.1.2, hmem.1.1⟩, hmem.2⟩
    · intro ⟨j1, i1⟩ _ ⟨j2, i2⟩ _ heq
      simp only [Prod.mk.injEq] at heq
      exact Prod.ext heq.2 heq.1
    · intro ⟨i, j⟩ hmem
      simp only [Finset.mem_filter, Finset.mem_product] at hmem
      exact ⟨(j, i), by simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hmem.1.2, hmem.1.1⟩, hmem.2⟩, rfl⟩
  -- n1 + #{i<j} = |I|×|J|
  have hsum : n1 + ((I ×ˢ J).filter (fun p => p.1 < p.2)).card = I.card * J.card := by
    have hcover : (I ×ˢ J) = ((I ×ˢ J).filter (fun p => p.2 < p.1)) ∪
                             ((I ×ˢ J).filter (fun p => p.1 < p.2)) := by
      ext ⟨i, j⟩
      simp only [Finset.mem_product, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro ⟨hi, hj⟩
        by_cases hij : j < i
        · left; exact ⟨⟨hi, hj⟩, hij⟩
        · right
          have hne : i ≠ j := by
            intro heq; rw [heq] at hi
            have hmem : j ∈ I ∩ J := Finset.mem_inter.mpr ⟨hi, hj⟩
            rw [h] at hmem; exact absurd hmem (Finset.notMem_empty j)
          exact ⟨⟨hi, hj⟩, lt_of_le_of_ne (Nat.le_of_not_lt hij) hne⟩
      · intro hx; cases hx with | inl h' => exact h'.1 | inr h' => exact h'.1
    have hdisj : Disjoint ((I ×ˢ J).filter (fun p => p.2 < p.1))
                          ((I ×ˢ J).filter (fun p => p.1 < p.2)) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      ext ⟨i, j⟩
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.notMem_empty, iff_false]
      intro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
      exact absurd h1 (not_lt.mpr (le_of_lt h2))
    rw [← Finset.card_union_of_disjoint hdisj, ← hcover, Finset.card_product]
  -- |I|×|J| is even, so n1 % 2 = #{i<j} % 2
  have h_mod : n1 % 2 = ((I ×ˢ J).filter (fun p => p.1 < p.2)).card % 2 := by
    have hN_even : (I.card * J.card) % 2 = 0 := by
      have : Even (I.card * J.card) := Even.mul_right (Nat.even_iff.mpr hI) J.card
      exact Nat.even_iff.mp this
    omega
  -- Now use that (-1)^n2 = (-1)^n1 since n2 = #{i<j} and #{i<j} % 2 = n1 % 2
  calc (-1 : ℤ) ^ n2
      = (-1 : ℤ) ^ ((I ×ˢ J).filter (fun p => p.1 < p.2)).card := by rw [hn2_eq]
    _ = (-1 : ℤ) ^ n1 := neg_one_pow_eq_of_mod_eq h_mod.symm

/-- When both |I| and |J| are odd, sign(J,I) = -sign(I,J) -/
theorem reorderSign_swap_odd {I J : Finset (Fin q)} (h : I ∩ J = ∅)
    (hI : I.card % 2 = 1) (hJ : J.card % 2 = 1) :
    reorderSign J I = -reorderSign I J := by
  unfold reorderSign
  have hJI : J ∩ I = ∅ := by rw [Finset.inter_comm]; exact h
  simp only [h, hJI, ↓reduceIte]
  -- Let n1 = #{(i,j) ∈ I×J : j < i}, n2 = #{(j,i) ∈ J×I : i < j}
  let n1 := ((I ×ˢ J).filter (fun p => p.2 < p.1)).card
  let n2 := ((J ×ˢ I).filter (fun p => p.2 < p.1)).card
  -- n2 = #{(i,j) ∈ I×J : i < j} by swapping coordinates
  have hn2_eq : n2 = ((I ×ˢ J).filter (fun p => p.1 < p.2)).card := by
    apply Finset.card_bij (fun ⟨j, i⟩ _ => (i, j))
    · intro ⟨j, i⟩ hmem
      simp only [Finset.mem_filter, Finset.mem_product] at hmem ⊢
      exact ⟨⟨hmem.1.2, hmem.1.1⟩, hmem.2⟩
    · intro ⟨j1, i1⟩ _ ⟨j2, i2⟩ _ heq
      simp only [Prod.mk.injEq] at heq
      exact Prod.ext heq.2 heq.1
    · intro ⟨i, j⟩ hmem
      simp only [Finset.mem_filter, Finset.mem_product] at hmem
      refine ⟨(j, i), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hmem.1.2, hmem.1.1⟩, hmem.2⟩
  -- n1 + #{i<j} = |I|×|J|
  have hsum : n1 + ((I ×ˢ J).filter (fun p => p.1 < p.2)).card = I.card * J.card := by
    have hcover : (I ×ˢ J) = ((I ×ˢ J).filter (fun p => p.2 < p.1)) ∪
                             ((I ×ˢ J).filter (fun p => p.1 < p.2)) := by
      ext ⟨i, j⟩
      simp only [Finset.mem_product, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro ⟨hi, hj⟩
        by_cases hij : j < i
        · left; exact ⟨⟨hi, hj⟩, hij⟩
        · right
          have hne : i ≠ j := by
            intro heq; rw [heq] at hi
            have hmem : j ∈ I ∩ J := Finset.mem_inter.mpr ⟨hi, hj⟩
            rw [h] at hmem; exact absurd hmem (Finset.notMem_empty j)
          exact ⟨⟨hi, hj⟩, lt_of_le_of_ne (Nat.le_of_not_lt hij) hne⟩
      · intro hx; cases hx with | inl h' => exact h'.1 | inr h' => exact h'.1
    have hdisj : Disjoint ((I ×ˢ J).filter (fun p => p.2 < p.1))
                          ((I ×ˢ J).filter (fun p => p.1 < p.2)) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      ext ⟨i, j⟩
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.notMem_empty, iff_false]
      intro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
      exact absurd h1 (not_lt.mpr (le_of_lt h2))
    rw [← Finset.card_union_of_disjoint hdisj, ← hcover, Finset.card_product]
  -- |I|×|J| is odd, so n1 % 2 ≠ #{i<j} % 2
  have h_mod : n1 % 2 ≠ ((I ×ˢ J).filter (fun p => p.1 < p.2)).card % 2 := by
    have hN_odd : (I.card * J.card) % 2 = 1 := by
      have hI_odd : Odd I.card := Nat.odd_iff.mpr hI
      have hJ_odd : Odd J.card := Nat.odd_iff.mpr hJ
      have : Odd (I.card * J.card) := hI_odd.mul hJ_odd
      exact Nat.odd_iff.mp this
    omega
  -- (-1)^n2 = -(-1)^n1 since parities differ
  have hparity_diff : (n1 + n2) % 2 = 1 := by
    have := hsum
    rw [hn2_eq] at *
    have hN_odd : (I.card * J.card) % 2 = 1 := by
      have hI_odd : Odd I.card := Nat.odd_iff.mpr hI
      have hJ_odd : Odd J.card := Nat.odd_iff.mpr hJ
      have : Odd (I.card * J.card) := hI_odd.mul hJ_odd
      exact Nat.odd_iff.mp this
    omega
  have hn2_parity : n2 % 2 ≠ n1 % 2 := by
    rw [hn2_eq]; exact h_mod.symm
  -- If n1 is even, n2 is odd: (-1)^n2 = -1 = -1 = -(-1)^n1
  -- If n1 is odd, n2 is even: (-1)^n2 = 1 = -(-1) = -(-1)^n1
  cases Nat.mod_two_eq_zero_or_one n1 with
  | inl hn1_even =>
    have hn2_odd : n2 % 2 = 1 := by
      cases Nat.mod_two_eq_zero_or_one n2 with
      | inl h =>
        exfalso
        apply hn2_parity
        rw [h, hn1_even]
      | inr h => exact h
    have h1 : ((-1 : ℤ) ^ n1 : ℤ) = 1 := (Nat.even_iff.mpr hn1_even).neg_one_pow
    have h2 : ((-1 : ℤ) ^ n2 : ℤ) = -1 := (Nat.odd_iff.mpr hn2_odd).neg_one_pow
    calc (-1 : ℤ) ^ n2 = -1 := h2
      _ = -(1 : ℤ) := rfl
      _ = -(-1 : ℤ) ^ n1 := by rw [h1]
  | inr hn1_odd =>
    have hn2_even : n2 % 2 = 0 := by
      cases Nat.mod_two_eq_zero_or_one n2 with
      | inl h => exact h
      | inr h =>
        exfalso
        apply hn2_parity
        rw [h, hn1_odd]
    have h1 : ((-1 : ℤ) ^ n1 : ℤ) = -1 := (Nat.odd_iff.mpr hn1_odd).neg_one_pow
    have h2 : ((-1 : ℤ) ^ n2 : ℤ) = 1 := (Nat.even_iff.mpr hn2_even).neg_one_pow
    calc (-1 : ℤ) ^ n2 = 1 := h2
      _ = -(-1 : ℤ) := by decide
      _ = -(-1 : ℤ) ^ n1 := by rw [h1]

/-- Grassmann multiplication: (fg)_K = Σ_{I ∪ J = K, I ∩ J = ∅} sign(I,J) · f_I · g_J -/
instance : Mul (FiniteGrassmannCarrier q) := ⟨fun f g K =>
  Finset.univ.sum fun I =>
    Finset.univ.sum fun J =>
      if I ∪ J = K ∧ I ∩ J = ∅ then
        reorderSign I J * f I * g J
      else 0⟩

/-- Grassmann multiplication at a given index -/
@[simp]
lemma mul_apply (f g : FiniteGrassmannCarrier q) (K : Finset (Fin q)) :
    (f * g) K = Finset.univ.sum fun I =>
      Finset.univ.sum fun J =>
        if I ∪ J = K ∧ I ∩ J = ∅ then
          reorderSign I J * f I * g J
        else 0 := rfl

/-- NatCast instance for FiniteGrassmannCarrier -/
instance : NatCast (FiniteGrassmannCarrier q) := ⟨fun n I => if I = ∅ then n else 0⟩

/-- IntCast instance for FiniteGrassmannCarrier -/
instance : IntCast (FiniteGrassmannCarrier q) := ⟨fun n I => if I = ∅ then n else 0⟩

/-! ### Helper lemmas for associativity -/

/-- Helper: expand the 4-fold sum for LHS of associativity ((a*b)*c) -/
private theorem mul_assoc_lhs_expand (a b c : FiniteGrassmannCarrier q) (K : Finset (Fin q)) :
    (∑ L : Finset (Fin q), ∑ C : Finset (Fin q),
      if L ∪ C = K ∧ L ∩ C = ∅ then
        (reorderSign L C : ℝ) * (∑ J : Finset (Fin q), ∑ M : Finset (Fin q),
          if J ∪ M = L ∧ J ∩ M = ∅ then reorderSign J M * a J * b M else 0)
        * c C
      else 0) =
    ∑ L, ∑ C, ∑ J, ∑ M,
      if L ∪ C = K ∧ L ∩ C = ∅ ∧ J ∪ M = L ∧ J ∩ M = ∅ then
        (reorderSign L C : ℝ) * reorderSign J M * a J * b M * c C
      else 0 := by
  apply Finset.sum_congr rfl; intro L _
  apply Finset.sum_congr rfl; intro C _
  split_ifs with hLC
  · -- hLC holds: expand the product into the sum
    calc (reorderSign L C : ℝ) * (∑ J, ∑ M,
          if J ∪ M = L ∧ J ∩ M = ∅ then reorderSign J M * a J * b M else 0) * c C
      = (∑ J, ∑ M,
          if J ∪ M = L ∧ J ∩ M = ∅ then
            (reorderSign L C : ℝ) * reorderSign J M * a J * b M else 0) * c C := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro J _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro M _
          split_ifs <;> ring
      _ = ∑ J, ∑ M,
          (if J ∪ M = L ∧ J ∩ M = ∅ then
            (reorderSign L C : ℝ) * reorderSign J M * a J * b M else 0) * c C := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl; intro J _
            rw [Finset.sum_mul]
      _ = ∑ J, ∑ M,
          if J ∪ M = L ∧ J ∩ M = ∅ then
            (reorderSign L C : ℝ) * reorderSign J M * a J * b M * c C
          else 0 := by
            apply Finset.sum_congr rfl; intro J _
            apply Finset.sum_congr rfl; intro M _
            split_ifs <;> ring
      _ = _ := by
            apply Finset.sum_congr rfl; intro J _
            apply Finset.sum_congr rfl; intro M _
            simp only [hLC, true_and]
  · -- hLC false: both sides are 0
    symm
    apply Finset.sum_eq_zero; intro J _
    apply Finset.sum_eq_zero; intro M _
    rw [if_neg]
    intro hcond
    exact hLC ⟨hcond.1, hcond.2.1⟩

/-- Helper: expand the 4-fold sum for RHS of associativity (a*(b*c)) -/
private theorem mul_assoc_rhs_expand (a b c : FiniteGrassmannCarrier q) (K : Finset (Fin q)) :
    (∑ A : Finset (Fin q), ∑ N : Finset (Fin q),
      if A ∪ N = K ∧ A ∩ N = ∅ then
        (reorderSign A N : ℝ) * a A *
        (∑ B : Finset (Fin q), ∑ C : Finset (Fin q),
          if B ∪ C = N ∧ B ∩ C = ∅ then reorderSign B C * b B * c C else 0)
      else 0) =
    ∑ A, ∑ N, ∑ B, ∑ C,
      if A ∪ N = K ∧ A ∩ N = ∅ ∧ B ∪ C = N ∧ B ∩ C = ∅ then
        (reorderSign A N : ℝ) * reorderSign B C * a A * b B * c C
      else 0 := by
  apply Finset.sum_congr rfl; intro A _
  apply Finset.sum_congr rfl; intro N _
  split_ifs with hAN
  · -- hAN holds: expand the product into the sum
    calc (reorderSign A N : ℝ) * a A *
        (∑ B, ∑ C, if B ∪ C = N ∧ B ∩ C = ∅ then reorderSign B C * b B * c C else 0)
      = ∑ B, ∑ C, (reorderSign A N : ℝ) * a A *
          (if B ∪ C = N ∧ B ∩ C = ∅ then reorderSign B C * b B * c C else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro B _
            rw [Finset.mul_sum]
      _ = ∑ B, ∑ C,
          if B ∪ C = N ∧ B ∩ C = ∅ then
            (reorderSign A N : ℝ) * reorderSign B C * a A * b B * c C
          else 0 := by
            apply Finset.sum_congr rfl; intro B _
            apply Finset.sum_congr rfl; intro C _
            split_ifs <;> ring
      _ = _ := by
            apply Finset.sum_congr rfl; intro B _
            apply Finset.sum_congr rfl; intro C _
            simp only [hAN, true_and]
  · -- hAN false: both sides are 0
    symm
    apply Finset.sum_eq_zero; intro B _
    apply Finset.sum_eq_zero; intro C _
    rw [if_neg]
    intro hcond
    exact hAN ⟨hcond.1, hcond.2.1⟩

/-- The Ring structure on FiniteGrassmannCarrier.
    Note: This is NOT a CommRing due to anticommutativity of odd elements.
    The multiplication is Grassmann multiplication with the Koszul sign convention. -/
instance : Ring (FiniteGrassmannCarrier q) where
  __ := inferInstanceAs (AddCommGroup (FiniteGrassmannCarrier q))
  natCast := fun n I => if I = ∅ then n else 0
  natCast_zero := funext fun I => by split_ifs <;> simp
  natCast_succ := fun n => funext fun I => by
    change (if I = ∅ then (↑(n + 1) : ℝ) else 0) =
           (if I = ∅ then (↑n : ℝ) else 0) + (if I = ∅ then 1 else 0)
    split_ifs <;> simp [Nat.cast_add]
  intCast := fun n I => if I = ∅ then n else 0
  intCast_ofNat := fun n => funext fun I => by
    change (if I = ∅ then (↑(Int.ofNat n) : ℝ) else 0) = (if I = ∅ then (↑n : ℝ) else 0)
    split_ifs <;> simp
  intCast_negSucc := fun n => funext fun I => by
    change (if I = ∅ then (↑(Int.negSucc n) : ℝ) else 0) =
           -(if I = ∅ then (↑(n + 1) : ℝ) else 0)
    split_ifs <;> simp [Int.cast_negSucc]
  mul_assoc := fun a b c => by
    funext K
    simp only [mul_apply]
    rw [mul_assoc_lhs_expand, mul_assoc_rhs_expand]

    -- Define the canonical triple sum that both sides equal
    let canonicalSum :=
      ∑ A : Finset (Fin q), ∑ B : Finset (Fin q), ∑ C : Finset (Fin q),
        if A ∪ B ∪ C = K ∧ A ∩ B = ∅ ∧ B ∩ C = ∅ ∧ A ∩ C = ∅ then
          (reorderSign (A ∪ B) C * reorderSign A B : ℝ) * a A * b B * c C
        else 0

    -- LHS (4-fold sum) equals canonical sum by reducing L to J ∪ M
    have lhs_eq : (∑ L, ∑ C, ∑ J, ∑ M,
        if L ∪ C = K ∧ L ∩ C = ∅ ∧ J ∪ M = L ∧ J ∩ M = ∅ then
          (reorderSign L C : ℝ) * reorderSign J M * a J * b M * c C
        else 0) = canonicalSum := by
      simp only [canonicalSum]
      -- Reorder sums: L, C, J, M -> J, M, C, L
      calc _ = ∑ C, ∑ L, ∑ J, ∑ M,
          if L ∪ C = K ∧ L ∩ C = ∅ ∧ J ∪ M = L ∧ J ∩ M = ∅ then
            (reorderSign L C : ℝ) * reorderSign J M * a J * b M * c C
          else 0 := Finset.sum_comm
        _ = ∑ C, ∑ J, ∑ L, ∑ M,
          if L ∪ C = K ∧ L ∩ C = ∅ ∧ J ∪ M = L ∧ J ∩ M = ∅ then
            (reorderSign L C : ℝ) * reorderSign J M * a J * b M * c C
          else 0 := by apply Finset.sum_congr rfl; intro C _; exact Finset.sum_comm
        _ = ∑ C, ∑ J, ∑ M, ∑ L,
          if L ∪ C = K ∧ L ∩ C = ∅ ∧ J ∪ M = L ∧ J ∩ M = ∅ then
            (reorderSign L C : ℝ) * reorderSign J M * a J * b M * c C
          else 0 := by
            apply Finset.sum_congr rfl; intro C _
            apply Finset.sum_congr rfl; intro J _
            exact Finset.sum_comm
        _ = ∑ J, ∑ C, ∑ M, ∑ L,
          if L ∪ C = K ∧ L ∩ C = ∅ ∧ J ∪ M = L ∧ J ∩ M = ∅ then
            (reorderSign L C : ℝ) * reorderSign J M * a J * b M * c C
          else 0 := Finset.sum_comm
        _ = ∑ J, ∑ M, ∑ C, ∑ L,
          if L ∪ C = K ∧ L ∩ C = ∅ ∧ J ∪ M = L ∧ J ∩ M = ∅ then
            (reorderSign L C : ℝ) * reorderSign J M * a J * b M * c C
          else 0 := by apply Finset.sum_congr rfl; intro J _; exact Finset.sum_comm
        _ = ∑ J, ∑ M, ∑ C,
          if (J ∪ M) ∪ C = K ∧ (J ∪ M) ∩ C = ∅ ∧ J ∩ M = ∅ then
            (reorderSign (J ∪ M) C : ℝ) * reorderSign J M * a J * b M * c C
          else 0 := by
            apply Finset.sum_congr rfl; intro J _
            apply Finset.sum_congr rfl; intro M _
            apply Finset.sum_congr rfl; intro C _
            rw [Finset.sum_eq_single (J ∪ M)]
            rotate_left
            · intro L _ hL
              split_ifs with hcond
              · exact absurd hcond.2.2.1 (Ne.symm hL)
              · rfl
            · intro habs; exact absurd (Finset.mem_univ _) habs
            simp only [true_and]
        _ = _ := by
            apply Finset.sum_congr rfl; intro J _
            apply Finset.sum_congr rfl; intro M _
            apply Finset.sum_congr rfl; intro C _
            -- Show conditions are equivalent
            by_cases hvalid : J ∪ M ∪ C = K ∧ J ∩ M = ∅ ∧ M ∩ C = ∅ ∧ J ∩ C = ∅
            · obtain ⟨hJMC, hJM, hMC, hJC⟩ := hvalid
              have hLC_d : (J ∪ M) ∩ C = ∅ := by
                rw [Finset.union_inter_distrib_right, hJC, hMC, Finset.empty_union]
              simp only [hJMC, hLC_d, hJM, hMC, hJC, and_self, ↓reduceIte]
            · have hLHS_false : ¬((J ∪ M) ∪ C = K ∧ (J ∪ M) ∩ C = ∅ ∧ J ∩ M = ∅) := by
                intro ⟨hU, hD, hJM⟩
                apply hvalid
                refine ⟨hU, hJM, ?_, ?_⟩
                · rw [← Finset.disjoint_iff_inter_eq_empty] at hD ⊢
                  exact Finset.disjoint_of_subset_left Finset.subset_union_right hD
                · rw [← Finset.disjoint_iff_inter_eq_empty] at hD ⊢
                  exact Finset.disjoint_of_subset_left Finset.subset_union_left hD
              simp only [hvalid, hLHS_false, ↓reduceIte]

    -- RHS (4-fold sum) equals canonical sum by reducing N to B ∪ C
    have rhs_eq : (∑ A, ∑ N, ∑ B, ∑ C,
        if A ∪ N = K ∧ A ∩ N = ∅ ∧ B ∪ C = N ∧ B ∩ C = ∅ then
          (reorderSign A N : ℝ) * reorderSign B C * a A * b B * c C
        else 0) = canonicalSum := by
      simp only [canonicalSum]
      apply Finset.sum_congr rfl; intro A _
      -- Reorder sums: N, B, C -> B, C, N
      calc _ = ∑ B, ∑ N, ∑ C,
          if A ∪ N = K ∧ A ∩ N = ∅ ∧ B ∪ C = N ∧ B ∩ C = ∅ then
            (reorderSign A N : ℝ) * reorderSign B C * a A * b B * c C
          else 0 := Finset.sum_comm
        _ = ∑ B, ∑ C, ∑ N,
          if A ∪ N = K ∧ A ∩ N = ∅ ∧ B ∪ C = N ∧ B ∩ C = ∅ then
            (reorderSign A N : ℝ) * reorderSign B C * a A * b B * c C
          else 0 := by apply Finset.sum_congr rfl; intro B _; exact Finset.sum_comm
        _ = ∑ B, ∑ C,
          if A ∪ (B ∪ C) = K ∧ A ∩ (B ∪ C) = ∅ ∧ B ∩ C = ∅ then
            (reorderSign A (B ∪ C) : ℝ) * reorderSign B C * a A * b B * c C
          else 0 := by
            apply Finset.sum_congr rfl; intro B _
            apply Finset.sum_congr rfl; intro C _
            rw [Finset.sum_eq_single (B ∪ C)]
            rotate_left
            · intro N _ hN
              split_ifs with hcond
              · exact absurd hcond.2.2.1 (Ne.symm hN)
              · rfl
            · intro habs; exact absurd (Finset.mem_univ _) habs
            simp only [true_and]
        _ = ∑ B, ∑ C,
          if A ∪ B ∪ C = K ∧ A ∩ B = ∅ ∧ B ∩ C = ∅ ∧ A ∩ C = ∅ then
            (reorderSign (A ∪ B) C * reorderSign A B : ℝ) * a A * b B * c C
          else 0 := by
            apply Finset.sum_congr rfl; intro B _
            apply Finset.sum_congr rfl; intro C _
            by_cases hvalid : A ∪ B ∪ C = K ∧ A ∩ B = ∅ ∧ B ∩ C = ∅ ∧ A ∩ C = ∅
            · have hvalid' := hvalid
              obtain ⟨hABC, hAB, hBC, hAC⟩ := hvalid
              have hABC' : A ∪ (B ∪ C) = K := by rw [← Finset.union_assoc]; exact hABC
              have hA_BC : A ∩ (B ∪ C) = ∅ := by
                rw [Finset.inter_union_distrib_left, hAB, hAC, Finset.union_empty]
              have hLHS_cond : A ∪ (B ∪ C) = K ∧ A ∩ (B ∪ C) = ∅ ∧ B ∩ C = ∅ := ⟨hABC', hA_BC, hBC⟩
              rw [if_pos hLHS_cond, if_pos hvalid']
              -- Use reorderSign_assoc: sign(A∪B, C) * sign(A, B) = sign(A, B∪C) * sign(B, C)
              have hsign := reorderSign_assoc hAB hAC hBC
              -- Convert to show the signs match
              congr 1
              simp only [← Int.cast_mul, hsign]
            · have hLHS_false : ¬(A ∪ (B ∪ C) = K ∧ A ∩ (B ∪ C) = ∅ ∧ B ∩ C = ∅) := by
                intro ⟨hU, hD, hBC⟩
                apply hvalid
                have hAB : A ∩ B = ∅ := by
                  rw [← Finset.disjoint_iff_inter_eq_empty] at hD ⊢
                  exact Finset.disjoint_of_subset_right Finset.subset_union_left hD
                have hAC : A ∩ C = ∅ := by
                  rw [← Finset.disjoint_iff_inter_eq_empty] at hD ⊢
                  exact Finset.disjoint_of_subset_right Finset.subset_union_right hD
                refine ⟨?_, hAB, hBC, hAC⟩
                rw [Finset.union_assoc]; exact hU
              rw [if_neg hLHS_false, if_neg hvalid]

    rw [lhs_eq, rhs_eq]
  zero_mul := fun f => by
    funext K
    simp only [mul_apply, zero_apply]
    -- 0 * f = 0: all terms have factor 0
    apply Finset.sum_eq_zero
    intro I _
    apply Finset.sum_eq_zero
    intro J _
    split_ifs with h
    · simp only [mul_zero, zero_mul]
    · rfl
  mul_zero := fun f => by
    funext K
    simp only [mul_apply, zero_apply]
    -- f * 0 = 0: all terms have factor 0
    apply Finset.sum_eq_zero
    intro I _
    apply Finset.sum_eq_zero
    intro J _
    split_ifs with h
    · simp only [mul_zero]
    · rfl
  one_mul := fun f => by
    funext K
    simp only [mul_apply, one_apply]
    -- 1 * f = f: only the I = ∅, J = K term contributes
    rw [Finset.sum_eq_single ∅]
    · -- The I = ∅ case
      rw [Finset.sum_eq_single K]
      · -- The I = ∅, J = K case
        simp only [Finset.empty_union, Finset.empty_inter, and_self, ↓reduceIte,
          reorderSign_empty_left, Int.cast_one]
        ring
      · -- J ≠ K terms are zero
        intro J _ hJK
        simp only [Finset.empty_union, Finset.empty_inter, and_true]
        rw [if_neg hJK]
      · intro hK; exact absurd (Finset.mem_univ K) hK
    · -- I ≠ ∅ terms: the (if I = ∅ then 1 else 0) factor makes them zero
      intro I _ hI
      apply Finset.sum_eq_zero
      intro J _
      -- Use simp to substitute (if I = ∅ then 1 else 0) → 0
      simp only [hI, ↓reduceIte]
      split_ifs with h
      · ring
      · rfl
    · intro h0; exact absurd (Finset.mem_univ ∅) h0
  mul_one := fun f => by
    funext K
    simp only [mul_apply, one_apply]
    -- f * 1 = f: only the I = K, J = ∅ term contributes
    rw [Finset.sum_eq_single K]
    · -- The I = K case
      rw [Finset.sum_eq_single ∅]
      · -- The I = K, J = ∅ case
        simp only [Finset.union_empty, Finset.inter_empty, and_self, ↓reduceIte,
          reorderSign_empty_right, Int.cast_one]
        ring
      · -- J ≠ ∅ terms: the (if J = ∅ then 1 else 0) factor makes them zero
        intro J _ hJ
        simp only [hJ, ↓reduceIte]
        split_ifs with h
        · ring
        · rfl
      · intro h0; exact absurd (Finset.mem_univ ∅) h0
    · -- I ≠ K terms are zero
      intro I _ hI
      apply Finset.sum_eq_zero
      intro J _
      split_ifs with h hJeq
      · -- If I ∪ J = K and I ∩ J = ∅ and J = ∅, then I = K, contradiction
        obtain ⟨hIJ_eq, hIJ_disj⟩ := h
        simp only [hJeq, Finset.union_empty] at hIJ_eq
        exact absurd hIJ_eq hI
      · -- J ≠ ∅, so (if J = ∅ then 1 else 0) = 0
        ring
      · rfl
    · intro hK; exact absurd (Finset.mem_univ K) hK
  left_distrib := fun a b c => by
    funext K
    -- a * (b + c) = a * b + a * c - follows from linearity of sum
    simp only [mul_apply, add_apply]
    -- Distribute the sum: Σ_I Σ_J (...(b J + c J)...) = Σ_I Σ_J (...b J...) + Σ_I Σ_J (...c J...)
    have h : ∀ I J, (if I ∪ J = K ∧ I ∩ J = ∅ then reorderSign I J * a I * (b J + c J) else 0) =
        (if I ∪ J = K ∧ I ∩ J = ∅ then reorderSign I J * a I * b J else 0) +
        (if I ∪ J = K ∧ I ∩ J = ∅ then reorderSign I J * a I * c J else 0) := by
      intro I J
      split_ifs with hIJ
      · ring
      · ring
    simp_rw [h]
    -- Now we have: Σ_I Σ_J (term1 + term2) = Σ_I Σ_J term1 + Σ_I Σ_J term2
    trans (∑ I : Finset (Fin q), ∑ J : Finset (Fin q),
             (if I ∪ J = K ∧ I ∩ J = ∅ then ↑(reorderSign I J) * a I * b J else 0)) +
          (∑ I : Finset (Fin q), ∑ J : Finset (Fin q),
             (if I ∪ J = K ∧ I ∩ J = ∅ then ↑(reorderSign I J) * a I * c J else 0))
    · rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro I _
      rw [← Finset.sum_add_distrib]
    · rfl
  right_distrib := fun a b c => by
    funext K
    -- (a + b) * c = a * c + b * c - follows from linearity of sum
    simp only [mul_apply, add_apply]
    have h : ∀ I J, (if I ∪ J = K ∧ I ∩ J = ∅ then reorderSign I J * (a I + b I) * c J else 0) =
        (if I ∪ J = K ∧ I ∩ J = ∅ then reorderSign I J * a I * c J else 0) +
        (if I ∪ J = K ∧ I ∩ J = ∅ then reorderSign I J * b I * c J else 0) := by
      intro I J
      split_ifs with hIJ
      · ring
      · ring
    simp_rw [h]
    trans (∑ I : Finset (Fin q), ∑ J : Finset (Fin q),
             (if I ∪ J = K ∧ I ∩ J = ∅ then ↑(reorderSign I J) * a I * c J else 0)) +
          (∑ I : Finset (Fin q), ∑ J : Finset (Fin q),
             (if I ∪ J = K ∧ I ∩ J = ∅ then ↑(reorderSign I J) * b I * c J else 0))
    · rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro I _
      rw [← Finset.sum_add_distrib]
    · rfl

/-- The algebraMap from ℝ to FiniteGrassmannCarrier -/
def algebraMapReal : ℝ →+* FiniteGrassmannCarrier q where
  toFun := fun c I => if I = ∅ then c else 0
  map_one' := rfl
  map_mul' := fun x y => by
    funext K
    simp only [mul_apply]
    -- Only the I = ∅, J = ∅ term contributes
    rw [Finset.sum_eq_single ∅]
    · rw [Finset.sum_eq_single ∅]
      · simp only [Finset.empty_union, Finset.empty_inter, reorderSign_empty_left, Int.cast_one]
        by_cases hK : K = ∅
        · simp only [hK, true_and, ↓reduceIte, one_mul]
        · have h : ¬(∅ = K ∧ True) := fun ⟨hc, _⟩ => hK hc.symm
          simp only [hK, ↓reduceIte, h]
      · intro J _ hJ
        simp only [Finset.empty_union, Finset.empty_inter, hJ, ↓reduceIte]
        split_ifs with h
        · -- J = K case: but then (if J = ∅ then y else 0) = 0 since J ≠ ∅
          simp only [mul_zero]
        · rfl
      · intro; exact absurd (Finset.mem_univ ∅) (by assumption)
    · intro I _ hI
      apply Finset.sum_eq_zero
      intro J _
      simp only [hI, ↓reduceIte]
      split_ifs <;> simp
    · intro; exact absurd (Finset.mem_univ ∅) (by assumption)
  map_zero' := by funext K; simp
  map_add' := fun x y => by
    funext K
    simp only [add_apply]
    by_cases hK : K = ∅
    · simp only [hK, ↓reduceIte]
    · simp only [hK, ↓reduceIte, add_zero]

/-- The ℝ-algebra structure on FiniteGrassmannCarrier -/
instance : Algebra ℝ (FiniteGrassmannCarrier q) where
  smul := fun c f I => c * f I
  algebraMap := algebraMapReal
  commutes' := fun r x => by
    funext K
    simp only [algebraMapReal, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, mul_apply]
    -- r * x = x * r: scalars commute with everything
    -- LHS: Σ_I Σ_J (if I∪J=K ∧ I∩J=∅ then sign(I,J) * (if I=∅ then r else 0) * x J else 0)
    -- Only I=∅ contributes: Σ_J (if J=K then r * x J else 0) = r * x K
    -- RHS: Σ_I Σ_J (if I∪J=K ∧ I∩J=∅ then sign(I,J) * x I * (if J=∅ then r else 0) else 0)
    -- Only J=∅ contributes: Σ_I (if I=K then x I * r else 0) = x K * r
    rw [Finset.sum_eq_single ∅]
    · rw [Finset.sum_eq_single K]
      · simp only [Finset.empty_union, Finset.empty_inter, and_self, ↓reduceIte,
          reorderSign_empty_left, Int.cast_one]
        rw [Finset.sum_eq_single K]
        · rw [Finset.sum_eq_single ∅]
          · simp only [Finset.union_empty, Finset.inter_empty, and_self, ↓reduceIte,
              reorderSign_empty_right, Int.cast_one]
            ring
          · intro J _ hJ
            simp only [hJ, ↓reduceIte, mul_zero]
            split_ifs with h <;> rfl
          · intro; exact absurd (Finset.mem_univ ∅) (by assumption)
        · intro I _ hI
          apply Finset.sum_eq_zero
          intro J _
          -- The sum term is: if I ∪ J = K ∧ I ∩ J = ∅ then sign * x I * (if J = ∅ then r else 0) else 0
          by_cases hJ : J = ∅
          · -- J = ∅ case: condition becomes I = K which contradicts hI
            simp only [hJ, Finset.union_empty, Finset.inter_empty, and_true]
            rw [if_neg hI]
          · -- J ≠ ∅ case: the inner (if J = ∅ then r else 0) = 0
            split_ifs with h
            · simp only [mul_zero]
            · rfl
        · intro; exact absurd (Finset.mem_univ K) (by assumption)
      · intro J _ hJ
        simp only [Finset.empty_union, Finset.empty_inter, and_true]
        rw [if_neg hJ]
      · intro; exact absurd (Finset.mem_univ K) (by assumption)
    · intro I _ hI
      apply Finset.sum_eq_zero
      intro J _
      simp only [hI, ↓reduceIte, zero_mul, mul_zero]
      split_ifs <;> rfl
    · intro; exact absurd (Finset.mem_univ ∅) (by assumption)
  smul_def' := fun r x => by
    funext K
    simp only [algebraMapReal, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, mul_apply,
      HSMul.hSMul]
    -- r • x = (algebraMap r) * x
    -- LHS: r * x K
    -- RHS: Σ_I Σ_J (if I∪J=K ∧ I∩J=∅ then sign(I,J) * (if I=∅ then r else 0) * x J else 0)
    -- Only I=∅ contributes: Σ_J (if J=K then r * x J else 0) = r * x K
    rw [Finset.sum_eq_single ∅]
    · rw [Finset.sum_eq_single K]
      · simp only [Finset.empty_union, Finset.empty_inter, and_self, ↓reduceIte,
          reorderSign_empty_left, Int.cast_one]
        ring
      · intro J _ hJ
        simp only [Finset.empty_union, Finset.empty_inter, and_true]
        rw [if_neg hJ]
      · intro; exact absurd (Finset.mem_univ K) (by assumption)
    · intro I _ hI
      apply Finset.sum_eq_zero
      intro J _
      simp only [hI, ↓reduceIte, zero_mul, mul_zero]
      split_ifs <;> rfl
    · intro; exact absurd (Finset.mem_univ ∅) (by assumption)

/-! ### Even and Odd Subspaces -/

/-- An element is even if all odd-cardinality coefficients vanish -/
def isEven (x : FiniteGrassmannCarrier q) : Prop :=
  ∀ I : Finset (Fin q), I.card % 2 = 1 → x I = 0

/-- An element is odd if all even-cardinality coefficients vanish -/
def isOdd (x : FiniteGrassmannCarrier q) : Prop :=
  ∀ I : Finset (Fin q), I.card % 2 = 0 → x I = 0

/-- Zero is even -/
theorem zero_isEven : isEven (0 : FiniteGrassmannCarrier q) := fun _ _ => rfl

/-- One is even -/
theorem one_isEven : isEven (1 : FiniteGrassmannCarrier q) := by
  intro I hI
  simp only [one_apply]
  have hI_ne : I ≠ ∅ := fun h => by rw [h] at hI; simp at hI
  simp [hI_ne]

/-- Sum of even elements is even -/
theorem isEven_add (x y : FiniteGrassmannCarrier q) (hx : isEven x) (hy : isEven y) :
    isEven (x + y) := by
  intro I hI
  simp only [add_apply]
  rw [hx I hI, hy I hI, add_zero]

/-- Negation preserves evenness -/
theorem isEven_neg (x : FiniteGrassmannCarrier q) (hx : isEven x) : isEven (-x) := by
  intro I hI
  simp only [neg_apply]
  rw [hx I hI, neg_zero]

/-- Product of even elements is even -/
theorem isEven_mul_even (x y : FiniteGrassmannCarrier q) (hx : isEven x) (hy : isEven y) :
    isEven (x * y) := by
  intro K hK
  simp only [mul_apply]
  apply Finset.sum_eq_zero
  intro I _
  apply Finset.sum_eq_zero
  intro J _
  split_ifs with h
  · obtain ⟨hIJ_eq, hIJ_disj⟩ := h
    -- |K| = |I| + |J| since disjoint
    have hcard : K.card = I.card + J.card := by
      rw [← hIJ_eq]
      exact Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr hIJ_disj)
    -- |K| odd means |I| + |J| odd, so one of |I|, |J| is odd
    rw [hcard] at hK
    have hodd : (I.card + J.card) % 2 = 1 := hK
    cases Nat.even_or_odd I.card with
    | inl hI_even =>
      have hJ_odd : J.card % 2 = 1 := by
        have : (I.card % 2 + J.card % 2) % 2 = 1 := by omega
        rw [Nat.even_iff.mp hI_even] at this
        omega
      -- Since y J = 0 (because J has odd cardinality and y is even)
      simp only [hy J hJ_odd, mul_zero]
    | inr hI_odd =>
      -- Since x I = 0 (because I has odd cardinality and x is even)
      simp only [hx I (Nat.odd_iff.mp hI_odd), mul_zero, zero_mul]
  · rfl

/-- Product of odd elements is even -/
theorem isOdd_mul_odd (x y : FiniteGrassmannCarrier q) (hx : isOdd x) (hy : isOdd y) :
    isEven (x * y) := by
  intro K hK
  simp only [mul_apply]
  apply Finset.sum_eq_zero
  intro I _
  apply Finset.sum_eq_zero
  intro J _
  split_ifs with h
  · obtain ⟨hIJ_eq, hIJ_disj⟩ := h
    have hcard : K.card = I.card + J.card := by
      rw [← hIJ_eq]
      exact Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr hIJ_disj)
    rw [hcard] at hK
    -- |K| odd = |I| + |J|, so one of I, J has even cardinality
    cases Nat.even_or_odd I.card with
    | inl hI_even =>
      simp only [hx I (Nat.even_iff.mp hI_even), mul_zero, zero_mul]
    | inr hI_odd =>
      have hJ_even : J.card % 2 = 0 := by
        have : (I.card % 2 + J.card % 2) % 2 = 1 := by omega
        rw [Nat.odd_iff.mp hI_odd] at this
        omega
      simp only [hy J hJ_even, mul_zero]
  · rfl

/-! ### Body Map -/

/-- The body map: extract the scalar (∅ coefficient) -/
def body (x : FiniteGrassmannCarrier q) : ℝ := x ∅

theorem body_add (x y : FiniteGrassmannCarrier q) : body (x + y) = body x + body y := rfl

theorem body_one : body (1 : FiniteGrassmannCarrier q) = 1 := by simp [body]

theorem body_algebraMap (c : ℝ) : body (algebraMap ℝ (FiniteGrassmannCarrier q) c) = c := by
  simp [body, Algebra.algebraMap_eq_smul_one]

theorem body_mul (x y : FiniteGrassmannCarrier q) : body (x * y) = body x * body y := by
  simp only [body, mul_apply]
  -- Only the term I = ∅, J = ∅ contributes to the ∅ coefficient
  rw [Finset.sum_eq_single ∅]
  · rw [Finset.sum_eq_single ∅]
    · -- I = ∅, J = ∅ term
      simp only [Finset.empty_union, Finset.empty_inter, and_self, ↓reduceIte,
        reorderSign_empty_left, Int.cast_one, one_mul]
    · -- J ≠ ∅ terms are zero because ∅ ∪ J = ∅ requires J = ∅
      intro J _ hJ
      have h : ¬(∅ ∪ J = ∅ ∧ ∅ ∩ J = ∅) := by
        simp only [Finset.empty_union, Finset.empty_inter]
        intro ⟨hJeq, _⟩
        exact hJ hJeq
      simp only [h, ↓reduceIte]
    · intro; exact absurd (Finset.mem_univ ∅) (by assumption)
  · -- I ≠ ∅ terms are zero because I ∪ J = ∅ requires I = ∅
    intro I _ hI
    apply Finset.sum_eq_zero
    intro J _
    have h : ¬(I ∪ J = ∅ ∧ I ∩ J = ∅) := by
      intro ⟨hU, _⟩
      have hI_empty : I = ∅ := by
        ext x
        constructor
        · intro hx
          have : x ∈ I ∪ J := Finset.mem_union_left J hx
          rw [hU] at this
          exact absurd this (Finset.notMem_empty x)
        · intro hx
          exact absurd hx (Finset.notMem_empty x)
      exact hI hI_empty
    simp only [h, ↓reduceIte]
  · intro; exact absurd (Finset.mem_univ ∅) (by assumption)

end FiniteGrassmannCarrier

/-!
## Even Carrier Type

The even part needs CommRing structure for determinant computations.
-/

/-- The even part of the finite Grassmann algebra as a subtype -/
def FiniteGrassmannEven (q : ℕ) := {x : FiniteGrassmannCarrier q // x.isEven}

namespace FiniteGrassmannEven

variable {q : ℕ}

instance : Zero (FiniteGrassmannEven q) :=
  ⟨⟨0, FiniteGrassmannCarrier.zero_isEven⟩⟩

instance : One (FiniteGrassmannEven q) :=
  ⟨⟨1, FiniteGrassmannCarrier.one_isEven⟩⟩

instance : Add (FiniteGrassmannEven q) :=
  ⟨fun x y => ⟨x.val + y.val, FiniteGrassmannCarrier.isEven_add _ _ x.property y.property⟩⟩

instance : Neg (FiniteGrassmannEven q) :=
  ⟨fun x => ⟨-x.val, FiniteGrassmannCarrier.isEven_neg _ x.property⟩⟩

instance : Mul (FiniteGrassmannEven q) :=
  ⟨fun x y => ⟨x.val * y.val, FiniteGrassmannCarrier.isEven_mul_even _ _ x.property y.property⟩⟩

/-- Helper: nsmul preserves evenness -/
theorem isEven_nsmul (n : ℕ) (x : FiniteGrassmannCarrier q) (hx : FiniteGrassmannCarrier.isEven x) :
    FiniteGrassmannCarrier.isEven (n • x) := by
  intro I hI
  -- nsmul for FiniteGrassmannCarrier: (n • x) I = n * x I
  show (n : ℝ) * x I = 0
  rw [hx I hI, mul_zero]

/-- Helper: zsmul preserves evenness -/
theorem isEven_zsmul (n : ℤ) (x : FiniteGrassmannCarrier q) (hx : FiniteGrassmannCarrier.isEven x) :
    FiniteGrassmannCarrier.isEven (n • x) := by
  intro I hI
  -- n • x at I = n * x I
  show n * x I = 0
  rw [hx I hI, mul_zero]

/-- The CommRing structure on the even part.
    The even part is COMMUTATIVE because products of even elements commute. -/
instance : CommRing (FiniteGrassmannEven q) where
  add_assoc := fun _ _ _ => Subtype.ext (add_assoc _ _ _)
  zero_add := fun _ => Subtype.ext (zero_add _)
  add_zero := fun _ => Subtype.ext (add_zero _)
  nsmul := fun n x => ⟨n • x.val, isEven_nsmul n x.val x.property⟩
  nsmul_zero := fun x => Subtype.ext (zero_smul ℕ x.val)
  nsmul_succ := fun n x => Subtype.ext (succ_nsmul x.val n)
  neg_add_cancel := fun _ => Subtype.ext (neg_add_cancel _)
  add_comm := fun _ _ => Subtype.ext (add_comm _ _)
  zsmul := fun n x => ⟨n • x.val, isEven_zsmul n x.val x.property⟩
  zsmul_zero' := fun x => Subtype.ext (zero_smul ℤ x.val)
  zsmul_succ' := fun n x => Subtype.ext (SubNegMonoid.zsmul_succ' n x.val)
  zsmul_neg' := fun n x => Subtype.ext (SubNegMonoid.zsmul_neg' n x.val)
  mul_assoc := fun _ _ _ => Subtype.ext (mul_assoc _ _ _)
  one_mul := fun _ => Subtype.ext (one_mul _)
  mul_one := fun _ => Subtype.ext (mul_one _)
  zero_mul := fun _ => Subtype.ext (zero_mul _)
  mul_zero := fun _ => Subtype.ext (mul_zero _)
  left_distrib := fun _ _ _ => Subtype.ext (left_distrib _ _ _)
  right_distrib := fun _ _ _ => Subtype.ext (right_distrib _ _ _)
  mul_comm := fun x y => Subtype.ext (by
    -- Even elements commute in the Grassmann algebra
    -- Key insight: for even x, y only terms with |I|, |J| both even contribute
    -- For such terms, sign(I,J) = sign(J,I) and x_I · y_J = y_J · x_I (real multiplication)
    funext K
    -- The goal is (x * y) K = (y * x) K where * is Grassmann multiplication
    show (x.val * y.val) K = (y.val * x.val) K
    simp only [FiniteGrassmannCarrier.mul_apply]
    -- Reindex the sum: swap I ↔ J
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I _
    apply Finset.sum_congr rfl
    intro J _
    -- Now comparing: sign(I,J) * x I * y J vs sign(J,I) * y J * x I
    by_cases hIJ : I ∪ J = K ∧ I ∩ J = ∅
    · -- hIJ holds
      have hJI : J ∪ I = K ∧ J ∩ I = ∅ := by
        obtain ⟨hIJ_eq, hIJ_disj⟩ := hIJ
        constructor
        · rw [Finset.union_comm]; exact hIJ_eq
        · rw [Finset.inter_comm]; exact hIJ_disj
      rw [if_pos hIJ, if_pos hJI]
      -- Since x, y are even, if |I| or |J| is odd, that term is 0
      by_cases hI_odd : I.card % 2 = 1
      · -- I has odd cardinality, so x.val I = 0
        simp only [x.property I hI_odd, mul_zero, zero_mul]
      · by_cases hJ_odd : J.card % 2 = 1
        · -- J has odd cardinality, so y.val J = 0
          simp only [y.property J hJ_odd, mul_zero, zero_mul]
        · -- Both I and J have even cardinality
          have hI_even : I.card % 2 = 0 := by
            cases Nat.mod_two_eq_zero_or_one I.card with
            | inl h => exact h
            | inr h => exact absurd h hI_odd
          have hJ_even : J.card % 2 = 0 := by
            cases Nat.mod_two_eq_zero_or_one J.card with
            | inl h => exact h
            | inr h => exact absurd h hJ_odd
          -- Use that sign(J,I) = sign(I,J) for even |I|, |J|
          rw [FiniteGrassmannCarrier.reorderSign_swap_even hIJ.2 hI_even hJ_even]
          ring
    · -- hIJ doesn't hold
      have hJI : ¬(J ∪ I = K ∧ J ∩ I = ∅) := by
        intro ⟨hJI_eq, hJI_disj⟩
        apply hIJ
        constructor
        · rw [Finset.union_comm]; exact hJI_eq
        · rw [Finset.inter_comm]; exact hJI_disj
      rw [if_neg hIJ, if_neg hJI])

/-- algebraMap from ℝ to FiniteGrassmannEven preserves evenness -/
theorem algebraMap_isEven (c : ℝ) :
    FiniteGrassmannCarrier.isEven (algebraMap ℝ (FiniteGrassmannCarrier q) c) := by
  intro I hI
  simp only [Algebra.algebraMap_eq_smul_one, FiniteGrassmannCarrier.smul_apply,
    FiniteGrassmannCarrier.one_apply]
  have hI_ne : I ≠ ∅ := fun h => by rw [h] at hI; simp at hI
  simp [hI_ne]

/-- The algebraMap from ℝ to FiniteGrassmannEven -/
def algebraMapEven : ℝ →+* FiniteGrassmannEven q where
  toFun := fun c => ⟨algebraMap ℝ (FiniteGrassmannCarrier q) c, algebraMap_isEven c⟩
  map_one' := Subtype.ext rfl
  map_mul' := fun x y => Subtype.ext (by
    simp only [HMul.hMul, Mul.mul]
    -- algebraMap (x * y) = algebraMap x * algebraMap y on carrier
    exact RingHom.map_mul (algebraMap ℝ (FiniteGrassmannCarrier q)) x y)
  map_zero' := Subtype.ext (RingHom.map_zero _)
  map_add' := fun x y => Subtype.ext (RingHom.map_add _ x y)

instance : Algebra ℝ (FiniteGrassmannEven q) where
  smul := fun c x => ⟨c • x.val, by
    intro I hI
    show c * x.val I = 0
    rw [x.property I hI, mul_zero]⟩
  algebraMap := algebraMapEven
  commutes' := fun r x => by
    apply Subtype.ext
    -- r * x = x * r for scalars
    exact Algebra.commutes r x.val
  smul_def' := fun r x => by
    apply Subtype.ext
    exact Algebra.smul_def r x.val

/-- Body map on even part -/
def body (x : FiniteGrassmannEven q) : ℝ := x.val.body

theorem body_one : body (1 : FiniteGrassmannEven q) = 1 := FiniteGrassmannCarrier.body_one

theorem body_add (x y : FiniteGrassmannEven q) : body (x + y) = body x + body y := rfl

theorem body_mul (x y : FiniteGrassmannEven q) : body (x * y) = body x * body y :=
  FiniteGrassmannCarrier.body_mul x.val y.val

end FiniteGrassmannEven

/-!
## Nilpotency for Elements with Zero Body

Key lemma: If `y ∅ = 0` (zero body), then `y^(q+1) = 0` in `FiniteGrassmannCarrier q`.
This follows because multiplication preserves the property that coefficients are zero
on small sets, and there are no sets of cardinality > q in Finset (Fin q).
-/
namespace FiniteGrassmannCarrier

/-- For elements with zero body, powers have vanishing coefficients on small sets.
    More precisely, if `y ∅ = 0`, then `(y^n) K = 0` whenever `K.card < n`. -/
theorem pow_vanishes_small_card {y : FiniteGrassmannCarrier q} (hy : y ∅ = 0) :
    ∀ n : ℕ, ∀ K : Finset (Fin q), K.card < n → (y^n) K = 0 := by
  intro n
  induction n with
  | zero =>
    intro K hK
    simp at hK
  | succ n ih =>
    intro K hK
    -- y^(n+1) = y^n * y
    rw [pow_succ]
    -- Expand (y^n * y) K = Σ_I Σ_J (if I ∪ J = K ∧ I ∩ J = ∅ then sign * (y^n) I * y J else 0)
    simp only [mul_apply]
    apply Finset.sum_eq_zero
    intro I _
    apply Finset.sum_eq_zero
    intro J _
    split_ifs with h
    · obtain ⟨hIJ_eq, hIJ_disj⟩ := h
      -- If I ∪ J = K and I ∩ J = ∅, then |K| = |I| + |J|
      have hcard : K.card = I.card + J.card := by
        rw [← hIJ_eq]
        exact Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr hIJ_disj)
      -- We have |K| < n + 1, so |I| + |J| < n + 1
      -- Case 1: J = ∅, then y J = y ∅ = 0
      -- Case 2: J ≠ ∅, so |J| ≥ 1, so |I| < n, so (y^n) I = 0 by IH
      by_cases hJ : J = ∅
      · -- y J = y ∅ = 0
        rw [hJ, hy, mul_zero]
      · -- J ≠ ∅ means |J| ≥ 1
        have hJ_ne : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr hJ
        have hJ_card : J.card ≥ 1 := Finset.one_le_card.mpr hJ_ne
        have hI_small : I.card < n := by omega
        rw [ih I hI_small, mul_zero, zero_mul]
    · rfl

/-- If `y ∅ = 0`, then `y^(q+1) = 0` since all sets have cardinality ≤ q < q+1. -/
theorem pow_zero_body_nilpotent {y : FiniteGrassmannCarrier q} (hy : y ∅ = 0) :
    y^(q + 1) = 0 := by
  funext K
  apply pow_vanishes_small_card hy
  -- K.card ≤ q < q + 1
  have hK_le : K.card ≤ q := Finset.card_le_card (Finset.subset_univ K) |>.trans (by simp)
  omega

end FiniteGrassmannCarrier

/-!
## The GrassmannAlgebra Instance

We now construct `finiteGrassmannAlgebra q : GrassmannAlgebra ℝ`.
-/

/-- The inclusion of even elements into the carrier -/
def evenToCarrierHom : FiniteGrassmannEven q →+* FiniteGrassmannCarrier q where
  toFun := Subtype.val
  map_one' := rfl
  map_mul' := fun _ _ => rfl
  map_zero' := rfl
  map_add' := fun _ _ => rfl

noncomputable def finiteGrassmannAlgebra (q : ℕ) : GrassmannAlgebra ℝ where
  carrier := FiniteGrassmannCarrier q
  carrierRing := inferInstance
  carrierAlgebra := inferInstance
  evenCarrier := FiniteGrassmannEven q
  evenRing := inferInstance
  evenAlgebra := inferInstance
  evenToCarrier := evenToCarrierHom
  evenToCarrier_injective := Subtype.val_injective
  evenToCarrier_algebraMap := fun c => rfl
  even := {
    carrier := {x | x.isEven}
    add_mem' := fun hx hy => FiniteGrassmannCarrier.isEven_add _ _ hx hy
    zero_mem' := FiniteGrassmannCarrier.zero_isEven
    smul_mem' := fun c x hx => by
      intro I hI
      show c * x I = 0
      rw [hx I hI, mul_zero]
  }
  even_mem_iff := fun x => by
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · intro ⟨y, hy⟩
      rw [← hy]
      exact y.property
  odd := {
    carrier := {x | x.isOdd}
    add_mem' := fun {a} {b} ha hb I hI => by
      show a I + b I = 0
      rw [ha I hI, hb I hI, add_zero]
    zero_mem' := fun _ _ => rfl
    smul_mem' := fun c x hx => by
      intro I hI
      show c * x I = 0
      rw [hx I hI, mul_zero]
  }
  body := FiniteGrassmannEven.body
  body_algebraMap := fun c => by
    simp only [FiniteGrassmannEven.body, FiniteGrassmannCarrier.body]
    rfl
  body_add := FiniteGrassmannEven.body_add
  body_mul := FiniteGrassmannEven.body_mul
  body_one := FiniteGrassmannEven.body_one
  nilpotent_part := fun x => by
    -- The nilpotent part y = x - body(x) has y_∅ = 0, so it's "purely nilpotent"
    -- By pow_zero_body_nilpotent, y^(q+1) = 0
    use q
    -- y = x - algebraMap ℝ evenCarrier (body x)
    -- We need to show y^(q+1) = 0 as an element of FiniteGrassmannEven q
    -- First, show the underlying carrier element has zero body
    have hy_body : (x.val - algebraMap ℝ (FiniteGrassmannCarrier q) (FiniteGrassmannEven.body x)) ∅ = 0 := by
      simp only [FiniteGrassmannEven.body, FiniteGrassmannCarrier.body]
      show x.val ∅ - (algebraMap ℝ (FiniteGrassmannCarrier q) (x.val ∅)) ∅ = 0
      simp only [Algebra.algebraMap_eq_smul_one, FiniteGrassmannCarrier.smul_apply,
        FiniteGrassmannCarrier.one_apply, ↓reduceIte, mul_one, sub_self]
    -- y^(q+1) = 0 follows from pow_zero_body_nilpotent
    -- Goal: (x - algebraMap ...)^(q+1) = 0 in FiniteGrassmannEven
    -- We prove this by showing the underlying carrier is 0
    have hpow : (x.val - algebraMap ℝ (FiniteGrassmannCarrier q) (FiniteGrassmannEven.body x)) ^ (q + 1) = 0 :=
      FiniteGrassmannCarrier.pow_zero_body_nilpotent hy_body
    -- Need to show: (x - algebraMap ℝ evenCarrier (body x))^(q+1) = 0
    -- The key is that operations on FiniteGrassmannEven are inherited from FiniteGrassmannCarrier
    apply Subtype.ext
    -- Goal: ↑((x - ...)^(q+1)) = ↑0
    -- Need to show: carrier of power = 0
    show ((x - algebraMap ℝ (FiniteGrassmannEven q) (FiniteGrassmannEven.body x)) ^ (q + 1)).val = 0
    -- The carrier of (y^n) equals (carrier of y)^n by induction on n
    have h_pow_val : ∀ n : ℕ, ((x - algebraMap ℝ (FiniteGrassmannEven q) (FiniteGrassmannEven.body x)) ^ n).val =
        (x.val - (algebraMap ℝ (FiniteGrassmannEven q) (FiniteGrassmannEven.body x)).val) ^ n := fun n => by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ, pow_succ]
        -- Goal: ((y^n) * y).val = y.val^n * y.val
        -- For subtypes, (a * b).val = a.val * b.val definitionally
        show (((x - _) ^ n) * (x - _)).val = _
        -- Multiplication on FiniteGrassmannEven (a subring) preserves the underlying value
        calc (((x - _) ^ n) * (x - _)).val
            = ((x - _) ^ n).val * (x - _).val := rfl
          _ = (x.val - _) ^ n * (x - _).val := by rw [ih]
          _ = (x.val - _) ^ n * (x.val - _) := rfl
    rw [h_pow_val]
    -- algebraMap to FiniteGrassmannEven then to carrier equals algebraMap to carrier
    have h_alg : (algebraMap ℝ (FiniteGrassmannEven q) (FiniteGrassmannEven.body x)).val =
                 algebraMap ℝ (FiniteGrassmannCarrier q) (FiniteGrassmannEven.body x) := rfl
    rw [h_alg]
    exact hpow
  odd_nilpotent := fun x hx => by
    -- Odd elements square to 0 using antisymmetry of the sum
    use 1
    funext K
    simp only [pow_succ, pow_zero, one_mul, FiniteGrassmannCarrier.mul_apply,
      FiniteGrassmannCarrier.zero_apply]
    -- Define the summand function
    let f := fun I J => if I ∪ J = K ∧ I ∩ J = ∅ then
        (FiniteGrassmannCarrier.reorderSign I J : ℝ) * x I * x J else 0
    -- The sum S = Σ_I Σ_J f(I,J)
    -- Key observation: f(J,I) = -f(I,J) when both |I|, |J| are odd (from reorderSign_swap_odd)
    -- and f(I,I) = 0 (diagonal terms vanish)
    -- Therefore S = -S, so 2S = 0, so S = 0 (in ℝ)

    -- Strategy: show sum equals its negative via sum reindexing
    -- Key: f(J,I) = -f(I,J) when the condition holds
    have hf_antisym : ∀ I J, f J I = -f I J := by
      intro I J
      simp only [f]
      by_cases hJI_cond : J ∪ I = K ∧ J ∩ I = ∅
      · obtain ⟨hJI_eq, hJI_disj⟩ := hJI_cond
        have hIJ_eq : I ∪ J = K := by rw [Finset.union_comm]; exact hJI_eq
        have hIJ_disj : I ∩ J = ∅ := by rw [Finset.inter_comm]; exact hJI_disj
        have hIJ_cond' : I ∪ J = K ∧ I ∩ J = ∅ := ⟨hIJ_eq, hIJ_disj⟩
        have hJI_cond' : J ∪ I = K ∧ J ∩ I = ∅ := ⟨hJI_eq, hJI_disj⟩
        rw [if_pos hJI_cond', if_pos hIJ_cond']
        -- Now show sign(J,I) x_J x_I = -sign(I,J) x_I x_J
        by_cases hI_even : I.card % 2 = 0
        · -- |I| is even, so x I = 0
          have hxI : x I = 0 := hx I hI_even
          simp only [hxI, mul_zero, zero_mul, neg_zero]
        · by_cases hJ_even : J.card % 2 = 0
          · -- |J| is even, so x J = 0
            have hxJ : x J = 0 := hx J hJ_even
            simp only [hxJ, mul_zero, zero_mul, neg_zero]
          · -- Both |I| and |J| are odd
            have hI_odd : I.card % 2 = 1 := by omega
            have hJ_odd : J.card % 2 = 1 := by omega
            -- Use reorderSign_swap_odd
            have hsign : FiniteGrassmannCarrier.reorderSign J I =
                         -FiniteGrassmannCarrier.reorderSign I J :=
              FiniteGrassmannCarrier.reorderSign_swap_odd hIJ_disj hI_odd hJ_odd
            simp only [hsign, Int.cast_neg, neg_mul]
            congr 1
            ring
      · -- Condition doesn't hold for (J,I)
        have hIJ_cond : ¬(I ∪ J = K ∧ I ∩ J = ∅) := by
          intro ⟨hIJ_eq, hIJ_disj⟩
          apply hJI_cond
          constructor
          · rw [Finset.union_comm]; exact hIJ_eq
          · rw [Finset.inter_comm]; exact hIJ_disj
        simp only [hJI_cond, hIJ_cond, ↓reduceIte, neg_zero]
    -- S = Σ_I Σ_J f(I,J) = Σ_J Σ_I f(I,J) = Σ_I Σ_J f(J,I) = Σ_I Σ_J (-f(I,J)) = -S
    have hsum_eq_neg : (∑ I, ∑ J, f I J) = -(∑ I, ∑ J, f I J) := by
      calc (∑ I, ∑ J, f I J)
          = ∑ J, ∑ I, f I J := Finset.sum_comm
        _ = ∑ I, ∑ J, f J I := by rfl  -- just renaming dummy variables
        _ = ∑ I, ∑ J, (-f I J) := by
            apply Finset.sum_congr rfl
            intro I _
            apply Finset.sum_congr rfl
            intro J _
            exact hf_antisym I J
        _ = -(∑ I, ∑ J, f I J) := by simp only [Finset.sum_neg_distrib]
    -- Now S = -S implies 2S = 0 implies S = 0
    have h2S : 2 * (∑ I, ∑ J, f I J) = 0 := by linarith
    have hS : (∑ I, ∑ J, f I J) = 0 := by linarith
    exact hS
  direct_sum := fun v => by
    -- Decompose v = v_even + v_odd
    let v_even : FiniteGrassmannCarrier q := fun I => if I.card % 2 = 0 then v I else 0
    let v_odd : FiniteGrassmannCarrier q := fun I => if I.card % 2 = 1 then v I else 0
    have hv_even : v_even.isEven := fun I hI => by simp [v_even, hI]
    have hv_odd : v_odd.isOdd := fun I hI => by simp [v_odd, hI]
    use ⟨v_even, hv_even⟩, ⟨v_odd, hv_odd⟩
    funext I
    show v I = v_even I + v_odd I
    simp only [v_even, v_odd]
    by_cases heven : I.card % 2 = 0
    · -- Even case: v_even I = v I, v_odd I = 0
      have hnodd : ¬(I.card % 2 = 1) := by
        intro h; rw [heven] at h; exact absurd h (by decide)
      simp only [heven, ↓reduceIte]
      -- Goal: v I = v I + if 0 = 1 then v I else 0
      simp only [Nat.zero_ne_one, ↓reduceIte, add_zero]
    · -- Odd case: v_even I = 0, v_odd I = v I
      have hodd : I.card % 2 = 1 := by
        have h2 := Nat.mod_two_eq_zero_or_one I.card
        cases h2 with
        | inl h => exact absurd h heven
        | inr h => exact h
      simp only [hodd, ↓reduceIte]
      -- Goal: v I = (if 1 = 0 then v I else 0) + v I
      simp only [Nat.one_ne_zero, ↓reduceIte, zero_add]
  even_mul_even := fun a b ha hb => FiniteGrassmannCarrier.isEven_mul_even a b ha hb
  odd_mul_odd := fun a b ha hb => FiniteGrassmannCarrier.isOdd_mul_odd a b ha hb
  even_mul_odd := fun a b ha hb => by
    intro I hI
    simp only [FiniteGrassmannCarrier.mul_apply]
    apply Finset.sum_eq_zero
    intro I' _
    apply Finset.sum_eq_zero
    intro J _
    split_ifs with h
    · obtain ⟨hIJ_eq, hIJ_disj⟩ := h
      have hcard : I.card = I'.card + J.card := by
        rw [← hIJ_eq]
        exact Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr hIJ_disj)
      -- |I| even = |I'| + |J|. Since a is even and b is odd,
      -- either I' odd (then a I' = 0) or I' even and J even (contradicts b odd) or I' even and J odd (contradicts |I| even)
      rw [hcard] at hI
      cases Nat.even_or_odd I'.card with
      | inl hI'_even =>
        -- I' even, so |J| must be even for sum to be even. But b is odd, so b J = 0 when J even
        have hJ_even : J.card % 2 = 0 := by
          have : (I'.card % 2 + J.card % 2) % 2 = 0 := by omega
          rw [Nat.even_iff.mp hI'_even] at this
          omega
        simp only [hb J hJ_even, mul_zero]
      | inr hI'_odd =>
        -- I' odd, but a is even so a I' = 0
        simp only [ha I' (Nat.odd_iff.mp hI'_odd), mul_zero, zero_mul]
    · rfl
  odd_mul_even := fun a b ha hb => by
    intro I hI
    simp only [FiniteGrassmannCarrier.mul_apply]
    apply Finset.sum_eq_zero
    intro I' _
    apply Finset.sum_eq_zero
    intro J _
    split_ifs with h
    · obtain ⟨hIJ_eq, hIJ_disj⟩ := h
      have hcard : I.card = I'.card + J.card := by
        rw [← hIJ_eq]
        exact Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr hIJ_disj)
      -- |I| even = |I'| + |J|. Since a is odd and b is even,
      -- either I' even (then a I' = 0) or I' odd and J odd (contradicts b even) or I' odd and J even (contradicts |I| even)
      rw [hcard] at hI
      cases Nat.even_or_odd I'.card with
      | inl hI'_even =>
        -- I' even, but a is odd so a I' = 0
        simp only [ha I' (Nat.even_iff.mp hI'_even), mul_zero, zero_mul]
      | inr hI'_odd =>
        -- I' odd, so J must be odd for sum to be even. But b is even, so b J = 0 when J odd
        have hJ_odd : J.card % 2 = 1 := by
          have : (I'.card % 2 + J.card % 2) % 2 = 0 := by omega
          rw [Nat.odd_iff.mp hI'_odd] at this
          omega
        simp only [hb J hJ_odd, mul_zero]
    · rfl

end Supermanifolds.Helpers

/-!
## Evaluation of SuperDomainFunction

Connect `SuperDomainFunction p q` to `finiteGrassmannAlgebra q` via pointwise evaluation.
-/

namespace Supermanifolds

open Supermanifolds.Helpers

/-- Evaluate a super domain function at a point to get a finite Grassmann element. -/
def SuperDomainFunction.evalAtPoint {p q : ℕ} (f : SuperDomainFunction p q)
    (x : Fin p → ℝ) : (finiteGrassmannAlgebra q).carrier :=
  fun I => f.coefficients I x

/-- Evaluation preserves evenness -/
theorem SuperDomainFunction.evalAtPoint_even {p q : ℕ} (f : SuperDomainFunction p q)
    (hf : f.isEven) (x : Fin p → ℝ) : (f.evalAtPoint x).isEven := by
  intro I hI
  simp only [evalAtPoint]
  have h := hf I hI
  rw [h]
  rfl

/-- Evaluation preserves oddness -/
theorem SuperDomainFunction.evalAtPoint_odd {p q : ℕ} (f : SuperDomainFunction p q)
    (hf : f.isOdd) (x : Fin p → ℝ) : (f.evalAtPoint x).isOdd := by
  intro I hI
  simp only [evalAtPoint]
  have h := hf I hI
  rw [h]
  rfl

/-!
## SuperJacobian to SuperMatrix Conversion

At each point, convert `SuperJacobian p q` to `SuperMatrix (finiteGrassmannAlgebra q) p q`.
-/

/-- Convert a SuperJacobian to a SuperMatrix at a point.

    At x₀ ∈ ℝ^p, each entry of the Jacobian (a SuperDomainFunction) is evaluated
    to give an element of the finite Grassmann algebra Λ_q. -/
noncomputable def SuperJacobian.toSuperMatrixAt {p q : ℕ} (J : SuperJacobian p q)
    (x : Fin p → ℝ) : Helpers.SuperMatrix (finiteGrassmannAlgebra q) p q where
  Ablock := fun i j => (J.Ablock i j).evalAtPoint x
  Bblock := fun i j => (J.Bblock i j).evalAtPoint x
  Cblock := fun a j => (J.Cblock a j).evalAtPoint x
  Dblock := fun a b => (J.Dblock a b).evalAtPoint x
  Ablock_even := fun i j => SuperDomainFunction.evalAtPoint_even _ (J.Ablock_even i j) x
  Bblock_odd := fun i j => SuperDomainFunction.evalAtPoint_odd _ (J.Bblock_odd i j) x
  Cblock_odd := fun a j => SuperDomainFunction.evalAtPoint_odd _ (J.Cblock_odd a j) x
  Dblock_even := fun a b => SuperDomainFunction.evalAtPoint_even _ (J.Dblock_even a b) x

/-- The Berezinian of the super Jacobian at a point.

    This connects the super Jacobian to the rigorous Berezinian computation
    in `SuperMatrix.ber`. -/
noncomputable def SuperJacobian.berezinianAt {p q : ℕ} (J : SuperJacobian p q)
    (x : Fin p → ℝ)
    (hD : (finiteGrassmannAlgebra q).IsInvertible (J.toSuperMatrixAt x).D_lifted.det)
    (hBDinv : ∀ i j, ((J.toSuperMatrixAt x).Bblock * (J.toSuperMatrixAt x).D_inv_carrier) i j ∈
        (finiteGrassmannAlgebra q).odd) :
    (finiteGrassmannAlgebra q).evenCarrier :=
  (J.toSuperMatrixAt x).ber hD hBDinv

/-!
## SuperTransition to SuperJacobian Conversion

A `SuperTransition` between charts contains:
- `evenTransition`: the new even coordinates x'(x, θ)
- `oddTransition`: the new odd coordinates θ'(x, θ)

The super Jacobian is computed by taking partial derivatives:
- A block: ∂x'/∂x = partialEven j (evenTransition i)
- B block: ∂x'/∂θ = partialOdd a (evenTransition i)
- C block: ∂θ'/∂x = partialEven j (oddTransition a)
- D block: ∂θ'/∂θ = partialOdd b (oddTransition a)
-/

/-- Convert a SuperTransition to a SuperJacobian.

    The Jacobian is computed by taking partial derivatives of the coordinate
    transformation functions. -/
noncomputable def SuperTransition.toSuperJacobian {dim : SuperDimension} {M : Supermanifold dim}
    {chart₁ chart₂ : SuperChart M} (t : SuperTransition chart₁ chart₂) :
    SuperJacobian dim.even dim.odd where
  Ablock := fun i j => partialEven j (t.evenTransition i)
  Bblock := fun i a => partialOdd a (t.evenTransition i)
  Cblock := fun a j => partialEven j (t.oddTransition a)
  Dblock := fun a b => partialOdd b (t.oddTransition a)
  Ablock_even := fun i j => by
    -- partialEven of an even function is even
    -- partialEven doesn't change the index set, only differentiates the coefficient
    intro I hI
    -- Goal: (partialEven j (evenTransition i)).coefficients I = 0
    -- partialEven gives: coefficient I ↦ fderiv of (evenTransition i).coefficients I
    -- If I has odd cardinality, evenTransition_even says the coefficient is 0
    -- fderiv of the constant 0 function is 0
    simp only [partialEven]
    -- The coefficient at I is the derivative of (evenTransition i).coefficients I
    -- which is 0 because evenTransition i is even
    have hcoeff : (t.evenTransition i).coefficients I = 0 := t.evenTransition_even i I hI
    -- fderiv of 0 is 0
    ext x
    -- Show that the underlying function is the constant 0
    have hfun : (t.evenTransition i).coefficients I = (0 : SmoothFunction dim.even) := hcoeff
    -- (0 : SmoothFunction).toFun = fun _ => 0
    have htoFun : (0 : SmoothFunction dim.even).toFun = fun _ => 0 := rfl
    simp only [hfun, htoFun, fderiv_const_apply, ContinuousLinearMap.zero_apply]
  Bblock_odd := fun i a => by
    -- partialOdd of an even function is odd
    -- partialOdd a f at I: if a ∉ I then sign • f.coefficients(I ∪ {a}) else 0
    intro I hI  -- I has even cardinality
    simp only [partialOdd]
    by_cases ha : a ∈ I
    · -- Case a ∈ I: partialOdd gives 0
      simp only [ha, not_true_eq_false, ↓reduceIte]
    · -- Case a ∉ I: coefficient is sign • (evenTransition i).coefficients(I ∪ {a})
      simp only [ha, not_false_eq_true, ↓reduceIte]
      -- |I ∪ {a}| = |I| + 1, which is odd since |I| is even
      have hIa_odd : (insert a I).card % 2 = 1 := by
        rw [Finset.card_insert_of_notMem ha]
        omega
      -- evenTransition is even, so coefficient at odd index is 0
      have hcoeff : (t.evenTransition i).coefficients (insert a I) = 0 :=
        t.evenTransition_even i (insert a I) hIa_odd
      simp only [hcoeff, smul_zero]
  Cblock_odd := fun a j => by
    -- partialEven of an odd function is odd
    -- partialEven doesn't change the index, just differentiates
    intro I hI  -- I has even cardinality
    simp only [partialEven]
    -- oddTransition is odd, so coefficient at even I is 0
    have hcoeff : (t.oddTransition a).coefficients I = 0 := t.oddTransition_odd a I hI
    ext x
    -- Show that the underlying function is the constant 0
    have hfun : (t.oddTransition a).coefficients I = (0 : SmoothFunction dim.even) := hcoeff
    have htoFun : (0 : SmoothFunction dim.even).toFun = fun _ => 0 := rfl
    simp only [hfun, htoFun, fderiv_const_apply, ContinuousLinearMap.zero_apply]
  Dblock_even := fun a b => by
    -- partialOdd of an odd function is even
    -- partialOdd b f at I: if b ∉ I then sign • f.coefficients(I ∪ {b}) else 0
    intro I hI  -- I has odd cardinality
    simp only [partialOdd]
    by_cases hb : b ∈ I
    · -- Case b ∈ I: partialOdd gives 0
      simp only [hb, not_true_eq_false, ↓reduceIte]
    · -- Case b ∉ I: coefficient is sign • (oddTransition a).coefficients(I ∪ {b})
      simp only [hb, not_false_eq_true, ↓reduceIte]
      -- |I ∪ {b}| = |I| + 1, which is even since |I| is odd
      have hIb_even : (insert b I).card % 2 = 0 := by
        rw [Finset.card_insert_of_notMem hb]
        omega
      -- oddTransition is odd, so coefficient at even index is 0
      have hcoeff : (t.oddTransition a).coefficients (insert b I) = 0 :=
        t.oddTransition_odd a (insert b I) hIb_even
      simp only [hcoeff, smul_zero]

/-- The Berezinian of a SuperTransition at a point.

    This gives the Jacobian factor for coordinate change in Berezin integration:
      ∫ dθ' f(x', θ') = Ber(J)⁻¹ · ∫ dθ (f ∘ φ)(x, θ) -/
noncomputable def SuperTransition.berezinianAt {dim : SuperDimension} {M : Supermanifold dim}
    {chart₁ chart₂ : SuperChart M} (t : SuperTransition chart₁ chart₂)
    (x : Fin dim.even → ℝ)
    (hD : (finiteGrassmannAlgebra dim.odd).IsInvertible
        (t.toSuperJacobian.toSuperMatrixAt x).D_lifted.det)
    (hBDinv : ∀ i j, ((t.toSuperJacobian.toSuperMatrixAt x).Bblock *
        (t.toSuperJacobian.toSuperMatrixAt x).D_inv_carrier) i j ∈
        (finiteGrassmannAlgebra dim.odd).odd) :
    (finiteGrassmannAlgebra dim.odd).evenCarrier :=
  t.toSuperJacobian.berezinianAt x hD hBDinv

end Supermanifolds

end
