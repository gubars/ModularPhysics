import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.FunctionField
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Divisors on Algebraic Curves (Pure Algebraic Approach)

This file develops the theory of divisors on algebraic curves from a purely
algebraic perspective, without reference to Riemann surfaces or complex manifolds.

## Main Definitions

* `Divisor` - Formal sum of points with integer coefficients
* `Divisor.degree` - Sum of coefficients
* `principalDivisor` - The divisor div(f) of a nonzero function
* `LinearlyEquivalent` - D₁ ~ D₂ iff D₁ - D₂ is principal
-/

namespace RiemannSurfaces.Algebraic.Core

open Set Classical

/-!
## Divisors as Formal Sums
-/

/-- A divisor on an algebraic curve -/
structure Divisor (C : AlgebraicCurve) where
  /-- Coefficient at each point -/
  coeff : C.Point → ℤ
  /-- Finite support -/
  finiteSupport : Set.Finite { p | coeff p ≠ 0 }

namespace Divisor

variable {C : AlgebraicCurve}

/-!
### Basic Operations
-/

/-- The zero divisor -/
def zero : Divisor C where
  coeff := fun _ => 0
  finiteSupport := by
    convert Set.finite_empty
    ext p
    simp

/-- Addition of divisors -/
def add (D₁ D₂ : Divisor C) : Divisor C where
  coeff := fun p => D₁.coeff p + D₂.coeff p
  finiteSupport := by
    apply Set.Finite.subset (D₁.finiteSupport.union D₂.finiteSupport)
    intro p hp
    simp only [mem_setOf_eq] at hp
    simp only [mem_union, mem_setOf_eq]
    by_contra h
    push_neg at h
    omega

/-- Negation of divisors -/
def neg (D : Divisor C) : Divisor C where
  coeff := fun p => -D.coeff p
  finiteSupport := by
    convert D.finiteSupport using 1
    ext p; simp

/-- Subtraction of divisors -/
def sub (D₁ D₂ : Divisor C) : Divisor C := add D₁ (neg D₂)

instance : Zero (Divisor C) := ⟨zero⟩
instance : Add (Divisor C) := ⟨add⟩
instance : Neg (Divisor C) := ⟨neg⟩
instance : Sub (Divisor C) := ⟨sub⟩

/-- Extensionality for divisors -/
@[ext]
theorem ext {D₁ D₂ : Divisor C} (h : ∀ p, D₁.coeff p = D₂.coeff p) : D₁ = D₂ := by
  cases D₁; cases D₂; simp only [mk.injEq]; ext p; exact h p

@[simp] theorem zero_coeff (p : C.Point) : (0 : Divisor C).coeff p = 0 := rfl
@[simp] theorem add_coeff (D₁ D₂ : Divisor C) (p : C.Point) :
    (D₁ + D₂).coeff p = D₁.coeff p + D₂.coeff p := rfl
@[simp] theorem neg_coeff (D : Divisor C) (p : C.Point) : (-D).coeff p = -D.coeff p := rfl

@[simp] theorem sub_coeff (D₁ D₂ : Divisor C) (p : C.Point) :
    (D₁ - D₂).coeff p = D₁.coeff p - D₂.coeff p := by
  show (add D₁ (neg D₂)).coeff p = D₁.coeff p - D₂.coeff p
  simp only [add, neg]
  ring

/-- Divisors form an abelian group -/
instance : AddCommGroup (Divisor C) where
  add_assoc := fun a b c => by ext p; simp [add_assoc]
  zero_add := fun a => by ext p; simp
  add_zero := fun a => by ext p; simp
  neg_add_cancel := fun a => by ext p; simp
  add_comm := fun a b => by ext p; simp [add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec

/-!
### Point Divisors
-/

/-- A single point as a divisor.
    Uses classical logic to handle decidability of point equality. -/
noncomputable def point (p : C.Point) : Divisor C where
  coeff := fun q => if q = p then 1 else 0
  finiteSupport := by
    apply Set.Finite.subset (Set.finite_singleton p)
    intro q hq
    simp only [mem_setOf_eq, mem_singleton_iff] at hq ⊢
    by_contra h
    have : (if q = p then (1 : ℤ) else 0) = 0 := if_neg h
    exact hq this

/-- Point divisor at the same point -/
theorem point_coeff_self (p : C.Point) : (point p).coeff p = 1 := by
  simp only [point, if_true]

/-- Point divisor at a different point -/
theorem point_coeff_ne (p q : C.Point) (h : q ≠ p) : (point p).coeff q = 0 := by
  simp only [point, if_neg h]

/-!
### Scalar Multiplication
-/

/-- Scalar multiple of a divisor -/
def smul (n : ℤ) (D : Divisor C) : Divisor C where
  coeff := fun p => n * D.coeff p
  finiteSupport := by
    by_cases hn : n = 0
    · convert Set.finite_empty
      ext p
      simp only [hn, zero_mul, mem_setOf_eq, ne_eq, not_true_eq_false, mem_empty_iff_false]
    · convert D.finiteSupport using 1
      ext p
      simp only [mem_setOf_eq]
      constructor
      · intro h hD; rw [hD, mul_zero] at h; exact h rfl
      · intro h; exact fun hcontra => h (mul_eq_zero.mp hcontra |>.resolve_left hn)

instance : SMul ℤ (Divisor C) := ⟨smul⟩

@[simp] theorem smul_coeff (n : ℤ) (D : Divisor C) (p : C.Point) :
    (n • D).coeff p = n * D.coeff p := rfl

/-!
## Degree of a Divisor
-/

/-- The support of a divisor -/
def support (D : Divisor C) : Set C.Point := { p | D.coeff p ≠ 0 }

/-- The degree of a divisor (sum of coefficients) -/
noncomputable def degree (D : Divisor C) : ℤ :=
  D.finiteSupport.toFinset.sum (fun p => D.coeff p)

/-- The zero divisor has degree 0 -/
@[simp] theorem degree_zero : (0 : Divisor C).degree = 0 := by
  unfold degree
  have h : (0 : Divisor C).finiteSupport.toFinset = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    rw [Set.Finite.mem_toFinset, mem_setOf_eq] at hp
    simp only [zero_coeff, ne_eq, not_true_eq_false] at hp
  rw [h, Finset.sum_empty]

/-- Degree of a point divisor is 1 -/
theorem degree_point (p : C.Point) : (point p).degree = 1 := by
  unfold degree
  have hsup : (point p).finiteSupport.toFinset = {p} := by
    ext q
    simp only [Set.Finite.mem_toFinset, mem_setOf_eq, Finset.mem_singleton]
    constructor
    · intro h
      by_contra hne
      simp only [point, if_neg hne, ne_eq, not_true_eq_false] at h
    · intro heq
      simp only [heq, point, if_true, ne_eq, one_ne_zero, not_false_eq_true]
  rw [hsup]
  simp only [Finset.sum_singleton, point_coeff_self]

/-- Degree is additive -/
theorem degree_add (D₁ D₂ : Divisor C) : (D₁ + D₂).degree = D₁.degree + D₂.degree := by
  unfold degree
  let S := (D₁ + D₂).finiteSupport.toFinset
  let S₁ := D₁.finiteSupport.toFinset
  let S₂ := D₂.finiteSupport.toFinset
  let U := S₁ ∪ S₂

  have hS_sub : S ⊆ U := by
    intro p hp
    rw [Set.Finite.mem_toFinset] at hp
    rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    simp only [mem_setOf_eq] at hp ⊢
    by_contra h
    push_neg at h
    simp only [add_coeff] at hp
    omega

  have hS1_sub : S₁ ⊆ U := Finset.subset_union_left
  have hS2_sub : S₂ ⊆ U := Finset.subset_union_right

  have hsum_S : S.sum (fun p => (D₁ + D₂).coeff p) = U.sum (fun p => (D₁ + D₂).coeff p) := by
    apply Finset.sum_subset hS_sub
    intro p _ hp
    rw [Set.Finite.mem_toFinset, mem_setOf_eq, not_not] at hp
    exact hp

  have hsum_S1 : S₁.sum D₁.coeff = U.sum D₁.coeff := by
    apply Finset.sum_subset hS1_sub
    intro p _ hp
    rw [Set.Finite.mem_toFinset, mem_setOf_eq, not_not] at hp
    exact hp

  have hsum_S2 : S₂.sum D₂.coeff = U.sum D₂.coeff := by
    apply Finset.sum_subset hS2_sub
    intro p _ hp
    rw [Set.Finite.mem_toFinset, mem_setOf_eq, not_not] at hp
    exact hp

  rw [hsum_S, hsum_S1, hsum_S2, ← Finset.sum_add_distrib]
  rfl

/-- Degree of negation -/
@[simp] theorem degree_neg (D : Divisor C) : (-D).degree = -D.degree := by
  unfold degree
  have hsupp : (-D).finiteSupport.toFinset = D.finiteSupport.toFinset := by
    ext p; simp [Set.Finite.mem_toFinset, mem_setOf_eq]
  rw [hsupp]
  simp only [neg_coeff, Finset.sum_neg_distrib]

/-- Subtraction is add neg -/
theorem sub_eq_add_neg (D₁ D₂ : Divisor C) : D₁ - D₂ = D₁ + -D₂ := rfl

/-- Degree of scalar multiplication -/
theorem degree_smul (n : ℤ) (D : Divisor C) : (n • D).degree = n * D.degree := by
  unfold degree
  by_cases hn : n = 0
  · subst hn
    simp only [zero_mul]
    have h : ((0 : ℤ) • D).finiteSupport.toFinset = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      rw [Set.Finite.mem_toFinset, mem_setOf_eq] at hp
      simp only [smul_coeff, zero_mul, ne_eq, not_true_eq_false] at hp
    rw [h, Finset.sum_empty]
  · have hsupp : (n • D).finiteSupport.toFinset = D.finiteSupport.toFinset := by
      ext p
      simp only [Set.Finite.mem_toFinset, mem_setOf_eq, smul_coeff]
      constructor
      · intro h hD; rw [hD, mul_zero] at h; exact h rfl
      · intro h; exact fun hcontra => h (mul_eq_zero.mp hcontra |>.resolve_left hn)
    rw [hsupp, Finset.mul_sum]
    rfl

/-!
## Principal Divisors
-/

/-- The divisor of a nonzero function in the function field -/
noncomputable def divOf (f : C.FunctionField) (hf : f ≠ 0) : Divisor C where
  coeff := fun p => C.valuation p f
  finiteSupport := C.valuation_finiteSupport f hf

/-- Coefficient of div(f) at p is the valuation -/
theorem divOf_coeff (f : C.FunctionField) (hf : f ≠ 0) (p : C.Point) :
    (divOf f hf).coeff p = C.valuation p f := rfl

/-- The degree of div(f) equals the order sum (argument principle uses this).
    This connects Core.Divisor.divOf to AlgebraicCurve.orderSum. -/
theorem divOf_degree_eq_orderSum (f : C.FunctionField) (hf : f ≠ 0) :
    (divOf f hf).degree = C.orderSum f hf := by
  -- Both are sums of valuations over the same finite support
  unfold degree AlgebraicCurve.orderSum AlgebraicCurve.divisorOf AlgebraicCurve.Divisor.degree
  simp only
  -- The supports are the same set and coefficients are the same
  have h_supp_eq : (divOf f hf).finiteSupport.toFinset =
      (C.valuation_finiteSupport f hf).toFinset := by
    ext p
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, divOf, ne_eq]
  rw [h_supp_eq]
  -- The coefficients are the same (both are C.valuation p f)
  apply Finset.sum_congr rfl
  intro p _
  rfl

/-- div(f) + div(g) = div(fg) for f, g ≠ 0 -/
theorem divOf_mul (f g : C.FunctionField) (hf : f ≠ 0) (hg : g ≠ 0) :
    divOf f hf + divOf g hg = divOf (f * g) (mul_ne_zero hf hg) := by
  ext p
  simp only [add_coeff, divOf_coeff]
  exact (C.valuation_mul p f g hf hg).symm

/-- div(f⁻¹) = -div(f) -/
theorem divOf_inv (f : C.FunctionField) (hf : f ≠ 0) :
    divOf f⁻¹ (inv_ne_zero hf) = -divOf f hf := by
  ext p
  simp only [neg_coeff, divOf_coeff]
  exact C.valuation_inv p f hf

/-- A divisor is principal if it's div(f) for some f ∈ K(C)* -/
def IsPrincipal (D : Divisor C) : Prop :=
  ∃ (f : C.FunctionField) (hf : f ≠ 0), D = divOf f hf

/-!
## Linear Equivalence
-/

/-- Two divisors are linearly equivalent if they differ by a principal divisor -/
def LinearlyEquivalent (D₁ D₂ : Divisor C) : Prop :=
  IsPrincipal (D₁ - D₂)

notation:50 D₁ " ~ " D₂ => LinearlyEquivalent D₁ D₂

/-- Linear equivalence is reflexive -/
theorem linearlyEquivalent_refl (D : Divisor C) : D ~ D := by
  unfold LinearlyEquivalent IsPrincipal
  use 1, one_ne_zero
  ext p
  simp only [sub_self, zero_coeff, divOf_coeff, C.valuation_one]

/-- Linear equivalence is symmetric -/
theorem linearlyEquivalent_symm {D₁ D₂ : Divisor C} (h : D₁ ~ D₂) : D₂ ~ D₁ := by
  unfold LinearlyEquivalent IsPrincipal at h ⊢
  obtain ⟨f, hf, heq⟩ := h
  use f⁻¹, inv_ne_zero hf
  ext p
  have h1 := congrArg (·.coeff p) heq
  simp only [sub_coeff, divOf_coeff] at h1 ⊢
  rw [C.valuation_inv p f hf]
  omega

/-- Linear equivalence is transitive -/
theorem linearlyEquivalent_trans {D₁ D₂ D₃ : Divisor C}
    (h12 : D₁ ~ D₂) (h23 : D₂ ~ D₃) : D₁ ~ D₃ := by
  unfold LinearlyEquivalent IsPrincipal at h12 h23 ⊢
  obtain ⟨f, hf, heq1⟩ := h12
  obtain ⟨g, hg, heq2⟩ := h23
  use f * g, mul_ne_zero hf hg
  ext p
  have h1 := congrArg (·.coeff p) heq1
  have h2 := congrArg (·.coeff p) heq2
  simp only [sub_coeff, divOf_coeff] at h1 h2 ⊢
  rw [C.valuation_mul p f g hf hg]
  omega

/-!
## Effective Divisors
-/

/-- A divisor is effective if all coefficients are non-negative -/
def IsEffective (D : Divisor C) : Prop := ∀ p, 0 ≤ D.coeff p

/-- The zero divisor is effective -/
theorem zero_isEffective : IsEffective (0 : Divisor C) := fun _ => le_refl 0

/-- Point divisors are effective -/
theorem point_isEffective (p : C.Point) : IsEffective (point p) := by
  intro q
  unfold point
  by_cases h : q = p
  · simp only [if_pos h]; omega
  · simp only [if_neg h]; omega

/-- Effective divisors have non-negative degree -/
theorem degree_nonneg_of_isEffective (D : Divisor C) (heff : IsEffective D) :
    0 ≤ D.degree := by
  unfold degree
  apply Finset.sum_nonneg
  intro p _
  exact heff p

/-!
### Support Cardinality (for induction)
-/

/-- The cardinality of the support (finite by definition) -/
noncomputable def supportCard (D : Divisor C) : ℕ := D.finiteSupport.toFinset.card

/-- A nonzero divisor has nonempty support -/
theorem exists_mem_support_of_ne_zero (D : Divisor C) (hD : D ≠ 0) :
    ∃ p, p ∈ D.support := by
  by_contra h
  push_neg at h
  have h0 : D = 0 := by
    ext p
    have hp := h p
    simp only [support, Set.mem_setOf_eq, not_not] at hp
    simp [hp]
  exact hD h0

/-- Subtracting the coefficient-multiple of a point reduces support -/
theorem supportCard_sub_coeff_point_lt (D : Divisor C) (p : C.Point) (hp : D.coeff p ≠ 0) :
    (D - D.coeff p • point p).supportCard < D.supportCard := by
  unfold supportCard
  apply Finset.card_lt_card
  constructor
  · -- show (D - D.coeff p • point p).finiteSupport ⊆ D.finiteSupport
    intro q hq
    rw [Set.Finite.mem_toFinset] at hq ⊢
    simp only [Set.mem_setOf_eq] at hq ⊢
    by_contra hq0
    simp only [sub_coeff, smul_coeff, point] at hq
    by_cases hqp : q = p
    · simp only [hqp, if_true, mul_one] at hq; omega
    · simp only [if_neg hqp, mul_zero, sub_zero] at hq; exact hq hq0
  · -- show not ⊆ in other direction
    intro h
    have hp_mem : p ∈ D.finiteSupport.toFinset := by
      rw [Set.Finite.mem_toFinset]; simp only [Set.mem_setOf_eq]; exact hp
    have hp_not : p ∉ (D - D.coeff p • point p).finiteSupport.toFinset := by
      rw [Set.Finite.mem_toFinset]
      simp only [Set.mem_setOf_eq, sub_coeff, smul_coeff, point, if_true, mul_one, sub_self,
                 ne_eq, not_true_eq_false, not_false_eq_true]
    exact hp_not (h hp_mem)

end Divisor

end RiemannSurfaces.Algebraic.Core
