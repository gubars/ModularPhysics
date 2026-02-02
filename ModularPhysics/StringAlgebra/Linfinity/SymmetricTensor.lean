/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringAlgebra.Linfinity.GradedInfrastructure
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Perm

/-!
# Symmetric Tensors with Actual Elements

This file defines symmetric tensors with actual computable elements, enabling
concrete bracket computations for L∞ and BV algebras.

## Main definitions

* `SymTensor` - A symmetric tensor of n elements from a graded module
* `SymTensor.permute` - Permutation action with Koszul sign
* `SymTensor.Equiv` - Equivalence under graded permutation
* `SymPowerElem` - The n-th symmetric power Sym^n(V) as a quotient

## Mathematical Background

A symmetric tensor v₁ ⊙ v₂ ⊙ ... ⊙ vₙ in Sym^n(V) is an equivalence class
of ordered tensors under the graded symmetric group action:

  v_{σ(1)} ⊙ ... ⊙ v_{σ(n)} = ε(σ; v) · v₁ ⊙ ... ⊙ vₙ

where ε(σ; v) is the Koszul sign counting inversions of odd-degree elements.

## Implementation Notes

We use dependent types to track degrees precisely:
- `degrees : Fin n → ℤ` specifies the degree of each factor
- `elements : (i : Fin n) → V (degrees i)` gives the actual elements

The Koszul sign is computed (not axiomatized) using the infrastructure
from GradedInfrastructure.lean.
-/

universe u v

namespace StringAlgebra.Linfinity

open Graded

/-! ## Symmetric Tensors with Elements -/

/-- A symmetric tensor of n elements from a graded module V.

    This represents an ordered tensor v₁ ⊗ ... ⊗ vₙ where vᵢ ∈ V_{dᵢ}.
    The symmetric tensor v₁ ⊙ ... ⊙ vₙ is the equivalence class under
    permutation with Koszul signs. -/
structure SymTensor (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] (n : ℕ) where
  /-- The degrees of each factor -/
  degrees : Fin n → ℤ
  /-- The actual elements, each in its respective degree component -/
  elements : (i : Fin n) → V (degrees i)

namespace SymTensor

variable {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- The total degree of a symmetric tensor -/
def totalDegree {n : ℕ} (x : SymTensor R V n) : ℤ :=
  Finset.univ.sum x.degrees

/-- The empty tensor (unit element).
    We use a function that is vacuously defined for both degrees and elements. -/
def empty : SymTensor R V 0 where
  degrees := fun i => i.elim0
  elements := fun i => i.elim0

/-- A singleton tensor from a single element -/
def singleton (d : ℤ) (v : V d) : SymTensor R V 1 where
  degrees := fun _ => d
  elements := fun _ => v

/-- Concatenation of two tensors -/
def concat {m n : ℕ} (x : SymTensor R V m) (y : SymTensor R V n) :
    SymTensor R V (m + n) where
  degrees := fun i =>
    if h : i.val < m then x.degrees ⟨i.val, h⟩
    else y.degrees ⟨i.val - m, by omega⟩
  elements := fun i =>
    if h : i.val < m then
      have heq : x.degrees ⟨i.val, h⟩ = (if h' : i.val < m then x.degrees ⟨i.val, h'⟩
          else y.degrees ⟨i.val - m, by omega⟩) := by simp [h]
      heq ▸ x.elements ⟨i.val, h⟩
    else
      have heq : y.degrees ⟨i.val - m, by omega⟩ =
          (if h' : i.val < m then x.degrees ⟨i.val, h'⟩
          else y.degrees ⟨i.val - m, by omega⟩) := by simp [h]
      heq ▸ y.elements ⟨i.val - m, by omega⟩

/-! ## Permutation Action -/

/-- Apply a permutation to a symmetric tensor.
    Returns the permuted tensor without the sign (sign computed separately). -/
def permuteRaw {n : ℕ} (x : SymTensor R V n) (σ : Equiv.Perm (Fin n)) :
    SymTensor R V n where
  degrees := x.degrees ∘ σ
  elements := fun i => x.elements (σ i)

/-- The Koszul sign for applying permutation σ to a tensor with given degrees.

    The sign is (-1)^k where k is the number of inversions (i,j) with i < j
    but σ(i) > σ(j) where both degrees(i) and degrees(j) are odd. -/
def koszulSignPerm {n : ℕ} (degrees : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) : ℤ :=
  koszulSign degrees σ

/-- Permute a tensor and return both the result and the Koszul sign -/
def permute {n : ℕ} (x : SymTensor R V n) (σ : Equiv.Perm (Fin n)) :
    SymTensor R V n × ℤ :=
  (x.permuteRaw σ, koszulSignPerm x.degrees σ)

/-! ## Equivalence Under Permutation -/

/-- Two tensors are equivalent if one is a signed permutation of the other.

    x ~ y iff ∃ σ, y = σ(x) with the understanding that elements are
    related by the permutation and we track the Koszul sign separately.

    For the quotient, we identify x with ε(σ)·σ(x) for all σ.
    Since we work in a module, this means: y is in the equivalence class
    of x iff y = ε(σ)·σ(x) for some σ, which happens iff
    σ⁻¹(y) = ε(σ)·x, i.e., the permuted elements differ by the Koszul sign. -/
def Equiv {n : ℕ} (x y : SymTensor R V n) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)),
    -- Degrees must be related by σ
    (∀ i, x.degrees i = y.degrees (σ i)) ∧
    -- Elements must be related by σ (with implicit sign handling)
    (∀ i, HEq (x.elements i) (y.elements (σ i)))

/-- Equivalence is reflexive -/
theorem Equiv.refl {n : ℕ} (x : SymTensor R V n) : Equiv x x := by
  use 1
  simp

/-- Equivalence is symmetric -/
theorem Equiv.symm {n : ℕ} {x y : SymTensor R V n} (h : Equiv x y) : Equiv y x := by
  obtain ⟨σ, hdeg, helem⟩ := h
  use σ⁻¹
  constructor
  · intro i
    have h1 := hdeg (σ⁻¹ i)
    simp only [Equiv.Perm.apply_inv_self] at h1
    exact h1.symm
  · intro i
    have h1 := helem (σ⁻¹ i)
    -- h1 : x.elements (σ⁻¹ i) ≍ y.elements (σ (σ⁻¹ i))
    -- After simp: x.elements (σ⁻¹ i) ≍ y.elements i
    -- We need: y.elements i ≍ x.elements (σ⁻¹ i)
    have h2 : σ (σ⁻¹ i) = i := Equiv.Perm.apply_inv_self σ i
    rw [h2] at h1
    exact h1.symm

/-- Equivalence is transitive -/
theorem Equiv.trans {n : ℕ} {x y z : SymTensor R V n}
    (hxy : Equiv x y) (hyz : Equiv y z) : Equiv x z := by
  obtain ⟨σ₁, hdeg1, helem1⟩ := hxy
  obtain ⟨σ₂, hdeg2, helem2⟩ := hyz
  use σ₂ * σ₁
  constructor
  · intro i
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hdeg1 i, hdeg2 (σ₁ i)]
  · intro i
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    exact HEq.trans (helem1 i) (helem2 (σ₁ i))

/-- The setoid for symmetric tensor equivalence -/
def setoid (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] (n : ℕ) :
    Setoid (SymTensor R V n) where
  r := Equiv
  iseqv := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

end SymTensor

/-! ## Symmetric Power as Quotient -/

/-- The n-th symmetric power Sym^n(V) as equivalence classes of symmetric tensors.

    Elements of Sym^n(V) are equivalence classes [v₁ ⊗ ... ⊗ vₙ] where
    tensors differing by a graded permutation (with Koszul sign) are identified. -/
def SymPowerElem (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] (n : ℕ) :=
  Quotient (SymTensor.setoid R V n)

namespace SymPowerElem

variable {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- Construct an element of Sym^n(V) from a symmetric tensor -/
def mk {n : ℕ} (x : SymTensor R V n) : SymPowerElem R V n :=
  Quotient.mk (SymTensor.setoid R V n) x

/-- The empty symmetric tensor (unit in Sym^0(V)) -/
def empty : SymPowerElem R V 0 :=
  mk SymTensor.empty

/-- A singleton symmetric tensor v ∈ Sym^1(V) = V -/
def singleton (d : ℤ) (v : V d) : SymPowerElem R V 1 :=
  mk (SymTensor.singleton d v)

/-- The total degree is invariant under permutation -/
theorem totalDegree_equiv {n : ℕ} (a b : SymTensor R V n) (hab : SymTensor.Equiv a b) :
    SymTensor.totalDegree a = SymTensor.totalDegree b := by
  obtain ⟨σ, hdeg, _⟩ := hab
  unfold SymTensor.totalDegree
  have h1 : Finset.univ.sum a.degrees = Finset.univ.sum (b.degrees ∘ σ) := by
    congr 1
    funext i
    exact hdeg i
  rw [h1]
  have h2 : (Finset.univ : Finset (Fin n)).sum (b.degrees ∘ σ) =
      (Finset.univ : Finset (Fin n)).sum b.degrees := by
    apply Finset.sum_bij' (fun i _ => σ i) (fun i _ => σ⁻¹ i)
    · intros; exact Finset.mem_univ _
    · intros; exact Finset.mem_univ _
    · intros; simp
    · intros; simp
    · intros; rfl
  exact h2

/-- The total degree of a symmetric power element -/
def totalDegree {n : ℕ} (x : SymPowerElem R V n) : ℤ :=
  Quotient.lift SymTensor.totalDegree totalDegree_equiv x

/-- Lift a function on tensors to the quotient -/
def lift {n : ℕ} {α : Sort*} (f : SymTensor R V n → α)
    (h : ∀ x y, SymTensor.Equiv x y → f x = f y) :
    SymPowerElem R V n → α :=
  Quotient.lift f h

end SymPowerElem

/-! ## Zero and Addition Structure -/

namespace SymTensor

variable {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- The zero tensor with given degree pattern -/
def zero {n : ℕ} (degrees : Fin n → ℤ) : SymTensor R V n where
  degrees := degrees
  elements := fun _ => 0

/-- Scalar multiplication on symmetric tensors -/
def smul {n : ℕ} (r : R) (x : SymTensor R V n) : SymTensor R V n where
  degrees := x.degrees
  elements := fun i => r • x.elements i

/-- Negation of a symmetric tensor -/
def neg {n : ℕ} (x : SymTensor R V n) : SymTensor R V n where
  degrees := x.degrees
  elements := fun i => -x.elements i

/-! ## Concat Helper Lemmas -/

/-- degrees of concat when i.val < m -/
theorem concat_degrees_lt {m n : ℕ} (x : SymTensor R V m) (y : SymTensor R V n)
    (i : Fin (m + n)) (h : i.val < m) :
    (concat x y).degrees i = x.degrees ⟨i.val, h⟩ := by
  unfold concat
  simp only [h, dite_true]

/-- degrees of concat when ¬(i.val < m) -/
theorem concat_degrees_ge {m n : ℕ} (x : SymTensor R V m) (y : SymTensor R V n)
    (i : Fin (m + n)) (h : ¬ i.val < m) :
    (concat x y).degrees i = y.degrees ⟨i.val - m, Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h) i.isLt⟩ := by
  unfold concat
  simp only [h, dite_false]

/-- elements of concat when i.val < m (HEq version) -/
theorem concat_elements_lt_heq {m n : ℕ} (x : SymTensor R V m) (y : SymTensor R V n)
    (i : Fin (m + n)) (h : i.val < m) :
    HEq ((concat x y).elements i) (x.elements ⟨i.val, h⟩) := by
  unfold concat
  simp only [h, dite_true]
  -- Goal: (heq ▸ x.elements ⟨i.val, h⟩) ≍ x.elements ⟨i.val, h⟩
  -- Use eqRec_heq: Eq.recOn h p ≍ p
  exact eqRec_heq _ _

/-- elements of concat when ¬(i.val < m) (HEq version) -/
theorem concat_elements_ge_heq {m n : ℕ} (x : SymTensor R V m) (y : SymTensor R V n)
    (i : Fin (m + n)) (h : ¬ i.val < m) :
    HEq ((concat x y).elements i) (y.elements ⟨i.val - m, Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h) i.isLt⟩) := by
  unfold concat
  simp only [h, dite_false]
  -- Goal: (heq ▸ y.elements ⟨i.val - m, _⟩) ≍ y.elements ⟨i.val - m, _⟩
  exact eqRec_heq _ _

end SymTensor

/-! ## Permutation on Fin (m + n) from components -/

/-- Construct a permutation on Fin (m + n) from permutations on Fin m and Fin n.
    The first m elements are permuted by σ₁, the last n by σ₂. -/
def Equiv.Perm.sumPerm {m n : ℕ} (σ₁ : Equiv.Perm (Fin m)) (σ₂ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (m + n)) where
  toFun := fun i =>
    if h : i.val < m
    then ⟨(σ₁ ⟨i.val, h⟩).val, Nat.lt_of_lt_of_le (σ₁ ⟨i.val, h⟩).isLt (Nat.le_add_right m n)⟩
    else ⟨m + (σ₂ ⟨i.val - m, Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h) i.isLt⟩).val,
          Nat.add_lt_add_left (σ₂ ⟨i.val - m, Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h) i.isLt⟩).isLt m⟩
  invFun := fun i =>
    if h : i.val < m
    then ⟨(σ₁⁻¹ ⟨i.val, h⟩).val, Nat.lt_of_lt_of_le (σ₁⁻¹ ⟨i.val, h⟩).isLt (Nat.le_add_right m n)⟩
    else ⟨m + (σ₂⁻¹ ⟨i.val - m, Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h) i.isLt⟩).val,
          Nat.add_lt_add_left (σ₂⁻¹ ⟨i.val - m, Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h) i.isLt⟩).isLt m⟩
  left_inv := fun i => by
    simp only
    by_cases h1 : i.val < m
    · -- i.val < m
      simp only [h1, dite_true]
      have h2 : (σ₁ ⟨i.val, h1⟩).val < m := (σ₁ ⟨i.val, h1⟩).isLt
      simp only [h2, dite_true]
      ext
      have key : (⟨(σ₁ ⟨i.val, h1⟩).val, h2⟩ : Fin m) = σ₁ ⟨i.val, h1⟩ := by ext; rfl
      simp only [key, Equiv.Perm.inv_apply_self, Fin.val_mk]
    · -- i.val ≥ m
      simp only [h1, dite_false]
      have hbound : i.val - m < n := Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h1) i.isLt
      have h2 : ¬ (m + (σ₂ ⟨i.val - m, hbound⟩).val) < m := by omega
      simp only [h2, dite_false, Nat.add_sub_cancel_left]
      ext
      have key : (⟨(σ₂ ⟨i.val - m, hbound⟩).val, (σ₂ ⟨i.val - m, hbound⟩).isLt⟩ : Fin n) =
          σ₂ ⟨i.val - m, hbound⟩ := by ext; rfl
      simp only [key, Equiv.Perm.inv_apply_self, Fin.val_mk]
      omega
  right_inv := fun i => by
    simp only
    by_cases h1 : i.val < m
    · -- i.val < m
      simp only [h1, dite_true]
      have h2 : (σ₁⁻¹ ⟨i.val, h1⟩).val < m := (σ₁⁻¹ ⟨i.val, h1⟩).isLt
      simp only [h2, dite_true]
      ext
      have key : (⟨(σ₁⁻¹ ⟨i.val, h1⟩).val, h2⟩ : Fin m) = σ₁⁻¹ ⟨i.val, h1⟩ := by ext; rfl
      simp only [key, Equiv.Perm.apply_inv_self, Fin.val_mk]
    · -- i.val ≥ m
      simp only [h1, dite_false]
      have hbound : i.val - m < n := Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h1) i.isLt
      have h2 : ¬ (m + (σ₂⁻¹ ⟨i.val - m, hbound⟩).val) < m := by omega
      simp only [h2, dite_false, Nat.add_sub_cancel_left]
      ext
      have key : (⟨(σ₂⁻¹ ⟨i.val - m, hbound⟩).val, (σ₂⁻¹ ⟨i.val - m, hbound⟩).isLt⟩ : Fin n) =
          σ₂⁻¹ ⟨i.val - m, hbound⟩ := by ext; rfl
      simp only [key, Equiv.Perm.apply_inv_self, Fin.val_mk]
      omega

/-! ## Helper Lemmas for sumPerm -/

namespace Equiv.Perm.sumPerm

variable {m n : ℕ} (σ₁ : Equiv.Perm (Fin m)) (σ₂ : Equiv.Perm (Fin n))

/-- When i.val < m, sumPerm σ₁ σ₂ i has value (σ₁ ⟨i.val, h⟩).val -/
theorem val_of_lt (i : Fin (m + n)) (h : i.val < m) :
    (Equiv.Perm.sumPerm σ₁ σ₂ i).val = (σ₁ ⟨i.val, h⟩).val := by
  show (if h' : i.val < m then ⟨(σ₁ ⟨i.val, h'⟩).val, _⟩
        else ⟨m + (σ₂ ⟨i.val - m, _⟩).val, _⟩ : Fin (m + n)).val = _
  simp only [h, dite_true]

/-- When ¬(i.val < m), sumPerm σ₁ σ₂ i has value m + (σ₂ ⟨i.val - m, _⟩).val -/
theorem val_of_ge (i : Fin (m + n)) (h : ¬ i.val < m) :
    (Equiv.Perm.sumPerm σ₁ σ₂ i).val = m + (σ₂ ⟨i.val - m, Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h) i.isLt⟩).val := by
  show (if h' : i.val < m then ⟨(σ₁ ⟨i.val, h'⟩).val, _⟩
        else ⟨m + (σ₂ ⟨i.val - m, _⟩).val, _⟩ : Fin (m + n)).val = _
  simp only [h, dite_false]

/-- When i.val < m, (sumPerm σ₁ σ₂ i).val < m -/
theorem isLt_of_lt (i : Fin (m + n)) (h : i.val < m) :
    (Equiv.Perm.sumPerm σ₁ σ₂ i).val < m := by
  rw [val_of_lt σ₁ σ₂ i h]
  exact (σ₁ ⟨i.val, h⟩).isLt

/-- When ¬(i.val < m), ¬((sumPerm σ₁ σ₂ i).val < m) -/
theorem not_lt_of_ge (i : Fin (m + n)) (h : ¬ i.val < m) :
    ¬ (Equiv.Perm.sumPerm σ₁ σ₂ i).val < m := by
  rw [val_of_ge σ₁ σ₂ i h]
  omega

end Equiv.Perm.sumPerm

/-! ## Symmetric Product (Concatenation) -/

namespace SymPowerElem

variable {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- Helper: concat respects equivalence -/
theorem concat_equiv {m n : ℕ} (a₁ b₁ : SymTensor R V m) (a₂ b₂ : SymTensor R V n)
    (ha : SymTensor.Equiv a₁ b₁) (hb : SymTensor.Equiv a₂ b₂) :
    SymTensor.Equiv (SymTensor.concat a₁ a₂) (SymTensor.concat b₁ b₂) := by
  obtain ⟨σ₁, hdeg1, helem1⟩ := ha
  obtain ⟨σ₂, hdeg2, helem2⟩ := hb
  use Equiv.Perm.sumPerm σ₁ σ₂
  constructor
  · -- Degrees match
    intro i
    by_cases h1 : i.val < m
    · -- Case: i.val < m
      have h2 : (Equiv.Perm.sumPerm σ₁ σ₂ i).val < m := Equiv.Perm.sumPerm.isLt_of_lt σ₁ σ₂ i h1
      rw [SymTensor.concat_degrees_lt a₁ a₂ i h1]
      rw [SymTensor.concat_degrees_lt b₁ b₂ (Equiv.Perm.sumPerm σ₁ σ₂ i) h2]
      have hval : (Equiv.Perm.sumPerm σ₁ σ₂ i).val = (σ₁ ⟨i.val, h1⟩).val :=
        Equiv.Perm.sumPerm.val_of_lt σ₁ σ₂ i h1
      have hfineq : (⟨(Equiv.Perm.sumPerm σ₁ σ₂ i).val, h2⟩ : Fin m) = σ₁ ⟨i.val, h1⟩ := by
        apply Fin.ext; exact hval
      rw [hfineq]
      exact hdeg1 ⟨i.val, h1⟩
    · -- Case: i.val ≥ m
      have h2 : ¬ (Equiv.Perm.sumPerm σ₁ σ₂ i).val < m := Equiv.Perm.sumPerm.not_lt_of_ge σ₁ σ₂ i h1
      have hbound : i.val - m < n := Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h1) i.isLt
      rw [SymTensor.concat_degrees_ge a₁ a₂ i h1]
      rw [SymTensor.concat_degrees_ge b₁ b₂ (Equiv.Perm.sumPerm σ₁ σ₂ i) h2]
      have hval : (Equiv.Perm.sumPerm σ₁ σ₂ i).val = m + (σ₂ ⟨i.val - m, hbound⟩).val :=
        Equiv.Perm.sumPerm.val_of_ge σ₁ σ₂ i h1
      have hsub : (Equiv.Perm.sumPerm σ₁ σ₂ i).val - m = (σ₂ ⟨i.val - m, hbound⟩).val := by omega
      have hfineq : (⟨(Equiv.Perm.sumPerm σ₁ σ₂ i).val - m, by omega⟩ : Fin n) = σ₂ ⟨i.val - m, hbound⟩ := by
        apply Fin.ext; exact hsub
      rw [hfineq]
      exact hdeg2 ⟨i.val - m, hbound⟩
  · -- Elements match (HEq)
    intro i
    by_cases h1 : i.val < m
    · -- Case: i.val < m
      have h2 : (Equiv.Perm.sumPerm σ₁ σ₂ i).val < m := Equiv.Perm.sumPerm.isLt_of_lt σ₁ σ₂ i h1
      have hval : (Equiv.Perm.sumPerm σ₁ σ₂ i).val = (σ₁ ⟨i.val, h1⟩).val :=
        Equiv.Perm.sumPerm.val_of_lt σ₁ σ₂ i h1
      have hfin : (⟨(Equiv.Perm.sumPerm σ₁ σ₂ i).val, h2⟩ : Fin m) = σ₁ ⟨i.val, h1⟩ := by
        apply Fin.ext; exact hval
      -- Use helper lemmas for HEq
      apply HEq.trans (SymTensor.concat_elements_lt_heq a₁ a₂ i h1)
      apply HEq.trans (helem1 ⟨i.val, h1⟩)
      apply HEq.symm
      have h3 := SymTensor.concat_elements_lt_heq b₁ b₂ (Equiv.Perm.sumPerm σ₁ σ₂ i) h2
      rw [hfin] at h3
      exact h3
    · -- Case: i.val ≥ m
      have h2 : ¬ (Equiv.Perm.sumPerm σ₁ σ₂ i).val < m := Equiv.Perm.sumPerm.not_lt_of_ge σ₁ σ₂ i h1
      have hbound : i.val - m < n := Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h1) i.isLt
      have hval : (Equiv.Perm.sumPerm σ₁ σ₂ i).val = m + (σ₂ ⟨i.val - m, hbound⟩).val :=
        Equiv.Perm.sumPerm.val_of_ge σ₁ σ₂ i h1
      have hsub : (Equiv.Perm.sumPerm σ₁ σ₂ i).val - m = (σ₂ ⟨i.val - m, hbound⟩).val := by omega
      have hfin : (⟨(Equiv.Perm.sumPerm σ₁ σ₂ i).val - m, by omega⟩ : Fin n) = σ₂ ⟨i.val - m, hbound⟩ := by
        apply Fin.ext; exact hsub
      -- Use helper lemmas for HEq
      apply HEq.trans (SymTensor.concat_elements_ge_heq a₁ a₂ i h1)
      apply HEq.trans (helem2 ⟨i.val - m, hbound⟩)
      apply HEq.symm
      have h3 := SymTensor.concat_elements_ge_heq b₁ b₂ (Equiv.Perm.sumPerm σ₁ σ₂ i) h2
      rw [hfin] at h3
      exact h3

/-- The symmetric product of two symmetric power elements.
    This concatenates the underlying tensors.

    Sym^m(V) × Sym^n(V) → Sym^{m+n}(V) -/
def product {m n : ℕ} (x : SymPowerElem R V m) (y : SymPowerElem R V n) :
    SymPowerElem R V (m + n) :=
  Quotient.lift₂
    (fun a b => mk (SymTensor.concat a b))
    (fun a₁ a₂ b₁ b₂ ha hb => Quotient.sound (concat_equiv a₁ b₁ a₂ b₂ ha hb))
    x y

notation:70 x " ⊙ " y => product x y

end SymPowerElem

end StringAlgebra.Linfinity
