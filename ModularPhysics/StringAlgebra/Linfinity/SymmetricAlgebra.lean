/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringAlgebra.Linfinity.SymmetricTensor

/-!
# Symmetric Algebra with Actual Elements

This file defines the symmetric algebra S(V) and reduced symmetric algebra S⁺(V)
with actual computable elements, building on the symmetric tensors.

## Main definitions

* `SymAlgebraElem` - The full symmetric algebra S(V) = ⨁_{n≥0} Sym^n(V)
* `ReducedSymAlgebraElem` - The reduced symmetric algebra S⁺(V) = ⨁_{n≥1} Sym^n(V)
* `IsShuffle` - Definition of (p,q)-shuffles
* `SymTensor.splitAt` - Split a tensor at position p

## Mathematical Background

The symmetric coalgebra structure is given by the shuffle coproduct:
  Δ(v₁ ⊙ ... ⊙ vₙ) = ∑_{(p,q)-shuffles σ} ε(σ;v) (v_{σ(1)} ⊙ ... ⊙ v_{σ(p)}) ⊗ (v_{σ(p+1)} ⊙ ... ⊙ v_{σ(n)})

where a (p,q)-shuffle is a permutation σ of {1,...,n} with n=p+q such that
σ(1) < ... < σ(p) and σ(p+1) < ... < σ(n).

The coproduct is coassociative and makes S(V) into a graded cocommutative coalgebra.
-/

universe u v

namespace StringAlgebra.Linfinity

open Graded

/-! ## Symmetric Algebra Elements -/

/-- An element of the symmetric algebra S(V) = ⨁_{n≥0} Sym^n(V).

    This is a dependent pair (n, x) where x ∈ Sym^n(V). -/
def SymAlgebraElem (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] :=
  Σ (n : ℕ), SymPowerElem R V n

/-- An element of the reduced symmetric algebra S⁺(V) = ⨁_{n≥1} Sym^n(V).

    This excludes the unit (empty tensor) component. -/
structure ReducedSymAlgebraElem (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] where
  /-- The word length (arity) -/
  wordLength : ℕ
  /-- Proof that word length is at least 1 -/
  wordLength_pos : wordLength ≥ 1
  /-- The underlying symmetric power element -/
  elem : SymPowerElem R V wordLength

namespace SymAlgebraElem

variable {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- The word length (arity) of a symmetric algebra element -/
def wordLength (x : SymAlgebraElem R V) : ℕ := x.1

/-- The total degree of a symmetric algebra element -/
def totalDegree (x : SymAlgebraElem R V) : ℤ := x.2.totalDegree

/-- The unit element 1 ∈ S⁰(V) -/
def one : SymAlgebraElem R V := ⟨0, SymPowerElem.empty⟩

/-- Construct from a symmetric power element -/
def ofSymPower {n : ℕ} (x : SymPowerElem R V n) : SymAlgebraElem R V := ⟨n, x⟩

/-- Construct from a single element v ∈ V -/
def ofElement (d : ℤ) (v : V d) : SymAlgebraElem R V :=
  ⟨1, SymPowerElem.singleton d v⟩

/-- The product in the symmetric algebra.
    S^m(V) ⊗ S^n(V) → S^{m+n}(V) -/
def mul (x y : SymAlgebraElem R V) : SymAlgebraElem R V :=
  ⟨x.1 + y.1, x.2 ⊙ y.2⟩

instance : HMul (SymAlgebraElem R V) (SymAlgebraElem R V) (SymAlgebraElem R V) where
  hMul := mul

end SymAlgebraElem

namespace ReducedSymAlgebraElem

variable {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- The total degree of a reduced symmetric algebra element -/
def totalDegree (x : ReducedSymAlgebraElem R V) : ℤ := x.elem.totalDegree

/-- Construct from a symmetric power element with n ≥ 1 -/
def ofSymPower {n : ℕ} (hn : n ≥ 1) (x : SymPowerElem R V n) : ReducedSymAlgebraElem R V :=
  ⟨n, hn, x⟩

/-- Construct from a single element v ∈ V -/
def ofElement (d : ℤ) (v : V d) : ReducedSymAlgebraElem R V :=
  ⟨1, Nat.one_pos, SymPowerElem.singleton d v⟩

/-- Convert to the full symmetric algebra -/
def toSymAlgebra (x : ReducedSymAlgebraElem R V) : SymAlgebraElem R V :=
  ⟨x.wordLength, x.elem⟩

/-- The product in the reduced symmetric algebra.
    S⁺(V) ⊗ S⁺(V) → S⁺(V) -/
def mul (x y : ReducedSymAlgebraElem R V) : ReducedSymAlgebraElem R V :=
  ⟨x.wordLength + y.wordLength,
   Nat.le_add_right_of_le x.wordLength_pos,
   x.elem ⊙ y.elem⟩

end ReducedSymAlgebraElem

/-! ## Shuffles -/

/-- A (p,q)-shuffle is a permutation σ of Fin (p+q) such that
    σ⁻¹ restricted to {0,...,p-1} is increasing and
    σ⁻¹ restricted to {p,...,p+q-1} is increasing.

    Equivalently, the images of {0,...,p-1} and {p,...,p+q-1} appear
    in increasing order in σ. -/
def IsShuffle (p q : ℕ) (σ : Equiv.Perm (Fin (p + q))) : Prop :=
  (∀ i j : Fin p, i < j → (σ ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right p q)⟩).val <
                          (σ ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right p q)⟩).val) ∧
  (∀ i j : Fin q, i < j → (σ ⟨p + i.val, Nat.add_lt_add_left i.isLt p⟩).val <
                          (σ ⟨p + j.val, Nat.add_lt_add_left j.isLt p⟩).val)

/-! ## Splitting Tensors -/

/-- Split a symmetric tensor at position p into left and right parts.
    Given x ∈ Sym^{p+q}(V), returns (left ∈ Sym^p(V), right ∈ Sym^q(V)).

    This is the unsymmetrized split - it just takes the first p and last q elements. -/
def SymTensor.splitAt {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    {n : ℕ} (x : SymTensor R V n) (p : ℕ) (hp : p ≤ n) :
    SymTensor R V p × SymTensor R V (n - p) :=
  let left : SymTensor R V p := {
    degrees := fun i => x.degrees ⟨i.val, Nat.lt_of_lt_of_le i.isLt hp⟩
    elements := fun i =>
      have h : i.val < n := Nat.lt_of_lt_of_le i.isLt hp
      have heq : x.degrees ⟨i.val, h⟩ = x.degrees ⟨i.val, Nat.lt_of_lt_of_le i.isLt hp⟩ := rfl
      heq ▸ x.elements ⟨i.val, h⟩
  }
  let right : SymTensor R V (n - p) := {
    degrees := fun i => x.degrees ⟨p + i.val, by omega⟩
    elements := fun i =>
      have h : p + i.val < n := by omega
      have heq : x.degrees ⟨p + i.val, h⟩ = x.degrees ⟨p + i.val, by omega⟩ := rfl
      heq ▸ x.elements ⟨p + i.val, h⟩
  }
  (left, right)

/-! ## Projection to V -/

/-- Project a word-length-1 symmetric power element to V.
    For x ∈ Sym^1(V), x is determined by a single element v ∈ V_d. -/
def SymPowerElem.toV {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (x : SymPowerElem R V 1) : Σ (d : ℤ), V d :=
  Quotient.lift
    (fun t => ⟨t.degrees 0, t.elements 0⟩)
    (fun a b hab => by
      obtain ⟨σ, hdeg, helem⟩ := hab
      -- For Fin 1, σ must be the identity
      have hσ0 : σ 0 = 0 := by
        have h0 : (σ 0).val < 1 := (σ 0).isLt
        ext
        omega
      have h1 : a.degrees 0 = b.degrees 0 := by
        have := hdeg 0
        rw [hσ0] at this
        exact this
      have h2 : HEq (a.elements 0) (b.elements 0) := by
        have := helem 0
        rw [hσ0] at this
        exact this
      -- Use Sigma.ext_iff: x = y ↔ x.fst = y.fst ∧ x.snd ≍ y.snd
      rw [Sigma.ext_iff]
      exact ⟨h1, h2⟩)
    x

/-! ## Extraction from Reduced Symmetric Algebra -/

/-- Extract the underlying element when word length is 1 -/
def ReducedSymAlgebraElem.toV {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (x : ReducedSymAlgebraElem R V) (h : x.wordLength = 1) : Σ (d : ℤ), V d :=
  (h ▸ x.elem).toV

/-! ## Coderivations on Actual Elements -/

/-- A coderivation acting on actual symmetric tensors.

    This extends the abstract coderivation to work with concrete elements,
    enabling explicit bracket computation.

    A coderivation D on S⁺(V) is determined by its projections to V:
    D_n : Sym^n(V) → V for n ≥ 1 -/
structure CoderivationElem (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] where
  /-- The degree of the coderivation -/
  degree : ℤ
  /-- The components D_n : Sym^n(V) → ⨁_d V_d for n ≥ 1.
      This maps a symmetric tensor of n elements to an element in V. -/
  components : (n : ℕ) → (hn : n ≥ 1) → SymPowerElem R V n → Σ (d : ℤ), V d

namespace CoderivationElem

variable {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- The n-th bracket l_n extracted from the coderivation.

    For an L∞ structure, the coderivation D on S⁺(V[1]) of degree 1
    gives brackets l_n : V^⊗n → V of degree 2-n.

    Here we extract the component D_n : Sym^n(V) → V. -/
def bracket (D : CoderivationElem R V) (n : ℕ) (hn : n ≥ 1) :
    SymPowerElem R V n → Σ (d : ℤ), V d :=
  D.components n hn

/-- The binary bracket l₂.

    This is the fundamental bracket operation for L∞ algebras.
    For x, y ∈ V, we have l₂(x, y) ∈ V. -/
def l2 (D : CoderivationElem R V) (d₁ d₂ : ℤ) (x : V d₁) (y : V d₂) : Σ (d : ℤ), V d :=
  let tensor : SymTensor R V 2 := {
    degrees := ![d₁, d₂]
    elements := fun i =>
      match i with
      | ⟨0, _⟩ => (Matrix.cons_val_zero d₁ ![d₂]).symm ▸ x
      | ⟨1, _⟩ => (Matrix.cons_val_succ d₁ ![d₂] ⟨0, Nat.zero_lt_one⟩).symm ▸ y
  }
  D.components 2 (by norm_num) (SymPowerElem.mk tensor)

/-- The unary bracket l₁ (the differential).

    For an L∞ algebra, l₁ : V → V with l₁² = 0. -/
def l1 (D : CoderivationElem R V) (d : ℤ) (x : V d) : Σ (d : ℤ), V d :=
  let tensor : SymTensor R V 1 := SymTensor.singleton d x
  D.components 1 (by norm_num) (SymPowerElem.mk tensor)

end CoderivationElem

/-! ## L∞ Structure with Elements -/

/-- An L∞ algebra structure on V with actual computable brackets.

    This is equivalent to a degree 1 square-zero coderivation on S⁺(V[1]),
    but represented in a way that allows explicit bracket computation. -/
structure LInftyElem (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] where
  /-- The underlying coderivation -/
  D : CoderivationElem R V
  /-- D has degree 1 (for L∞ on V[1]) -/
  degree_one : D.degree = 1

namespace LInftyElem

variable {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- The differential l₁ of an L∞ algebra -/
def differential (L : LInftyElem R V) (d : ℤ) (x : V d) : Σ (d : ℤ), V d :=
  L.D.l1 d x

/-- The binary bracket l₂ of an L∞ algebra -/
def binaryBracket (L : LInftyElem R V) (d₁ d₂ : ℤ) (x : V d₁) (y : V d₂) : Σ (d : ℤ), V d :=
  L.D.l2 d₁ d₂ x y

/-- The n-th bracket l_n of an L∞ algebra -/
def nthBracket (L : LInftyElem R V) (n : ℕ) (hn : n ≥ 1) :
    SymPowerElem R V n → Σ (d : ℤ), V d :=
  L.D.bracket n hn

end LInftyElem

end StringAlgebra.Linfinity
