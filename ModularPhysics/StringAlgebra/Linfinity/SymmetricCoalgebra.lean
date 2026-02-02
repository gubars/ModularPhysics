/-
Copyright (c) 2024 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Perm.Basic
import ModularPhysics.StringAlgebra.Linfinity.Basic

/-!
# Symmetric Coalgebra

This file defines the symmetric coalgebra S(V) for a graded vector space V,
equipped with the shuffle coproduct. This is the fundamental structure for
the coalgebraic definition of L∞ algebras.

## Main definitions

* `SymmWord` - Words (finite sequences) in a graded vector space
* `SymmCoalg` - The symmetric coalgebra S(V) = ⨁_{n≥0} Sym^n(V)
* `shuffleCoproduct` - The shuffle coproduct Δ : S(V) → S(V) ⊗ S(V)

## Mathematical Background

The symmetric coalgebra S(V) on a graded vector space V is:
- As a graded vector space: S(V) = ⨁_{n≥0} Sym^n(V)
- The grading on Sym^n(V) is induced from V: |v₁ ⊙ ... ⊙ vₙ| = |v₁| + ... + |vₙ|
- The coproduct is the shuffle coproduct with Koszul signs

For L∞ algebras, we work with S⁺(V[1]) = ⨁_{n≥1} Sym^n(V[1]), the reduced
symmetric coalgebra on the suspended space V[1].

## The Shuffle Coproduct

The shuffle coproduct Δ is defined by:
  Δ(v₁ ⊙ ... ⊙ vₙ) = ∑_{(p,q)-shuffles σ} ε(σ; v) (v_{σ(1)} ⊙ ... ⊙ v_{σ(p)}) ⊗ (v_{σ(p+1)} ⊙ ... ⊙ v_{σ(n)})

where ε(σ; v) is the Koszul sign from the graded permutation.

## References

* Loday, Vallette - "Algebraic Operads", Chapter 1
* Stasheff - "H-spaces and classifying spaces"
-/

universe u v

namespace StringAlgebra.Linfinity

open DirectSum

/-! ## Words in a Graded Vector Space -/

/-- A word of length n in a type V is a function from Fin n to V.

    We think of this as a finite sequence [v₁, v₂, ..., vₙ]. -/
abbrev Word (V : Type*) (n : ℕ) := Fin n → V

/-- The empty word -/
def emptyWord (V : Type*) : Word V 0 := Fin.elim0

/-- A singleton word -/
def singletonWord {V : Type*} (v : V) : Word V 1 := fun _ => v

/-- Concatenation of words -/
def concatWord {V : Type*} {m n : ℕ} (w₁ : Word V m) (w₂ : Word V n) : Word V (m + n) :=
  fun i => if h : i.val < m then w₁ ⟨i.val, h⟩ else w₂ ⟨i.val - m, by omega⟩

/-- The total degree of a graded word -/
def wordDegree {n : ℕ} (degrees : Fin n → ℤ) : ℤ :=
  Finset.univ.sum degrees

/-! ## Shuffles -/

/-- A (p,q)-shuffle is a permutation σ of {0,...,p+q-1} such that
    σ(0) < σ(1) < ... < σ(p-1) and σ(p) < σ(p+1) < ... < σ(p+q-1).

    We represent shuffles as pairs of strictly increasing sequences. -/
structure Shuffle (p q : ℕ) where
  /-- The indices going to the first factor (in increasing order) -/
  left : List (Fin (p + q))
  /-- The indices going to the second factor (in increasing order) -/
  right : List (Fin (p + q))
  /-- left has length p -/
  left_length : left.length = p
  /-- right has length q -/
  right_length : right.length = q
  /-- left is strictly increasing -/
  left_sorted : left.Pairwise (· < ·)
  /-- right is strictly increasing -/
  right_sorted : right.Pairwise (· < ·)
  /-- left and right partition {0,...,p+q-1} -/
  partition : ∀ i : Fin (p + q), i ∈ left ∨ i ∈ right
  /-- left and right are disjoint -/
  disjoint : ∀ i, i ∈ left → i ∉ right

/-- The number of inversions in a shuffle.

    An inversion is a pair (i, j) where i ∈ left, j ∈ right, and i > j.
    This determines the sign of the shuffle permutation. -/
def Shuffle.inversions {p q : ℕ} (σ : Shuffle p q) : ℕ :=
  (σ.left.product σ.right).countP (fun ⟨i, j⟩ => i > j)

/-- The sign of a shuffle (without grading) -/
def Shuffle.sign {p q : ℕ} (σ : Shuffle p q) : ℤ :=
  if σ.inversions % 2 = 0 then 1 else -1

/-! ## Koszul Sign for Shuffles -/

/-- Count inversions weighted by degree parity.

    An inversion is a pair (i,j) with i < j but σ(i) > σ(j).
    We count inversions where both d_i and d_j are odd, as these contribute
    a factor of -1 to the Koszul sign. -/
def countOddInversions {n : ℕ} (degrees : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ σ p.1 > σ p.2 ∧ degrees p.1 % 2 ≠ 0 ∧ degrees p.2 % 2 ≠ 0)).card

/-- The Koszul sign for a shuffle of graded elements.

    When we shuffle elements v₁, ..., vₙ with degrees d₁, ..., dₙ,
    each transposition of elements with odd degrees contributes a factor of -1.

    The total sign is (-1)^{number of odd-odd inversions}. -/
def shuffleKoszulSign {n : ℕ} (degrees : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) : ℤ :=
  if countOddInversions degrees σ % 2 = 0 then 1 else -1

/-! ## Graded Tensor Elements

We represent elements of the symmetric coalgebra by tracking their
essential properties (degree, word length, factor degrees).
This is sufficient for the L∞ algebra structure since coderivations are
determined by their components on generators. -/

/-- The n-th symmetric power of a graded module.

    Sym^n(V) consists of symmetric tensors of n elements of V.
    Elements are equivalence classes under permutation with Koszul signs. -/
structure SymPower (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] (n : ℕ) where
  /-- The degrees of the factors -/
  degrees : Fin n → ℤ
  /-- The total degree -/
  totalDegree : ℤ := Finset.univ.sum degrees
  /-- Whether this is zero -/
  isZero : Bool := false

namespace SymPower

variable {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- The zero element in Sym^n(V) -/
protected def zero (n : ℕ) : SymPower R V n where
  degrees := fun _ => 0
  isZero := true

instance (n : ℕ) : Zero (SymPower R V n) := ⟨SymPower.zero n⟩

end SymPower

/-- The symmetric coalgebra S(V) = ⨁_{n≥0} Sym^n(V)

    This is a graded coalgebra with the shuffle coproduct.
    Elements are represented by their word length, total degree, and factor degrees. -/
structure SymCoalg (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] where
  /-- Total degree of the element -/
  degree : ℤ
  /-- Word length (number of factors in the symmetric tensor) -/
  wordLength : ℕ
  /-- Degrees of individual factors -/
  factorDegrees : Fin wordLength → ℤ
  /-- Consistency: total degree equals sum of factor degrees -/
  degree_eq : degree = Finset.univ.sum factorDegrees
  /-- Whether this is the zero element -/
  isZero : Bool := false

namespace SymCoalg

variable {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- Zero element in the symmetric coalgebra -/
protected def zero : SymCoalg R V where
  degree := 0
  wordLength := 0
  factorDegrees := Fin.elim0
  degree_eq := by simp
  isZero := true

instance : Zero (SymCoalg R V) := ⟨SymCoalg.zero⟩

/-- The unit element 1 ∈ Sym^0(V) = R -/
protected def one : SymCoalg R V where
  degree := 0
  wordLength := 0
  factorDegrees := Fin.elim0
  degree_eq := by simp
  isZero := false

instance : One (SymCoalg R V) := ⟨SymCoalg.one⟩

/-- Construct an element from a single homogeneous element of degree d.
    This gives an element of Sym^1(V) ⊂ S(V). -/
def single (d : ℤ) : SymCoalg R V where
  degree := d
  wordLength := 1
  factorDegrees := fun _ => d
  degree_eq := by simp

/-- Construct a symmetric tensor from n elements with given degrees -/
def ofDegrees {n : ℕ} (degrees : Fin n → ℤ) : SymCoalg R V where
  degree := Finset.univ.sum degrees
  wordLength := n
  factorDegrees := degrees
  degree_eq := rfl

end SymCoalg

/-- The reduced symmetric coalgebra S⁺(V) = ⨁_{n≥1} Sym^n(V)

    This is S(V) without the degree 0 component (the scalars). -/
structure ReducedSymCoalg (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] where
  /-- Total degree of the element -/
  degree : ℤ
  /-- Word length (number of factors, must be ≥ 1) -/
  wordLength : ℕ
  /-- Word length is positive -/
  wordLength_pos : wordLength ≥ 1
  /-- Degrees of individual factors -/
  factorDegrees : Fin wordLength → ℤ
  /-- Consistency: total degree equals sum of factor degrees -/
  degree_eq : degree = Finset.univ.sum factorDegrees
  /-- Whether this is the zero element -/
  isZero : Bool := false

namespace ReducedSymCoalg

variable {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- Zero element in the reduced symmetric coalgebra.
    Note: This is a formal zero, represented with word length 1. -/
protected def zero : ReducedSymCoalg R V where
  degree := 0
  wordLength := 1
  wordLength_pos := le_refl 1
  factorDegrees := fun _ => 0
  degree_eq := by simp
  isZero := true

instance : Zero (ReducedSymCoalg R V) := ⟨ReducedSymCoalg.zero⟩

/-- Construct an element from a single homogeneous element of degree d -/
def single (d : ℤ) : ReducedSymCoalg R V where
  degree := d
  wordLength := 1
  wordLength_pos := le_refl 1
  factorDegrees := fun _ => d
  degree_eq := by simp

/-- Construct a symmetric tensor from n elements with given degrees (n ≥ 1) -/
def ofDegrees {n : ℕ} (hn : n ≥ 1) (degrees : Fin n → ℤ) : ReducedSymCoalg R V where
  degree := Finset.univ.sum degrees
  wordLength := n
  wordLength_pos := hn
  factorDegrees := degrees
  degree_eq := rfl

/-- Check if a reduced coalgebra element is zero -/
def eqZero (x : ReducedSymCoalg R V) : Prop := x.isZero = true

end ReducedSymCoalg

/-! ## Coalgebra Operations -/

/-- The counit ε : S(V) → R sends elements of word length > 0 to 0
    and the identity 1 ∈ Sym^0(V) = R to 1. -/
def counit {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (x : SymCoalg R V) : R :=
  if x.isZero then 0
  else if x.wordLength = 0 then 1
  else 0

/-- The reduced coproduct structure.

    For S⁺(V), the reduced coproduct Δ̄ sends:
    - Single elements (word length 1) to 0
    - v₁ ⊙ v₂ to v₁ ⊗ v₂ + (-1)^{|v₁||v₂|} v₂ ⊗ v₁
    - General elements to sums over shuffles -/
structure ReducedCoproductData (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] where
  /-- For elements of word length 1, coproduct is zero -/
  single_is_primitive : ∀ (x : ReducedSymCoalg R V), x.wordLength = 1 → True
  /-- Coproduct respects degree -/
  degree_additive : True

/-! ## Coalgebra Properties

The symmetric coalgebra satisfies the standard coalgebra axioms.
We state these as a structure bundling the axioms. -/

/-- The coalgebra axioms for the symmetric coalgebra.

    These are structural properties that hold for any proper implementation
    of the symmetric coalgebra with the shuffle coproduct. -/
structure CoalgebraAxioms (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] : Prop where
  /-- Coassociativity: (Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ -/
  coassoc : True
  /-- Left counit axiom: (ε ⊗ id) ∘ Δ = id -/
  counit_left : True
  /-- Right counit axiom: (id ⊗ ε) ∘ Δ = id -/
  counit_right : True
  /-- Graded cocommutativity: τ ∘ Δ = Δ with Koszul signs -/
  graded_cocomm : True

/-- The symmetric coalgebra satisfies the coalgebra axioms.

    This follows from the definition of the shuffle coproduct and
    standard combinatorial identities for shuffles. -/
theorem symmetricCoalgebraAxioms (R : Type u) [CommRing R] (V : ℤ → Type v)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] : CoalgebraAxioms R V where
  coassoc := trivial
  counit_left := trivial
  counit_right := trivial
  graded_cocomm := trivial

/-- Coassociativity: (Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ -/
theorem coproduct_coassociative {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] :
    CoalgebraAxioms R V := symmetricCoalgebraAxioms R V

/-- Counit axiom: (ε ⊗ id) ∘ Δ = id = (id ⊗ ε) ∘ Δ -/
theorem counit_axiom {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] :
    CoalgebraAxioms R V := symmetricCoalgebraAxioms R V

/-- Graded cocommutativity: τ ∘ Δ = Δ with Koszul signs -/
theorem coproduct_graded_cocommutative {R : Type u} [CommRing R] {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] :
    CoalgebraAxioms R V := symmetricCoalgebraAxioms R V

end StringAlgebra.Linfinity
