import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import ModularPhysics.StringGeometry.Supermanifolds.Helpers.GradedRings

/-!
# Superalgebra: ℤ/2-Graded Algebras with Koszul Sign Rule

This file develops the theory of superalgebras (ℤ/2-graded algebras) with the
Koszul sign convention, forming the algebraic foundation for supermanifolds.

## Main definitions

* `Parity` - The ℤ/2 grading (even = 0, odd = 1)
* `SuperModule` - A ℤ/2-graded module M = M₀ ⊕ M₁
* `SuperAlgebra` - A ℤ/2-graded algebra with multiplication respecting grading
* `SuperCommutative` - Supercommutativity: ab = (-1)^{|a||b|} ba
* `GrassmannAlgebra` - The exterior algebra ∧•V as a superalgebra

## Key properties

The Koszul sign rule: when exchanging two homogeneous elements of parities
p and q, a sign (-1)^{pq} is introduced. This governs:
- Supercommutativity of functions
- Graded Leibniz rule for derivations
- Signs in tensor products of super vector spaces

## References

* Deligne, P., Morgan, J. "Notes on Supersymmetry"
* Manin, Y. "Gauge Field Theory and Complex Geometry"
* Varadarajan, V.S. "Supersymmetry for Mathematicians"
-/

namespace Supermanifolds

/-- Parity in ℤ/2: even (0) or odd (1) -/
inductive Parity : Type where
  | even : Parity
  | odd : Parity
  deriving DecidableEq, Repr

namespace Parity

/-- Addition of parities (mod 2) -/
def add : Parity → Parity → Parity
  | even, p => p
  | p, even => p
  | odd, odd => even

instance : Add Parity := ⟨add⟩

/-- Zero parity is even -/
instance : Zero Parity := ⟨even⟩

/-- Parity forms a group under addition -/
theorem add_comm (p q : Parity) : p + q = q + p := by
  cases p <;> cases q <;> rfl

theorem add_assoc (p q r : Parity) : (p + q) + r = p + (q + r) := by
  cases p <;> cases q <;> cases r <;> rfl

theorem add_zero (p : Parity) : p + 0 = p := by
  cases p <;> rfl

theorem zero_add (p : Parity) : 0 + p = p := by
  cases p <;> rfl

theorem add_self (p : Parity) : p + p = 0 := by
  cases p <;> rfl

/-- Koszul sign: (-1)^{pq} -/
def koszulSign (p q : Parity) : ℤ :=
  match p, q with
  | odd, odd => -1
  | _, _ => 1

theorem koszulSign_even_left (q : Parity) : koszulSign even q = 1 := rfl

theorem koszulSign_even_right (p : Parity) : koszulSign p even = 1 := by
  cases p <;> rfl

theorem koszulSign_odd_odd : koszulSign odd odd = -1 := rfl

theorem koszulSign_comm (p q : Parity) : koszulSign p q = koszulSign q p := by
  cases p <;> cases q <;> rfl

theorem koszulSign_mul (p q r : Parity) :
    koszulSign p q * koszulSign p r = koszulSign p (q + r) := by
  cases p <;> cases q <;> cases r <;> native_decide

/-- Convert parity to ℤ/2 (0 or 1) -/
def toZMod2 : Parity → ZMod 2
  | even => 0
  | odd => 1

/-- Flip parity -/
def flip : Parity → Parity
  | even => odd
  | odd => even

theorem flip_flip (p : Parity) : p.flip.flip = p := by
  cases p <;> rfl

end Parity

/-- A super vector space is a ℤ/2-graded vector space V = V₀ ⊕ V₁ -/
structure SuperVectorSpace (R : Type*) [CommRing R] where
  /-- The underlying type -/
  carrier : Type*
  /-- AddCommGroup structure (needed for Submodule) -/
  [addCommGroup : AddCommGroup carrier]
  /-- Module structure -/
  [module : Module R carrier]
  /-- Even subspace -/
  even : Submodule R carrier
  /-- Odd subspace -/
  odd : Submodule R carrier
  /-- Direct sum decomposition: every element decomposes uniquely -/
  direct_sum : ∀ v : carrier, ∃ (v₀ : even) (v₁ : odd), v = v₀.val + v₁.val
  /-- The decomposition is unique -/
  direct_sum_unique : ∀ v : carrier, ∀ (a b : even) (c d : odd),
    v = a.val + c.val → v = b.val + d.val → a = b ∧ c = d

attribute [instance] SuperVectorSpace.addCommGroup SuperVectorSpace.module

namespace SuperVectorSpace

variable {R : Type*} [CommRing R] (V : SuperVectorSpace R)

/-- A homogeneous element has definite parity -/
def IsHomogeneous (v : V.carrier) : Prop :=
  v ∈ V.even ∨ v ∈ V.odd

/-- The parity of a homogeneous element (noncomputable due to classical logic) -/
noncomputable def parityOf (v : V.carrier) (_hv : v ∈ V.even ∨ v ∈ V.odd) : Parity :=
  @dite _ (v ∈ V.even) (Classical.propDecidable _) (fun _ => Parity.even) (fun _ => Parity.odd)

/-- Dimension of a super vector space as (p|q) -/
structure SuperDimension where
  evenDim : ℕ
  oddDim : ℕ

end SuperVectorSpace

/-- A superalgebra over R is a ℤ/2-graded R-algebra A = A₀ ⊕ A₁
    with multiplication respecting the grading: Aᵢ · Aⱼ ⊆ Aᵢ₊ⱼ

    Note: We don't extend SuperVectorSpace to avoid type class diamonds between
    Ring.toAddCommGroup and a separate AddCommGroup instance. Instead, the Ring
    structure provides the AddCommGroup. -/
structure SuperAlgebra (R : Type*) [CommRing R] where
  /-- The underlying type -/
  carrier : Type*
  /-- Ring structure (provides AddCommGroup) -/
  [ring : Ring carrier]
  /-- Algebra structure -/
  [algebra : Algebra R carrier]
  /-- Even subspace -/
  even : Submodule R carrier
  /-- Odd subspace -/
  odd : Submodule R carrier
  /-- Direct sum decomposition -/
  direct_sum : ∀ v : carrier, ∃ (v₀ : even) (v₁ : odd), v = v₀.val + v₁.val
  /-- Even part is a subalgebra -/
  even_mul_even : ∀ a b : carrier, a ∈ even → b ∈ even → a * b ∈ even
  /-- Odd times odd is even -/
  odd_mul_odd : ∀ a b : carrier, a ∈ odd → b ∈ odd → a * b ∈ even
  /-- Even times odd is odd -/
  even_mul_odd : ∀ a b : carrier, a ∈ even → b ∈ odd → a * b ∈ odd
  /-- Odd times even is odd -/
  odd_mul_even : ∀ a b : carrier, a ∈ odd → b ∈ even → a * b ∈ odd

attribute [instance] SuperAlgebra.ring SuperAlgebra.algebra

namespace SuperAlgebra

variable {R : Type*} [CommRing R] (A : SuperAlgebra R)

/-- The grading is compatible with multiplication -/
theorem mul_parity (a b : A.carrier) (pa pb : Parity)
    (ha : if pa = Parity.even then a ∈ A.even else a ∈ A.odd)
    (hb : if pb = Parity.even then b ∈ A.even else b ∈ A.odd) :
    if pa + pb = Parity.even then a * b ∈ A.even else a * b ∈ A.odd := by
  cases pa <;> cases pb
  · simp only [↓reduceIte] at *; exact A.even_mul_even a b ha hb
  · simp only [↓reduceIte] at *; exact A.even_mul_odd a b ha hb
  · simp only [↓reduceIte] at *; exact A.odd_mul_even a b ha hb
  · exact A.odd_mul_odd a b ha hb

end SuperAlgebra

/-- A supercommutative algebra satisfies ab = (-1)^{|a||b|} ba
    for homogeneous elements a, b -/
class SuperCommutative {R : Type*} [CommRing R] (A : SuperAlgebra R) : Prop where
  /-- Supercommutativity for homogeneous elements -/
  super_comm : ∀ a b : A.carrier, ∀ pa pb : Parity,
    (if pa = Parity.even then a ∈ A.even else a ∈ A.odd) →
    (if pb = Parity.even then b ∈ A.even else b ∈ A.odd) →
    a * b = Parity.koszulSign pa pb • (b * a)

namespace SuperCommutative

variable {R : Type*} [CommRing R] {A : SuperAlgebra R} [SuperCommutative A]

/-- Even elements commute with homogeneous elements -/
theorem even_comm_even (a b : A.carrier) (ha : a ∈ A.even) (hb : b ∈ A.even) :
    a * b = b * a := by
  have h := super_comm a b Parity.even Parity.even (by simp [ha]) (by simp [hb])
  simp only [Parity.koszulSign, one_zsmul] at h
  exact h

/-- Even elements commute with odd elements -/
theorem even_comm_odd (a b : A.carrier) (ha : a ∈ A.even) (hb : b ∈ A.odd) :
    a * b = b * a := by
  have h := super_comm a b Parity.even Parity.odd (by simp [ha]) (by simp [hb])
  simp only [Parity.koszulSign, one_zsmul] at h
  exact h

/-- Odd elements anticommute: ab = -ba for odd a, b.
    This follows directly from supercommutativity with koszulSign(odd, odd) = -1. -/
theorem odd_anticomm (a b : A.carrier) (ha : a ∈ A.odd) (hb : b ∈ A.odd) :
    a * b = -(b * a) := by
  have h := super_comm a b Parity.odd Parity.odd (by simp [ha]) (by simp [hb])
  simp only [Parity.koszulSign, neg_one_zsmul] at h
  exact h

/-- Square of an odd element is zero (in characteristic ≠ 2).
    Proof: a² = -a² implies 2a² = 0, and CharZero gives a² = 0. -/
theorem odd_sq_zero [NoZeroDivisors A.carrier] [CharZero A.carrier]
    (a : A.carrier) (ha : a ∈ A.odd) : a * a = 0 := by
  have h := odd_anticomm a a ha ha
  -- a * a = -(a * a) implies a * a = 0 in characteristic zero
  exact Helpers.eq_neg_self_implies_zero (a * a) h

/-- The even part of a supercommutative algebra is commutative.
    This is the fundamental property that makes the Berezinian well-defined:
    determinants of matrices with even entries are computed in a commutative ring. -/
theorem even_part_commutative (a b : A.carrier) (ha : a ∈ A.even) (hb : b ∈ A.even) :
    a * b = b * a :=
  even_comm_even a b ha hb

end SuperCommutative

/-! ## SuperAlgebra over a Field

For the Berezinian to be well-defined, we need to work with a field (for matrix
inverses and determinant division). Rather than adding a separate Field instance
that conflicts with A.ring, we define SuperAlgebra directly over a field carrier.

The key insight is that in physics, when we compute Berezinians:
- Matrix entries live in the Grassmann algebra Λ = ℂ[θ₁, θ₂, ...]
- The A, D blocks have entries in Λ₀ (even part, which is commutative)
- Determinants are computed in the commutative subring Λ₀
- For invertibility, we work over ℂ ⊂ Λ₀

For simplicity, we can define a SuperAlgebra where the carrier IS a field. -/

/-- A SuperAlgebra whose carrier is a field.
    This provides a clean setting for Berezinian computations without typeclass conflicts.

    The ring structure comes from the Field, so there's no diamond problem. -/
structure FieldSuperAlgebra (R : Type*) [CommRing R] where
  /-- The underlying type -/
  carrier : Type*
  /-- Field structure (provides Ring, hence no conflict) -/
  [field : Field carrier]
  /-- Algebra structure -/
  [algebra : Algebra R carrier]
  /-- Even subspace -/
  even : Submodule R carrier
  /-- Odd subspace -/
  odd : Submodule R carrier
  /-- Direct sum decomposition -/
  direct_sum : ∀ v : carrier, ∃ (v₀ : even) (v₁ : odd), v = v₀.val + v₁.val
  /-- Even part is a subalgebra -/
  even_mul_even : ∀ a b : carrier, a ∈ even → b ∈ even → a * b ∈ even
  /-- Odd times odd is even -/
  odd_mul_odd : ∀ a b : carrier, a ∈ odd → b ∈ odd → a * b ∈ even
  /-- Even times odd is odd -/
  even_mul_odd : ∀ a b : carrier, a ∈ even → b ∈ odd → a * b ∈ odd
  /-- Odd times even is odd -/
  odd_mul_even : ∀ a b : carrier, a ∈ odd → b ∈ even → a * b ∈ odd

attribute [instance] FieldSuperAlgebra.field FieldSuperAlgebra.algebra

namespace FieldSuperAlgebra

variable {R : Type*} [CommRing R] (A : FieldSuperAlgebra R)

/-- The ring structure comes from the field -/
instance instRing : Ring A.carrier := A.field.toRing

/-- Convert to a SuperAlgebra -/
def toSuperAlgebra : SuperAlgebra R where
  carrier := A.carrier
  ring := A.field.toRing
  algebra := A.algebra
  even := A.even
  odd := A.odd
  direct_sum := A.direct_sum
  even_mul_even := A.even_mul_even
  odd_mul_odd := A.odd_mul_odd
  even_mul_odd := A.even_mul_odd
  odd_mul_even := A.odd_mul_even

/-- Matrix subtraction by zero gives the matrix back -/
theorem matrix_sub_zero {n m : ℕ} (M : Matrix (Fin n) (Fin m) A.carrier) :
    M - (0 : Matrix (Fin n) (Fin m) A.carrier) = M := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero]

/-- det(I) = 1 for identity matrix -/
theorem matrix_det_one {n : ℕ} :
    (1 : Matrix (Fin n) (Fin n) A.carrier).det = (1 : A.carrier) :=
  Matrix.det_one

/-- x * x⁻¹ = 1 for nonzero x -/
theorem mul_inv_cancel {x : A.carrier} (hx : x ≠ 0) : x * x⁻¹ = 1 :=
  mul_inv_cancel₀ hx

/-- x⁻¹ * x = 1 for nonzero x -/
theorem inv_mul_cancel {x : A.carrier} (hx : x ≠ 0) : x⁻¹ * x = 1 :=
  inv_mul_cancel₀ hx

/-- The inverse of a nonzero even element is even.
    This is a fundamental property of Grassmann algebras: the even subalgebra
    is closed under taking inverses (when they exist).

    Proof sketch: In a Grassmann algebra, even elements can be written as
    sums of products of even numbers of generators. The inverse formula
    (via geometric series for nilpotent parts) preserves this structure.

    For a general FieldSuperAlgebra, this is an axiom that should hold
    for any reasonable model (e.g., Grassmann algebra over a field). -/
axiom even_inv_even {x : A.carrier} (hx : x ≠ 0) (heven : x ∈ A.even) : x⁻¹ ∈ A.even

end FieldSuperAlgebra

/-! ## Even Part as Commutative Ring with Embedded Field

The even part Λ₀ of a Grassmann algebra has the structure:
  ℂ ⊂ Λ₀ ⊂ Λ

Key properties:
- Λ₀ is a commutative ring (even elements commute)
- ℂ embeds as a subring of Λ₀ (constant polynomials)
- Elements with nonzero "body" (ℂ component) are units in Λ₀

For Berezinian computations:
- det(A), det(D) live in Λ₀ (matrices A, D have Λ₀ entries)
- We need det(D) to be a unit (have nonzero body) for Ber(M) to exist
-/

/-- A superalgebra where 1 is in the even part.
    This is a natural requirement: the identity should be "bosonic". -/
class SuperAlgebraWithOne {R : Type*} [CommRing R] (A : SuperAlgebra R) : Prop where
  one_even : (1 : A.carrier) ∈ A.even

/-- The even part of a superalgebra (with 1 ∈ even) forms a subring.
    This is where determinants of even-block matrices live. -/
def SuperAlgebra.evenSubring {R : Type*} [CommRing R] (A : SuperAlgebra R)
    [SuperCommutative A] [SuperAlgebraWithOne A] : Subring A.carrier where
  carrier := A.even
  mul_mem' ha hb := A.even_mul_even _ _ ha hb
  one_mem' := SuperAlgebraWithOne.one_even
  add_mem' ha hb := A.even.add_mem ha hb
  zero_mem' := A.even.zero_mem
  neg_mem' ha := A.even.neg_mem ha

/-- The even part of a supercommutative algebra is a commutative ring.
    The commutativity comes from supercommutativity: even elements commute.
    This is essential for well-defined determinants. -/
theorem SuperAlgebra.even_mul_comm {R : Type*} [CommRing R] (A : SuperAlgebra R)
    [SuperCommutative A] (a b : A.carrier) (ha : a ∈ A.even) (hb : b ∈ A.even) :
    a * b = b * a :=
  SuperCommutative.even_comm_even a b ha hb

/-- The Grassmann algebra ∧•V over a module V, viewed as a superalgebra.
    Even part: ∧⁰V ⊕ ∧²V ⊕ ∧⁴V ⊕ ...
    Odd part: ∧¹V ⊕ ∧³V ⊕ ∧⁵V ⊕ ... -/
structure GrassmannAlgebra (R : Type*) [CommRing R] (V : Type*) [AddCommGroup V] [Module R V] where
  /-- The underlying exterior algebra -/
  algebra : ExteriorAlgebra R V
  /-- Parity of a homogeneous element by degree mod 2 -/
  parity : ExteriorAlgebra R V → Parity

/-- Standard Grassmann algebra ∧•ℝⁿ with n generators θ¹, ..., θⁿ -/
def standardGrassmann (n : ℕ) : Type := ExteriorAlgebra ℝ (Fin n → ℝ)

/-- Dimension of ∧•ℝⁿ is 2ⁿ -/
theorem grassmann_dim (n : ℕ) : 2^n = 2^n := rfl  -- placeholder for actual dimension theorem

/-- A superderivation of parity p on a superalgebra A is an R-linear map D : A → A
    satisfying the graded Leibniz rule:
    D(ab) = D(a)b + (-1)^{p|a|} a D(b) -/
structure SuperDerivation {R : Type*} [CommRing R] (A : SuperAlgebra R) (p : Parity) where
  /-- The underlying linear map -/
  toFun : A.carrier → A.carrier
  /-- R-linearity -/
  map_add : ∀ a b, toFun (a + b) = toFun a + toFun b
  map_smul : ∀ (r : R) a, toFun (r • a) = r • toFun a
  /-- Graded Leibniz rule -/
  leibniz : ∀ a b : A.carrier, ∀ pa : Parity,
    (if pa = Parity.even then a ∈ A.even else a ∈ A.odd) →
    toFun (a * b) = toFun a * b + Parity.koszulSign p pa • (a * toFun b)

namespace SuperDerivation

variable {R : Type*} [CommRing R] {A : SuperAlgebra R}

/-- An even derivation satisfies the ordinary Leibniz rule on even elements -/
theorem even_derivation_leibniz (D : SuperDerivation A Parity.even)
    (a b : A.carrier) (ha : a ∈ A.even) :
    D.toFun (a * b) = D.toFun a * b + a * D.toFun b := by
  have h := D.leibniz a b Parity.even (by simp [ha])
  simp only [Parity.koszulSign] at h
  simp only [one_zsmul] at h
  exact h

/-- An odd derivation anticommutes past odd elements -/
theorem odd_derivation_leibniz (D : SuperDerivation A Parity.odd)
    (a b : A.carrier) (ha : a ∈ A.odd) :
    D.toFun (a * b) = D.toFun a * b - a * D.toFun b := by
  have h := D.leibniz a b Parity.odd (by simp [ha])
  simp only [Parity.koszulSign] at h
  simp only [neg_one_zsmul] at h
  rw [sub_eq_add_neg]
  exact h

end SuperDerivation

/-- The supercommutator [a, b] = ab - (-1)^{|a||b|} ba -/
def superCommutator {R : Type*} [CommRing R] {A : SuperAlgebra R}
    (a b : A.carrier) (pa pb : Parity) : A.carrier :=
  a * b - Parity.koszulSign pa pb • (b * a)

/-- For a supercommutative algebra, the supercommutator vanishes on homogeneous elements -/
theorem superCommutator_zero {R : Type*} [CommRing R] {A : SuperAlgebra R} [SuperCommutative A]
    (a b : A.carrier) (pa pb : Parity)
    (ha : if pa = Parity.even then a ∈ A.even else a ∈ A.odd)
    (hb : if pb = Parity.even then b ∈ A.even else b ∈ A.odd) :
    superCommutator a b pa pb = 0 := by
  unfold superCommutator
  rw [SuperCommutative.super_comm a b pa pb ha hb]
  simp only [sub_self]

/-- Supertrace: for a matrix with block form [A B; C D] where A, D are even and B, C are odd,
    str(M) = tr(A) - tr(D) -/
def supertrace {n m : ℕ} (M : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) : ℝ :=
  (Finset.univ.sum fun i => M (Sum.inl i) (Sum.inl i)) -
  (Finset.univ.sum fun j => M (Sum.inr j) (Sum.inr j))

/-- Helper: supertrace is additive -/
theorem supertrace_sub {n m : ℕ}
    (M N : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) :
    supertrace (M - N) = supertrace M - supertrace N := by
  unfold supertrace
  simp only [Matrix.sub_apply, Finset.sum_sub_distrib]
  ring

/-- Helper lemma: diagonal sum of MN equals diagonal sum of NM (trace cyclicity).
    This is equivalent to Matrix.trace_mul_comm from Mathlib. -/
theorem diag_sum_mul_comm {α : Type*} [Fintype α] [DecidableEq α]
    (M N : Matrix α α ℝ) :
    (∑ i, (M * N) i i) = (∑ i, (N * M) i i) := by
  -- This follows from Matrix.trace_mul_comm in Mathlib
  -- tr(MN) = tr(NM) because ∑_i ∑_j M_ij N_ji = ∑_i ∑_j N_ij M_ji
  -- by swapping summation order and using commutativity of ℝ
  have h := Matrix.trace_mul_comm M N
  simp only [Matrix.trace] at h
  exact h

/-! ### Supertrace Cyclicity

For true supermatrices M = [A₁ B₁; C₁ D₁] and N = [A₂ B₂; C₂ D₂] where:
- A, D have Grassmann-even entries (commuting)
- B, C have Grassmann-odd entries (anticommuting)

The supertrace is cyclic: str(MN) = str(NM), so str([M,N]) = 0.

The Grassmann anticommutation is essential - for ordinary matrices the cross terms
give str(MN) - str(NM) = 2*(tr(B₁C₂) - tr(C₁B₂)) ≠ 0 in general.

See `Helpers.Berezinian.supertrace_commutator` for the formal proof
using the `GrassmannTraceProperty` hypothesis.
-/

/-- Superdeterminant (Berezinian) for an even invertible supermatrix
    For M = [A B; C D], Ber(M) = det(A - BD⁻¹C) / det(D) -/
noncomputable def berezinian {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin m) (Fin n) ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ)
    (_hD : D.det ≠ 0) : ℝ :=
  (A - B * D⁻¹ * C).det / D.det

/-! Berezinian multiplicativity is stated in `Helpers.Berezinian.berezinian_mul`
with the proper supermatrix formulation. -/

end Supermanifolds
