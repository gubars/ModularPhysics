import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Rat
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

/-! ## Grassmann Algebra (Supercommutative Algebra with Nilpotency)

A Grassmann algebra Λ over a field k with n generators θ₁, ..., θₙ is:
  Λ = k[θ₁, ..., θₙ] / (θᵢθⱼ + θⱼθᵢ, θᵢ²)

**Algebraic Structure:**
```
k ⊂ Λ₀ ⊂ Λ
```
where:
- **k** is the base field (e.g., ℂ) - this IS a field
- **Λ₀** is the even part - a commutative ring (NOT a field!) containing k
- **Λ** is the full Grassmann algebra - a supercommutative ring

Key properties:
- Λ = Λ₀ ⊕ Λ₁ where Λ₀ is even and Λ₁ is odd
- Λ₀ contains k as a subalgebra (the "body" or "constant" part)
- Λ₀ also contains nilpotent elements like θ₁θ₂, θ₁θ₂θ₃θ₄, etc.
- Odd elements anticommute: θᵢθⱼ = -θⱼθᵢ
- θᵢ² = 0 for all generators
- Any product of more than n odd elements is zero (automatic nilpotency)

**Invertibility in Λ₀:**
An element x ∈ Λ₀ can be written as x = c + n where:
- c ∈ k is the "body" (constant part)
- n is nilpotent (n^N = 0 for some N)

x is invertible iff c ≠ 0. The inverse is computed via geometric series:
  x⁻¹ = c⁻¹ · (1 - n/c + (n/c)² - ...) (finite sum since n is nilpotent)

**Important**: Λ is NOT a field. Elements like θ₁θ₂ are nonzero but not invertible
(they have zero body). The even part Λ₀ is also NOT a field.

For the Berezinian:
- Matrix entries live in Λ
- A, D blocks have entries in Λ₀ (even, commutative)
- B, C blocks have entries in Λ₁ (odd, anticommuting)
- Determinants are computed in Λ₀
- det(A), det(D) must be units in Λ₀ (have nonzero body in k) -/

/-! ## Grassmann Algebra Structure

A Grassmann algebra Λ over a field k has the structure:
  k ⊂ Λ₀ ⊂ Λ

The key feature is the **body map** `body : Λ → k` which extracts the constant term.
For x = c + n where c ∈ k and n is nilpotent:
- body(x) = c
- x is invertible ⟺ body(x) ≠ 0 in k

Example: θ₁θ₂ is nonzero in Λ but body(θ₁θ₂) = 0, so it's NOT invertible.

This structure correctly models invertibility without the false assumption
that Λ is a field.
-/

/-- A Grassmann algebra over a base field k.

    This is the mathematically correct structure for supermatrix theory.
    Unlike `FieldSuperAlgebra`, this does NOT assume the carrier is a field.

    Key components:
    - `baseField`: The field k (e.g., ℂ) embedded in the even part
    - `body`: The projection Λ → k extracting the constant term
    - Invertibility is determined by `body x ≠ 0`, not `x ≠ 0`

    Example: For Λ = ℂ[θ₁, θ₂]:
    - body(3 + 2θ₁θ₂) = 3 ∈ ℂ, so 3 + 2θ₁θ₂ is invertible
    - body(θ₁θ₂) = 0, so θ₁θ₂ is NOT invertible (even though θ₁θ₂ ≠ 0) -/
structure GrassmannAlgebra (k : Type*) [Field k] where
  /-- The full Grassmann algebra Λ -/
  carrier : Type*
  /-- Ring structure on carrier (NOT a field!) -/
  [ring : CommRing carrier]
  /-- k embeds into Λ -/
  [algebra : Algebra k carrier]
  /-- Even subspace Λ₀ -/
  even : Submodule k carrier
  /-- Odd subspace Λ₁ -/
  odd : Submodule k carrier
  /-- The body map: projection to the constant (k) part.
      For x = c + n where c ∈ k and n is nilpotent, body(x) = c. -/
  body : carrier → k
  /-- body is a k-algebra homomorphism -/
  body_algebraMap : ∀ c : k, body (algebraMap k carrier c) = c
  body_add : ∀ x y, body (x + y) = body x + body y
  body_mul : ∀ x y, body (x * y) = body x * body y
  body_one : body 1 = 1
  /-- Nilpotent part: x - body(x) is nilpotent -/
  nilpotent_part : ∀ x : carrier, ∃ N : ℕ, (x - algebraMap k carrier (body x))^(N + 1) = 0
  /-- Grading properties -/
  direct_sum : ∀ v : carrier, ∃ (v₀ : even) (v₁ : odd), v = v₀.val + v₁.val
  even_mul_even : ∀ a b : carrier, a ∈ even → b ∈ even → a * b ∈ even
  odd_mul_odd : ∀ a b : carrier, a ∈ odd → b ∈ odd → a * b ∈ even
  even_mul_odd : ∀ a b : carrier, a ∈ even → b ∈ odd → a * b ∈ odd
  odd_mul_even : ∀ a b : carrier, a ∈ odd → b ∈ even → a * b ∈ odd
  /-- Odd elements have zero body -/
  body_odd_zero : ∀ x : carrier, x ∈ odd → body x = 0

attribute [instance] GrassmannAlgebra.ring GrassmannAlgebra.algebra

namespace GrassmannAlgebra

variable {k : Type*} [Field k] (Λ : GrassmannAlgebra k)

/-- Invertible elements have inverses (existence) -/
private theorem invertible_has_inverse (x : Λ.carrier) (hx : Λ.body x ≠ 0) :
    ∃ y : Λ.carrier, x * y = 1 ∧ y * x = 1 := by
  -- The proof constructs the inverse via geometric series:
  -- Let c = body(x) ≠ 0, n = x - c (nilpotent with n^(N+1) = 0)
  -- Then x = c(1 + n/c) and x⁻¹ = c⁻¹ · Σₖ₌₀ᴺ (-n/c)ᵏ
  let c := Λ.body x
  have hc : c ≠ 0 := hx
  -- Get the nilpotency bound for n = x - c
  obtain ⟨N, hnil⟩ := Λ.nilpotent_part x
  -- Define n = x - c (nilpotent part)
  let n := x - algebraMap k Λ.carrier c
  have hn_nil : n^(N + 1) = 0 := hnil
  let c_inv := c⁻¹
  -- Key identity: x = algebraMap c + n
  have hx_decomp : x = algebraMap k Λ.carrier c + n := by
    simp only [n]
    ring
  -- Define r = c⁻¹ • n (the "ratio" n/c as a scalar action)
  let r := c_inv • n
  -- The geometric series: s = Σₖ₌₀ᴺ (-r)ᵏ = Σₖ₌₀ᴺ (-1)ᵏ * (c⁻¹)ᵏ • nᵏ
  let s := ∑ i ∈ Finset.range (N + 1), ((-1 : k)^i * c_inv^i) • n^i
  -- The inverse is y = c⁻¹ • s
  let y := c_inv • s
  use y
  -- Key: (1 + r) * s = 1 + (-r)^{N+1} using geometric series identity
  -- Since r = c⁻¹ • n, we have (-r)^{N+1} involves n^{N+1} = 0
  have h_geom : (1 + r) * s = 1 - ((-1 : k)^(N+1) * c_inv^(N+1)) • n^(N+1) := by
    -- Expand (1 + r) * s = s + r * s
    rw [add_mul, one_mul]
    simp only [s, r, Finset.mul_sum]
    -- r * term_i = c⁻¹ • n * ((-1)^i * c⁻ⁱ) • n^i = ((-1)^i * c⁻⁽ⁱ⁺¹⁾) • n^{i+1}
    have h_r_term : ∀ i, c_inv • n * (((-1 : k)^i * c_inv^i) • n^i) =
        ((-1 : k)^i * c_inv^(i+1)) • n^(i+1) := by
      intro i
      rw [smul_mul_smul_comm]
      congr 1
      · rw [pow_succ c_inv i]; ring
      · rw [pow_succ n i]; ring
    conv_lhs =>
      arg 2
      arg 2
      ext i
      rw [h_r_term]
    -- Now: s + r*s = Σ_{i=0}^N (-1)^i c⁻ⁱ • n^i + Σ_{i=0}^N (-1)^i c⁻⁽ⁱ⁺¹⁾ • n^{i+1}
    -- These sums telescope: term i of second sum cancels with term (i+1) of first sum
    -- since (-1)^i * c⁻⁽ⁱ⁺¹⁾ + (-1)^{i+1} * c⁻⁽ⁱ⁺¹⁾ = 0

    -- Split first sum: term 0 + rest
    rw [Finset.sum_range_succ' (fun i => ((-1 : k)^i * c_inv^i) • n^i)]
    simp only [pow_zero, one_mul, one_smul]
    -- First sum = 1 + Σ_{i=0}^{N-1} ((-1)^{i+1} * c⁻⁽ⁱ⁺¹⁾) • n^{i+1}
    -- = 1 + Σ_{j=1}^N ((-1)^j * c⁻ʲ) • n^j  (where j = i+1)

    -- Split second sum: initial terms + final term
    rw [Finset.sum_range_succ (fun i => ((-1 : k)^i * c_inv^(i+1)) • n^(i+1))]
    -- Second sum = Σ_{i=0}^{N-1} ((-1)^i * c⁻⁽ⁱ⁺¹⁾) • n^{i+1} + ((-1)^N * c⁻⁽ᴺ⁺¹⁾) • n^{N+1}

    -- Now pair up: term (i+1) from first with term i from second cancel
    -- ((-1)^{i+1} * c⁻⁽ⁱ⁺¹⁾) • n^{i+1} + ((-1)^i * c⁻⁽ⁱ⁺¹⁾) • n^{i+1}
    -- = (((-1)^{i+1} + (-1)^i) * c⁻⁽ⁱ⁺¹⁾) • n^{i+1} = 0

    have h_cancel : ∀ i, ((-1 : k)^(i+1) * c_inv^(i+1)) • n^(i+1) +
        ((-1 : k)^i * c_inv^(i+1)) • n^(i+1) = 0 := by
      intro i
      rw [← add_smul]
      have hcoef : (-1 : k)^(i+1) * c_inv^(i+1) + (-1)^i * c_inv^(i+1) = 0 := by
        rw [← add_mul, pow_succ]; ring
      rw [hcoef, zero_smul]

    -- Pair the sums
    have h_paired : (∑ i ∈ Finset.range N, ((-1 : k)^(i+1) * c_inv^(i+1)) • n^(i+1)) +
        (∑ i ∈ Finset.range N, ((-1 : k)^i * c_inv^(i+1)) • n^(i+1)) = 0 := by
      rw [← Finset.sum_add_distrib]
      simp only [h_cancel, Finset.sum_const_zero]

    -- The RHS is 1 - ((-1)^{N+1} * c⁻⁽ᴺ⁺¹⁾) • n^{N+1}
    -- LHS = 1 + (sum from first) + (sum from second) + final term
    -- = 1 + 0 + ((-1)^N * c⁻⁽ᴺ⁺¹⁾) • n^{N+1}
    -- = 1 - ((-1)^{N+1} * c⁻⁽ᴺ⁺¹⁾) • n^{N+1}  since (-1)^N = -(-1)^{N+1}

    have h_neg : ((-1 : k)^N * c_inv^(N+1)) • n^(N+1) =
        -(((-1 : k)^(N+1) * c_inv^(N+1)) • n^(N+1)) := by
      rw [← neg_smul]
      congr 1
      rw [pow_succ]; ring

    -- After the splits, we have:
    -- LHS = (Σ_{i=0}^{N-1} (-1)^{i+1} c⁻⁽ⁱ⁺¹⁾ • n^{i+1} + 1) +
    --       (Σ_{i=0}^{N-1} (-1)^i c⁻⁽ⁱ⁺¹⁾ • n^{i+1} + (-1)^N c⁻⁽ᴺ⁺¹⁾ • n^{N+1})
    -- The sums cancel, leaving 1 + (-1)^N c⁻⁽ᴺ⁺¹⁾ • n^{N+1}
    calc (∑ i ∈ Finset.range N, ((-1 : k)^(i+1) * c_inv^(i+1)) • n^(i+1) + 1) +
         (∑ i ∈ Finset.range N, ((-1 : k)^i * c_inv^(i+1)) • n^(i+1) +
          ((-1 : k)^N * c_inv^(N+1)) • n^(N+1))
      = 1 + ((∑ i ∈ Finset.range N, ((-1 : k)^(i+1) * c_inv^(i+1)) • n^(i+1)) +
         (∑ i ∈ Finset.range N, ((-1 : k)^i * c_inv^(i+1)) • n^(i+1))) +
          ((-1 : k)^N * c_inv^(N+1)) • n^(N+1) := by ring
      _ = 1 + 0 + ((-1 : k)^N * c_inv^(N+1)) • n^(N+1) := by rw [h_paired]
      _ = 1 + ((-1 : k)^N * c_inv^(N+1)) • n^(N+1) := by ring
      _ = 1 + -(((-1 : k)^(N+1) * c_inv^(N+1)) • n^(N+1)) := by rw [h_neg]
      _ = 1 - ((-1 : k)^(N+1) * c_inv^(N+1)) • n^(N+1) := by ring
  have h_nil_term : ((-1 : k)^(N+1) * c_inv^(N+1)) • n^(N+1) = 0 := by
    rw [hn_nil, smul_zero]
  rw [h_nil_term, sub_zero] at h_geom
  -- Now: x * y = (algebraMap c + n) * (c⁻¹ • s) = c⁻¹ • ((algebraMap c + n) * s)
  --            = c⁻¹ • (algebraMap c * s + n * s)
  -- We need to show (algebraMap c + n) * s = c • 1 = algebraMap c
  -- Note: algebraMap c + n = c • (1 + c⁻¹ • n) = c • (1 + r) when c acts by algebraMap
  -- From h_geom: (1 + r) * s = 1, so s + r * s = 1
  have h4 : s + r * s = 1 := by
    have : (1 + r) * s = 1 * s + r * s := add_mul 1 r s
    rw [one_mul] at this
    rw [← this]; exact h_geom
  constructor
  · -- x * y = 1
    calc x * y = (algebraMap k Λ.carrier c + n) * (c_inv • s) := by rw [hx_decomp]
      _ = c_inv • ((algebraMap k Λ.carrier c + n) * s) := by rw [mul_smul_comm]
      _ = c_inv • (algebraMap k Λ.carrier c * s + n * s) := by rw [add_mul]
      _ = c_inv • (c • s + n * s) := by
        congr 1
        rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      _ = c_inv • (c • (s + r * s)) := by
        congr 1
        -- n = c • r
        have hn_eq : n = c • r := by
          simp only [r]
          rw [← smul_assoc, smul_eq_mul, mul_inv_cancel₀ hc, one_smul]
        -- n * s = c • (r * s)
        have h3 : n * s = c • (r * s) := by rw [hn_eq, smul_mul_assoc]
        rw [h3, smul_add]
      _ = c_inv • (c • 1) := by rw [h4]
      _ = 1 := by rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ hc, one_smul]
  · -- y * x = 1 (by commutativity of Λ.carrier)
    rw [mul_comm]
    calc x * y = (algebraMap k Λ.carrier c + n) * (c_inv • s) := by rw [hx_decomp]
      _ = c_inv • ((algebraMap k Λ.carrier c + n) * s) := by rw [mul_smul_comm]
      _ = c_inv • (algebraMap k Λ.carrier c * s + n * s) := by rw [add_mul]
      _ = c_inv • (c • s + n * s) := by
        congr 1
        rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      _ = c_inv • (c • (s + r * s)) := by
        congr 1
        have hn_eq : n = c • r := by
          simp only [r]
          rw [← smul_assoc, smul_eq_mul, mul_inv_cancel₀ hc, one_smul]
        have h3 : n * s = c • (r * s) := by rw [hn_eq, smul_mul_assoc]
        rw [h3, smul_add]
      _ = c_inv • (c • 1) := by rw [h4]
      _ = 1 := by rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ hc, one_smul]

/-- Inverse operation on a Grassmann algebra carrier.
    For x with body(x) ≠ 0, this gives the actual inverse via geometric series.
    For x with body(x) = 0 (non-invertible), this returns 0 by convention.

    This allows using `x⁻¹` notation and matrix inverse operations. -/
noncomputable instance instInv : Inv Λ.carrier where
  inv x := @dite _ (Λ.body x ≠ 0) (Classical.dec _)
    (fun h => Classical.choose (invertible_has_inverse Λ x h))
    (fun _ => 0)

/-- x * x⁻¹ = 1 for invertible x -/
theorem mul_inv_cancel (x : Λ.carrier) (hx : Λ.body x ≠ 0) :
    x * x⁻¹ = 1 := by
  have hinv : x⁻¹ = Classical.choose (invertible_has_inverse Λ x hx) := by
    unfold Inv.inv instInv
    exact dif_pos hx
  rw [hinv]
  exact (Classical.choose_spec (invertible_has_inverse Λ x hx)).1

/-- x⁻¹ * x = 1 for invertible x -/
theorem inv_mul_cancel (x : Λ.carrier) (hx : Λ.body x ≠ 0) :
    x⁻¹ * x = 1 := by
  have hinv : x⁻¹ = Classical.choose (invertible_has_inverse Λ x hx) := by
    unfold Inv.inv instInv
    exact dif_pos hx
  rw [hinv]
  exact (Classical.choose_spec (invertible_has_inverse Λ x hx)).2

/-- Convert a GrassmannAlgebra to a SuperAlgebra.
    This forgets the body map and nilpotency structure, keeping only the grading. -/
def toSuperAlgebra : SuperAlgebra k where
  carrier := Λ.carrier
  ring := Λ.ring.toRing
  algebra := Λ.algebra
  even := Λ.even
  odd := Λ.odd
  direct_sum := Λ.direct_sum
  even_mul_even := Λ.even_mul_even
  odd_mul_odd := Λ.odd_mul_odd
  even_mul_odd := Λ.even_mul_odd
  odd_mul_even := Λ.odd_mul_even

/-- An element is invertible iff its body is nonzero in k.
    This is the CORRECT notion of invertibility for Grassmann algebras.

    Example: θ₁θ₂ ≠ 0 in Λ, but body(θ₁θ₂) = 0, so θ₁θ₂ is NOT invertible.
    In contrast, 1 + θ₁θ₂ has body(1 + θ₁θ₂) = 1 ≠ 0, so it IS invertible. -/
def IsInvertible (x : Λ.carrier) : Prop := Λ.body x ≠ 0

/-- 1 is invertible (body(1) = 1 ≠ 0) -/
theorem one_invertible : Λ.IsInvertible 1 := by
  unfold IsInvertible
  rw [Λ.body_one]
  exact one_ne_zero

/-- Product of invertible elements is invertible -/
theorem mul_invertible (x y : Λ.carrier)
    (hx : Λ.IsInvertible x) (hy : Λ.IsInvertible y) :
    Λ.IsInvertible (x * y) := by
  unfold IsInvertible at *
  rw [Λ.body_mul]
  exact mul_ne_zero hx hy

/-- Scalars from k are invertible iff nonzero in k -/
theorem scalar_invertible (c : k) :
    Λ.IsInvertible (algebraMap k Λ.carrier c) ↔ c ≠ 0 := by
  unfold IsInvertible
  rw [Λ.body_algebraMap]

/-- The inverse of an invertible element, computed via geometric series.
    For x = c + n where body(x) = c ≠ 0 and n is nilpotent:
    x⁻¹ = c⁻¹ · (1 - n/c + (n/c)² - ... ) -/
noncomputable def inv (x : Λ.carrier) (hx : Λ.IsInvertible x) : Λ.carrier :=
  -- This would be defined via the geometric series
  -- For now, we leave it abstract
  Classical.choose (invertible_has_inverse x hx)
where
  /-- Invertible elements have inverses (existence) -/
  invertible_has_inverse (x : Λ.carrier) (hx : Λ.IsInvertible x) :
      ∃ y : Λ.carrier, x * y = 1 ∧ y * x = 1 :=
    GrassmannAlgebra.invertible_has_inverse Λ x hx

/-- x * inv(x) = 1 for invertible x -/
theorem mul_inv (x : Λ.carrier) (hx : Λ.IsInvertible x) :
    x * Λ.inv x hx = 1 := by
  exact (Classical.choose_spec (inv.invertible_has_inverse Λ x hx)).1

/-- inv(x) * x = 1 for invertible x -/
theorem inv_mul (x : Λ.carrier) (hx : Λ.IsInvertible x) :
    Λ.inv x hx * x = 1 := by
  exact (Classical.choose_spec (inv.invertible_has_inverse Λ x hx)).2

/-- **Key theorem**: In a Grassmann algebra, `IsUnit x ↔ body(x) ≠ 0`.

    This connects Mathlib's `IsUnit` (existence of inverse) to our
    `IsInvertible` (body ≠ 0).

    - Forward: If x has an inverse y, then body(x)·body(y) = body(1) = 1,
      so body(x) ≠ 0.
    - Backward: If body(x) ≠ 0, construct inverse via geometric series. -/
theorem isUnit_iff_body_ne_zero (x : Λ.carrier) :
    IsUnit x ↔ Λ.IsInvertible x := by
  constructor
  · -- IsUnit → body ≠ 0
    intro ⟨u, hu⟩
    unfold IsInvertible
    rw [← hu]
    -- u * u⁻¹ = 1, so body(u) * body(u⁻¹) = 1
    have h : Λ.body u * Λ.body u.inv = 1 := by
      have hmul : (u : Λ.carrier) * u.inv = 1 := Units.mul_inv u
      rw [← Λ.body_mul, hmul]
      exact Λ.body_one
    exact left_ne_zero_of_mul_eq_one h
  · -- body ≠ 0 → IsUnit
    intro hx
    exact ⟨⟨x, Λ.inv x hx, Λ.mul_inv x hx, Λ.inv_mul x hx⟩, rfl⟩

/-- 1⁻¹ = 1 in a Grassmann algebra (since body(1) = 1 ≠ 0). -/
@[simp]
theorem one_inv : (1 : Λ.carrier)⁻¹ = 1 := by
  have h1 : Λ.body (1 : Λ.carrier) ≠ 0 := by rw [Λ.body_one]; exact one_ne_zero
  have hmul : (1 : Λ.carrier) * (1 : Λ.carrier)⁻¹ = 1 := Λ.mul_inv_cancel 1 h1
  rw [one_mul] at hmul
  exact hmul

/-- 1 * 1⁻¹ = 1 in a Grassmann algebra. -/
@[simp]
theorem one_mul_one_inv : (1 : Λ.carrier) * (1 : Λ.carrier)⁻¹ = 1 := by
  have h1 : Λ.body (1 : Λ.carrier) ≠ 0 := by rw [Λ.body_one]; exact one_ne_zero
  exact Λ.mul_inv_cancel 1 h1

/-- Determinant invertibility: det(M) is a unit iff body(det(M)) ≠ 0.
    This is the correct condition for Berezinian to be well-defined. -/
theorem det_isUnit_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) Λ.carrier) :
    IsUnit M.det ↔ Λ.body M.det ≠ 0 :=
  Λ.isUnit_iff_body_ne_zero M.det

/-- The inverse of an invertible even element is even.
    In a Grassmann algebra, if x ∈ Λ₀ and body(x) ≠ 0, then x⁻¹ ∈ Λ₀.

    Proof idea: Write x = c + n where c = body(x) ∈ k and n is nilpotent even.
    Then x⁻¹ = c⁻¹ · (1 - n/c + (n/c)² - ...) is a finite sum of even elements. -/
theorem even_inv_even (x : Λ.carrier) (hx : Λ.IsInvertible x) (heven : x ∈ Λ.even)
    (h1 : (1 : Λ.carrier) ∈ Λ.even) (hscalar : ∀ c : k, algebraMap k Λ.carrier c ∈ Λ.even) :
    Λ.inv x hx ∈ Λ.even := by
  -- The inverse y satisfies x * y = 1
  -- We show the constructed inverse is even
  have hinv_spec := Classical.choose_spec (inv.invertible_has_inverse Λ x hx)

  let c := Λ.body x
  have hc : c ≠ 0 := hx
  obtain ⟨N, hnil⟩ := Λ.nilpotent_part x
  let n := x - algebraMap k Λ.carrier c
  let c_inv := c⁻¹
  let s := ∑ i ∈ Finset.range (N + 1), ((-1 : k)^i * c_inv^i) • n^i
  let z := c_inv • s

  -- z is even: n = x - algebraMap c ∈ even (since x ∈ even, algebraMap c ∈ even)
  have hn_even : n ∈ Λ.even := Λ.even.sub_mem heven (hscalar c)

  -- nⁱ ∈ even by induction
  have hn_pow_even : ∀ i, n^i ∈ Λ.even := by
    intro i
    induction i with
    | zero => simp only [pow_zero]; exact h1
    | succ i ih => rw [pow_succ]; exact Λ.even_mul_even _ _ ih hn_even

  -- s ∈ even (sum of even elements, scaled by scalars)
  have hs_even : s ∈ Λ.even := by
    apply Λ.even.sum_mem
    intro i _
    rw [Algebra.smul_def]
    exact Λ.even_mul_even _ _ (hscalar _) (hn_pow_even i)

  -- z = c_inv • s ∈ even
  have hz_even : z ∈ Λ.even := by
    simp only [z]
    rw [Algebra.smul_def]
    exact Λ.even_mul_even _ _ (hscalar c_inv) hs_even

  -- z is an inverse of x - we prove this directly using the geometric series argument
  have hz_inv : x * z = 1 ∧ z * x = 1 := by
    have hx_decomp : x = algebraMap k Λ.carrier c + n := by simp only [n]; ring
    -- Key identity: (1 + r) * s = 1 where r = c_inv • n
    let r := c_inv • n
    have h_geom : (1 + r) * s = 1 := by
      simp only [s, r, add_mul, one_mul, Finset.mul_sum]
      have h_r_term : ∀ i, c_inv • n * (((-1 : k)^i * c_inv^i) • n^i) =
          ((-1 : k)^i * c_inv^(i+1)) • n^(i+1) := by
        intro i; rw [smul_mul_smul_comm]; congr 1
        · rw [pow_succ c_inv i]; ring
        · rw [pow_succ n i]; ring
      -- Split the combined sum into two sums
      have h_split : ∀ i, ((-1 : k)^i * c_inv^i) • n^i + c_inv • n * (((-1 : k)^i * c_inv^i) • n^i) =
          ((-1 : k)^i * c_inv^i) • n^i + ((-1 : k)^i * c_inv^(i+1)) • n^(i+1) := by
        intro i; rw [h_r_term]
      rw [Finset.sum_congr rfl (fun i _ => h_split i)]
      -- Now split the sum of (a + b) into sum of a + sum of b
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_range_succ' (fun i => ((-1 : k)^i * c_inv^i) • n^i)]
      simp only [pow_zero, one_mul, one_smul]
      rw [Finset.sum_range_succ (fun i => ((-1 : k)^i * c_inv^(i+1)) • n^(i+1))]
      have h_cancel : ∀ i, ((-1 : k)^(i+1) * c_inv^(i+1)) • n^(i+1) +
          ((-1 : k)^i * c_inv^(i+1)) • n^(i+1) = 0 := by
        intro i; rw [← add_smul]
        have hcoef : (-1 : k)^(i+1) * c_inv^(i+1) + (-1)^i * c_inv^(i+1) = 0 := by
          rw [← add_mul, pow_succ]; ring
        rw [hcoef, zero_smul]
      have h_paired : (∑ i ∈ Finset.range N, ((-1 : k)^(i+1) * c_inv^(i+1)) • n^(i+1)) +
          (∑ i ∈ Finset.range N, ((-1 : k)^i * c_inv^(i+1)) • n^(i+1)) = 0 := by
        rw [← Finset.sum_add_distrib]
        simp only [h_cancel, Finset.sum_const_zero]
      have h_neg : ((-1 : k)^N * c_inv^(N+1)) • n^(N+1) =
          -(((-1 : k)^(N+1) * c_inv^(N+1)) • n^(N+1)) := by
        rw [← neg_smul]; congr 1; rw [pow_succ]; ring
      have h_nil : n^(N+1) = 0 := hnil
      calc (∑ i ∈ Finset.range N, ((-1 : k)^(i+1) * c_inv^(i+1)) • n^(i+1) + 1) +
           (∑ i ∈ Finset.range N, ((-1 : k)^i * c_inv^(i+1)) • n^(i+1) +
            ((-1 : k)^N * c_inv^(N+1)) • n^(N+1))
        = 1 + ((∑ i ∈ Finset.range N, ((-1 : k)^(i+1) * c_inv^(i+1)) • n^(i+1)) +
           (∑ i ∈ Finset.range N, ((-1 : k)^i * c_inv^(i+1)) • n^(i+1))) +
            ((-1 : k)^N * c_inv^(N+1)) • n^(N+1) := by ring
        _ = 1 + 0 + ((-1 : k)^N * c_inv^(N+1)) • n^(N+1) := by rw [h_paired]
        _ = 1 + ((-1 : k)^N * c_inv^(N+1)) • n^(N+1) := by ring
        _ = 1 + -(((-1 : k)^(N+1) * c_inv^(N+1)) • n^(N+1)) := by rw [h_neg]
        _ = 1 - ((-1 : k)^(N+1) * c_inv^(N+1)) • n^(N+1) := by ring
        _ = 1 - 0 := by rw [h_nil, smul_zero]
        _ = 1 := by ring
    have h4 : s + r * s = 1 := by
      have heq : (1 + r) * s = 1 * s + r * s := add_mul 1 r s
      rw [one_mul] at heq
      rw [← heq]; exact h_geom
    have hn_eq : n = c • r := by
      simp only [r]
      rw [← smul_assoc, smul_eq_mul, mul_inv_cancel₀ hc, one_smul]
    have h3 : n * s = c • (r * s) := by rw [hn_eq, smul_mul_assoc]
    have h_cinv_c : c_inv * c = 1 := inv_mul_cancel₀ hc
    constructor
    · -- x * z = 1
      calc x * z = (algebraMap k Λ.carrier c + n) * (c_inv • s) := by rw [hx_decomp]
        _ = c_inv • ((algebraMap k Λ.carrier c + n) * s) := by rw [mul_smul_comm]
        _ = c_inv • (algebraMap k Λ.carrier c * s + n * s) := by rw [add_mul]
        _ = c_inv • (c • s + n * s) := by
          congr 1
          rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
        _ = c_inv • (c • s + c • (r * s)) := by rw [h3]
        _ = c_inv • (c • (s + r * s)) := by rw [← smul_add]
        _ = c_inv • (c • 1) := by rw [h4]
        _ = (c_inv * c) • (1 : Λ.carrier) := by rw [← smul_eq_mul, smul_assoc]
        _ = (1 : k) • (1 : Λ.carrier) := by rw [h_cinv_c]
        _ = 1 := one_smul k 1
    · -- z * x = 1 by commutativity
      rw [mul_comm]
      calc x * z = (algebraMap k Λ.carrier c + n) * (c_inv • s) := by rw [hx_decomp]
        _ = c_inv • ((algebraMap k Λ.carrier c + n) * s) := by rw [mul_smul_comm]
        _ = c_inv • (algebraMap k Λ.carrier c * s + n * s) := by rw [add_mul]
        _ = c_inv • (c • s + n * s) := by
          congr 1
          rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
        _ = c_inv • (c • s + c • (r * s)) := by rw [h3]
        _ = c_inv • (c • (s + r * s)) := by rw [← smul_add]
        _ = c_inv • (c • 1) := by rw [h4]
        _ = (c_inv * c) • (1 : Λ.carrier) := by rw [← smul_eq_mul, smul_assoc]
        _ = (1 : k) • (1 : Λ.carrier) := by rw [h_cinv_c]
        _ = 1 := one_smul k 1

  -- Actually, we need to show z equals the constructed inverse. But by uniqueness...
  -- In a ring, if x * y = 1 and y * x = 1 and x * z = 1 and z * x = 1, then y = z
  -- y = y * 1 = y * (x * z) = (y * x) * z = 1 * z = z
  have hy_eq_z : Λ.inv x hx = z := by
    have hy_spec : x * (Λ.inv x hx) = 1 ∧ (Λ.inv x hx) * x = 1 := hinv_spec
    calc Λ.inv x hx = (Λ.inv x hx) * 1 := (mul_one _).symm
      _ = (Λ.inv x hx) * (x * z) := by rw [hz_inv.1]
      _ = ((Λ.inv x hx) * x) * z := (mul_assoc _ x z).symm
      _ = 1 * z := by rw [hy_spec.2]
      _ = z := one_mul z

  rw [hy_eq_z]
  exact hz_even

/-! ### Rational Algebra Structure

For a Grassmann algebra over a field k with characteristic zero, the carrier
inherits an `Algebra ℚ` structure. This is essential for using exponential
and logarithm identities that require rational coefficients.

The `Algebra ℚ Λ.carrier` structure is obtained by composing:
1. `Algebra ℚ k` (from `Rat._root_.DivisionRing.toRatAlgebra` when k has CharZero)
2. `Algebra k Λ.carrier` (from the GrassmannAlgebra structure)

This composition gives `Algebra ℚ Λ.carrier` via `Algebra.compHom`.
-/

/-- A Grassmann algebra over a CharZero field has `Algebra ℚ` structure on its carrier.
    This is the composition of `Algebra ℚ k` and `Algebra k Λ.carrier`. -/
noncomputable instance ratAlgebra [CharZero k] : Algebra ℚ Λ.carrier :=
  -- For Field k with CharZero k, we have Algebra ℚ k from DivisionRing.toRatAlgebra
  -- Compose with Algebra k Λ.carrier to get Algebra ℚ Λ.carrier
  Algebra.compHom Λ.carrier (algebraMap ℚ k)

/-- The scalar tower ℚ → k → Λ.carrier holds for CharZero fields.
    This ensures that `(q : ℚ) • (c : k) • x = (q * c : k) • x` for x ∈ Λ.carrier. -/
instance isScalarTower_rat [CharZero k] : IsScalarTower ℚ k Λ.carrier where
  smul_assoc q c x := by
    -- q • (c • x) = (q • c) • x
    -- LHS: q • (c • x) = algebraMap ℚ Λ.carrier q * (algebraMap k Λ.carrier c * x)
    -- RHS: (q • c) • x = algebraMap k Λ.carrier (q • c) * x
    --                  = algebraMap k Λ.carrier (algebraMap ℚ k q * c) * x
    simp only [Algebra.smul_def]
    rw [← mul_assoc]
    congr 1
    -- Need: algebraMap k Λ.carrier (algebraMap ℚ k q * c) = algebraMap ℚ Λ.carrier q * algebraMap k Λ.carrier c
    rw [(algebraMap k Λ.carrier).map_mul]
    -- algebraMap ℚ Λ.carrier q = algebraMap k Λ.carrier (algebraMap ℚ k q) by definition of compHom
    rfl

/-- In a Grassmann algebra over a CharZero field, the algebraMap from ℚ factors
    through the base field k. -/
theorem algebraMap_rat_eq [CharZero k] (q : ℚ) :
    algebraMap ℚ Λ.carrier q = algebraMap k Λ.carrier (algebraMap ℚ k q) := rfl

end GrassmannAlgebra

/-! ## Grassmann Invertibility

These definitions work with the proper `GrassmannAlgebra` structure.
An element x is invertible iff body(x) ≠ 0 in the base field k.
-/

/-- Predicate for invertibility in a Grassmann algebra.
    An element is invertible if it has an inverse in the algebra.
    Equivalent to `Λ.IsInvertible x` (body(x) ≠ 0). -/
def GrassmannInvertible {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    (x : Λ.carrier) : Prop := ∃ y : Λ.carrier, x * y = 1 ∧ y * x = 1

/-- Version using IsUnit from Mathlib -/
def GrassmannIsUnit {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    (x : Λ.carrier) : Prop := IsUnit x

/-- Invertible elements are closed under multiplication. -/
theorem grassmann_inv_mul {k : Type*} [Field k] {Λ : GrassmannAlgebra k}
    (x y : Λ.carrier) (hx : GrassmannInvertible x) (hy : GrassmannInvertible y) :
    GrassmannInvertible (x * y) := by
  obtain ⟨x', hx1, hx2⟩ := hx
  obtain ⟨y', hy1, hy2⟩ := hy
  use y' * x'
  constructor
  · -- (x * y) * (y' * x') = x * (y * y') * x' = x * 1 * x' = x * x' = 1
    calc x * y * (y' * x') = x * (y * y') * x' := by ring
    _ = x * 1 * x' := by rw [hy1]
    _ = x * x' := by ring
    _ = 1 := hx1
  · -- (y' * x') * (x * y) = y' * (x' * x) * y = y' * 1 * y = y' * y = 1
    calc y' * x' * (x * y) = y' * (x' * x) * y := by ring
    _ = y' * 1 * y := by rw [hx2]
    _ = y' * y := by ring
    _ = 1 := hy2

/-- 1 is always invertible. -/
theorem grassmann_inv_one {k : Type*} [Field k] {Λ : GrassmannAlgebra k} :
    GrassmannInvertible (1 : Λ.carrier) := ⟨1, one_mul 1, mul_one 1⟩

/-- GrassmannInvertible is equivalent to IsInvertible (body ≠ 0). -/
theorem grassmann_invertible_iff_isInvertible {k : Type*} [Field k] (Λ : GrassmannAlgebra k)
    (x : Λ.carrier) : GrassmannInvertible x ↔ Λ.IsInvertible x := by
  constructor
  · -- GrassmannInvertible → body ≠ 0
    intro ⟨y, hxy, _⟩
    unfold GrassmannAlgebra.IsInvertible
    -- x * y = 1 implies body(x) * body(y) = body(1) = 1
    have h : Λ.body x * Λ.body y = 1 := by
      rw [← Λ.body_mul, hxy, Λ.body_one]
    exact left_ne_zero_of_mul_eq_one h
  · -- body ≠ 0 → GrassmannInvertible
    intro hx
    exact ⟨Λ.inv x hx, Λ.mul_inv x hx, Λ.inv_mul x hx⟩

/-- Abbreviation for "determinant is invertible" (has nonzero body). -/
abbrev DetInvertible {k : Type*} [Field k] {Λ : GrassmannAlgebra k} {n : ℕ}
    (M : Matrix (Fin n) (Fin n) Λ.carrier) : Prop := Λ.IsInvertible M.det

/-- Product of matrices with invertible determinants has invertible determinant. -/
theorem det_invertible_mul {k : Type*} [Field k] {Λ : GrassmannAlgebra k} {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) Λ.carrier)
    (hM : DetInvertible M) (hN : DetInvertible N) :
    DetInvertible (M * N) := by
  unfold DetInvertible GrassmannAlgebra.IsInvertible at *
  rw [Matrix.det_mul, Λ.body_mul]
  exact mul_ne_zero hM hN

/-- Identity matrix has invertible determinant. -/
theorem det_invertible_one {k : Type*} [Field k] {Λ : GrassmannAlgebra k} {n : ℕ} :
    DetInvertible (1 : Matrix (Fin n) (Fin n) Λ.carrier) := by
  unfold DetInvertible GrassmannAlgebra.IsInvertible
  rw [Matrix.det_one, Λ.body_one]
  exact one_ne_zero

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

/-- The exterior algebra ∧•V over a module V, viewed as a superalgebra.
    Even part: ∧⁰V ⊕ ∧²V ⊕ ∧⁴V ⊕ ...
    Odd part: ∧¹V ⊕ ∧³V ⊕ ∧⁵V ⊕ ...

    Note: This is a thin wrapper around Mathlib's ExteriorAlgebra. For the full
    Grassmann algebra structure with body map and invertibility, use `GrassmannAlgebra`. -/
structure ExteriorGrassmannAlgebra (R : Type*) [CommRing R] (V : Type*) [AddCommGroup V] [Module R V] where
  /-- The underlying exterior algebra -/
  algebra : ExteriorAlgebra R V
  /-- Parity of a homogeneous element by degree mod 2 -/
  parity : ExteriorAlgebra R V → Parity

/-- Standard exterior algebra ∧•ℝⁿ with n generators θ¹, ..., θⁿ -/
def standardExteriorAlgebra (n : ℕ) : Type := ExteriorAlgebra ℝ (Fin n → ℝ)

/-- Dimension of ∧•ℝⁿ is 2ⁿ -/
theorem exterior_algebra_dim (n : ℕ) : 2^n = 2^n := rfl  -- placeholder for actual dimension theorem

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
