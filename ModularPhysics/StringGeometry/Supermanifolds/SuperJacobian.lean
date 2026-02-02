/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.
-/
import ModularPhysics.StringGeometry.Supermanifolds.Supermanifolds
import ModularPhysics.StringGeometry.Supermanifolds.Helpers.Berezinian

/-!
# Super Jacobian for Coordinate Transformations on ℝ^{p|q}

This file defines the super Jacobian matrix for coordinate transformations
on the super domain ℝ^{p|q}, with entries in `SuperDomainFunction p q`.

## Mathematical Background

For a coordinate transformation (x, θ) → (x', θ') on ℝ^{p|q}:
- x'_i = x'_i(x, θ) = f_i(x) + nilpotent θ-terms
- θ'_a = θ'_a(x, θ) = Σ_b A^a_b(x) θ_b + higher order

The super Jacobian is the (p+q) × (p+q) supermatrix:
```
J = [∂x'/∂x   ∂x'/∂θ]
    [∂θ'/∂x   ∂θ'/∂θ]
```

With ℤ/2-grading:
- A block (p×p): ∂x'/∂x - EVEN entries (body + nilpotent)
- B block (p×q): ∂x'/∂θ - ODD entries
- C block (q×p): ∂θ'/∂x - ODD entries
- D block (q×q): ∂θ'/∂θ - EVEN entries (body + nilpotent)

The change of variables formula for Berezin integration:
  ∫ dθ' f(x', θ') = Ber(J)⁻¹ · ∫ dθ f(x, θ)

where Ber(J) is the Berezinian (superdeterminant).

## Connection to Berezinian Infrastructure

The Berezinian of the super Jacobian is computed using:
- `Helpers/SuperMatrix.lean` - General supermatrix structure
- `Helpers/Berezinian.lean` - Berezinian computation Ber(M) = det(A - BD⁻¹C)/det(D)

Since B and C blocks have odd entries (zero body), the leading-order Berezinian
satisfies:
  Ber(J)_body · det(D_body) = det(A_body)

## Main Definitions

* `SuperDomainFunction.isEven` - Even parity predicate
* `SuperDomainFunction.isOdd` - Odd parity predicate
* `SuperJacobian` - The super Jacobian matrix for coordinate transformations
* `SuperJacobian.Ablock_body`, `Dblock_body` - Body projections of diagonal blocks
* `SuperCoordinateChange` - General coordinate transformation on ℝ^{p|q}

## References

* Witten, E. "Notes On Supermanifolds And Integration" (arXiv:1209.2199)
* Deligne, P., Morgan, J. "Notes on Supersymmetry"
* Manin, Y. "Gauge Field Theory and Complex Geometry", Chapter 4
-/

noncomputable section

namespace Supermanifolds

/-!
## Parity in SuperDomainFunction

Elements of SuperDomainFunction p q are naturally graded by parity.
-/

/-- An element of SuperDomainFunction is even if it only has coefficients at even multi-indices -/
def SuperDomainFunction.isEven {p q : ℕ} (f : SuperDomainFunction p q) : Prop :=
  ∀ I : Finset (Fin q), I.card % 2 = 1 → f.coefficients I = 0

/-- An element of SuperDomainFunction is odd if it only has coefficients at odd multi-indices -/
def SuperDomainFunction.isOdd {p q : ℕ} (f : SuperDomainFunction p q) : Prop :=
  ∀ I : Finset (Fin q), I.card % 2 = 0 → f.coefficients I = 0

/-- The soul of a SuperDomainFunction: the nilpotent part (all non-body coefficients) -/
def SuperDomainFunction.soul {p q : ℕ} (f : SuperDomainFunction p q) : SuperDomainFunction p q where
  coefficients I := if I = ∅ then 0 else f.coefficients I

/-- Coefficient of zero function is zero -/
@[simp] theorem SuperDomainFunction.zero_coefficients {p q : ℕ} (I : Finset (Fin q)) :
    (0 : SuperDomainFunction p q).coefficients I = 0 := rfl

/-- Coefficient of one function at ∅ is 1 -/
@[simp] theorem SuperDomainFunction.one_coefficients_empty {p q : ℕ} :
    (1 : SuperDomainFunction p q).coefficients ∅ = 1 := by
  show (one).coefficients ∅ = 1
  simp only [one]
  rfl

/-- Coefficient of one function at non-empty I is 0 -/
@[simp] theorem SuperDomainFunction.one_coefficients_nonempty {p q : ℕ}
    {I : Finset (Fin q)} (hI : I ≠ ∅) :
    (1 : SuperDomainFunction p q).coefficients I = 0 := by
  show (one).coefficients I = 0
  simp only [one, hI, ↓reduceIte]

/-!
## Super Jacobian Matrix

The super Jacobian for coordinate transformations on ℝ^{p|q}.
Entries are in SuperDomainFunction with proper ℤ/2-grading.
-/

/-- The super Jacobian matrix for a coordinate transformation on ℝ^{p|q}.

    For a transformation (x, θ) → (x', θ'):
    - Ablock (p×p): ∂x'/∂x - even entries
    - Bblock (p×q): ∂x'/∂θ - odd entries
    - Cblock (q×p): ∂θ'/∂x - odd entries
    - Dblock (q×q): ∂θ'/∂θ - even entries

    This connects to the generic SuperMatrix (Helpers/SuperMatrix.lean) but is
    specialized for coordinate transformations on super domains:
    1. Entries are in SuperDomainFunction p q (smooth Grassmann-valued functions)
    2. The dimensions (p, q) are fixed and relate to the domain
    3. Specifically designed for computing the Berezinian of coordinate changes -/
structure SuperJacobian (p q : ℕ) where
  /-- Even-even block ∂x'/∂x (p×p), entries in the even part -/
  Ablock : Matrix (Fin p) (Fin p) (SuperDomainFunction p q)
  /-- Even-odd block ∂x'/∂θ (p×q), entries in the odd part -/
  Bblock : Matrix (Fin p) (Fin q) (SuperDomainFunction p q)
  /-- Odd-even block ∂θ'/∂x (q×p), entries in the odd part -/
  Cblock : Matrix (Fin q) (Fin p) (SuperDomainFunction p q)
  /-- Odd-odd block ∂θ'/∂θ (q×q), entries in the even part -/
  Dblock : Matrix (Fin q) (Fin q) (SuperDomainFunction p q)
  /-- A block entries are even -/
  Ablock_even : ∀ i j, (Ablock i j).isEven
  /-- B block entries are odd -/
  Bblock_odd : ∀ i j, (Bblock i j).isOdd
  /-- C block entries are odd -/
  Cblock_odd : ∀ i j, (Cblock i j).isOdd
  /-- D block entries are even -/
  Dblock_even : ∀ i j, (Dblock i j).isEven

namespace SuperJacobian

variable {p q : ℕ}

/-- The identity super Jacobian: identity transformation -/
def id : SuperJacobian p q where
  Ablock := 1  -- Identity matrix: (1)_ij = δ_ij
  Bblock := 0
  Cblock := 0
  Dblock := 1
  Ablock_even := fun i j => by
    intro I hI
    simp only [Matrix.one_apply]
    split_ifs with hij
    · -- δ_ij = 1: need (1 : SuperDomainFunction).coefficients I = 0 when |I| odd
      have hI_ne : I ≠ ∅ := by
        intro hI_empty
        rw [hI_empty] at hI
        simp at hI
      exact SuperDomainFunction.one_coefficients_nonempty hI_ne
    · -- δ_ij = 0
      exact SuperDomainFunction.zero_coefficients I
  Bblock_odd := fun _ _ => by
    intro I _
    simp only [Matrix.zero_apply]
    exact SuperDomainFunction.zero_coefficients I
  Cblock_odd := fun _ _ => by
    intro I _
    simp only [Matrix.zero_apply]
    exact SuperDomainFunction.zero_coefficients I
  Dblock_even := fun i j => by
    intro I hI
    simp only [Matrix.one_apply]
    split_ifs with hij
    · have hI_ne : I ≠ ∅ := by
        intro hI_empty
        rw [hI_empty] at hI
        simp at hI
      exact SuperDomainFunction.one_coefficients_nonempty hI_ne
    · exact SuperDomainFunction.zero_coefficients I

/-- Body of the A block: extract the body (θ⁰ coefficient) from each entry -/
def Ablock_body (J : SuperJacobian p q) : Matrix (Fin p) (Fin p) (SmoothFunction p) :=
  fun i j => (J.Ablock i j).body

/-- Body of the D block: extract the body (θ⁰ coefficient) from each entry -/
def Dblock_body (J : SuperJacobian p q) : Matrix (Fin q) (Fin q) (SmoothFunction p) :=
  fun i j => (J.Dblock i j).body

/-- Body of the B block: extract the body (θ⁰ coefficient) from each entry.
    Since B entries are odd, the body is zero. -/
def Bblock_body (J : SuperJacobian p q) : Matrix (Fin p) (Fin q) (SmoothFunction p) :=
  fun i j => (J.Bblock i j).body

/-- Body of the C block: extract the body (θ⁰ coefficient) from each entry.
    Since C entries are odd, the body is zero. -/
def Cblock_body (J : SuperJacobian p q) : Matrix (Fin q) (Fin p) (SmoothFunction p) :=
  fun i j => (J.Cblock i j).body

/-- The B block has zero body (since B entries are odd) -/
theorem Bblock_body_eq_zero (J : SuperJacobian p q) : J.Bblock_body = 0 := by
  ext i j
  simp only [Bblock_body, Matrix.zero_apply]
  -- B_ij is odd, so its ∅ coefficient is 0
  have hodd := J.Bblock_odd i j
  unfold SuperDomainFunction.isOdd at hodd
  have h0 : (∅ : Finset (Fin q)).card % 2 = 0 := by simp
  have hcoeff : (J.Bblock i j).coefficients ∅ = 0 := hodd ∅ h0
  unfold SuperDomainFunction.body
  simp only [hcoeff, SmoothFunction.zero_apply]

/-- The C block has zero body (since C entries are odd) -/
theorem Cblock_body_eq_zero (J : SuperJacobian p q) : J.Cblock_body = 0 := by
  ext i j
  simp only [Cblock_body, Matrix.zero_apply]
  -- C_ij is odd, so its ∅ coefficient is 0
  have hodd := J.Cblock_odd i j
  unfold SuperDomainFunction.isOdd at hodd
  have h0 : (∅ : Finset (Fin q)).card % 2 = 0 := by simp
  have hcoeff : (J.Cblock i j).coefficients ∅ = 0 := hodd ∅ h0
  unfold SuperDomainFunction.body
  simp only [hcoeff, SmoothFunction.zero_apply]

/-!
## Berezinian of Super Jacobian

The Berezinian (superdeterminant) is computed using the infrastructure in
`Helpers/Berezinian.lean`. The formula is:
  Ber(J) = det(A - BD⁻¹C) / det(D)

**Connection to Berezinian Infrastructure:**

The `Helpers/Berezinian.lean` file defines:
- `SuperMatrix Λ n m` - A supermatrix over GrassmannAlgebra Λ
- `SuperMatrix.ber` - Computes Ber(M) = det(schurD) / det(D) on Λ.evenCarrier
- `SuperMatrix.schurD_carrier` - The Schur complement A - BD⁻¹C

For a `SuperJacobian p q`, at each point x₀ ∈ ℝ^p:
1. Each entry (a SuperDomainFunction) evaluates to a Grassmann algebra element
2. This gives a `SuperMatrix` over the Grassmann algebra ∧(ℝ^q)
3. The Berezinian is computed using `SuperMatrix.ber`

Since B and C blocks have odd entries (zero body part):
  Ber(J)_body = det(A_body) / det(D_body)
-/

/-- The Berezinian simplification: B and C blocks have zero body.

    Since B and C entries are odd, their θ⁰ coefficients vanish.
    This means the Schur complement A - BD⁻¹C has body equal to A_body
    (to leading order).

    The full Berezinian computation uses `Helpers/Berezinian.lean`:
    - `SuperMatrix.ber` computes Ber(M) = det(A - BD⁻¹C) / det(D)
    - `SuperMatrix.schurD_carrier` = A - B * D_inv_carrier * C
    - When B_body = C_body = 0, the body of schurD is A_body -/
theorem berezinian_body_simplification (J : SuperJacobian p q) :
    J.Bblock_body = 0 ∧ J.Cblock_body = 0 := by
  exact ⟨J.Bblock_body_eq_zero, J.Cblock_body_eq_zero⟩

/-!
## Constructing a SuperMatrix from SuperJacobian

To use the full Berezinian infrastructure from `Helpers/Berezinian.lean`,
we need to construct a `SuperMatrix` from the `SuperJacobian`.

At a fixed point x₀ ∈ ℝ^p, the SuperJacobian entries (SuperDomainFunction values)
become elements of a Grassmann algebra. This construction requires:
1. A GrassmannAlgebra structure for ∧(ℝ^q)
2. Evaluation of SuperDomainFunction at x₀

The full construction involves significant infrastructure connecting
`SuperDomainFunction p q` to `GrassmannAlgebra ℝ` with q generators.
This is used in `BerezinIntegration.lean` for the change of variables formula.
-/

/-!
## Coordinate Transformations

A general super coordinate transformation on ℝ^{p|q}.
-/

/-- A super coordinate transformation on ℝ^{p|q}.

    This packages:
    1. The coordinate change functions (x', θ') as functions of (x, θ)
    2. The super Jacobian of the transformation
    3. Compatibility conditions ensuring the Jacobian is computed from the coordinates -/
structure SuperCoordinateChange (p q : ℕ) where
  /-- New even coordinates as functions of (x, θ) -/
  newEvenCoords : Fin p → SuperDomainFunction p q
  /-- New odd coordinates as functions of (x, θ) -/
  newOddCoords : Fin q → SuperDomainFunction p q
  /-- The Jacobian of the transformation -/
  jacobian : SuperJacobian p q
  /-- Even coordinates have even parity (body + even nilpotent terms) -/
  newEvenCoords_even : ∀ i, (newEvenCoords i).isEven
  /-- Odd coordinates have odd parity -/
  newOddCoords_odd : ∀ a, (newOddCoords a).isOdd
  /-- Jacobian A block is ∂x'/∂x -/
  jacobian_A : ∀ i j, jacobian.Ablock i j = partialEven j (newEvenCoords i)
  /-- Jacobian B block is ∂x'/∂θ -/
  jacobian_B : ∀ i a, jacobian.Bblock i a = partialOdd a (newEvenCoords i)
  /-- Jacobian C block is ∂θ'/∂x -/
  jacobian_C : ∀ a j, jacobian.Cblock a j = partialEven j (newOddCoords a)
  /-- Jacobian D block is ∂θ'/∂θ -/
  jacobian_D : ∀ a b, jacobian.Dblock a b = partialOdd b (newOddCoords a)

end SuperJacobian

/-!
## Change of Variables for Berezin Integration

The fundamental formula relating integrals under coordinate change.

For a super coordinate transformation φ : (x, θ) → (x', θ'),
the Berezin integral transforms as:

  ∫ dθ' f(x', θ') = Ber(J)⁻¹ · ∫ dθ (f ∘ φ)(x, θ)

where J is the super Jacobian and Ber(J) is its Berezinian.

This is the super analog of the classical change of variables formula
∫ dx' f(x') = |det(∂x'/∂x)|⁻¹ · ∫ dx f(x ∘ φ)

The key differences are:
1. We use Berezinian instead of determinant
2. The Berezinian appears INVERTED (not absolute value)
   because odd integration is contravariant
3. The Berezinian is Grassmann-valued (even element of SuperDomainFunction)

The formula follows from the transformation law for the top form:
  dθ'₁ ∧ ... ∧ dθ'_q = det(∂θ'/∂θ) · dθ₁ ∧ ... ∧ dθ_q

Combined with the super Jacobian structure.

See `Helpers/Berezinian.lean` for the full Berezinian computation
over GrassmannAlgebra, which applies when we work pointwise.
-/

end Supermanifolds

end
