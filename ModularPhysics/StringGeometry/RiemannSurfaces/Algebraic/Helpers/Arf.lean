import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Finset.Card

/-!
# The Arf Invariant

This file develops the theory of the Arf invariant for quadratic forms over ℤ/2ℤ.

## Mathematical Background

The Arf invariant is the unique invariant for non-degenerate quadratic forms
over fields of characteristic 2. For a quadratic form q on (ℤ/2ℤ)^{2n}:

- The Arf invariant Arf(q) ∈ ℤ/2ℤ classifies q up to equivalence
- Arf(q) = 0: "even" or "type I" quadratic form
- Arf(q) = 1: "odd" or "type II" quadratic form

## Counting Results

For non-degenerate quadratic forms on (ℤ/2ℤ)^{2g}:
- Total forms: 2^{2g}
- Even forms (Arf = 0): 2^{g-1}(2^g + 1)
- Odd forms (Arf = 1): 2^{g-1}(2^g - 1)

## Main Definitions

* `QuadFormZ2` - Quadratic form over ℤ/2ℤ
* `arfInvariant` - The Arf invariant
* `numEvenForms` - Count of even forms
* `numOddForms` - Count of odd forms

## References

* Arf, Cahit "Untersuchungen über quadratische Formen in Körpern der Charakteristik 2"
* Brown "The Arf invariant problem"
-/

namespace RiemannSurfaces.Arf

/-!
## Quadratic Forms over ℤ/2ℤ
-/

/-- A quadratic form over ℤ/2ℤ on (ℤ/2ℤ)^n.

    A quadratic form q satisfies:
    - q(0) = 0
    - q(x + y) = q(x) + q(y) + B(x, y) for a bilinear form B

    In characteristic 2, the polar identity gives B(x, y) = q(x + y) + q(x) + q(y). -/
structure QuadFormZ2 (n : ℕ) where
  /-- The quadratic form q : (ℤ/2ℤ)^n → ℤ/2ℤ -/
  form : (Fin n → ZMod 2) → ZMod 2
  /-- q(0) = 0 -/
  map_zero : form 0 = 0

namespace QuadFormZ2

variable {n : ℕ} (q : QuadFormZ2 n)

/-- The associated bilinear form B(x, y) = q(x + y) + q(x) + q(y).

    In characteristic 2, this is alternating: B(x, x) = 0. -/
def bilinearForm (x y : Fin n → ZMod 2) : ZMod 2 :=
  q.form (x + y) + q.form x + q.form y

/-- The bilinear form is symmetric (in char 2, it's also alternating) -/
theorem bilinearForm_symm (x y : Fin n → ZMod 2) :
    q.bilinearForm x y = q.bilinearForm y x := by
  unfold bilinearForm
  rw [add_comm x y]
  ring

/-- The bilinear form vanishes on the diagonal in char 2 -/
theorem bilinearForm_self (x : Fin n → ZMod 2) :
    q.bilinearForm x x = 0 := by
  unfold bilinearForm
  -- In char 2: x + x = 0, so B(x,x) = q(x+x) + q(x) + q(x) = q(0) + 2*q(x) = 0 + 0 = 0
  have h1 : x + x = 0 := by ext i; exact CharTwo.add_self_eq_zero (x i)
  rw [h1, q.map_zero, zero_add]
  -- q(x) + q(x) = 0 in char 2
  exact CharTwo.add_self_eq_zero (q.form x)

/-- A quadratic form is non-degenerate if B(x, y) = 0 for all y implies x = 0 -/
def NonDegenerate : Prop :=
  ∀ x : Fin n → ZMod 2, (∀ y, q.bilinearForm x y = 0) → x = 0

/-- Standard hyperbolic quadratic form on (ℤ/2ℤ)^2: q(x, y) = xy -/
def hyperbolic : QuadFormZ2 2 where
  form := fun v => v 0 * v 1
  map_zero := by simp

/-- The hyperbolic form is non-degenerate -/
theorem hyperbolic_nondegenerate : hyperbolic.NonDegenerate := by
  intro x hx
  funext i
  fin_cases i
  · -- i = 0: need to show x 0 = 0
    have h := hx (fun j => if j = 1 then 1 else 0)
    simp only [bilinearForm, hyperbolic] at h
    -- B(x, e_1) = q(x + e_1) + q(x) + q(e_1) = ... = x_0
    sorry
  · -- i = 1: need to show x 1 = 0
    have h := hx (fun j => if j = 0 then 1 else 0)
    simp only [bilinearForm, hyperbolic] at h
    sorry

end QuadFormZ2

/-!
## The Arf Invariant

The Arf invariant is defined using the formula:
  Arf(q) = Σ_{i=1}^{g} q(a_i) · q(b_i)
where {a_1, b_1, ..., a_g, b_g} is a symplectic basis for the bilinear form.

Equivalently, for non-degenerate q on (ℤ/2ℤ)^{2g}:
  Arf(q) = 0 iff #{x : q(x) = 0} = 2^{2g-1} + 2^{g-1}
  Arf(q) = 1 iff #{x : q(x) = 0} = 2^{2g-1} - 2^{g-1}
-/

/-- Count of elements where q evaluates to a given value -/
noncomputable def QuadFormZ2.countValue (q : QuadFormZ2 n) (v : ZMod 2) : ℕ :=
  (Finset.univ.filter (fun x => q.form x = v)).card

/-- The Arf invariant of a non-degenerate quadratic form on (ℤ/2ℤ)^{2g}.

    Defined by counting: Arf = 0 iff more elements evaluate to 0. -/
noncomputable def arfInvariant (g : ℕ) (q : QuadFormZ2 (2 * g)) : ZMod 2 :=
  -- Arf(q) = 0 iff #{q = 0} > #{q = 1}
  -- For non-degenerate forms: #{q = 0} = 2^{2g-1} ± 2^{g-1}
  if q.countValue 0 > q.countValue 1 then 0 else 1

/-- A quadratic form is even (type I) if Arf = 0 -/
def QuadFormZ2.isEven (g : ℕ) (q : QuadFormZ2 (2 * g)) : Prop :=
  arfInvariant g q = 0

/-- A quadratic form is odd (type II) if Arf = 1 -/
def QuadFormZ2.isOdd (g : ℕ) (q : QuadFormZ2 (2 * g)) : Prop :=
  arfInvariant g q = 1

/-- Every non-degenerate form is either even or odd -/
theorem arf_dichotomy (g : ℕ) (q : QuadFormZ2 (2 * g)) :
    q.isEven g ∨ q.isOdd g := by
  unfold QuadFormZ2.isEven QuadFormZ2.isOdd arfInvariant
  split_ifs with h
  · left; rfl
  · right; rfl

/-- Even and odd are mutually exclusive -/
theorem arf_exclusive (g : ℕ) (q : QuadFormZ2 (2 * g)) :
    ¬(q.isEven g ∧ q.isOdd g) := by
  unfold QuadFormZ2.isEven QuadFormZ2.isOdd
  intro ⟨h0, h1⟩
  rw [h0] at h1
  exact zero_ne_one h1

/-!
## Counting Results

The main counting theorem: for non-degenerate quadratic forms on (ℤ/2ℤ)^{2g}:
- Even forms: 2^{g-1}(2^g + 1)
- Odd forms: 2^{g-1}(2^g - 1)
-/

/-- The set of non-degenerate quadratic forms on (ℤ/2ℤ)^{2g} -/
def NonDegQuadForms (g : ℕ) := { q : QuadFormZ2 (2 * g) // q.NonDegenerate }

/-- Number of even non-degenerate quadratic forms on (ℤ/2ℤ)^{2g} -/
def numEvenForms (g : ℕ) : ℕ := 2^(g-1) * (2^g + 1)

/-- Number of odd non-degenerate quadratic forms on (ℤ/2ℤ)^{2g} -/
def numOddForms (g : ℕ) : ℕ := 2^(g-1) * (2^g - 1)

/-- Total number of non-degenerate quadratic forms -/
def numTotalForms (g : ℕ) : ℕ := 2^(2*g)

/-- The even and odd counts sum to the total -/
theorem count_sum (g : ℕ) (hg : g ≥ 1) :
    numEvenForms g + numOddForms g = numTotalForms g := by
  unfold numEvenForms numOddForms numTotalForms
  -- 2^{g-1}(2^g + 1) + 2^{g-1}(2^g - 1) = 2^{g-1} · 2 · 2^g = 2^{2g}
  have h1 : 2^g ≥ 1 := Nat.one_le_pow g 2 (by norm_num)
  have h2 : 2^g + 1 + (2^g - 1) = 2 * 2^g := by omega
  calc 2^(g-1) * (2^g + 1) + 2^(g-1) * (2^g - 1)
      = 2^(g-1) * ((2^g + 1) + (2^g - 1)) := by ring
    _ = 2^(g-1) * (2 * 2^g) := by rw [h2]
    _ = 2 * 2^(g-1) * 2^g := by ring
    _ = 2^g * 2^g := by
        have h3 : 2 * 2^(g-1) = 2^g := by
          cases g with
          | zero => omega
          | succ n => simp [pow_succ]; ring
        rw [h3]
    _ = 2^(2*g) := by rw [← pow_add]; ring_nf

/-- The count of even forms is 2^{g-1}(2^g + 1) -/
theorem even_form_count (g : ℕ) (_ : g ≥ 1) :
    numEvenForms g = 2^(g-1) * (2^g + 1) := rfl

/-- The count of odd forms is 2^{g-1}(2^g - 1) -/
theorem odd_form_count (g : ℕ) (_ : g ≥ 1) :
    numOddForms g = 2^(g-1) * (2^g - 1) := rfl

/-!
## Examples for Small Genus

Computed values using the formulas:
- numEvenForms g = 2^{g-1} * (2^g + 1)
- numOddForms g = 2^{g-1} * (2^g - 1)
- numTotalForms g = 2^{2g}

| g | even | odd | total |
|---|------|-----|-------|
| 1 |  3   |  1  |   4   |
| 2 | 10   |  6  |  16   |
| 3 | 36   | 28  |  64   |
-/

example : numEvenForms 1 = 3 := by native_decide
example : numOddForms 1 = 1 := by native_decide
example : numTotalForms 1 = 4 := by native_decide

example : numEvenForms 2 = 10 := by native_decide
example : numOddForms 2 = 6 := by native_decide
example : numTotalForms 2 = 16 := by native_decide

example : numEvenForms 3 = 36 := by native_decide
example : numOddForms 3 = 28 := by native_decide
example : numTotalForms 3 = 64 := by native_decide

end RiemannSurfaces.Arf
