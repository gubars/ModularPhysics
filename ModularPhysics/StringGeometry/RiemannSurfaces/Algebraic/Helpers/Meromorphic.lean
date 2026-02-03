import ModularPhysics.StringGeometry.RiemannSurfaces.Basic
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Meromorphic Functions on Riemann Surfaces

This file provides the basic infrastructure for meromorphic functions on
Riemann surfaces.

## Mathematical Background

A meromorphic function f : Σ → ℂ ∪ {∞} on a Riemann surface is holomorphic
except at isolated poles. In local coordinates z around a point p:
- f(z) = (z - p)^n · g(z) where g(p) ≠ 0, ∞
- n > 0: zero of order n
- n < 0: pole of order -n
- n = 0: regular point

## Main Definitions

* `MeromorphicFunction RS` - Meromorphic function on a Riemann surface
* `orderAt f p` - Order of f at point p
* `divisorOf f` - The divisor of zeros and poles

## Mathlib Integration

Mathlib provides `MeromorphicAt f x` for functions `f : ℂ → ℂ`. To connect
with Riemann surfaces, we need chart-based definitions (pending proper
implementation of `RiemannSurface.atlas`).

Key Mathlib modules:
- `Mathlib.Analysis.Meromorphic.Basic` - `MeromorphicAt`, `MeromorphicOn`
- `Mathlib.Analysis.Meromorphic.Divisor` - `MeromorphicOn.divisor`
- `Mathlib.Analysis.Meromorphic.IsolatedZeros` - Identity theorem

## References

* Farkas, Kra "Riemann Surfaces"
* Miranda "Algebraic Curves and Riemann Surfaces"
-/

namespace RiemannSurfaces

open RiemannSurfaces

/-!
## Meromorphic Function Structure

We use a bundled approach where the order function is part of the structure,
with consistency axioms. This avoids needing chart-based definitions while
maintaining soundness.
-/

/-- A meromorphic function on a Riemann surface.

    **Bundled approach:** We include the order function as part of the structure,
    with consistency axioms relating orders to function values.

    **Key properties (enforced by structure):**
    - order p > 0 ↔ f(p) = 0 (zeros have positive order)
    - order p < 0 ↔ f(p) = ∞ (poles have negative order)
    - {p | order p ≠ 0} is finite (identity theorem) -/
structure MeromorphicFunction (RS : RiemannSurface) where
  /-- The function Σ → ℂ ∪ {∞}, represented as ℂ ⊕ Unit (Unit = ∞) -/
  toFun : RS.carrier → ℂ ⊕ Unit
  /-- Order at each point: positive for zeros, negative for poles, zero otherwise -/
  order : RS.carrier → ℤ
  /-- Positive order iff the point is a zero -/
  order_pos_iff : ∀ p, 0 < order p ↔ toFun p = Sum.inl 0
  /-- Negative order iff the point is a pole -/
  order_neg_iff : ∀ p, order p < 0 ↔ toFun p = Sum.inr ()
  /-- Only finitely many zeros and poles (identity theorem) -/
  order_finiteSupport : Set.Finite { p | order p ≠ 0 }

namespace MeromorphicFunction

variable {RS : RiemannSurface}

/-- Coercion to function -/
instance : CoeFun (MeromorphicFunction RS) (fun _ => RS.carrier → ℂ ⊕ Unit) where
  coe := MeromorphicFunction.toFun

/-- Order is zero at regular points -/
theorem order_zero_iff (f : MeromorphicFunction RS) (p : RS.carrier) :
    f.order p = 0 ↔ (∃ z : ℂ, z ≠ 0 ∧ f.toFun p = Sum.inl z) := by
  constructor
  · intro h
    have hnpos : ¬(0 < f.order p) := by omega
    have hnneg : ¬(f.order p < 0) := by omega
    rw [f.order_pos_iff] at hnpos
    rw [f.order_neg_iff] at hnneg
    cases hfp : f.toFun p with
    | inl z =>
      use z
      constructor
      · intro hz
        apply hnpos
        rw [hfp, hz]
      · rfl
    | inr _ => exact absurd hfp hnneg
  · intro ⟨z, hz, hfp⟩
    have hnpos : ¬(0 < f.order p) := by
      rw [f.order_pos_iff, hfp]
      simp [hz]
    have hnneg : ¬(f.order p < 0) := by
      rw [f.order_neg_iff]
      simp [hfp]
    omega

/-!
## Basic Operations
-/

/-- The constant function 1 -/
def one : MeromorphicFunction RS where
  toFun := fun _ => Sum.inl 1
  order := fun _ => 0
  order_pos_iff := fun _ => by simp
  order_neg_iff := fun _ => by simp
  order_finiteSupport := by simp [Set.finite_empty]

/-- Reciprocal of a meromorphic function (exchanges zeros and poles).
    - Poles of g⁻¹ are zeros of g
    - Zeros of g⁻¹ are poles of g
    - order(g⁻¹, p) = -order(g, p) -/
noncomputable def inv (g : MeromorphicFunction RS) : MeromorphicFunction RS where
  toFun := fun p => match g.toFun p with
    | Sum.inl z => if z = 0 then Sum.inr () else Sum.inl z⁻¹
    | Sum.inr () => Sum.inl 0
  order := fun p => -g.order p
  order_pos_iff := fun p => by
    simp only [neg_pos]
    rw [g.order_neg_iff]
    constructor
    · intro h; simp [h]
    · intro h
      cases hg : g.toFun p with
      | inl z =>
        simp only [hg] at h
        split_ifs at h with hz
        all_goals simp_all
      | inr _ => rfl
  order_neg_iff := fun p => by
    simp only [neg_lt_zero]
    rw [g.order_pos_iff]
    constructor
    · intro h; simp [h]
    · intro h
      cases hg : g.toFun p with
      | inl z =>
        simp only [hg] at h
        split_ifs at h with hz
        subst hz; rfl
      | inr _ =>
        simp only [hg] at h
        cases h
  order_finiteSupport := by
    convert g.order_finiteSupport using 1
    ext p; simp

/-- Product of meromorphic functions.
    order(g*h, p) = order(g, p) + order(h, p)

    **Implementation note**: The toFun value must be determined by the sum of orders,
    not by pattern matching on individual values, because a zero of order n times
    a pole of order m gives a zero/pole of order n-m, which depends on the orders
    not just the values. -/
noncomputable def mul (g h : MeromorphicFunction RS) : MeromorphicFunction RS where
  toFun := fun p =>
    let sumOrder := g.order p + h.order p
    if sumOrder > 0 then
      Sum.inl 0  -- zero
    else if sumOrder < 0 then
      Sum.inr ()  -- pole
    else
      -- Orders sum to zero: regular point with product of values
      match g.toFun p, h.toFun p with
      | Sum.inl z₁, Sum.inl z₂ => Sum.inl (z₁ * z₂)
      -- When one is a zero and one is a pole with canceling orders,
      -- the result is a nonzero finite value (the "leading coefficient")
      | _, _ => Sum.inl 1  -- Placeholder for the limiting value
  order := fun p => g.order p + h.order p
  order_pos_iff := fun p => by
    constructor
    · intro h_pos
      show (if g.order p + h.order p > 0 then Sum.inl 0
            else if g.order p + h.order p < 0 then Sum.inr ()
            else _) = Sum.inl 0
      simp only [h_pos, ↓reduceIte]
    · intro h_eq
      show 0 < g.order p + h.order p
      by_contra h_not_pos
      push_neg at h_not_pos
      -- So g.order p + h.order p ≤ 0
      have h_not_pos' : ¬(g.order p + h.order p > 0) := by omega
      unfold toFun at h_eq
      simp only [h_not_pos', ↓reduceIte] at h_eq
      by_cases h_neg : g.order p + h.order p < 0
      · simp only [h_neg, ↓reduceIte] at h_eq
        cases h_eq
      · -- g.order p + h.order p = 0
        have h_zero : g.order p + h.order p = 0 := by omega
        simp only [h_neg, ↓reduceIte] at h_eq
        -- Now h_eq says the match result = Sum.inl 0
        -- When sum is 0, we need to analyze what each order can be
        -- Case analysis on whether g has a zero, pole, or regular point
        by_cases h_g_pos : g.order p > 0
        · -- g has a zero, so h.order p < 0 (pole) since sum = 0
          have h_h_neg : h.order p < 0 := by omega
          have h_h_pole : h.toFun p = Sum.inr () := (h.order_neg_iff p).mp h_h_neg
          have h_g_zero : g.toFun p = Sum.inl 0 := (g.order_pos_iff p).mp h_g_pos
          simp only [h_g_zero, h_h_pole, Sum.inl.injEq] at h_eq
          exact one_ne_zero h_eq
        · by_cases h_g_neg : g.order p < 0
          · -- g has a pole, so h.order p > 0 (zero) since sum = 0
            have h_h_pos : h.order p > 0 := by omega
            have h_g_pole : g.toFun p = Sum.inr () := (g.order_neg_iff p).mp h_g_neg
            have h_h_zero : h.toFun p = Sum.inl 0 := (h.order_pos_iff p).mp h_h_pos
            simp only [h_g_pole, h_h_zero, Sum.inl.injEq] at h_eq
            exact one_ne_zero h_eq
          · -- g.order p = 0, so h.order p = 0 since sum = 0
            have h_g_zero_ord : g.order p = 0 := by omega
            have h_h_zero_ord : h.order p = 0 := by omega
            -- Both are regular points with nonzero values
            obtain ⟨z1, hz1_ne, hg⟩ := (g.order_zero_iff p).mp h_g_zero_ord
            obtain ⟨z2, hz2_ne, hh⟩ := (h.order_zero_iff p).mp h_h_zero_ord
            simp only [hg, hh, Sum.inl.injEq] at h_eq
            -- h_eq : z1 * z2 = 0, but z1 ≠ 0 and z2 ≠ 0
            have := mul_ne_zero hz1_ne hz2_ne
            exact this h_eq
  order_neg_iff := fun p => by
    constructor
    · intro h_neg
      show (if g.order p + h.order p > 0 then Sum.inl 0
            else if g.order p + h.order p < 0 then Sum.inr ()
            else _) = Sum.inr ()
      have h_not_pos : ¬(g.order p + h.order p > 0) := by omega
      simp only [h_not_pos, ↓reduceIte, h_neg]
    · intro h_eq
      show g.order p + h.order p < 0
      by_contra h_not_neg
      push_neg at h_not_neg
      unfold toFun at h_eq
      by_cases h_pos : g.order p + h.order p > 0
      · simp only [h_pos, ↓reduceIte] at h_eq
        cases h_eq
      · -- g.order p + h.order p = 0
        have h_zero : g.order p + h.order p = 0 := by omega
        have h_not_neg : ¬(g.order p + h.order p < 0) := by omega
        simp only [h_pos, ↓reduceIte, h_not_neg] at h_eq
        -- Now h_eq should be: (match ...) = Sum.inr (), but the match always gives Sum.inl _
        cases hg : g.toFun p with
        | inl z1 =>
          cases hh : h.toFun p with
          | inl z2 =>
            simp only [hg, hh] at h_eq
            -- h_eq : Sum.inl (z1 * z2) = Sum.inr ()
            exact (Sum.inl_ne_inr h_eq).elim
          | inr _ =>
            simp only [hg, hh] at h_eq
            exact (Sum.inl_ne_inr h_eq).elim
        | inr _ =>
          cases hh : h.toFun p with
          | inl z2 =>
            simp only [hg, hh] at h_eq
            exact (Sum.inl_ne_inr h_eq).elim
          | inr _ =>
            simp only [hg, hh] at h_eq
            exact (Sum.inl_ne_inr h_eq).elim
  order_finiteSupport := by
    apply Set.Finite.subset (g.order_finiteSupport.union h.order_finiteSupport)
    intro p hp
    simp only [Set.mem_setOf_eq, ne_eq] at hp ⊢
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_contra hcon
    push_neg at hcon
    omega

instance : One (MeromorphicFunction RS) := ⟨MeromorphicFunction.one⟩
noncomputable instance : Inv (MeromorphicFunction RS) := ⟨MeromorphicFunction.inv⟩
noncomputable instance : Mul (MeromorphicFunction RS) := ⟨MeromorphicFunction.mul⟩

end MeromorphicFunction

/-!
## Order Function and Theorems
-/

/-- Order of a meromorphic function at a point -/
def orderAt {RS : RiemannSurface} (f : MeromorphicFunction RS) (p : RS.carrier) : ℤ :=
  f.order p

/-- A meromorphic function has finitely many zeros and poles (identity theorem) -/
theorem orderFiniteSupport {RS : RiemannSurface} (f : MeromorphicFunction RS) :
    Set.Finite { p | orderAt f p ≠ 0 } :=
  f.order_finiteSupport

/-- The constant function 1 has order 0 everywhere -/
theorem orderAt_one {RS : RiemannSurface} (p : RS.carrier) :
    orderAt (1 : MeromorphicFunction RS) p = 0 :=
  rfl

/-- Order of inverse: ord_p(1/f) = -ord_p(f) -/
theorem orderAt_inv {RS : RiemannSurface} (f : MeromorphicFunction RS) (p : RS.carrier) :
    orderAt f⁻¹ p = -orderAt f p :=
  rfl

/-- Order of product: ord_p(fg) = ord_p(f) + ord_p(g) -/
theorem orderAt_mul {RS : RiemannSurface} (f g : MeromorphicFunction RS) (p : RS.carrier) :
    orderAt (f * g) p = orderAt f p + orderAt g p :=
  rfl

end RiemannSurfaces
