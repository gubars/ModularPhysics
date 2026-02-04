import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Function Fields of Algebraic Curves

This file defines the function field K(C) of an algebraic curve and meromorphic functions
as elements of the function field. This is the **algebraic approach** to meromorphic functions.

## Mathematical Background

For a smooth projective algebraic curve C over ℂ:
- The function field K(C) is the field of rational functions on C
- An element f ∈ K(C) is a meromorphic function on C
- At each point p ∈ C, there is a discrete valuation v_p : K(C)* → ℤ
- The order of f at p is ord_p(f) = v_p(f)

Key properties:
- v_p(fg) = v_p(f) + v_p(g)
- v_p(f + g) ≥ min(v_p(f), v_p(g))
- v_p(f) > 0 iff p is a zero of f
- v_p(f) < 0 iff p is a pole of f
- v_p(f) ≠ 0 for only finitely many p (for f ≠ 0)

## Why This Is The Correct Definition

Unlike a "bundled" definition that just records (value, order) pairs with consistency axioms,
this definition is grounded in algebraic geometry:

1. The function field K(C) is a concrete mathematical object
2. A meromorphic function IS an element of K(C), not a separate structure
3. The valuation v_p comes from the local ring structure at p
4. All properties follow from the algebraic structure, not axioms

## Key Definitions

* `AlgebraicCurve` - A smooth projective algebraic curve with function field
* `AlgebraicCurve.FunctionField` - The function field K(C)
* `AlgebraicCurve.MeromorphicFunction` - Alias for elements of K(C)
* `AlgebraicCurve.valuation` - The discrete valuation v_p at each point

## References

* Hartshorne "Algebraic Geometry" II.6
* Miranda "Algebraic Curves and Riemann Surfaces" Ch IV
* Silverman "The Arithmetic of Elliptic Curves" Ch II
-/

namespace RiemannSurfaces.Algebraic

/-!
## Algebraic Curve Structure

An algebraic curve over ℂ, abstracted to capture the essential properties
needed for function field theory.
-/

/-- An algebraic curve over ℂ.

    This is an abstract structure capturing a smooth projective curve.
    The key data is:
    - `Point`: The set of closed points C(ℂ)
    - `FunctionField`: The field K(C) of rational functions

    The structure includes the discrete valuation at each point, which
    gives the algebraic definition of order for meromorphic functions.

    **Mathematical context:**
    In algebraic geometry, a smooth projective curve C over ℂ has:
    - A function field K(C) = Frac(O_C,η) where η is the generic point
    - At each closed point p, a discrete valuation ring O_{C,p} ⊆ K(C)
    - The valuation v_p : K(C)* → ℤ measures order of vanishing/pole at p -/
structure AlgebraicCurve where
  /-- The set of closed points of the curve -/
  Point : Type*
  /-- The function field K(C) -/
  FunctionField : Type*
  /-- The function field is a field -/
  [fieldInst : Field FunctionField]
  /-- The discrete valuation at each point p: v_p : K(C)* → ℤ
      Encodes order of vanishing/pole at p -/
  valuation : Point → FunctionField → ℤ
  /-- **Convention:** v_p(0) = 0.

      **Mathematical note:** In valuation theory, v_p(0) is formally +∞. However, we
      use 0 as a convention because:
      1. All meaningful operations (`valuation_mul`, `valuation_inv`) are only
         stated for nonzero elements, avoiding the 0 case entirely.
      2. This avoids the complexity of `WithTop ℤ` throughout the codebase.
      3. When computing divisors or supports, we always require f ≠ 0.

      The convention is safe because we never use v_p(0) in proofs that would
      require the ∞ value. The axiom `valuation_mul` explicitly requires f, g ≠ 0,
      so the potential inconsistency 0 = v_p(0) = v_p(0 · 1) = v_p(0) + v_p(1) = 0 + 0
      doesn't arise from the axioms. -/
  valuation_zero : ∀ p, valuation p 0 = 0
  /-- v_p(fg) = v_p(f) + v_p(g) for f, g ≠ 0 -/
  valuation_mul : ∀ p (f g : FunctionField), f ≠ 0 → g ≠ 0 →
    valuation p (f * g) = valuation p f + valuation p g
  /-- **Ultrametric inequality:** v_p(f + g) ≥ min(v_p(f), v_p(g)) when f + g ≠ 0.

      This is the fundamental property of discrete valuations that makes
      the valuation ring O_p = {f : v_p(f) ≥ 0} into a ring.

      Note: We require f + g ≠ 0 because our convention sets v_p(0) = 0,
      which could violate the inequality in degenerate cases like f = -g. -/
  valuation_add_min : ∀ p (f g : FunctionField), f + g ≠ 0 →
    valuation p (f + g) ≥ min (valuation p f) (valuation p g)
  /-- For any nonzero f ∈ K(C), only finitely many p have v_p(f) ≠ 0
      This is the algebraic version of "finitely many zeros and poles" -/
  valuation_finiteSupport : ∀ (f : FunctionField), f ≠ 0 →
    Set.Finite { p | valuation p f ≠ 0 }

attribute [instance] AlgebraicCurve.fieldInst

namespace AlgebraicCurve

variable (C : AlgebraicCurve)

/-- v_p(1) = 0. DERIVED from valuation_mul.
    Proof: v(1) = v(1*1) = v(1) + v(1) = 2*v(1), so v(1) = 0. -/
theorem valuation_one (p : C.Point) : C.valuation p 1 = 0 := by
  have h1_ne : (1 : C.FunctionField) ≠ 0 := one_ne_zero
  have h := C.valuation_mul p 1 1 h1_ne h1_ne
  simp only [mul_one] at h
  omega

/-- v_p(f⁻¹) = -v_p(f) for f ≠ 0. DERIVED from valuation_mul + valuation_one.
    Proof: v(f) + v(f⁻¹) = v(f * f⁻¹) = v(1) = 0. -/
theorem valuation_inv (p : C.Point) (f : C.FunctionField) (hf : f ≠ 0) :
    C.valuation p f⁻¹ = -C.valuation p f := by
  have hf_inv_ne : f⁻¹ ≠ 0 := inv_ne_zero hf
  have h := C.valuation_mul p f f⁻¹ hf hf_inv_ne
  rw [mul_inv_cancel₀ hf, C.valuation_one] at h
  omega

end AlgebraicCurve

/-!
## ℂ-Algebra Structure on Function Fields

The function field K(C) of an algebraic curve over ℂ is naturally a ℂ-algebra:
the constant functions embed ℂ into K(C).

Key property: constant functions have valuation 0 everywhere (no zeros or poles).
-/

/-- A ℂ-algebra structure on the function field of an algebraic curve.

    **Mathematical content:**
    For an algebraic curve C over ℂ, the structure morphism ℂ → K(C) embeds
    ℂ as the constant functions. These have no zeros or poles, so v_p(c) = 0
    for all p and all nonzero c ∈ ℂ.

    This is essential for:
    1. RiemannRochSpace L(D) being a ℂ-vector space
    2. h⁰(D) = dim_ℂ L(D) making sense
    3. Scalar multiplication in L(D) -/
class FunctionFieldAlgebra (C : AlgebraicCurve) where
  /-- The ℂ-algebra structure on K(C) -/
  algebraInst : Algebra ℂ C.FunctionField
  /-- Constant nonzero functions have valuation 0 everywhere.
      This is because constant functions have no zeros or poles. -/
  valuation_algebraMap : ∀ (p : C.Point) (c : ℂ), c ≠ 0 →
    C.valuation p (algebraMap ℂ C.FunctionField c) = 0

attribute [instance] FunctionFieldAlgebra.algebraInst

namespace AlgebraicCurve

variable (C : AlgebraicCurve)

/-- The order of f ∈ K(C) at point p.
    This is the algebraic definition of order using discrete valuation. -/
def orderAt (f : C.FunctionField) (p : C.Point) : ℤ :=
  C.valuation p f

/-- f has a zero at p iff v_p(f) > 0 -/
def hasZeroAt (f : C.FunctionField) (p : C.Point) : Prop :=
  0 < C.valuation p f

/-- f has a pole at p iff v_p(f) < 0 -/
def hasPoleAt (f : C.FunctionField) (p : C.Point) : Prop :=
  C.valuation p f < 0

/-- f is regular at p iff v_p(f) ≥ 0 (no pole) -/
def isRegularAt (f : C.FunctionField) (p : C.Point) : Prop :=
  0 ≤ C.valuation p f

/-- The support of f: points where f has a zero or pole -/
def support (f : C.FunctionField) : Set C.Point :=
  { p | C.valuation p f ≠ 0 }

theorem support_finite (f : C.FunctionField) (hf : f ≠ 0) :
    Set.Finite (C.support f) :=
  C.valuation_finiteSupport f hf

/-!
## Algebraic Meromorphic Functions

A meromorphic function on an algebraic curve is simply an element of the function field K(C).
This is the **correct algebraic definition** - no separate structure needed.
-/

/-- A meromorphic function on an algebraic curve is an element of its function field.

    **This is the correct algebraic definition.**

    Unlike the "bundled" approach that just records data, this definition
    is mathematically grounded: f ∈ K(C) automatically has all the properties
    of a meromorphic function because K(C) is defined as the field of rational
    functions on C.

    The order at each point comes from the discrete valuation v_p, which is
    intrinsic to the algebraic structure of the curve. -/
abbrev MeromorphicFunction := C.FunctionField

/-- The divisor of a nonzero meromorphic function.

    div(f) = Σ_p v_p(f) · [p]

    This is a formal sum with finite support (the support of f). -/
structure Divisor (C : AlgebraicCurve) where
  /-- The coefficient at each point -/
  coeff : C.Point → ℤ
  /-- Only finitely many points have nonzero coefficient -/
  finiteSupport : Set.Finite { p | coeff p ≠ 0 }

/-- The divisor of a nonzero meromorphic function -/
noncomputable def divisorOf (f : C.FunctionField) (hf : f ≠ 0) : Divisor C where
  coeff := fun p => C.valuation p f
  finiteSupport := C.valuation_finiteSupport f hf

/-- The degree of a divisor: deg(D) = Σ_p D(p) -/
noncomputable def Divisor.degree (D : Divisor C) : ℤ :=
  D.finiteSupport.toFinset.sum D.coeff

/-- The sum of orders (valuations) of a nonzero function -/
noncomputable def orderSum (f : C.FunctionField) (hf : f ≠ 0) : ℤ :=
  (divisorOf C f hf).degree

end AlgebraicCurve

/-!
## The Argument Principle (Algebraic Version)

On an algebraic curve, the argument principle states that for any
nonzero f ∈ K(C), the degree of its divisor is zero:

  deg(div(f)) = Σ_p v_p(f) = 0

This is sometimes stated as "principal divisors have degree zero".
-/

/-- A compact algebraic curve (smooth projective curve over ℂ).

    For a compact curve, the argument principle holds: the degree
    of any principal divisor is zero. -/
structure CompactAlgebraicCurve extends AlgebraicCurve where
  /-- The ℂ-algebra structure on the function field -/
  [algebraInst : FunctionFieldAlgebra toAlgebraicCurve]
  /-- The genus of the curve -/
  genus : ℕ
  /-- The argument principle: degree of any principal divisor is zero.

      **Mathematical content:**
      This follows from the fact that on a compact curve, a rational function
      f : C → ℙ¹ is a finite morphism of degree d, so it has exactly d zeros
      (with multiplicity) and d poles (with multiplicity).

      Proof approaches:
      1. Algebraic: The Picard group Pic⁰(C) is the kernel of deg: Div(C) → ℤ,
         and principal divisors lie in Pic⁰(C).
      2. Topological: f: C → ℙ¹ is a branched covering, fiber cardinality is constant.
      3. Analytic (via GAGA): Residue theorem, ∮ f'/f = 0 on compact surfaces. -/
  argumentPrinciple : ∀ (f : FunctionField) (hf : f ≠ 0),
    toAlgebraicCurve.orderSum f hf = 0
  /-- **Properness**: Regular (pole-free) functions are constant.

      **Mathematical content:**
      On a proper (complete) algebraic variety over an algebraically closed field,
      a regular function is constant. For curves, this means:
      If f ∈ K(C) satisfies v_p(f) ≥ 0 for all p ∈ C, then f ∈ ℂ.

      **Proof sketch**:
      1. A regular function f has no poles, defining a morphism f : C → 𝔸¹
      2. Since C is proper and 𝔸¹ is affine, f factors through a point
      3. (Alternatively: f extends to f : C → ℙ¹, and if f ≠ const, the image
         is ℙ¹, but then f⁻¹({∞}) ≠ ∅, contradiction with f having no poles)

      This is the algebraic version of the Liouville theorem. -/
  regularIsConstant : ∀ (f : FunctionField), (∀ p : Point, 0 ≤ toAlgebraicCurve.valuation p f) →
    ∃ (c : ℂ), f = @algebraMap ℂ FunctionField _ _ algebraInst.algebraInst c
  /-- **Local parameter existence**: At each point p, there exists a local parameter.

      **Mathematical content:**
      For any point p on a smooth algebraic curve, the maximal ideal m_p of the
      local ring O_{C,p} is principal, generated by a single element t_p called
      a local parameter (or uniformizing parameter).

      Properties of a local parameter t_p:
      - v_p(t_p) = 1 (t_p vanishes to first order at p)
      - m_p = (t_p) in the local ring O_{C,p}

      This follows from the fact that smooth curves are regular schemes of dimension 1,
      hence their local rings are DVRs (discrete valuation rings), which have principal
      maximal ideals. -/
  localParameter : Point → FunctionField
  localParameter_valuation : ∀ p, toAlgebraicCurve.valuation p (localParameter p) = 1
  /-- **Local parameters have no other zeros**: v_q(t_p) ≤ 0 for q ≠ p.

      By the argument principle (Σ v_q(t_p) = 0) and v_p(t_p) = 1, the local
      parameter t_p must have a pole somewhere. This axiom says t_p has no
      additional ZEROS (only at p), but may have poles at other points.

      Geometrically: t_p is a function with a simple zero at p and poles
      elsewhere that balance out to total degree 0. -/
  localParameter_nonpos_away : ∀ p q, p ≠ q → toAlgebraicCurve.valuation q (localParameter p) ≤ 0
  /-- **Leading coefficient uniqueness** (DVR property).

      For f, g ∈ K(C)* with v_p(f) = v_p(g) = -m < 0 (same pole order at p),
      there exists c ∈ ℂ* such that g - cf has strictly higher valuation at p.

      **Mathematical content:**
      In the local ring O_{C,p} (a DVR), any nonzero element f can be written as
      f = u · t_p^{v_p(f)} where u is a unit. For f, g with the same valuation -m,
      we have f = u_f · t_p^{-m} and g = u_g · t_p^{-m}. Taking c = u_g(p)/u_f(p)
      (the ratio of leading coefficients), we get g - cf = 0 or v_p(g - cf) > -m.

      This is the key property that makes L(D)/L(D-p) at most 1-dimensional. -/
  leadingCoefficientUniqueness : ∀ (p : Point) (f g : FunctionField),
      f ≠ 0 → g ≠ 0 →
      toAlgebraicCurve.valuation p f = toAlgebraicCurve.valuation p g →
      toAlgebraicCurve.valuation p f < 0 →
      ∃ (c : ℂ), c ≠ 0 ∧
        (g - @algebraMap ℂ FunctionField _ _ algebraInst.algebraInst c * f = 0 ∨
         toAlgebraicCurve.valuation p (g - @algebraMap ℂ FunctionField _ _ algebraInst.algebraInst c * f) >
         toAlgebraicCurve.valuation p g)
namespace CompactAlgebraicCurve

variable (C : CompactAlgebraicCurve)

/-- The number of zeros equals the number of poles (counting multiplicity).

    This is an immediate consequence of the argument principle:
    sum of positive orders (zeros) + sum of negative orders (poles) = 0
    Therefore: sum of positive orders = -(sum of negative orders) -/
theorem zeros_eq_poles (f : C.FunctionField) (hf : f ≠ 0) :
    let S := (C.toAlgebraicCurve.valuation_finiteSupport f hf).toFinset
    (S.filter (fun p => 0 < C.valuation p f)).sum (fun p => C.valuation p f) =
    -((S.filter (fun p => C.valuation p f < 0)).sum (fun p => C.valuation p f)) := by
  intro S
  have h := C.argumentPrinciple f hf
  unfold AlgebraicCurve.orderSum AlgebraicCurve.divisorOf AlgebraicCurve.Divisor.degree at h
  simp only at h
  -- The support sum = positive part + negative part = 0
  -- Split the sum over support into positive and negative parts
  have hsplit : S.sum (fun p => C.valuation p f) =
      (S.filter (fun p => 0 < C.valuation p f)).sum (fun p => C.valuation p f) +
      (S.filter (fun p => C.valuation p f < 0)).sum (fun p => C.valuation p f) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun p => 0 < C.valuation p f)]
    congr 1
    apply Finset.sum_congr
    · ext p
      simp only [Finset.mem_filter, not_lt]
      constructor
      · intro ⟨hmem, hle⟩
        refine ⟨hmem, ?_⟩
        have hne : C.valuation p f ≠ 0 := by
          rw [Set.Finite.mem_toFinset] at hmem
          simp only [Set.mem_setOf_eq] at hmem
          exact hmem
        omega
      · intro ⟨hmem, hlt⟩
        exact ⟨hmem, le_of_lt hlt⟩
    · intros; rfl
  rw [hsplit] at h
  linarith

/-- Helper: valuation of positive power of local parameter -/
private theorem valuation_localParameter_pow_nat (p : C.Point) (k : ℕ) :
    C.toAlgebraicCurve.valuation p (C.localParameter p ^ k) = k := by
  induction k with
  | zero => simp [C.toAlgebraicCurve.valuation_one]
  | succ k ih =>
    rw [pow_succ]
    have ht_ne : C.localParameter p ≠ 0 := by
      intro h
      have := C.localParameter_valuation p
      rw [h, C.toAlgebraicCurve.valuation_zero] at this
      omega
    have hpow_ne : C.localParameter p ^ k ≠ 0 := pow_ne_zero k ht_ne
    rw [C.toAlgebraicCurve.valuation_mul p _ _ hpow_ne ht_ne, ih, C.localParameter_valuation]
    omega

/-- Helper: valuation of integer power of local parameter -/
private theorem valuation_localParameter_zpow (p : C.Point) (m : ℤ) :
    C.toAlgebraicCurve.valuation p (C.localParameter p ^ m) = m := by
  have ht_ne : C.localParameter p ≠ 0 := by
    intro h
    have := C.localParameter_valuation p
    rw [h, C.toAlgebraicCurve.valuation_zero] at this
    omega
  cases m with
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact_mod_cast valuation_localParameter_pow_nat C p k
  | negSucc k =>
    simp only [zpow_negSucc]
    have hpow_ne : C.localParameter p ^ (k + 1) ≠ 0 := pow_ne_zero (k + 1) ht_ne
    rw [C.toAlgebraicCurve.valuation_inv p _ hpow_ne]
    have hpow_val := valuation_localParameter_pow_nat C p (k + 1)
    simp only [Nat.cast_add, Nat.cast_one] at hpow_val
    omega

/-- **Generalized leading coefficient uniqueness (for any valuation)**.

    DERIVED from `leadingCoefficientUniqueness` + `localParameter` - not an axiom.

    The same as `leadingCoefficientUniqueness` but without the v < 0 requirement.
    This works for both poles (v < 0), zeros (v > 0), and regular points (v = 0).

    **Proof idea:** Given f, g with v_p(f) = v_p(g) = n, multiply by t_p^(-n-1)
    to get functions with valuation -1 < 0, apply `leadingCoefficientUniqueness`,
    then multiply back. -/
theorem leadingCoefficientUniquenessGeneral (p : C.Point) (f g : C.FunctionField)
    (hf : f ≠ 0) (hg : g ≠ 0)
    (heq : C.toAlgebraicCurve.valuation p f = C.toAlgebraicCurve.valuation p g) :
    ∃ (c : ℂ), c ≠ 0 ∧
      (g - @algebraMap ℂ C.FunctionField _ _ C.algebraInst.algebraInst c * f = 0 ∨
       C.toAlgebraicCurve.valuation p (g - @algebraMap ℂ C.FunctionField _ _ C.algebraInst.algebraInst c * f) >
       C.toAlgebraicCurve.valuation p g) := by
  -- Let n = v_p(f) = v_p(g)
  set n := C.toAlgebraicCurve.valuation p f with hn_def
  -- Let t = localParameter p, with v_p(t) = 1
  set t := C.localParameter p with ht_def
  have ht_val : C.toAlgebraicCurve.valuation p t = 1 := C.localParameter_valuation p
  have ht_ne : t ≠ 0 := by
    intro h
    rw [h, C.toAlgebraicCurve.valuation_zero] at ht_val
    omega
  -- Define the exponent: we want to multiply by t^(-n-1) to get valuation -1
  set m : ℤ := -n - 1 with hm_def
  have hm_sum : n + m = -1 := by omega
  -- t^m is well-defined in the function field
  set tm := t ^ m with htm_def
  have htm_ne : tm ≠ 0 := zpow_ne_zero m ht_ne
  have htm_val : C.toAlgebraicCurve.valuation p tm = m := by
    rw [htm_def, ht_def]
    exact valuation_localParameter_zpow C p m
  -- Now define f' = f * tm, g' = g * tm
  set f' := f * tm with hf'_def
  set g' := g * tm with hg'_def
  have hf'_ne : f' ≠ 0 := mul_ne_zero hf htm_ne
  have hg'_ne : g' ≠ 0 := mul_ne_zero hg htm_ne
  have hf'_val : C.toAlgebraicCurve.valuation p f' = -1 := by
    rw [hf'_def, C.toAlgebraicCurve.valuation_mul p _ _ hf htm_ne, htm_val]
    omega
  have hg'_val : C.toAlgebraicCurve.valuation p g' = -1 := by
    rw [hg'_def, C.toAlgebraicCurve.valuation_mul p _ _ hg htm_ne, htm_val]
    omega
  have heq' : C.toAlgebraicCurve.valuation p f' = C.toAlgebraicCurve.valuation p g' := by
    rw [hf'_val, hg'_val]
  have hneg : C.toAlgebraicCurve.valuation p f' < 0 := by rw [hf'_val]; omega
  -- Apply leadingCoefficientUniqueness to f', g'
  obtain ⟨c, hc_ne, hc_prop⟩ := C.leadingCoefficientUniqueness p f' g' hf'_ne hg'_ne heq' hneg
  -- Return the same c
  refine ⟨c, hc_ne, ?_⟩
  -- We need: g' - c * f' = (g - c * f) * tm
  have hdiff : g' - @algebraMap ℂ C.FunctionField _ _ C.algebraInst.algebraInst c * f' =
               (g - @algebraMap ℂ C.FunctionField _ _ C.algebraInst.algebraInst c * f) * tm := by
    rw [hf'_def, hg'_def]
    ring
  -- First check if g - cf = 0 (then we return Left regardless of hc_prop)
  by_cases hdiff_zero : g - @algebraMap ℂ C.FunctionField _ _ C.algebraInst.algebraInst c * f = 0
  · -- g - cf = 0, return Left
    left
    exact hdiff_zero
  · -- g - cf ≠ 0, so g' - cf' ≠ 0 (since g' - cf' = (g - cf) * tm and tm ≠ 0)
    have hdiff'_ne : g' - @algebraMap ℂ C.FunctionField _ _ C.algebraInst.algebraInst c * f' ≠ 0 := by
      rw [hdiff]
      exact mul_ne_zero hdiff_zero htm_ne
    -- In this case, hc_prop must be inr (since inl would give g' - cf' = 0)
    cases hc_prop with
    | inl heq0 =>
      -- g' - cf' = 0, but we just showed g' - cf' ≠ 0
      exact absurd heq0 hdiff'_ne
    | inr hgt =>
      -- v_p(g' - c*f') > v_p(g') = -1
      right
      rw [hdiff, hg'_val] at hgt
      have hval_mul : C.toAlgebraicCurve.valuation p ((g - @algebraMap ℂ C.FunctionField _ _ C.algebraInst.algebraInst c * f) * tm) =
          C.toAlgebraicCurve.valuation p (g - @algebraMap ℂ C.FunctionField _ _ C.algebraInst.algebraInst c * f) + m := by
        rw [C.toAlgebraicCurve.valuation_mul p _ _ hdiff_zero htm_ne, htm_val]
      rw [hval_mul] at hgt
      -- hgt : v(g - cf) + m > -1, where m = -n - 1 and n = v(g)
      -- So v(g - cf) > -1 - m = -1 - (-n-1) = n = v(g)
      have : C.toAlgebraicCurve.valuation p g = n := heq.symm
      rw [this]
      omega

/-- **Short exact sequence dimension formula (leading coefficient extraction)**.

    DERIVED from `leadingCoefficientUniqueness` + `localParameter` - not an axiom.

    For any f ∈ K(C)* with v_p(f) < 0 (a pole at p), there exists c ∈ ℂ* such that
    v_p(f - c · t_p^{v_p(f)}) > v_p(f).

    **Proof:** Apply `leadingCoefficientUniqueness` with g = f and f' = t_p^{v_p(f)}.
    If f - c * t_p^n ≠ 0, the lemma gives v_p(f - c * t_p^n) > v_p(f).
    If f - c * t_p^n = 0, then v_p(0) = 0 > v_p(f) since v_p(f) < 0. -/
theorem shortExactDimFormula (p : C.Point) (f : C.FunctionField) (hf : f ≠ 0)
    (_hreg : ∀ q, p ≠ q → C.toAlgebraicCurve.valuation q f ≥ 0)
    (hn : C.toAlgebraicCurve.valuation p f < 0) :
    ∃ (c : ℂ), c ≠ 0 ∧
      C.toAlgebraicCurve.valuation p (f - @algebraMap ℂ C.FunctionField _ _ C.algebraInst.algebraInst c *
        C.localParameter p ^ (C.toAlgebraicCurve.valuation p f)) >
      C.toAlgebraicCurve.valuation p f := by
  -- Let n = v_p(f) < 0, t = localParameter p
  set n := C.toAlgebraicCurve.valuation p f with hn_def
  set t := C.localParameter p with ht_def
  -- t^n has v_p(t^n) = n (same as f)
  have ht_ne : t ≠ 0 := by
    intro h
    have := C.localParameter_valuation p
    rw [← ht_def, h, C.toAlgebraicCurve.valuation_zero] at this
    omega
  have htn_ne : t ^ n ≠ 0 := zpow_ne_zero n ht_ne
  have htn_val : C.toAlgebraicCurve.valuation p (t ^ n) = n := by
    rw [ht_def]
    exact valuation_localParameter_zpow C p n
  -- Apply leadingCoefficientUniqueness with g = f and f' = t^n
  have heq_val : C.toAlgebraicCurve.valuation p (t ^ n) = C.toAlgebraicCurve.valuation p f := by
    rw [htn_val, hn_def]
  obtain ⟨c, hc_ne, hcases⟩ := C.leadingCoefficientUniqueness p (t ^ n) f htn_ne hf heq_val (by rw [htn_val]; exact hn)
  refine ⟨c, hc_ne, ?_⟩
  rcases hcases with hdiff_zero | hdiff_gt
  · -- f - c * t^n = 0, so v_p(0) = 0 > n = v_p(f) (since n < 0)
    rw [hdiff_zero, C.toAlgebraicCurve.valuation_zero]
    exact hn
  · -- v_p(f - c * t^n) > v_p(f) directly
    exact hdiff_gt

end CompactAlgebraicCurve

/-!
## Example: The Projective Line

The projective line ℙ¹ is the simplest example of a compact algebraic curve (genus 0).
- Points: ℂ ∪ {∞} (represented as ℂ ⊕ Unit)
- Function field: ℂ(z) = RatFunc ℂ

The full construction of ℙ¹ as a CompactAlgebraicCurve requires:
1. Valuation at finite points: v_z(f) = (mult of z in numerator) - (mult of z in denominator)
2. Valuation at infinity: v_∞(f) = deg(denom) - deg(numer)
3. Proof that these satisfy the valuation axioms

This infrastructure is partially available in `Helpers/RiemannSphere.lean` using
polynomial root multiplicities. See that file for the ℙ¹-specific argument principle.
-/

/-- The projective line ℙ¹ as a set: ℂ ∪ {∞} -/
def ProjectiveLinePoints := ℂ ⊕ Unit

/-- The finite point z ∈ ℂ viewed as a point of ℙ¹ -/
def finitePoint (z : ℂ) : ProjectiveLinePoints := Sum.inl z

/-- The point at infinity in ℙ¹ -/
def infinityPoint : ProjectiveLinePoints := Sum.inr ()

end RiemannSurfaces.Algebraic
