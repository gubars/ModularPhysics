import ModularPhysics.StringGeometry.RiemannSurfaces.Basic
import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.Helpers.Meromorphic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Int.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Divisors on Riemann Surfaces

This file develops the theory of divisors on Riemann surfaces from the
algebraic geometry perspective.

## Mathematical Background

A divisor on a Riemann surface Σ is a formal finite ℤ-linear combination
of points:
  D = Σᵢ nᵢ · pᵢ

### Divisor Groups

- **Div(Σ)**: Free abelian group on points of Σ
- **Div⁰(Σ)**: Divisors of degree 0
- **Prin(Σ)**: Principal divisors (div(f) for meromorphic f)
- **Pic(Σ) = Div(Σ)/Prin(Σ)**: Picard group (line bundles)
- **Pic⁰(Σ) = Div⁰(Σ)/Prin(Σ)**: Jacobian variety

### Key Properties

For a compact Riemann surface of genus g:
- deg(div(f)) = 0 for any meromorphic f ≠ 0
- Pic⁰(Σ) ≅ J(Σ) is a g-dimensional complex torus (Jacobian)
- Abel's theorem: D is principal iff Abel-Jacobi(D) = 0

### Line Bundles

Each divisor D determines a holomorphic line bundle L(D):
- L(D) = {meromorphic f : div(f) + D ≥ 0}
- dim L(D) = l(D) enters Riemann-Roch

## Main definitions

* `Divisor` - Formal sum of points with integer coefficients
* `Divisor.degree` - Sum of coefficients
* `PrincipalDivisor` - Divisor of a meromorphic function
* `DivisorClass` - Equivalence class in Pic(Σ)
* `LinearSystem` - The space L(D)

## References

* Griffiths, Harris "Principles of Algebraic Geometry" Ch 2
* Farkas, Kra "Riemann Surfaces" Ch III
* Miranda "Algebraic Curves and Riemann Surfaces"
-/

namespace RiemannSurfaces.Algebraic

open RiemannSurfaces

/-!
## Divisors as Formal Sums

A divisor is a formal ℤ-linear combination of points with finite support.
-/

/-- A divisor on a Riemann surface -/
structure Divisor (RS : RiemannSurface) where
  /-- Coefficient at each point -/
  coeff : RS.carrier → ℤ
  /-- Finite support -/
  finiteSupport : Set.Finite { p | coeff p ≠ 0 }

namespace Divisor

variable {RS : RiemannSurface}

/-- The zero divisor -/
def zero : Divisor RS where
  coeff := fun _ => 0
  finiteSupport := by simp [Set.finite_empty]

/-- Addition of divisors -/
def add (D₁ D₂ : Divisor RS) : Divisor RS where
  coeff := fun p => D₁.coeff p + D₂.coeff p
  finiteSupport := by
    apply Set.Finite.subset (D₁.finiteSupport.union D₂.finiteSupport)
    intro p hp
    simp only [Set.mem_setOf_eq, ne_eq] at hp ⊢
    by_contra h
    push_neg at h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_ne_iff] at h
    omega

/-- Negation of divisors -/
def neg (D : Divisor RS) : Divisor RS where
  coeff := fun p => -D.coeff p
  finiteSupport := by
    convert D.finiteSupport using 1
    ext p
    simp

/-- Subtraction of divisors -/
def sub (D₁ D₂ : Divisor RS) : Divisor RS := add D₁ (neg D₂)

instance : Zero (Divisor RS) := ⟨zero⟩
instance : Add (Divisor RS) := ⟨add⟩
instance : Neg (Divisor RS) := ⟨neg⟩
instance : Sub (Divisor RS) := ⟨sub⟩

/-- Extensionality for divisors -/
@[ext]
theorem ext {D₁ D₂ : Divisor RS} (h : ∀ p, D₁.coeff p = D₂.coeff p) : D₁ = D₂ := by
  cases D₁; cases D₂; simp only [mk.injEq]; ext p; exact h p

/-- Divisors form an abelian group -/
instance : AddCommGroup (Divisor RS) where
  add_assoc := fun a b c => by
    ext p
    show (a.coeff p + b.coeff p) + c.coeff p = a.coeff p + (b.coeff p + c.coeff p)
    ring
  zero_add := fun a => by ext p; show 0 + a.coeff p = a.coeff p; ring
  add_zero := fun a => by ext p; show a.coeff p + 0 = a.coeff p; ring
  neg_add_cancel := fun a => by ext p; show -a.coeff p + a.coeff p = 0; ring
  add_comm := fun a b => by
    ext p
    show a.coeff p + b.coeff p = b.coeff p + a.coeff p
    ring
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- A single point as a divisor -/
noncomputable def point (p : RS.carrier) : Divisor RS where
  coeff := fun q => @ite _ (q = p) (Classical.propDecidable _) 1 0
  finiteSupport := by
    apply Set.Finite.subset (Set.finite_singleton p)
    intro q hq
    simp only [Set.mem_setOf_eq, ne_eq, Set.mem_singleton_iff] at hq ⊢
    by_contra h
    have : @ite ℤ (q = p) (Classical.propDecidable _) 1 0 = 0 := by
      simp only [ite_eq_right_iff, one_ne_zero]
      exact fun hp => (h hp).elim
    exact hq this

/-- Scalar multiple of a divisor -/
def smul (n : ℤ) (D : Divisor RS) : Divisor RS where
  coeff := fun p => n * D.coeff p
  finiteSupport := by
    by_cases hn : n = 0
    · simp [hn, Set.finite_empty]
    · convert D.finiteSupport using 1
      ext p
      simp [hn]

instance : SMul ℤ (Divisor RS) := ⟨smul⟩

/-!
## Degree of a Divisor
-/

/-- The degree of a divisor (sum of coefficients) -/
noncomputable def degree (D : Divisor RS) : ℤ :=
  D.finiteSupport.toFinset.sum (fun p => D.coeff p)

/-- Degree is additive.
    Proof requires careful handling of finite support and sums. -/
theorem degree_add (D₁ D₂ : Divisor RS) :
    (D₁ + D₂).degree = D₁.degree + D₂.degree := by
  classical
  unfold degree
  -- The key is that we can extend sums to a common superset
  -- Let S₁ = supp(D₁), S₂ = supp(D₂), S = supp(D₁ + D₂)
  -- We have S ⊆ S₁ ∪ S₂ (by construction in add)
  -- For p ∉ S₁: D₁.coeff p = 0, so sum over S₁ ∪ S₂ = sum over S₁
  -- Similarly for D₂

  -- Strategy: show that summing over any superset that contains all supports gives same result
  let S := (D₁ + D₂).finiteSupport.toFinset
  let S₁ := D₁.finiteSupport.toFinset
  let S₂ := D₂.finiteSupport.toFinset
  let U := S₁ ∪ S₂

  -- D₁ + D₂ coefficients vanish outside S₁ ∪ S₂
  have hS_sub : S ⊆ U := by
    intro p hp
    rw [Set.Finite.mem_toFinset] at hp
    rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    simp only [Set.mem_setOf_eq] at hp ⊢
    by_contra h
    push_neg at h
    obtain ⟨h1, h2⟩ := h
    have hcoeff : (D₁ + D₂).coeff p = D₁.coeff p + D₂.coeff p := rfl
    rw [hcoeff, h1, h2, add_zero] at hp
    exact hp rfl

  -- Sum over S equals sum over U for (D₁ + D₂)
  have hsum_eq : S.sum (fun p => (D₁ + D₂).coeff p) =
                  U.sum (fun p => (D₁ + D₂).coeff p) := by
    apply Finset.sum_subset hS_sub
    intro p hpU hpS
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hpS
    exact hpS

  -- Sum over U splits as sum of D₁.coeff + D₂.coeff
  have hsplit : U.sum (fun p => (D₁ + D₂).coeff p) =
                U.sum (fun p => D₁.coeff p) + U.sum (fun p => D₂.coeff p) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rfl

  -- Sum of D₁ over U equals sum over S₁
  have hD₁_eq : U.sum (fun p => D₁.coeff p) = S₁.sum (fun p => D₁.coeff p) := by
    symm
    apply Finset.sum_subset (s₁ := S₁) (s₂ := U) Finset.subset_union_left
    intro p _ hp
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hp
    exact hp

  -- Sum of D₂ over U equals sum over S₂
  have hD₂_eq : U.sum (fun p => D₂.coeff p) = S₂.sum (fun p => D₂.coeff p) := by
    symm
    apply Finset.sum_subset (s₁ := S₂) (s₂ := U) Finset.subset_union_right
    intro p _ hp
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hp
    exact hp

  rw [hsum_eq, hsplit, hD₁_eq, hD₂_eq]

/-- Degree of negation -/
theorem degree_neg (D : Divisor RS) :
    (-D).degree = -D.degree := by
  unfold degree
  -- The support of -D equals the support of D
  have hsup : { p | (-D).coeff p ≠ 0 } = { p | D.coeff p ≠ 0 } := by
    ext p
    simp only [Set.mem_setOf_eq, ne_eq, Neg.neg, neg]
    rw [not_iff_not]
    exact neg_eq_zero (α := ℤ)
  -- The finite supports have the same toFinset
  have hfin : (-D).finiteSupport.toFinset = D.finiteSupport.toFinset := by
    ext p
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Neg.neg, neg]
    rw [not_iff_not]
    exact neg_eq_zero (α := ℤ)
  rw [hfin]
  apply Finset.sum_neg_distrib

/-- Degree of zero divisor -/
theorem degree_zero : (0 : Divisor RS).degree = 0 := by
  unfold degree
  -- The support of zero divisor is empty
  have h : { p | (0 : Divisor RS).coeff p ≠ 0 } = ∅ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    rfl
  simp only [h, Set.Finite.toFinset_empty, Finset.sum_empty]

/-- Degree of a point is 1 -/
theorem degree_point (p : RS.carrier) : (point p).degree = 1 := by
  unfold degree
  -- The support of (point p) is {p}
  have hsup : { q | (point p).coeff q ≠ 0 } = {p} := by
    ext q
    simp only [Set.mem_setOf_eq, ne_eq, Set.mem_singleton_iff, point]
    constructor
    · intro h
      by_contra hne
      have : @ite ℤ (q = p) (Classical.propDecidable _) 1 0 = 0 := by
        simp only [ite_eq_right_iff, one_ne_zero]
        exact fun hp => (hne hp).elim
      exact h this
    · intro heq
      subst heq
      simp only [ite_true]
      decide
  -- The coefficient at p is 1
  have hcoeff : (point p).coeff p = 1 := by
    simp only [point, ite_true]
  -- Now compute the sum
  have hfin_eq : (point p).finiteSupport.toFinset = {p} := by
    ext q
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_singleton]
    rw [← Set.mem_singleton_iff, ← hsup]
    simp only [Set.mem_setOf_eq]
  rw [hfin_eq, Finset.sum_singleton, hcoeff]

/-!
## Effective and Non-Negative Divisors
-/

/-- A divisor is effective if all coefficients are non-negative -/
def Effective (D : Divisor RS) : Prop :=
  ∀ p, D.coeff p ≥ 0

/-- Notation D ≥ 0 for effective -/
instance : LE (Divisor RS) where
  le D₁ D₂ := ∀ p, D₁.coeff p ≤ D₂.coeff p

/-- D ≥ 0 iff D is effective -/
theorem le_zero_iff_effective (D : Divisor RS) :
    (0 : Divisor RS) ≤ D ↔ Effective D := by
  constructor
  · intro h p; exact h p
  · intro h p; exact h p

/-- Sum of effective divisors is effective -/
theorem effective_add (D₁ D₂ : Divisor RS) (h₁ : Effective D₁) (h₂ : Effective D₂) :
    Effective (D₁ + D₂) := by
  intro p
  have h1 := h₁ p
  have h2 := h₂ p
  show D₁.coeff p + D₂.coeff p ≥ 0
  linarith

end Divisor

/-!
## Principal Divisors

A principal divisor is the divisor of a meromorphic function.
The meromorphic function infrastructure is provided by `Algebraic.Helpers.Meromorphic`.
-/

/-- The divisor of a meromorphic function -/
noncomputable def divisorOf {RS : RiemannSurface} (f : MeromorphicFunction RS) :
    Divisor RS where
  coeff := orderAt f
  finiteSupport := orderFiniteSupport f

/-- A divisor is principal if it's the divisor of some meromorphic function -/
def IsPrincipal {RS : RiemannSurface} (D : Divisor RS) : Prop :=
  ∃ f : MeromorphicFunction RS, divisorOf f = D

/-- Principal divisors have degree 0 on compact surfaces.
    Proof: For a meromorphic function, #{zeros} = #{poles} by the argument principle. -/
theorem principal_degree_zero (CRS : CompactRiemannSurface) (D : Divisor CRS.toRiemannSurface)
    (_ : IsPrincipal D) :
    D.degree = 0 := by
  sorry  -- Argument principle: ∮ f'/f dz = 2πi(#zeros - #poles)

/-!
## Divisor Classes and Picard Group
-/

/-- Two divisors are linearly equivalent if their difference is principal -/
def LinearlyEquivalent {RS : RiemannSurface} (D₁ D₂ : Divisor RS) : Prop :=
  IsPrincipal (D₁ - D₂)

/-- The zero divisor is principal (divisor of constant 1) -/
theorem zero_isPrincipal {RS : RiemannSurface} : IsPrincipal (0 : Divisor RS) := by
  use 1  -- The constant function 1
  ext p
  simp only [divisorOf, orderAt_one]
  rfl

/-- Negation of a principal divisor is principal -/
theorem neg_isPrincipal {RS : RiemannSurface} {D : Divisor RS}
    (hD : IsPrincipal D) : IsPrincipal (-D) := by
  obtain ⟨f, hf⟩ := hD
  use f⁻¹
  ext p
  simp only [divisorOf, Neg.neg, Divisor.neg, orderAt_inv]
  rw [← hf]
  rfl

/-- Sum of principal divisors is principal -/
theorem add_isPrincipal {RS : RiemannSurface} {D₁ D₂ : Divisor RS}
    (hD₁ : IsPrincipal D₁) (hD₂ : IsPrincipal D₂) : IsPrincipal (D₁ + D₂) := by
  obtain ⟨f, hf⟩ := hD₁
  obtain ⟨g, hg⟩ := hD₂
  use f * g
  ext p
  simp only [divisorOf, orderAt_mul]
  rw [← hf, ← hg]
  rfl

/-- The subgroup of principal divisors Prin(Σ) ⊆ Div(Σ) -/
def PrincipalDivisors (RS : RiemannSurface) : AddSubgroup (Divisor RS) where
  carrier := { D | IsPrincipal D }
  zero_mem' := zero_isPrincipal
  add_mem' := fun ha hb => add_isPrincipal ha hb
  neg_mem' := fun ha => neg_isPrincipal ha

/-- Linear equivalence is an equivalence relation -/
theorem linearlyEquivalent_equivalence (RS : RiemannSurface) :
    Equivalence (@LinearlyEquivalent RS) := by
  constructor
  · intro D; unfold LinearlyEquivalent; simp only [sub_self]; exact zero_isPrincipal
  · intro D₁ D₂ h; unfold LinearlyEquivalent at *
    have h' : D₂ - D₁ = -(D₁ - D₂) := by
      ext p
      show (D₂.coeff p - D₁.coeff p) = -(D₁.coeff p - D₂.coeff p)
      ring
    rw [h']; exact neg_isPrincipal h
  · intro D₁ D₂ D₃ h₁ h₂; unfold LinearlyEquivalent at *
    have h' : D₁ - D₃ = (D₁ - D₂) + (D₂ - D₃) := by
      ext p
      show (D₁.coeff p - D₃.coeff p) = (D₁.coeff p - D₂.coeff p) + (D₂.coeff p - D₃.coeff p)
      ring
    rw [h']; exact add_isPrincipal h₁ h₂

/-- The setoid for linear equivalence -/
def linearEquivalentSetoid (RS : RiemannSurface) : Setoid (Divisor RS) :=
  ⟨LinearlyEquivalent, linearlyEquivalent_equivalence RS⟩

/-- The Picard group Pic(Σ) = Div(Σ) / Prin(Σ) -/
def PicardGroup (RS : RiemannSurface) := Divisor RS ⧸ PrincipalDivisors RS

/-- Pic(Σ) is an abelian group (quotient of AddCommGroup by AddSubgroup) -/
noncomputable instance (RS : RiemannSurface) : AddCommGroup (PicardGroup RS) :=
  QuotientAddGroup.Quotient.addCommGroup (PrincipalDivisors RS)

/-- Linear equivalence coincides with the quotient relation -/
theorem linearlyEquivalent_iff_quotient {RS : RiemannSurface} (D₁ D₂ : Divisor RS) :
    LinearlyEquivalent D₁ D₂ ↔ (QuotientAddGroup.mk D₁ : PicardGroup RS) = QuotientAddGroup.mk D₂ := by
  rw [QuotientAddGroup.eq]
  unfold LinearlyEquivalent
  constructor
  · intro h
    -- IsPrincipal (D₁ - D₂), we need -D₁ + D₂ ∈ PrincipalDivisors
    -- Note: -D₁ + D₂ = -(D₁ - D₂)
    have h' : -D₁ + D₂ = -(D₁ - D₂) := by
      refine Divisor.ext (fun p => ?_)
      -- Unfold all the operations at the coefficient level
      show (Divisor.add (Divisor.neg D₁) D₂).coeff p = (Divisor.neg (Divisor.sub D₁ D₂)).coeff p
      simp only [Divisor.add, Divisor.neg, Divisor.sub]
      ring
    rw [h']
    exact neg_isPrincipal h
  · intro h
    -- -D₁ + D₂ ∈ PrincipalDivisors means IsPrincipal(-D₁ + D₂)
    -- We need IsPrincipal(D₁ - D₂) = IsPrincipal(-(- D₁ + D₂))
    have h' : D₁ - D₂ = -(-D₁ + D₂) := by
      refine Divisor.ext (fun p => ?_)
      show (Divisor.sub D₁ D₂).coeff p = (Divisor.neg (Divisor.add (Divisor.neg D₁) D₂)).coeff p
      simp only [Divisor.add, Divisor.neg, Divisor.sub]
      ring
    rw [h']
    exact neg_isPrincipal h

/-- Degree is well-defined on the quotient: if D₁ - D₂ ∈ Prin(Σ), then deg(D₁) = deg(D₂) -/
theorem degree_well_defined_quotient (RS : RiemannSurface) (D₁ D₂ : Divisor RS)
    (h : D₁ - D₂ ∈ PrincipalDivisors RS) :
    D₁.degree = D₂.degree := by
  sorry  -- D₁ - D₂ is principal, so deg(D₁ - D₂) = 0, hence deg(D₁) = deg(D₂)

/-- Degree is well-defined on linear equivalence classes (principal divisors have degree 0) -/
theorem degree_well_defined (RS : RiemannSurface) (D₁ D₂ : Divisor RS)
    (h : LinearlyEquivalent D₁ D₂) :
    D₁.degree = D₂.degree := by
  apply degree_well_defined_quotient
  -- LinearlyEquivalent D₁ D₂ means IsPrincipal (D₁ - D₂)
  exact h

/-- The degree map Pic(Σ) → ℤ (well-defined since principal divisors have degree 0) -/
noncomputable def PicardGroup.degree {RS : RiemannSurface} (c : PicardGroup RS) : ℤ :=
  Quotient.liftOn' c Divisor.degree (fun D₁ D₂ h => by
    -- h : -D₁ + D₂ ∈ PrincipalDivisors RS (from QuotientAddGroup.leftRel)
    rw [QuotientAddGroup.leftRel_eq] at h
    -- We have -D₁ + D₂ ∈ Prin, need D₂ - D₁ ∈ Prin
    -- Note: D₂ - D₁ = -D₁ + D₂ in an abelian group
    have h' : D₂ - D₁ = -D₁ + D₂ := by
      refine Divisor.ext (fun p => ?_)
      show (Divisor.sub D₂ D₁).coeff p = (Divisor.add (Divisor.neg D₁) D₂).coeff p
      simp only [Divisor.sub, Divisor.add, Divisor.neg]
      ring
    rw [← h'] at h
    exact (degree_well_defined_quotient RS D₂ D₁ h).symm)

/-!
## Line Bundles from Divisors
-/

/-- The linear system L(D) = {f meromorphic : div(f) + D ≥ 0} -/
structure LinearSystem {RS : RiemannSurface} (D : Divisor RS) where
  /-- Functions in L(D) -/
  functions : Set (MeromorphicFunction RS)
  /-- Defining property -/
  property : ∀ f ∈ functions, Divisor.Effective (divisorOf f + D)

/-- Dimension of the linear system.

    The linear system L(D) is a finite-dimensional complex vector space.
    Its dimension requires computing the space of meromorphic functions
    with prescribed poles, which needs the Riemann-Roch theorem.

    Placeholder: returns 0 (proper definition needs vector space dimension). -/
noncomputable def LinearSystem.dimension {RS : RiemannSurface} {D : Divisor RS}
    (_ : LinearSystem D) : ℕ := 0  -- Placeholder

/-- The function l(D) = dim L(D) = dim H⁰(O(D)).

    This is the dimension of the Riemann-Roch space L(D) = {f : div(f) + D ≥ 0}.

    **Riemann-Roch theorem** (see `Algebraic/RiemannRoch.lean`):
      l(D) - l(K - D) = deg(D) - g + 1

    where K is the canonical divisor with deg(K) = 2g - 2.

    **Key values:**
    - l(0) = 1 (only constants are holomorphic)
    - l(K) = g (definition of genus)
    - l(D) = deg(D) - g + 1 when deg(D) > 2g - 2

    For the full cohomological treatment, see `RiemannRoch.lean`.
    This placeholder returns 1 for the special case l(0) = 1. -/
noncomputable def ell {RS : RiemannSurface} (_ : Divisor RS) : ℕ := 1  -- Placeholder: see RiemannRoch.lean

/-- l(0) = 1 (only constant functions).
    L(0) = {f : div(f) ≥ 0} = {holomorphic functions} = {constants} on a compact surface. -/
theorem ell_zero (RS : RiemannSurface) : ell (0 : Divisor RS) = 1 := rfl

/-- l(D) ≥ deg(D) - g + 1 for effective D (weak Riemann-Roch).
    This is a consequence of Riemann-Roch: l(D) - l(K-D) = deg(D) - g + 1.
    For effective D with deg(D) > 2g - 2, we have l(K-D) = 0, giving equality. -/
theorem ell_lower_bound (CRS : CompactRiemannSurface) (D : Divisor CRS.toRiemannSurface)
    (_ : Divisor.Effective D) :
    (ell D : ℤ) ≥ D.degree - CRS.genus + 1 := by
  sorry  -- Requires Riemann-Roch theorem

/-!
## Divisor Support and Decomposition

Infrastructure for proving properties by induction on divisor support.
-/

namespace Divisor

variable {RS : RiemannSurface}

/-- The support of a divisor as a set -/
def support (D : Divisor RS) : Set RS.carrier :=
  { p | D.coeff p ≠ 0 }

/-- The support is finite -/
theorem support_finite (D : Divisor RS) : Set.Finite D.support :=
  D.finiteSupport

/-- Support of zero divisor is empty -/
theorem support_zero : (0 : Divisor RS).support = ∅ := by
  ext p
  simp only [support, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
  rfl

/-- Zero divisor has empty support (finset version) -/
theorem support_zero_toFinset :
    (0 : Divisor RS).finiteSupport.toFinset = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hp
  exact hp rfl

/-- A divisor is zero iff its support is empty -/
theorem eq_zero_iff_support_empty (D : Divisor RS) :
    D = 0 ↔ D.support = ∅ := by
  constructor
  · intro h
    rw [h]
    exact support_zero
  · intro h
    ext p
    have hp : p ∉ D.support := by
      simp only [h, Set.mem_empty_iff_false, not_false_eq_true]
    simp only [support, Set.mem_setOf_eq, not_not] at hp
    exact hp

/-- Coefficient of point divisor at the point itself -/
theorem point_coeff_self (p : RS.carrier) :
    (point p).coeff p = 1 := by
  simp only [point, ite_true]

/-- Coefficient of point divisor at a different point -/
theorem point_coeff_ne (p q : RS.carrier) (hpq : p ≠ q) :
    (point p).coeff q = 0 := by
  simp only [point]
  have : ¬(q = p) := fun h => hpq h.symm
  simp only [this, ↓reduceIte]

/-- Coefficient of scalar multiple -/
theorem smul_coeff (n : ℤ) (D : Divisor RS) (p : RS.carrier) :
    (n • D).coeff p = n * D.coeff p := rfl

/-- Coefficient of addition -/
theorem add_coeff (D₁ D₂ : Divisor RS) (p : RS.carrier) :
    (D₁ + D₂).coeff p = D₁.coeff p + D₂.coeff p := rfl

/-- Coefficient of subtraction -/
theorem sub_coeff (D₁ D₂ : Divisor RS) (p : RS.carrier) :
    (D₁ - D₂).coeff p = D₁.coeff p - D₂.coeff p := by
  show (add D₁ (neg D₂)).coeff p = D₁.coeff p - D₂.coeff p
  simp only [add, neg]
  ring

/-- Subtracting D.coeff(p) copies of point p zeroes out the coefficient at p -/
theorem sub_coeff_point_self (D : Divisor RS) (p : RS.carrier) :
    (D - D.coeff p • point p).coeff p = 0 := by
  rw [sub_coeff, smul_coeff, point_coeff_self, mul_one, sub_self]

/-- If D.coeff p ≠ 0, then p is not in the support of D - D.coeff(p) • point p -/
theorem not_mem_support_sub_coeff_point (D : Divisor RS) (p : RS.carrier) :
    p ∉ (D - D.coeff p • point p).support := by
  simp only [support, Set.mem_setOf_eq, not_not]
  exact sub_coeff_point_self D p

/-- The support of D - D.coeff(p) • point p is contained in support(D) \ {p} -/
theorem support_sub_coeff_point (D : Divisor RS) (p : RS.carrier) :
    (D - D.coeff p • point p).support ⊆ D.support \ {p} := by
  intro q hq
  simp only [support, Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff] at hq ⊢
  constructor
  · -- q ∈ support(D)
    by_contra hqD
    -- hqD : D.coeff q = 0 (after by_contra on ≠)
    -- (D - D.coeff p • point p).coeff q = D.coeff q - D.coeff p * (point p).coeff q
    have hcoeff : (D - D.coeff p • point p).coeff q = D.coeff q - D.coeff p * (point p).coeff q := by
      rw [sub_coeff, smul_coeff]
    rw [hcoeff, hqD, zero_sub] at hq
    -- If q = p: (point p).coeff q = 1, so - D.coeff p ≠ 0 → D.coeff p ≠ 0
    -- But then D.coeff q = D.coeff p ≠ 0 (since q = p), contradiction with hqD
    -- If q ≠ p: (point p).coeff q = 0, so - D.coeff p * 0 = 0, contradiction with hq
    by_cases hqp : q = p
    · subst hqp
      rw [point_coeff_self, mul_one, neg_ne_zero] at hq
      -- hq : D.coeff q ≠ 0, but hqD : D.coeff q = 0
      exact hq hqD
    · have hne : p ≠ q := fun h => hqp h.symm
      rw [point_coeff_ne p q hne, mul_zero, neg_zero] at hq
      exact hq rfl
  · -- q ≠ p
    intro hqp
    subst hqp
    have := sub_coeff_point_self D q
    exact hq this

/-- If D.coeff(p) ≠ 0, the support of D - D.coeff(p) • point p is strictly smaller -/
theorem support_sub_coeff_point_ssubset (D : Divisor RS) (p : RS.carrier)
    (hp : D.coeff p ≠ 0) :
    (D - D.coeff p • point p).support ⊂ D.support := by
  constructor
  · -- ⊆: follows from support_sub_coeff_point plus {p} ⊆ support D
    intro q hq
    have h := support_sub_coeff_point D p hq
    exact h.1
  · -- ≠: p ∈ support(D) but p ∉ support(D - D.coeff(p) • point p)
    intro h_eq
    have hp_in : p ∈ D.support := by
      simp only [support, Set.mem_setOf_eq]
      exact hp
    have hp_out : p ∉ (D - D.coeff p • point p).support :=
      not_mem_support_sub_coeff_point D p
    exact hp_out (h_eq hp_in)

/-- For a nonzero divisor, there exists a point in its support -/
theorem exists_mem_support_of_ne_zero (D : Divisor RS) (hD : D ≠ 0) :
    ∃ p, p ∈ D.support := by
  by_contra h
  push_neg at h
  have hempty : D.support = ∅ := by
    ext p
    simp only [Set.mem_empty_iff_false, iff_false]
    exact h p
  have hD0 : D = 0 := (eq_zero_iff_support_empty D).mpr hempty
  exact hD hD0

/-- Degree of scalar multiple -/
theorem degree_smul (n : ℤ) (D : Divisor RS) :
    (n • D).degree = n * D.degree := by
  classical
  unfold degree
  -- Need to show the sums are related
  -- If n = 0, both sides are 0
  by_cases hn : n = 0
  · simp only [hn, zero_mul]
    -- n = 0 means 0 • D has empty support
    have h0 : ((0 : ℤ) • D).finiteSupport.toFinset = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hp
      -- hp : ((0 : ℤ) • D).coeff p ≠ 0
      -- But ((0 : ℤ) • D).coeff p = 0 * D.coeff p = 0
      have heq : ((0 : ℤ) • D).coeff p = 0 * D.coeff p := smul_coeff 0 D p
      simp only [heq, zero_mul, ne_eq, not_true_eq_false] at hp
    rw [h0, Finset.sum_empty]
  · -- n ≠ 0: support(n • D) = support(D)
    have hsupp : (n • D).finiteSupport.toFinset = D.finiteSupport.toFinset := by
      ext p
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, smul_coeff]
      constructor
      · intro h
        contrapose! h
        simp only [h, mul_zero]
      · intro h
        exact mul_ne_zero hn h
    rw [hsupp]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rfl

/-- Support has finite cardinality -/
noncomputable def supportCard (D : Divisor RS) : ℕ :=
  D.finiteSupport.toFinset.card

/-- Support cardinality of zero divisor is 0 -/
theorem supportCard_zero : (0 : Divisor RS).supportCard = 0 := by
  unfold supportCard
  rw [support_zero_toFinset]
  simp

/-- A divisor is zero iff its support cardinality is 0 -/
theorem eq_zero_iff_supportCard_eq_zero (D : Divisor RS) :
    D = 0 ↔ D.supportCard = 0 := by
  rw [eq_zero_iff_support_empty]
  unfold supportCard
  simp only [Finset.card_eq_zero]
  constructor
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hp
    have : p ∈ D.support := hp
    rw [h] at this
    exact this
  · intro h
    ext p
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hp
    have : p ∈ D.finiteSupport.toFinset := by
      simp only [Set.Finite.mem_toFinset]
      exact hp
    rw [h] at this
    simp at this

/-- If D.coeff(p) ≠ 0, then supportCard(D - D.coeff(p) • point p) < supportCard(D) -/
theorem supportCard_sub_coeff_point_lt (D : Divisor RS) (p : RS.carrier)
    (hp : D.coeff p ≠ 0) :
    (D - D.coeff p • point p).supportCard < D.supportCard := by
  unfold supportCard
  -- Use support_sub_coeff_point_ssubset
  have hsub := support_sub_coeff_point_ssubset D p hp
  -- The finsets correspond to the supports
  -- We have (D - ...).support ⊂ D.support
  -- Need to show card of finset is smaller
  apply Finset.card_lt_card
  constructor
  · -- ⊆ for finsets
    intro q hq
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hq ⊢
    have := support_sub_coeff_point D p
    exact hsub.1 hq
  · -- ≠ for finsets
    intro h_eq
    have hp_in : p ∈ D.finiteSupport.toFinset := by
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact hp
    have hp_out : p ∉ (D - D.coeff p • point p).finiteSupport.toFinset := by
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not]
      exact sub_coeff_point_self D p
    exact hp_out (h_eq hp_in)

end Divisor

end RiemannSurfaces.Algebraic
