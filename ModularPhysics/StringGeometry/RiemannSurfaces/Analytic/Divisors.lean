import ModularPhysics.StringGeometry.RiemannSurfaces.Analytic.Basic
import ModularPhysics.StringGeometry.RiemannSurfaces.Analytic.MeromorphicFunction
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Int.Basic

/-!
# Divisors on Riemann Surfaces (Analytic Approach)

This file develops the theory of divisors on Riemann surfaces from the
**analytic** perspective.

## Mathematical Background

A divisor on a Riemann surface Σ is a formal finite ℤ-linear combination
of points:
  D = Σᵢ nᵢ · pᵢ

### Divisor Groups

- **Div(Σ)**: Free abelian group on points of Σ
- **Div⁰(Σ)**: Divisors of degree 0
- **Prin(Σ)**: Principal divisors (div(f) for meromorphic f)
- **Pic(Σ) = Div(Σ)/Prin(Σ)**: Picard group (holomorphic line bundles)
- **Pic⁰(Σ) = Div⁰(Σ)/Prin(Σ)**: Jacobian variety

### Analytic Definitions

In the analytic approach:
- Meromorphic functions are holomorphic maps f : Σ → ℂP¹
- The order at p comes from the Laurent series expansion
- The divisor div(f) = Σ_p ord_p(f) · [p]

### Key Theorems

For a compact Riemann surface of genus g:
- deg(div(f)) = 0 for any nonzero meromorphic f (argument principle)
- dim Pic⁰(Σ) = g (Jacobian is g-dimensional)

## References

* Farkas, Kra "Riemann Surfaces" Ch III
* Griffiths, Harris "Principles of Algebraic Geometry" Ch 2
-/

namespace RiemannSurfaces.Analytic

/-!
## Divisors on Riemann Surfaces

A divisor is a formal sum of points with integer coefficients.
-/

/-- A divisor on a Riemann surface is a finite formal sum of points with integer coefficients.

    D = n₁·p₁ + n₂·p₂ + ... + nₖ·pₖ

    where nᵢ ∈ ℤ and only finitely many nᵢ are nonzero. -/
structure Divisor (RS : RiemannSurface) where
  /-- The coefficient at each point -/
  coeff : RS.carrier → ℤ
  /-- Only finitely many points have nonzero coefficient -/
  finiteSupport : Set.Finite { p | coeff p ≠ 0 }

namespace Divisor

variable {RS : RiemannSurface}

/-- Extensionality for divisors -/
@[ext]
theorem ext {D₁ D₂ : Divisor RS} (h : ∀ p, D₁.coeff p = D₂.coeff p) : D₁ = D₂ := by
  cases D₁; cases D₂; simp only [mk.injEq]; ext p; exact h p

/-- The support of a divisor: points with nonzero coefficient -/
def support (D : Divisor RS) : Set RS.carrier :=
  { p | D.coeff p ≠ 0 }

/-- The degree of a divisor: deg(D) = Σ_p D(p) -/
noncomputable def degree (D : Divisor RS) : ℤ :=
  D.finiteSupport.toFinset.sum D.coeff

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
    simp only [Set.mem_setOf_eq, ne_eq] at hp
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_contra hcon
    push_neg at hcon
    have h1 : D₁.coeff p = 0 := hcon.1
    have h2 : D₂.coeff p = 0 := hcon.2
    rw [h1, h2, add_zero] at hp
    exact hp rfl

/-- Negation of a divisor -/
def neg (D : Divisor RS) : Divisor RS where
  coeff := fun p => -D.coeff p
  finiteSupport := by
    convert D.finiteSupport using 1
    ext p
    simp only [Set.mem_setOf_eq, neg_ne_zero]

/-- The point divisor [p] -/
noncomputable def point (p : RS.carrier) : Divisor RS where
  coeff := fun q => @ite _ (q = p) (Classical.propDecidable _) 1 0
  finiteSupport := by
    apply Set.Finite.subset (Set.finite_singleton p)
    intro q hq
    simp only [Set.mem_setOf_eq, ne_eq] at hq
    simp only [Set.mem_singleton_iff]
    by_contra h
    have : @ite ℤ (q = p) (Classical.propDecidable _) 1 0 = 0 := by
      simp only [ite_eq_right_iff, one_ne_zero]
      exact fun hp => (h hp).elim
    exact hq this

instance : Zero (Divisor RS) := ⟨zero⟩
instance : Add (Divisor RS) := ⟨add⟩
instance : Neg (Divisor RS) := ⟨neg⟩

/-- Subtraction of divisors -/
instance : Sub (Divisor RS) := ⟨fun D₁ D₂ => D₁ + (-D₂)⟩

/-- Divisors form an additive commutative group -/
instance : AddCommGroup (Divisor RS) where
  add_assoc := fun D₁ D₂ D₃ => by
    ext p
    show (D₁.coeff p + D₂.coeff p) + D₃.coeff p = D₁.coeff p + (D₂.coeff p + D₃.coeff p)
    ring
  zero_add := fun D => by
    ext p; show 0 + D.coeff p = D.coeff p; ring
  add_zero := fun D => by
    ext p; show D.coeff p + 0 = D.coeff p; ring
  neg_add_cancel := fun D => by
    ext p; show -D.coeff p + D.coeff p = 0; ring
  add_comm := fun D₁ D₂ => by
    ext p
    show D₁.coeff p + D₂.coeff p = D₂.coeff p + D₁.coeff p
    ring
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Degree is additive -/
theorem degree_add (D₁ D₂ : Divisor RS) :
    (D₁ + D₂).degree = D₁.degree + D₂.degree := by
  classical
  unfold degree
  -- Let S = supp(D₁ + D₂), S₁ = supp(D₁), S₂ = supp(D₂), U = S₁ ∪ S₂
  let S := (D₁ + D₂).finiteSupport.toFinset
  let S₁ := D₁.finiteSupport.toFinset
  let S₂ := D₂.finiteSupport.toFinset
  let U := S₁ ∪ S₂

  -- S ⊆ U
  have hS_sub : S ⊆ U := by
    intro p hp
    rw [Set.Finite.mem_toFinset] at hp
    rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    simp only [Set.mem_setOf_eq] at hp ⊢
    by_contra h
    push_neg at h
    have hcoeff : (D₁ + D₂).coeff p = D₁.coeff p + D₂.coeff p := rfl
    rw [hcoeff, h.1, h.2, add_zero] at hp
    exact hp rfl

  -- Sum over S = Sum over U for D₁ + D₂
  have hsum_eq : S.sum (fun p => (D₁ + D₂).coeff p) =
                  U.sum (fun p => (D₁ + D₂).coeff p) := by
    apply Finset.sum_subset hS_sub
    intro p _ hpS
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hpS
    exact hpS

  -- Sum over U splits
  have hsplit : U.sum (fun p => (D₁ + D₂).coeff p) =
                U.sum (fun p => D₁.coeff p) + U.sum (fun p => D₂.coeff p) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _; rfl

  -- Sum of D₁ over U = sum over S₁
  have hD₁_eq : U.sum (fun p => D₁.coeff p) = S₁.sum (fun p => D₁.coeff p) := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro p _ hp
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hp
    exact hp

  -- Sum of D₂ over U = sum over S₂
  have hD₂_eq : U.sum (fun p => D₂.coeff p) = S₂.sum (fun p => D₂.coeff p) := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro p _ hp
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hp
    exact hp

  rw [hsum_eq, hsplit, hD₁_eq, hD₂_eq]

/-- Degree of zero divisor is 0 -/
theorem degree_zero : (0 : Divisor RS).degree = 0 := by
  unfold degree
  have h : { p | (0 : Divisor RS).coeff p ≠ 0 } = ∅ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    rfl
  simp only [h, Set.Finite.toFinset_empty, Finset.sum_empty]

/-- Degree of negation: deg(-D) = -deg(D) -/
theorem degree_neg (D : Divisor RS) : (-D).degree = -D.degree := by
  classical
  unfold degree
  -- The support of -D is the same as D
  have hfin_eq : (-D).finiteSupport.toFinset = D.finiteSupport.toFinset := by
    ext p
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    show -D.coeff p ≠ 0 ↔ D.coeff p ≠ 0
    simp only [neg_ne_zero]
  rw [hfin_eq]
  -- Sum of (-D).coeff = sum of -D.coeff = -(sum of D.coeff)
  have hcoeff : ∀ p, (-D).coeff p = -D.coeff p := fun _ => rfl
  simp_rw [hcoeff, Finset.sum_neg_distrib]

/-- Degree of point divisor is 1 -/
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
  -- Compute the sum
  have hfin_eq : (point p).finiteSupport.toFinset = {p} := by
    ext q
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_singleton]
    rw [← Set.mem_singleton_iff, ← hsup]
    simp only [Set.mem_setOf_eq]
  rw [hfin_eq, Finset.sum_singleton, hcoeff]

/-- A divisor is effective if all coefficients are non-negative -/
def Effective (D : Divisor RS) : Prop :=
  ∀ p, 0 ≤ D.coeff p

/-- Effective divisors have non-negative degree.

    deg(D) = Σ_p D(p), and if all D(p) ≥ 0, then Σ D(p) ≥ 0. -/
theorem degree_nonneg_of_effective {D : Divisor RS} (heff : D.Effective) :
    D.degree ≥ 0 := by
  unfold degree
  apply Finset.sum_nonneg
  intro p _
  exact heff p

/-- Notation: D ≥ 0 means D is effective -/
instance : LE (Divisor RS) where
  le D₁ D₂ := Effective (D₂ + (-D₁))

/-!
## Degree Zero Divisors
-/

/-- A divisor has degree zero -/
def IsDegreeZero (D : Divisor RS) : Prop :=
  D.degree = 0

/-- The subgroup of degree zero divisors -/
def Div0 (RS : RiemannSurface) := { D : Divisor RS // D.IsDegreeZero }

end Divisor

/-!
## Principal Divisors

The divisor of a meromorphic function f is div(f) = Σ_p ord_p(f) · [p].
-/

/-- The divisor of an analytic meromorphic function -/
noncomputable def divisorOf (f : AnalyticMeromorphicFunction RS) :
    Divisor RS where
  coeff := f.order
  finiteSupport := f.order_finiteSupport

/-- A divisor is principal if it's the divisor of some meromorphic function -/
def Divisor.IsPrincipal (D : Divisor RS) : Prop :=
  ∃ f : AnalyticMeromorphicFunction RS, divisorOf f = D

/-!
## Argument Principle (Analytic Version)

For compact Riemann surfaces, the degree of any principal divisor is zero.
-/

/-- The degree of a principal divisor is zero (argument principle).

    **Analytic proof sketch:**
    1. For meromorphic f, consider the logarithmic derivative ω = df/f
    2. ω is a meromorphic 1-form with Res_p(ω) = ord_p(f)
    3. By the residue theorem: Σ_p Res_p(ω) = 0 on compact surfaces
    4. Therefore: Σ_p ord_p(f) = deg(div(f)) = 0 -/
theorem principal_divisor_degree_zero (CRS : CompactRiemannSurface)
    (f : AnalyticMeromorphicFunction CRS.toRiemannSurface) :
    (divisorOf f).degree = analyticOrderSum f := by
  unfold Divisor.degree divisorOf analyticOrderSum
  rfl

/-- For compact surfaces, principal divisors have degree zero -/
theorem principal_degree_zero_compact (CRS : CompactRiemannSurface)
    (f : AnalyticMeromorphicFunction CRS.toRiemannSurface) :
    (divisorOf f).degree = 0 :=
  (principal_divisor_degree_zero CRS f).trans (analyticArgumentPrinciple CRS f)

/-!
## Picard Group

Pic(Σ) = Div(Σ) / Prin(Σ) classifies holomorphic line bundles.
-/

/-- Linear equivalence of divisors: D₁ ~ D₂ if D₁ - D₂ is principal -/
def Divisor.LinearEquiv (D₁ D₂ : Divisor RS) : Prop :=
  (D₁ + (-D₂)).IsPrincipal

/-- The divisor of the constant function 1 is 0 -/
theorem divisorOf_one : divisorOf (1 : AnalyticMeromorphicFunction RS) = 0 := by
  ext p
  simp only [divisorOf]
  rfl

/-- The divisor of a product is the sum of divisors: div(fg) = div(f) + div(g) -/
theorem divisorOf_mul (f g : AnalyticMeromorphicFunction RS) :
    divisorOf (f * g) = divisorOf f + divisorOf g := by
  ext p
  show (f * g).order p = (divisorOf f + divisorOf g).coeff p
  simp only [AnalyticMeromorphicFunction.order_mul, divisorOf]
  rfl

/-- The divisor of an inverse negates the divisor: div(1/f) = -div(f) -/
theorem divisorOf_inv (f : AnalyticMeromorphicFunction RS) :
    divisorOf f⁻¹ = -divisorOf f := by
  ext p
  show f⁻¹.order p = (-divisorOf f).coeff p
  simp only [AnalyticMeromorphicFunction.order_inv, divisorOf]
  rfl

/-- Linear equivalence is an equivalence relation -/
theorem Divisor.linearEquiv_equivalence :
    Equivalence (@Divisor.LinearEquiv RS) where
  refl := fun D => by
    unfold LinearEquiv IsPrincipal
    -- D - D = 0 = div(1)
    use 1
    simp only [add_neg_cancel]
    exact divisorOf_one
  symm := fun {D₁ D₂} h => by
    unfold LinearEquiv IsPrincipal at *
    -- If D₁ - D₂ = div(f), then D₂ - D₁ = -(D₁ - D₂) = div(1/f)
    obtain ⟨f, hf⟩ := h
    use f⁻¹
    -- div(f⁻¹) = -div(f)
    rw [divisorOf_inv]
    -- Need: -(divisorOf f) = D₂ + -D₁
    -- From hf: divisorOf f = D₁ + -D₂
    rw [hf]
    -- -(D₁ + -D₂) = D₂ + -D₁
    ext p
    show -(D₁.coeff p + -D₂.coeff p) = D₂.coeff p + -D₁.coeff p
    ring
  trans := fun {D₁ D₂ D₃} h₁ h₂ => by
    unfold LinearEquiv IsPrincipal at *
    -- If D₁ - D₂ = div(f) and D₂ - D₃ = div(g), then D₁ - D₃ = div(fg)
    obtain ⟨f, hf⟩ := h₁
    obtain ⟨g, hg⟩ := h₂
    use f * g
    -- div(fg) = div(f) + div(g)
    rw [divisorOf_mul, hf, hg]
    -- (D₁ + -D₂) + (D₂ + -D₃) = D₁ + -D₃
    ext p
    show (D₁.coeff p + -D₂.coeff p) + (D₂.coeff p + -D₃.coeff p) = D₁.coeff p + -D₃.coeff p
    ring

/-- The Picard group Pic(Σ) = Div(Σ) / ~ -/
def PicardGroup (RS : RiemannSurface) :=
  Quotient (Setoid.mk (@Divisor.LinearEquiv RS) (@Divisor.linearEquiv_equivalence RS))

end RiemannSurfaces.Analytic
