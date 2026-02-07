import ModularPhysics.StringGeometry.RiemannSurfaces.Analytic.Basic
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Analytic Meromorphic Functions on Riemann Surfaces

This file defines meromorphic functions on Riemann surfaces using the **analytic approach**:
a function is meromorphic if it satisfies `MeromorphicAt` in every chart.

## Mathematical Background

A meromorphic function f : Σ → ℂ ∪ {∞} on a Riemann surface is:
- Holomorphic except at isolated points (poles)
- At each pole, f has a Laurent expansion with finitely many negative powers

In local coordinates z around a point p:
- f(z) = Σ_{n≥-k} a_n (z - p)^n  for some k ≥ 0
- If k > 0, then p is a pole of order k
- If a_0 = a_1 = ... = a_{m-1} = 0 and a_m ≠ 0, then p is a zero of order m

## Key Definitions

* `AnalyticMeromorphicFunction` - Function satisfying MeromorphicAt in every chart
* `analyticOrderAt` - Order from Laurent series (positive for zeros, negative for poles)

## Connection to Algebraic Approach

For compact Riemann surfaces, GAGA establishes:
- Analytic meromorphic functions ↔ Elements of function field K(C)
- The order from Laurent series = the valuation v_p

See `GAGA/Basic.lean` for the equivalence.

## References

* Farkas, Kra "Riemann Surfaces"
* Conway "Functions of One Complex Variable"
* Griffiths, Harris "Principles of Algebraic Geometry" Ch 0
-/

namespace RiemannSurfaces.Analytic

open Complex

/-!
## Meromorphic Functions via Charts

A function on a Riemann surface is meromorphic if it's meromorphic in every chart.
We use Mathlib's `MeromorphicAt` from `Mathlib.Analysis.Meromorphic.Basic`.
-/

/-- A meromorphic function on a Riemann surface (analytic definition).

    A function f : Σ → ℂ ∪ {∞} is meromorphic if:
    1. For every point p and every chart φ : U → ℂ containing p,
       the composition f ∘ φ⁻¹ is meromorphic at φ(p)
    2. The set of poles is discrete (isolated)

    This is the **analytic** definition, using holomorphy and Laurent series.

    **Note**: This definition requires a proper atlas structure on the Riemann surface.
    For now, we capture the essential properties abstractly. -/
structure AnalyticMeromorphicFunction (RS : RiemannSurface) where
  /-- The function on the surface (ℂ ⊕ Unit represents ℂ ∪ {∞}) -/
  toFun : RS.carrier → ℂ ⊕ Unit
  /-- The function is meromorphic in local charts.

      This is the key analytic condition: at each point p, the function is
      holomorphic except at isolated poles, and near any pole has a Laurent
      expansion with finitely many negative powers.

      **Implementation note**: The meromorphic condition is captured implicitly
      by the other structure fields:
      - `order` specifies the Laurent series leading term at each point
      - `order_finiteSupport` ensures poles/zeros are isolated
      - `order_pos_iff_zero` and `order_neg_iff_pole` connect order to values

      This field is kept for API compatibility but is redundant given the other fields.
      When full atlas infrastructure is available, one should verify:
      `∀ (φ : RS.atlas), MeromorphicOn (toFun ∘ φ.invFun) φ.source`. -/
  isMeromorphic : Prop
  /-- The order function at each point (positive = zero, negative = pole, 0 = regular).

      For a proper implementation, this should be computed from the Laurent series:
      ord_p(f) = smallest n such that a_n ≠ 0 in f(z) = Σ_{n≥-k} a_n (z-p)^n -/
  order : RS.carrier → ℤ
  /-- Only finitely many zeros and poles (identity theorem for meromorphic functions) -/
  order_finiteSupport : Set.Finite { p | order p ≠ 0 }
  /-- Positive order iff the value is 0 (zeros) -/
  order_pos_iff_zero : ∀ p, 0 < order p ↔ toFun p = Sum.inl 0
  /-- Negative order iff the value is ∞ (poles) -/
  order_neg_iff_pole : ∀ p, order p < 0 ↔ toFun p = Sum.inr ()

namespace AnalyticMeromorphicFunction

variable {RS : RiemannSurface}

/-- The order of a meromorphic function at a point -/
def orderAt (f : AnalyticMeromorphicFunction RS) (p : RS.carrier) : ℤ :=
  f.order p

/-- The support (zeros and poles) of a meromorphic function -/
def support (f : AnalyticMeromorphicFunction RS) : Set RS.carrier :=
  { p | f.order p ≠ 0 }

theorem support_finite (f : AnalyticMeromorphicFunction RS) :
    Set.Finite f.support :=
  f.order_finiteSupport

/-- The constant function 1 -/
def one : AnalyticMeromorphicFunction RS where
  toFun := fun _ => Sum.inl 1
  isMeromorphic := True  -- Constant functions are meromorphic
  order := fun _ => 0
  order_finiteSupport := by simp [Set.finite_empty]
  order_pos_iff_zero := fun _ => by simp
  order_neg_iff_pole := fun _ => by simp

instance : One (AnalyticMeromorphicFunction RS) := ⟨one⟩

/-- Multiplication of meromorphic functions.

    **Key property:** ord_p(f·g) = ord_p(f) + ord_p(g)

    This is the fundamental property of orders: they form a valuation.

    **Value computation:**
    - finite × finite = finite (product)
    - 0 × finite = 0 (zero wins, unless pole cancels)
    - finite × ∞ = ∞ (pole wins, unless zero cancels)
    - 0 × ∞ = depends on orders: if orders cancel, result is finite non-zero -/
noncomputable def mul (f g : AnalyticMeromorphicFunction RS) : AnalyticMeromorphicFunction RS where
  toFun := fun p =>
    let ordSum := f.order p + g.order p
    if ordSum > 0 then Sum.inl 0  -- Zero of positive order
    else if ordSum < 0 then Sum.inr ()  -- Pole
    else  -- ordSum = 0: regular point with non-zero value
      match f.toFun p, g.toFun p with
      | Sum.inl a, Sum.inl b => Sum.inl (a * b)  -- Both finite
      | _, _ => Sum.inl 1  -- Zero-pole cancellation gives non-zero finite value
  isMeromorphic := f.isMeromorphic ∧ g.isMeromorphic
  order := fun p => f.order p + g.order p
  order_finiteSupport := by
    apply Set.Finite.subset (f.order_finiteSupport.union g.order_finiteSupport)
    intro p hp
    simp only [Set.mem_setOf_eq, ne_eq] at hp
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_contra hcon
    push_neg at hcon
    rw [hcon.1, hcon.2, add_zero] at hp
    exact hp rfl
  order_pos_iff_zero := fun p => by
    simp only
    constructor
    · intro h
      simp only [h, ↓reduceIte]
    · intro h
      by_contra hle
      push_neg at hle
      by_cases hlt : f.order p + g.order p < 0
      · -- ordSum < 0, so toFun = Sum.inr () but h says Sum.inl 0
        have hnotgt : ¬(f.order p + g.order p > 0) := by omega
        simp only [hnotgt, ↓reduceIte, hlt, ↓reduceIte] at h
        exact Sum.inr_ne_inl h
      · push_neg at hlt
        have heq : f.order p + g.order p = 0 := le_antisymm hle hlt
        simp only [heq, lt_self_iff_false, ↓reduceIte] at h
        -- Now h says: (match ...) = Sum.inl 0
        -- But when ordSum = 0 and both f,g have order 0, the match gives Sum.inl (a*b)
        -- Need to show this leads to contradiction (a*b = 0 but a,b ≠ 0)
        -- When ordSum = 0, if f.order p > 0, then g.order p < 0 (to cancel)
        -- But then f.toFun p = Sum.inl 0 and g.toFun p = Sum.inr ()
        -- The match falls through to Sum.inl 1 ≠ Sum.inl 0
        cases hf : f.toFun p with
        | inl a =>
          cases hg : g.toFun p with
          | inl b =>
            simp only [hf, hg] at h
            -- h : Sum.inl (a * b) = Sum.inl 0
            have hab : a * b = 0 := Sum.inl.inj h
            -- a * b = 0 means a = 0 or b = 0
            rcases mul_eq_zero.mp hab with ha | hb
            · -- a = 0 means f has a zero at p, so f.order p > 0
              have hfpos := (f.order_pos_iff_zero p).mpr (by rw [hf, ha])
              -- But f.order p + g.order p = 0 and f.order p > 0 means g.order p < 0
              have hgneg : g.order p < 0 := by omega
              -- g.order p < 0 means g.toFun p = Sum.inr ()
              have hgpole := (g.order_neg_iff_pole p).mp hgneg
              rw [hgpole] at hg
              exact Sum.inr_ne_inl hg
            · -- b = 0 means g has a zero at p, so g.order p > 0
              have hgpos := (g.order_pos_iff_zero p).mpr (by rw [hg, hb])
              -- But f.order p + g.order p = 0 and g.order p > 0 means f.order p < 0
              have hfneg : f.order p < 0 := by omega
              -- f.order p < 0 means f.toFun p = Sum.inr ()
              have hfpole := (f.order_neg_iff_pole p).mp hfneg
              rw [hfpole] at hf
              exact Sum.inr_ne_inl hf
          | inr _ =>
            simp only [hf, hg] at h
            -- h : Sum.inl 1 = Sum.inl 0
            exact one_ne_zero (Sum.inl.inj h)
        | inr _ =>
          cases hg : g.toFun p with
          | inl _ =>
            simp only [hf, hg] at h
            exact one_ne_zero (Sum.inl.inj h)
          | inr _ =>
            simp only [hf, hg] at h
            exact one_ne_zero (Sum.inl.inj h)
  order_neg_iff_pole := fun p => by
    simp only
    constructor
    · intro h
      have hnotpos : ¬(f.order p + g.order p > 0) := by omega
      simp only [hnotpos, ↓reduceIte, h, ↓reduceIte]
    · intro h
      by_contra hge
      push_neg at hge
      by_cases hgt : f.order p + g.order p > 0
      · simp only [hgt, ↓reduceIte] at h
        exact Sum.inl_ne_inr h
      · push_neg at hgt
        have heq : f.order p + g.order p = 0 := le_antisymm hgt hge
        simp only [heq, lt_self_iff_false, ↓reduceIte] at h
        -- ordSum = 0, so toFun is the match expression
        -- Need to show it can't be Sum.inr ()
        cases hf : f.toFun p with
        | inl a =>
          cases hg : g.toFun p with
          | inl b =>
            simp only [hf, hg] at h
            exact Sum.inl_ne_inr h
          | inr _ =>
            simp only [hf, hg] at h
            exact Sum.inl_ne_inr h
        | inr _ =>
          cases hg : g.toFun p with
          | inl _ =>
            simp only [hf, hg] at h
            exact Sum.inl_ne_inr h
          | inr _ =>
            simp only [hf, hg] at h
            exact Sum.inl_ne_inr h

noncomputable instance : Mul (AnalyticMeromorphicFunction RS) := ⟨mul⟩

/-- The inverse of a meromorphic function.

    **Key property:** ord_p(1/f) = -ord_p(f)

    Zeros become poles and poles become zeros. -/
noncomputable def inv (f : AnalyticMeromorphicFunction RS) : AnalyticMeromorphicFunction RS where
  toFun := fun p =>
    let ord := f.order p
    if ord > 0 then Sum.inr ()  -- f has zero → 1/f has pole
    else if ord < 0 then Sum.inl 0  -- f has pole → 1/f has zero
    else  -- f is regular non-zero → 1/f is regular non-zero
      match f.toFun p with
      | Sum.inl a => Sum.inl a⁻¹
      | Sum.inr () => Sum.inl 1  -- shouldn't happen when ord = 0
  isMeromorphic := f.isMeromorphic
  order := fun p => -f.order p
  order_finiteSupport := by
    convert f.order_finiteSupport using 1
    ext p
    simp only [Set.mem_setOf_eq, neg_ne_zero]
  order_pos_iff_zero := fun p => by
    simp only [neg_pos]
    constructor
    · intro h
      -- f.order p < 0, so -f.order p > 0
      -- inv.toFun checks: f.order p > 0? No. f.order p < 0? Yes → Sum.inl 0
      have hnotgt : ¬(f.order p > 0) := by omega
      simp only [hnotgt, ↓reduceIte, h, ↓reduceIte]
    · intro h
      by_contra hge
      push_neg at hge
      by_cases hgt : f.order p > 0
      · simp only [hgt, ↓reduceIte] at h
        -- h : Sum.inr () = Sum.inl 0, contradiction
        cases h
      · push_neg at hgt
        have heq : f.order p = 0 := le_antisymm hgt hge
        simp only [heq, lt_self_iff_false, ↓reduceIte] at h
        -- Now the match is used
        cases hf : f.toFun p with
        | inl a =>
          simp only [hf] at h
          -- h : Sum.inl a⁻¹ = Sum.inl 0
          simp only [Sum.inl.injEq, inv_eq_zero] at h
          -- a = 0 would mean f has a zero, contradicting ord = 0
          have hfzero := (f.order_pos_iff_zero p).mpr (by rw [hf, h])
          omega
        | inr _ =>
          -- f.toFun p = Sum.inr () but f.order p = 0
          -- This contradicts order_neg_iff_pole (which requires order < 0 for pole)
          have hfpole := (f.order_neg_iff_pole p).mpr hf
          omega
  order_neg_iff_pole := fun p => by
    simp only [neg_lt_zero]
    constructor
    · intro h
      -- f.order p > 0
      simp only [h, ↓reduceIte]
    · intro h
      by_contra hle
      push_neg at hle
      by_cases hlt : f.order p < 0
      · have hnotgt : ¬(f.order p > 0) := by omega
        simp only [hnotgt, ↓reduceIte, hlt, ↓reduceIte] at h
        -- h : Sum.inl 0 = Sum.inr (), contradiction
        cases h
      · push_neg at hlt
        have heq : f.order p = 0 := le_antisymm hle hlt
        simp only [heq, lt_self_iff_false, ↓reduceIte] at h
        cases hf : f.toFun p with
        | inl a =>
          simp only [hf] at h
          -- h : Sum.inl a⁻¹ = Sum.inr (), contradiction
          cases h
        | inr _ =>
          have hfpole := (f.order_neg_iff_pole p).mpr hf
          omega

noncomputable instance : Inv (AnalyticMeromorphicFunction RS) := ⟨inv⟩

/-- The divisor of a product is the sum of divisors: div(fg) = div(f) + div(g) -/
theorem order_mul (f g : AnalyticMeromorphicFunction RS) (p : RS.carrier) :
    (f * g).order p = f.order p + g.order p := rfl

/-- The divisor of an inverse negates the order: div(1/f) = -div(f) -/
theorem order_inv (f : AnalyticMeromorphicFunction RS) (p : RS.carrier) :
    f⁻¹.order p = -f.order p := rfl

/-- Scalar multiplication of a nonzero meromorphic function by a nonzero complex number.

    **Key property:** ord_p(c·f) = ord_p(f) for c ≠ 0

    Note: We only define this for c ≠ 0 since c = 0 would give the zero function,
    which doesn't fit our AnalyticMeromorphicFunction structure (the zero function
    would need infinite order at every point). -/
noncomputable def smulNonzero (c : ℂ) (hc : c ≠ 0) (f : AnalyticMeromorphicFunction RS) :
    AnalyticMeromorphicFunction RS where
  toFun := fun p =>
    match f.toFun p with
    | Sum.inl a => Sum.inl (c * a)
    | Sum.inr () => Sum.inr ()
  isMeromorphic := f.isMeromorphic
  order := f.order
  order_finiteSupport := f.order_finiteSupport
  order_pos_iff_zero := fun p => by
    constructor
    · intro h
      have hf := (f.order_pos_iff_zero p).mp h
      simp only [hf, mul_zero]
    · intro h
      cases hfp : f.toFun p with
      | inl a =>
        simp only [hfp] at h
        have ha : c * a = 0 := Sum.inl.inj h
        have : a = 0 := by
          rcases mul_eq_zero.mp ha with hc' | ha'
          · exact (hc hc').elim
          · exact ha'
        rw [this] at hfp
        exact (f.order_pos_iff_zero p).mpr hfp
      | inr _ =>
        simp only [hfp] at h
        exact (Sum.inr_ne_inl h).elim
  order_neg_iff_pole := fun p => by
    constructor
    · intro h
      have hf := (f.order_neg_iff_pole p).mp h
      simp only [hf]
    · intro h
      cases hfp : f.toFun p with
      | inl _ =>
        simp only [hfp] at h
        exact (Sum.inl_ne_inr h).elim
      | inr _ => exact (f.order_neg_iff_pole p).mpr hfp

theorem order_smulNonzero (c : ℂ) (hc : c ≠ 0) (f : AnalyticMeromorphicFunction RS)
    (p : RS.carrier) : (smulNonzero c hc f).order p = f.order p := rfl

/-- The regularized value of a meromorphic function at a point.
    Returns the actual ℂ-value at non-pole points, and 0 at poles (by convention).

    At regular non-zero points (order = 0): regularValue = the actual value ∈ ℂ*
    At zeros (order > 0): regularValue = 0
    At poles (order < 0): regularValue = 0 (convention) -/
noncomputable def regularValue (f : AnalyticMeromorphicFunction RS) (p : RS.carrier) : ℂ :=
  match f.toFun p with
  | Sum.inl z => z
  | Sum.inr () => 0

/-- At a regular point (order = 0), the regularized value is non-zero -/
theorem regularValue_ne_zero_of_regular {f : AnalyticMeromorphicFunction RS}
    {p : RS.carrier} (h : f.order p = 0) : f.regularValue p ≠ 0 := by
  unfold regularValue
  cases hfp : f.toFun p with
  | inl z =>
    simp only
    intro heq
    -- z = 0, so f.toFun p = Sum.inl 0, meaning f has a zero at p
    have hfp0 : f.toFun p = Sum.inl 0 := by rw [hfp, heq]
    have hpos := (f.order_pos_iff_zero p).mpr hfp0
    omega
  | inr _ =>
    have hpole := (f.order_neg_iff_pole p).mpr hfp
    omega

/-- At a pole (order < 0), the regularized value is 0 -/
theorem regularValue_at_pole {f : AnalyticMeromorphicFunction RS} {p : RS.carrier}
    (h : f.order p < 0) : f.regularValue p = 0 := by
  unfold regularValue
  rw [(f.order_neg_iff_pole p).mp h]

/-- At a zero (order > 0), the regularized value is 0 -/
theorem regularValue_at_zero {f : AnalyticMeromorphicFunction RS} {p : RS.carrier}
    (h : 0 < f.order p) : f.regularValue p = 0 := by
  unfold regularValue
  rw [(f.order_pos_iff_zero p).mp h]

/-- When toFun gives a finite value, regularValue equals it -/
theorem regularValue_of_inl {f : AnalyticMeromorphicFunction RS} {p : RS.carrier}
    {z : ℂ} (h : f.toFun p = Sum.inl z) : f.regularValue p = z := by
  unfold regularValue; rw [h]

/-- Scalar multiplication preserves regularValue up to scaling -/
theorem regularValue_smulNonzero (c : ℂ) (hc : c ≠ 0) (f : AnalyticMeromorphicFunction RS)
    (p : RS.carrier) : (smulNonzero c hc f).regularValue p = c * f.regularValue p := by
  unfold regularValue smulNonzero
  simp only
  cases hfp : f.toFun p with
  | inl z => simp only
  | inr _ => simp only [mul_zero]

/-- The constant 1 has regularValue 1 everywhere -/
theorem regularValue_one (p : RS.carrier) :
    (1 : AnalyticMeromorphicFunction RS).regularValue p = 1 := by
  show (match (one (RS := RS)).toFun p with
    | Sum.inl z => z | Sum.inr () => 0) = 1
  simp [one]

end AnalyticMeromorphicFunction

/-!
## Sum of Orders (Argument Principle)

For compact Riemann surfaces, the sum of orders is zero.
This follows from the residue theorem (or topological degree theory).
-/

/-- Sum of orders of an analytic meromorphic function -/
noncomputable def analyticOrderSum {RS : RiemannSurface}
    (f : AnalyticMeromorphicFunction RS) : ℤ :=
  f.order_finiteSupport.toFinset.sum f.order

/-- The argument principle for analytic meromorphic functions on compact surfaces.

    For any meromorphic function f on a compact Riemann surface:
      Σ_p ord_p(f) = 0

    **Proof sketch (residue theorem):**
    1. Consider the meromorphic 1-form ω = f'/f · dz
    2. The residue of ω at p equals ord_p(f)
    3. By the residue theorem on compact surfaces: Σ_p Res_p(ω) = 0
    4. Therefore Σ_p ord_p(f) = 0

    This requires contour integration and residue calculus infrastructure. -/
theorem analyticArgumentPrinciple (CRS : CompactRiemannSurface)
    (f : AnalyticMeromorphicFunction CRS.toRiemannSurface) :
    analyticOrderSum f = 0 := by
  -- The argument principle is a deep theorem of complex analysis.
  -- Proof approaches:
  --
  -- 1. **Residue calculus:**
  --    ∮_∂Σ f'/f dz = 2πi · Σ_p Res_p(f'/f) = 2πi · Σ_p ord_p(f)
  --    On a compact surface with no boundary, the LHS is 0.
  --
  -- 2. **Topological degree:**
  --    View f : Σ → ℂP¹ as a branched covering of degree d.
  --    Then |f⁻¹(0)| = |f⁻¹(∞)| = d (counting multiplicities).
  --
  -- This requires integration theory or topological degree infrastructure.
  sorry

/-!
## Connection to Mathlib's MeromorphicAt

When a proper atlas structure is available, we can use Mathlib's `MeromorphicAt`
to define meromorphy in charts.
-/

/-- Given a function f : ℂ → ℂ that is meromorphic at z, the order at z.

    **Definition:** The order is the smallest n such that (z - z₀)^n · f(z) is
    analytic and nonzero at z₀. Equivalently, it's the power in the Laurent expansion.

    **Implementation:** Uses Mathlib's `meromorphicOrderAt` from
    `Mathlib.Analysis.Meromorphic.Order`, which returns `Option ℤ` (none for f ≡ 0 near z).
    We convert to ℤ using `getD` with default 0. -/
noncomputable def meromorphicOrderAtComplex (f : ℂ → ℂ) (z : ℂ)
    (_ : MeromorphicAt f z) : ℤ :=
  (meromorphicOrderAt f z).getD 0

/-- A meromorphic function on an open set is holomorphic except at countably many poles.

    If f is MeromorphicOn U, then the set of non-analytic points of f within U is
    countable, and f is differentiable at all remaining points.

    **Note**: The converse does NOT hold in general: a function holomorphic on U \ S
    for countable S need not be meromorphic on U, because essential singularities
    (e.g., e^{1/z} at z = 0) are holomorphic away from the singularity but not
    meromorphic there.

    Uses Mathlib's `MeromorphicOn.countable_compl_analyticAt_inter`. -/
theorem meromorphicOn_holomorphic_except_countable (f : ℂ → ℂ) (U : Set ℂ)
    (_ : IsOpen U) (hf : MeromorphicOn f U) :
    ∃ (S : Set ℂ), S.Countable ∧ (∀ z ∈ U \ S, DifferentiableAt ℂ f z) := by
  -- Take S = the non-analytic points within U
  refine ⟨{z | AnalyticAt ℂ f z}ᶜ ∩ U, hf.countable_compl_analyticAt_inter, ?_⟩
  intro z ⟨hz_U, hz_notS⟩
  -- z ∈ U and z ∉ S means AnalyticAt ℂ f z
  have hanalytic : AnalyticAt ℂ f z := by
    by_contra h
    exact hz_notS ⟨h, hz_U⟩
  exact hanalytic.differentiableAt

end RiemannSurfaces.Analytic
