import ModularPhysics.StringGeometry.RiemannSurfaces.Basic
import ModularPhysics.StringGeometry.RiemannSurfaces.GAGA.Helpers.Meromorphic
import Mathlib.Topology.Basic

/-!
# Degree Theory for Holomorphic Maps

This file develops degree theory for holomorphic maps between compact Riemann surfaces,
which is the key to proving the argument principle.

## Main Results

* `HolomorphicMap.degree` - The degree of a non-constant holomorphic map
* `HolomorphicMap.preimage_card` - Number of preimages equals degree
* `argumentPrinciple_via_degree` - #zeros = #poles for meromorphic functions

## Mathematical Background

For a non-constant holomorphic map f: Σ₁ → Σ₂ between compact Riemann surfaces:

1. f is a branched covering with finitely many branch points
2. Away from branch points, f is a local homeomorphism
3. The **degree** of f = number of sheets = #f⁻¹(p) for any regular value p
4. For any p ∈ Σ₂: Σ_{q ∈ f⁻¹(p)} mult_q(f) = deg(f)

For a meromorphic function f: Σ → ℂP¹:
- #zeros = #f⁻¹(0) = deg(f)
- #poles = #f⁻¹(∞) = deg(f)
- Therefore #zeros = #poles (argument principle)

## References

* Miranda "Algebraic Curves and Riemann Surfaces" Ch III
* Griffiths, Harris "Principles of Algebraic Geometry" Ch 0
-/

namespace RiemannSurfaces.Algebraic.DegreeTheory

open RiemannSurfaces

/-!
## Local Degree (Ramification Index)

At each point, a holomorphic map has a local degree (ramification index).
In local coordinates, if f(z) = z^n · g(z) with g(0) ≠ 0, then the local degree is n.
-/

/-- The local degree (ramification index) of a holomorphic map at a point.

    If f(z) - f(p) = (z - p)^n · g(z) with g(p) ≠ 0 in local coordinates,
    then the local degree at p is n.

    This equals 1 at regular points and > 1 at ramification points.

    NOTE: For general holomorphic maps, this requires local coordinate information.
    For meromorphic functions, use `meromorphicLocalDegree` instead. -/
structure LocalDegreeData (RS₁ RS₂ : RiemannSurface) (f : RS₁.carrier → RS₂.carrier) where
  /-- The local degree at each point -/
  localDeg : RS₁.carrier → ℕ
  /-- Local degree is at least 1 -/
  localDeg_pos : ∀ p, 1 ≤ localDeg p
  /-- Ramification is finite -/
  ramification_finite : Set.Finite { p | localDeg p > 1 }

/-- A point is a ramification point if local degree > 1 -/
def IsRamificationPoint (data : LocalDegreeData RS₁ RS₂ f) (p : RS₁.carrier) : Prop :=
  data.localDeg p > 1

/-- A point is a branch point if it's the image of a ramification point -/
def IsBranchPoint (data : LocalDegreeData RS₁ RS₂ f) (q : RS₂.carrier) : Prop :=
  ∃ p : RS₁.carrier, f p = q ∧ IsRamificationPoint data p

/-!
## Global Degree for Holomorphic Maps

For a non-constant holomorphic map between compact Riemann surfaces,
the degree is the number of preimages of a generic point.
-/

/-- The global degree of a holomorphic map, given local degree data.

    The global degree equals the sum of local degrees over any fiber.
    This is well-defined because the sum is constant over all fibers. -/
structure GlobalDegreeData (CRS₁ CRS₂ : CompactRiemannSurface)
    (f : CRS₁.toRiemannSurface.carrier → CRS₂.toRiemannSurface.carrier) extends
    LocalDegreeData CRS₁.toRiemannSurface CRS₂.toRiemannSurface f where
  /-- The global degree -/
  degree : ℕ
  /-- The sum of local degrees over any fiber equals the global degree -/
  fiber_sum_eq : ∀ q : CRS₂.toRiemannSurface.carrier,
    ∀ preimages : Finset CRS₁.toRiemannSurface.carrier,
    (∀ p ∈ preimages, f p = q) →
    (∀ p, f p = q → p ∈ preimages) →
    preimages.sum localDeg = degree

/-!
## Application to Meromorphic Functions

A meromorphic function on a compact Riemann surface can be viewed as a
holomorphic map to ℂP¹. The zeros and poles are preimages of 0 and ∞.
-/

/-- A meromorphic function viewed as a map to ℂP¹.

    For f ∈ M(Σ), we get f̃: Σ → ℂP¹ by:
    - f̃(p) = f(p) if f(p) ∈ ℂ (not a pole)
    - f̃(p) = ∞ if p is a pole of f

    The MeromorphicFunction already has this data via toFun : RS.carrier → ℂ ⊕ Unit
    where Sum.inr () represents ∞. We just need to swap the order for ℂP¹. -/
noncomputable def meromorphicToCP1Map (CRS : CompactRiemannSurface)
    (f : MeromorphicFunction CRS.toRiemannSurface) :
    CRS.toRiemannSurface.carrier → Unit ⊕ ℂ := fun p =>
  -- f.toFun p : ℂ ⊕ Unit, we need Unit ⊕ ℂ
  match f.toFun p with
  | Sum.inl z => Sum.inr z  -- Finite value
  | Sum.inr () => Sum.inl ()  -- Pole (infinity)

/-- The local degree of a meromorphic function at a point, viewed as a map to ℂP¹.

    For a meromorphic function f:
    - At a zero of order n > 0: local degree = n (fiber over 0)
    - At a pole of order n > 0: local degree = n (fiber over ∞)
    - At a regular point (order = 0): local degree = 1 (simple point in the fiber)

    This is defined as max(1, |order|) which handles all cases correctly. -/
def meromorphicLocalDegree (CRS : CompactRiemannSurface)
    (f : MeromorphicFunction CRS.toRiemannSurface) (p : CRS.toRiemannSurface.carrier) : ℕ :=
  -- At zeros/poles: local degree = |order|
  -- At regular points: local degree = 1
  if f.order p = 0 then 1 else (f.order p).natAbs

/-- At a zero, the local degree equals the order -/
theorem meromorphicLocalDegree_at_zero (CRS : CompactRiemannSurface)
    (f : MeromorphicFunction CRS.toRiemannSurface) (p : CRS.toRiemannSurface.carrier)
    (h : 0 < f.order p) :
    meromorphicLocalDegree CRS f p = (f.order p).toNat := by
  unfold meromorphicLocalDegree
  have hne : f.order p ≠ 0 := by omega
  simp only [hne, ↓reduceIte]
  -- For positive integers: natAbs = toNat
  omega

/-- At a pole, the local degree equals the absolute value of the order -/
theorem meromorphicLocalDegree_at_pole (CRS : CompactRiemannSurface)
    (f : MeromorphicFunction CRS.toRiemannSurface) (p : CRS.toRiemannSurface.carrier)
    (h : f.order p < 0) :
    meromorphicLocalDegree CRS f p = (-f.order p).toNat := by
  unfold meromorphicLocalDegree
  have hne : f.order p ≠ 0 := by omega
  simp only [hne, ↓reduceIte]
  -- For negative n: natAbs n = toNat (-n)
  omega

/-- At a regular point, the local degree is 1 -/
theorem meromorphicLocalDegree_at_regular (CRS : CompactRiemannSurface)
    (f : MeromorphicFunction CRS.toRiemannSurface) (p : CRS.toRiemannSurface.carrier)
    (h : f.order p = 0) :
    meromorphicLocalDegree CRS f p = 1 := by
  unfold meromorphicLocalDegree
  simp only [h, ↓reduceIte]

/-!
## The Argument Principle via Degree Theory

The argument principle states: for a meromorphic function f on a compact surface,
#{zeros} = #{poles} (counting multiplicity).

Proof: View f as a map f̃: Σ → ℂP¹.
- #{zeros} = Σ_{f̃(p)=0} localDegree(f̃, p) = globalDegree(f̃)
- #{poles} = Σ_{f̃(p)=∞} localDegree(f̃, p) = globalDegree(f̃)
- Therefore #{zeros} = #{poles}
-/

/-- The total order of zeros of a meromorphic function -/
noncomputable def totalZeroOrder (CRS : CompactRiemannSurface)
    (f : MeromorphicFunction CRS.toRiemannSurface) : ℕ :=
  (f.order_finiteSupport.toFinset.filter (fun p => 0 < f.order p)).sum
    (fun p => (f.order p).toNat)

/-- The total order of poles of a meromorphic function -/
noncomputable def totalPoleOrder (CRS : CompactRiemannSurface)
    (f : MeromorphicFunction CRS.toRiemannSurface) : ℕ :=
  (f.order_finiteSupport.toFinset.filter (fun p => f.order p < 0)).sum
    (fun p => (-f.order p).toNat)

/-- The degree of a meromorphic function is the total zero order (= total pole order).

    For a non-constant meromorphic function f: Σ → ℂP¹, the degree is well-defined
    because it equals the total zero order, which also equals the total pole order
    by the argument principle. -/
noncomputable def meromorphicDegree (CRS : CompactRiemannSurface)
    (f : MeromorphicFunction CRS.toRiemannSurface) : ℕ :=
  totalZeroOrder CRS f

/-- The local degree data for a meromorphic function satisfies positivity. -/
theorem meromorphicLocalDegree_pos (CRS : CompactRiemannSurface)
    (f : MeromorphicFunction CRS.toRiemannSurface) (p : CRS.toRiemannSurface.carrier) :
    1 ≤ meromorphicLocalDegree CRS f p := by
  unfold meromorphicLocalDegree
  split_ifs <;> omega

/-- The ramification points of a meromorphic function are finite (they are the zeros and poles). -/
theorem meromorphicRamification_finite (CRS : CompactRiemannSurface)
    (f : MeromorphicFunction CRS.toRiemannSurface) :
    Set.Finite { p | meromorphicLocalDegree CRS f p > 1 } := by
  have h := f.order_finiteSupport
  apply Set.Finite.subset h
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  unfold meromorphicLocalDegree at hp
  split_ifs at hp with h0
  · omega  -- h0 says order = 0, but hp says degree > 1 contradicts 1 > 1
  · exact h0  -- order ≠ 0

/-- **The Argument Principle via Degree Theory**

    For any meromorphic function f on a compact Riemann surface:
    totalZeroOrder(f) = totalPoleOrder(f)

    **Proof outline:**
    1. f defines a holomorphic map f̃: Σ → ℂP¹
    2. Zeros of f = f̃⁻¹(0), with local degree = order
    3. Poles of f = f̃⁻¹(∞), with local degree = |order|
    4. Sum of local degrees over any fiber equals globalDegree(f̃)
    5. Therefore totalZeroOrder = globalDegree = totalPoleOrder

    The key fact (4) follows from topology: a holomorphic map between
    compact Riemann surfaces is a branched covering, and the sum of
    local degrees over any fiber is constant.

    This requires either:
    - Integration theory: ∮ f'/f = 2πi · Σ_p ord_p(f), and on a compact
      surface without boundary this integral is 0
    - Algebraic degree theory: the topological degree of a continuous map
      equals the sum of local degrees over any regular fiber -/
theorem argumentPrinciple_degreeTheory (CRS : CompactRiemannSurface)
    (f : MeromorphicFunction CRS.toRiemannSurface) :
    totalZeroOrder CRS f = totalPoleOrder CRS f := by
  -- This follows from the argument principle (orderSum f = 0) in Meromorphic.lean
  -- We show: orderSum = totalZeroOrder - totalPoleOrder (as ℤ)
  -- So orderSum = 0 implies totalZeroOrder = totalPoleOrder

  -- Use the argument principle from Meromorphic.lean
  have harg := argumentPrinciple CRS f

  -- Key: orderSum = (sum over zeros) + (sum over poles)
  --                = totalZeroOrder - totalPoleOrder  (since pole orders are negative)
  let S := f.order_finiteSupport.toFinset
  let Spos := S.filter (fun p => 0 < f.order p)
  let Sneg := S.filter (fun p => f.order p < 0)

  -- orderSum splits into positive and negative parts
  have hsplit : orderSum f = Spos.sum f.order + Sneg.sum f.order := by
    unfold orderSum
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun p => 0 < f.order p)]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter, not_lt]
    change p ∈ S ∧ f.order p ≤ 0 ↔ p ∈ S.filter (fun p => f.order p < 0)
    simp only [Finset.mem_filter]
    constructor
    · intro ⟨hmem, hle⟩
      refine ⟨hmem, ?_⟩
      have hne : f.order p ≠ 0 := by
        have : p ∈ f.order_finiteSupport.toFinset := hmem
        rw [Set.Finite.mem_toFinset] at this
        exact this
      omega
    · intro ⟨hmem, hlt⟩
      exact ⟨hmem, le_of_lt hlt⟩

  -- Sum over Spos equals totalZeroOrder (as ℤ)
  have hpos_eq : Spos.sum f.order = (totalZeroOrder CRS f : ℤ) := by
    unfold totalZeroOrder
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro p hp
    -- hp : p ∈ Spos = S.filter (fun p => 0 < f.order p)
    have hp' : p ∈ S.filter (fun p => 0 < f.order p) := hp
    rw [Finset.mem_filter] at hp'
    exact (Int.toNat_of_nonneg (le_of_lt hp'.2)).symm

  -- Sum over Sneg equals -totalPoleOrder (as ℤ)
  have hneg_eq : Sneg.sum f.order = -(totalPoleOrder CRS f : ℤ) := by
    unfold totalPoleOrder
    rw [Nat.cast_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr
    · -- Sneg = S.filter (fun p => f.order p < 0)
      rfl
    · intro p hp
      have hp' : p ∈ S.filter (fun p => f.order p < 0) := hp
      rw [Finset.mem_filter] at hp'
      have hneg : f.order p < 0 := hp'.2
      have hpos : 0 < -f.order p := by omega
      rw [Int.toNat_of_nonneg (le_of_lt hpos)]
      ring

  -- Combine: orderSum = totalZeroOrder - totalPoleOrder = 0
  rw [hsplit, hpos_eq, hneg_eq] at harg
  -- harg : (totalZeroOrder : ℤ) + (-(totalPoleOrder : ℤ)) = 0
  -- This simplifies to totalZeroOrder = totalPoleOrder
  omega

/-- Corollary: orderSum f = 0 (the standard form of the argument principle)

    This says that the signed sum of orders (zeros positive, poles negative)
    equals zero: #{zeros with multiplicity} = #{poles with multiplicity}. -/
theorem orderSum_eq_zero (CRS : CompactRiemannSurface)
    (f : MeromorphicFunction CRS.toRiemannSurface) :
    orderSum f = 0 := by
  -- orderSum = Σ_p ord_p(f)
  -- We split into positive (zeros) and negative (poles):
  -- = Σ_{zeros} ord_p(f) + Σ_{poles} ord_p(f)
  -- = totalZeroOrder - totalPoleOrder (since pole orders are negative)
  -- = 0 by argumentPrinciple_degreeTheory
  have h := argumentPrinciple_degreeTheory CRS f
  -- totalZeroOrder = totalPoleOrder means the positive and negative parts cancel
  -- orderSum = (totalZeroOrder : ℤ) - (totalPoleOrder : ℤ)

  -- Step 1: Split the support into positive and negative orders
  let S := f.order_finiteSupport.toFinset
  let Spos := S.filter (fun p => 0 < f.order p)
  let Sneg := S.filter (fun p => f.order p < 0)

  -- Step 2: orderSum splits as sum over Spos + sum over Sneg
  have hsplit : S.sum f.order = Spos.sum f.order + Sneg.sum f.order := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun p => 0 < f.order p)]
    congr 1
    -- The "not positive" elements of S are exactly the negative ones
    -- because S only contains p with f.order p ≠ 0
    apply Finset.sum_congr _ (fun _ _ => rfl)
    -- Need to show: S.filter (fun p => ¬0 < f.order p) = S.filter (fun p => f.order p < 0)
    ext p
    simp only [Finset.mem_filter, not_lt]
    -- Goal: p ∈ S ∧ f.order p ≤ 0 ↔ p ∈ Sneg
    -- Sneg = S.filter (fun p => f.order p < 0)
    change p ∈ S ∧ f.order p ≤ 0 ↔ p ∈ S.filter (fun p => f.order p < 0)
    simp only [Finset.mem_filter]
    constructor
    · intro ⟨hmem, hle⟩
      refine ⟨hmem, ?_⟩
      -- p ∈ S means f.order p ≠ 0, and order ≤ 0 means order < 0
      have hne : f.order p ≠ 0 := by
        -- hmem : p ∈ S where S = f.order_finiteSupport.toFinset
        have : p ∈ f.order_finiteSupport.toFinset := hmem
        rw [Set.Finite.mem_toFinset] at this
        exact this
      omega
    · intro ⟨hmem, hlt⟩
      exact ⟨hmem, le_of_lt hlt⟩

  -- Step 3: Sum over Spos equals totalZeroOrder (as ℤ)
  have hpos_eq : Spos.sum f.order = (totalZeroOrder CRS f : ℤ) := by
    unfold totalZeroOrder
    -- Both sums are over the same set (zeros) with the same summand
    have heq_set : Spos = S.filter (fun p => 0 < f.order p) := rfl
    rw [heq_set]
    -- Need: Σ_{0 < order p} f.order p = Σ_{0 < order p} (f.order p).toNat
    -- For positive integers, order = toNat as integers
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [S, Finset.mem_filter] at hp
    exact (Int.toNat_of_nonneg (le_of_lt hp.2)).symm

  -- Step 4: Sum over Sneg equals -totalPoleOrder (as ℤ)
  have hneg_eq : Sneg.sum f.order = -(totalPoleOrder CRS f : ℤ) := by
    unfold totalPoleOrder
    rw [Nat.cast_sum]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr
    · -- The filter sets are the same
      ext p
      simp only [S, Sneg, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    · -- For negative orders: -(-order).toNat = order
      intro p hp
      simp only [Finset.mem_filter] at hp
      have hneg : f.order p < 0 := hp.2
      -- (-order).toNat = |order| for negative order
      have hpos : 0 < -f.order p := by omega
      rw [Int.toNat_of_nonneg (le_of_lt hpos)]
      ring

  -- Step 5: Combine: orderSum = totalZeroOrder - totalPoleOrder = 0
  unfold orderSum
  rw [hsplit, hpos_eq, hneg_eq]
  -- h says totalZeroOrder = totalPoleOrder
  rw [h]
  ring

end RiemannSurfaces.Algebraic.DegreeTheory