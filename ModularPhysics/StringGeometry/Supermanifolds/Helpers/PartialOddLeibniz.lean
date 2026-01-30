/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.
-/
import ModularPhysics.StringGeometry.Supermanifolds.Supermanifolds

/-!
# Helper Lemmas for partialOdd Leibniz Rule

This file provides helper lemmas for proving the graded Leibniz rule for odd partial
derivatives in supermanifold theory.

## Main Results

* `mul_homogeneous_coefficients` - Product of homogeneous functions simplifies
* `mul_eq_zero_of_inter_nonempty` - Product vanishes when supports overlap
* `partialOdd_eq_zero_of_not_mem'` - Derivative vanishes when variable not in support

## Mathematical Background

For homogeneous functions f (supported at I) and g (supported at J):
- If I ∩ J ≠ ∅, then f * g = 0 (since θⁱθⁱ = 0)
- If I ∩ J = ∅, then f * g is supported at I ∪ J with coefficient sign(I,J) * f_I * g_J

The graded Leibniz rule is:
  ∂_a(fg) = (∂_a f)g + (-1)^|I| f(∂_a g)

where the sign accounts for commuting the odd derivative past f.
-/

namespace Supermanifolds

open SuperDomainFunction

variable {p q : ℕ}

/-!
## Coefficients of products of homogeneous functions
-/

/-- For homogeneous functions, the product coefficient at K simplifies -/
theorem mul_homogeneous_coefficients (f g : SuperDomainFunction p q)
    (I J : Finset (Fin q))
    (hf : ∀ K ≠ I, f.coefficients K = 0)
    (hg : ∀ K ≠ J, g.coefficients K = 0)
    (K : Finset (Fin q)) :
    (f * g).coefficients K =
      if K = I ∪ J ∧ I ∩ J = ∅ then
        (reorderSign I J : ℝ) • (f.coefficients I * g.coefficients J)
      else 0 := by
  show (mul f g).coefficients K = _
  unfold mul
  simp only
  by_cases hKcond : K = I ∪ J ∧ I ∩ J = ∅
  · -- K = I ∪ J and supports are disjoint
    obtain ⟨hKU, hIJdisj⟩ := hKcond
    simp only [hKU, hIJdisj, and_self, ↓reduceIte]
    -- The sum reduces to the single term (I, J)
    rw [Finset.sum_eq_single I]
    · -- Show inner sum at I equals the expected term
      rw [Finset.sum_eq_single J]
      · simp only [hIJdisj, and_self, ↓reduceIte]; rfl
      · intro J' _ hJ'
        by_cases hIJ' : I ∪ J' = I ∪ J ∧ I ∩ J' = ∅
        · simp only [hIJ', hg J' hJ', mul_zero, smul_zero, ite_self]
        · simp only [hIJ', ↓reduceIte]
      · intro h; exact absurd (Finset.mem_univ J) h
    · intro I' _ hI'
      rw [Finset.sum_eq_zero]
      intro J' _
      by_cases hI'J' : I' ∪ J' = I ∪ J ∧ I' ∩ J' = ∅
      · simp only [hI'J', hf I' hI', zero_mul, smul_zero, ite_self]
      · simp only [hI'J', ↓reduceIte]
    · intro h; exact absurd (Finset.mem_univ I) h
  · -- K ≠ I ∪ J or supports overlap
    simp only [hKcond, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro I' _
    apply Finset.sum_eq_zero
    intro J' _
    split_ifs with hcond
    · obtain ⟨hU, hdisj⟩ := hcond
      by_cases hI' : I' = I
      · by_cases hJ' : J' = J
        · subst hI' hJ'
          -- This contradicts hKcond
          exact absurd ⟨hU.symm, hdisj⟩ hKcond
        · simp only [hg J' hJ', mul_zero, smul_zero]
      · simp only [hf I' hI', zero_mul, smul_zero]
    · rfl

/-- When supports overlap, the product is zero -/
theorem mul_eq_zero_of_inter_nonempty (f g : SuperDomainFunction p q)
    (I J : Finset (Fin q))
    (hf : ∀ K ≠ I, f.coefficients K = 0)
    (hg : ∀ K ≠ J, g.coefficients K = 0)
    (hIJ : I ∩ J ≠ ∅) :
    f * g = 0 := by
  ext K
  rw [mul_homogeneous_coefficients f g I J hf hg]
  simp only [hIJ, and_false, ↓reduceIte]
  rfl

/-- For homogeneous function, partialOdd vanishes if variable not in support -/
theorem partialOdd_eq_zero_of_not_mem' (a : Fin q) (f : SuperDomainFunction p q)
    (I : Finset (Fin q))
    (hf : ∀ K ≠ I, f.coefficients K = 0)
    (ha : a ∉ I) :
    partialOdd a f = 0 := by
  apply SuperDomainFunction.ext
  intro K
  show (partialOdd a f).coefficients K = zero.coefficients K
  simp only [partialOdd, zero]
  split_ifs with haK
  · -- a ∈ K: the partialOdd definition gives 0 here
    rfl
  · -- a ∉ K: coefficient at K comes from insert a K
    -- For this to be nonzero, insert a K = I
    -- But a ∉ I, so insert a K ≠ I
    have hne : insert a K ≠ I := by
      intro h
      rw [← h] at ha
      exact ha (Finset.mem_insert_self a K)
    simp only [hf (insert a K) hne, smul_zero]

/-- Support of partialOdd when variable is in support -/
theorem partialOdd_homogeneous_support (a : Fin q) (f : SuperDomainFunction p q)
    (I : Finset (Fin q))
    (hf : ∀ K ≠ I, f.coefficients K = 0)
    (ha : a ∈ I) :
    ∀ K ≠ I \ {a}, (partialOdd a f).coefficients K = 0 := by
  intro K hK
  simp only [partialOdd]
  split_ifs with haK
  · -- a ∈ K: partialOdd gives 0
    rfl
  · -- a ∉ K: the coefficient at K comes from insert a K
    -- For this to be nonzero, we need insert a K = I
    by_cases hins : insert a K = I
    · -- insert a K = I means K = I \ {a}
      have : K = I \ {a} := by
        ext x
        constructor
        · intro hx
          have hxI : x ∈ I := by rw [← hins]; exact Finset.mem_insert_of_mem hx
          refine Finset.mem_sdiff.mpr ⟨hxI, ?_⟩
          intro hxa
          simp only [Finset.mem_singleton] at hxa
          subst hxa
          exact haK hx
        · intro hx
          simp only [Finset.mem_sdiff, Finset.mem_singleton] at hx
          obtain ⟨hxI, hxa⟩ := hx
          have hxins : x ∈ insert a K := by rw [hins]; exact hxI
          rcases Finset.mem_insert.mp hxins with rfl | hxK
          · exact absurd rfl hxa
          · exact hxK
      exact absurd this hK
    · simp only [hf (insert a K) hins, smul_zero]

/-!
## Case lemmas for the Leibniz rule

The main theorem splits into cases based on:
1. Whether I ∩ J = ∅ (disjoint supports)
2. Whether a ∈ I and a ∈ J
-/

/-- Helper: union and sdiff identity for disjoint sets -/
theorem union_sdiff_of_disjoint_left {α : Type*} [DecidableEq α]
    {I J : Finset α} {a : α} (_hIJ : I ∩ J = ∅) (_ha : a ∈ I) (haJ : a ∉ J) :
    (I ∪ J) \ {a} = (I \ {a}) ∪ J := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
  constructor
  · intro ⟨hx, hxa⟩
    rcases hx with hxI | hxJ
    · left; exact ⟨hxI, hxa⟩
    · right; exact hxJ
  · intro hx
    rcases hx with ⟨hxI, hxa⟩ | hxJ
    · exact ⟨Or.inl hxI, hxa⟩
    · constructor
      · right; exact hxJ
      · intro hxa
        subst hxa
        exact haJ hxJ

/-- Helper: union and sdiff identity for disjoint sets (right version) -/
theorem union_sdiff_of_disjoint_right {α : Type*} [DecidableEq α]
    {I J : Finset α} {a : α} (_hIJ : I ∩ J = ∅) (haI : a ∉ I) (_ha : a ∈ J) :
    (I ∪ J) \ {a} = I ∪ (J \ {a}) := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
  constructor
  · intro ⟨hx, hxa⟩
    rcases hx with hxI | hxJ
    · left; exact hxI
    · right; exact ⟨hxJ, hxa⟩
  · intro hx
    rcases hx with hxI | ⟨hxJ, hxa⟩
    · constructor
      · left; exact hxI
      · intro hxa
        subst hxa
        exact haI hxI
    · exact ⟨Or.inr hxJ, hxa⟩

/-- Intersection of I \ {a} and J is empty when I ∩ J = ∅ -/
theorem sdiff_inter_empty_of_inter_empty {α : Type*} [DecidableEq α]
    {I J : Finset α} {a : α} (hIJ : I ∩ J = ∅) :
    (I \ {a}) ∩ J = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton] at hx
  obtain ⟨⟨hxI, _⟩, hxJ⟩ := hx
  have hmem : x ∈ I ∩ J := Finset.mem_inter.mpr ⟨hxI, hxJ⟩
  rw [hIJ] at hmem
  exact Finset.notMem_empty x hmem

/-- Intersection of I and J \ {a} is empty when I ∩ J = ∅ -/
theorem inter_sdiff_empty_of_inter_empty {α : Type*} [DecidableEq α]
    {I J : Finset α} {a : α} (hIJ : I ∩ J = ∅) :
    I ∩ (J \ {a}) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton] at hx
  obtain ⟨hxI, hxJ, _⟩ := hx
  have hmem : x ∈ I ∩ J := Finset.mem_inter.mpr ⟨hxI, hxJ⟩
  rw [hIJ] at hmem
  exact Finset.notMem_empty x hmem

/-- When a ∈ I, insert a (I \ {a}) = I -/
theorem insert_sdiff_self {α : Type*} [DecidableEq α]
    {I : Finset α} {a : α} (ha : a ∈ I) :
    insert a (I \ {a}) = I := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · intro hx
    rcases hx with rfl | ⟨hxI, _⟩
    · exact ha
    · exact hxI
  · intro hxI
    by_cases hxa : x = a
    · left; exact hxa
    · right; exact ⟨hxI, hxa⟩

/-- Key sign computation: filter for a in (I \ {a}) ∪ J equals filter in I \ {a} -/
theorem filter_lt_union_left {I J : Finset (Fin q)} {a : Fin q}
    (_hIJ : I ∩ J = ∅) (_ha : a ∈ I) (_haJ : a ∉ J) :
    ((I \ {a}) ∪ J).filter (· < a) = (I \ {a}).filter (· < a) ∪ J.filter (· < a) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · intro ⟨hx, hxa⟩
    rcases hx with ⟨hxI, hxna⟩ | hxJ
    · left; exact ⟨⟨hxI, hxna⟩, hxa⟩
    · right; exact ⟨hxJ, hxa⟩
  · intro hx
    rcases hx with ⟨⟨hxI, hxna⟩, hxa⟩ | ⟨hxJ, hxa⟩
    · exact ⟨Or.inl ⟨hxI, hxna⟩, hxa⟩
    · exact ⟨Or.inr hxJ, hxa⟩

/-- Filter for elements less than a in I \ {a} is the same as in I (since a is removed) -/
theorem filter_lt_sdiff_singleton {I : Finset (Fin q)} {a : Fin q} :
    (I \ {a}).filter (· < a) = I.filter (· < a) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · intro ⟨⟨hxI, _⟩, hxa⟩
    exact ⟨hxI, hxa⟩
  · intro ⟨hxI, hxa⟩
    refine ⟨⟨hxI, ?_⟩, hxa⟩
    intro hxeq
    subst hxeq
    exact absurd hxa (lt_irrefl _)

/-- Card of I \ {a} when a ∈ I -/
theorem card_sdiff_singleton_of_mem {α : Type*} [DecidableEq α]
    {I : Finset α} {a : α} (ha : a ∈ I) :
    (I \ {a}).card = I.card - 1 := by
  rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr ha)]
  simp only [Finset.card_singleton]

/-!
## Helper lemmas for overlapping case
-/

/-- When I ∩ J ≠ ∅ and a ∉ I, then I ∩ J = I ∩ (J \ {a}) ∪ (I ∩ {a}) = I ∩ (J \ {a}) (since a ∉ I) -/
theorem inter_sdiff_eq_of_not_mem_left {α : Type*} [DecidableEq α]
    {I J : Finset α} {a : α} (haI : a ∉ I) :
    I ∩ (J \ {a}) = I ∩ J := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · intro ⟨hxI, hxJ, _⟩; exact ⟨hxI, hxJ⟩
  · intro ⟨hxI, hxJ⟩
    refine ⟨hxI, hxJ, ?_⟩
    intro hxa; subst hxa; exact haI hxI

/-- When I ∩ J ≠ ∅ and a ∉ J, then (I \ {a}) ∩ J = I ∩ J -/
theorem sdiff_inter_eq_of_not_mem_right {α : Type*} [DecidableEq α]
    {I J : Finset α} {a : α} (haJ : a ∉ J) :
    (I \ {a}) ∩ J = I ∩ J := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · intro ⟨⟨hxI, _⟩, hxJ⟩; exact ⟨hxI, hxJ⟩
  · intro ⟨hxI, hxJ⟩
    refine ⟨⟨hxI, ?_⟩, hxJ⟩
    intro hxa; subst hxa; exact haJ hxJ

/-- When a ∈ I ∩ J, (I \ {a}) ∩ J = (I ∩ J) \ {a} -/
theorem sdiff_inter_eq_inter_sdiff {α : Type*} [DecidableEq α]
    {I J : Finset α} {a : α} :
    (I \ {a}) ∩ J = (I ∩ J) \ {a} := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · intro ⟨⟨hxI, hxa⟩, hxJ⟩; exact ⟨⟨hxI, hxJ⟩, hxa⟩
  · intro ⟨⟨hxI, hxJ⟩, hxa⟩; exact ⟨⟨hxI, hxa⟩, hxJ⟩

/-- Similarly: I ∩ (J \ {a}) = (I ∩ J) \ {a} -/
theorem inter_sdiff_eq_inter_sdiff {α : Type*} [DecidableEq α]
    {I J : Finset α} {a : α} :
    I ∩ (J \ {a}) = (I ∩ J) \ {a} := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · intro ⟨hxI, hxJ, hxa⟩; exact ⟨⟨hxI, hxJ⟩, hxa⟩
  · intro ⟨⟨hxI, hxJ⟩, hxa⟩; exact ⟨hxI, hxJ, hxa⟩

/-!
## Sign computations for reorderSign
-/

/-- When a ∈ I and I ∩ J = ∅, reorderSign I J = (-1)^|J.filter(·<a)| * reorderSign (I\{a}) J.
    This is because removing a from I removes inversions (a, j) for j < a in J. -/
theorem reorderSign_sdiff_singleton {I J : Finset (Fin q)} {a : Fin q}
    (haI : a ∈ I) (hIJ : I ∩ J = ∅) :
    reorderSign I J = (-1 : ℤ) ^ (J.filter (· < a)).card * reorderSign (I \ {a}) J := by
  have hIJ' : (I \ {a}) ∩ J = ∅ := sdiff_inter_empty_of_inter_empty hIJ
  simp only [reorderSign, hIJ, hIJ', ↓reduceIte]
  rw [← pow_add]
  congr 1
  -- Need: |inversions in I×J| = |J.filter(<a)| + |inversions in (I\{a})×J|
  -- The inversions in I×J are pairs (i,j) with i ∈ I, j ∈ J, j < i
  -- Split I×J into ({a}×J) ∪ ((I\{a})×J)
  have h1 : I ×ˢ J = ({a} ×ˢ J) ∪ ((I \ {a}) ×ˢ J) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_product, Finset.mem_union, Finset.mem_singleton,
               Finset.mem_sdiff]
    constructor
    · intro ⟨hxI, hyJ⟩
      by_cases hxa : x = a
      · left; exact ⟨hxa, hyJ⟩
      · right; exact ⟨⟨hxI, hxa⟩, hyJ⟩
    · intro h
      rcases h with ⟨rfl, hyJ⟩ | ⟨⟨hxI, _⟩, hyJ⟩
      · exact ⟨haI, hyJ⟩
      · exact ⟨hxI, hyJ⟩
  -- The sets {a}×J and (I\{a})×J are disjoint
  have hd : Disjoint ({a} ×ˢ J) ((I \ {a}) ×ˢ J) := by
    rw [Finset.disjoint_iff_ne]
    intro ⟨x₁, y₁⟩ h1 ⟨x₂, y₂⟩ h2
    simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_sdiff] at h1 h2
    intro heq
    have hx : x₁ = x₂ := (Prod.mk.inj heq).1
    rw [h1.1] at hx
    exact h2.1.2 hx.symm
  rw [h1, Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd)]
  -- Inversions from {a}×J: pairs (a, j) with j < a, count = |J.filter(<a)|
  have h2 : (({a} ×ˢ J).filter fun p => p.2 < p.1).card = (J.filter (· < a)).card := by
    apply Finset.card_bij (fun p _ => p.2)
    · intro ⟨x, y⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton] at hp
      simp only [Finset.mem_filter]
      exact ⟨hp.1.2, hp.1.1 ▸ hp.2⟩
    · intro ⟨x₁, y₁⟩ h₁ ⟨x₂, y₂⟩ h₂ heq
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton] at h₁ h₂
      simp only [Prod.mk.injEq]
      exact ⟨h₁.1.1.trans h₂.1.1.symm, heq⟩
    · intro y hy
      simp only [Finset.mem_filter] at hy
      exact ⟨⟨a, y⟩, by simp [hy.1, hy.2], rfl⟩
  rw [h2]

/-- Filter of (I \ {a}) ∪ J for elements < a equals union of filters -/
theorem filter_lt_sdiff_union {I J : Finset (Fin q)} {a : Fin q}
    (_hIJ : I ∩ J = ∅) :
    ((I \ {a}) ∪ J).filter (· < a) = (I \ {a}).filter (· < a) ∪ J.filter (· < a) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · intro ⟨hx, hxa⟩
    rcases hx with ⟨hxI, hxna⟩ | hxJ
    · left; exact ⟨⟨hxI, hxna⟩, hxa⟩
    · right; exact ⟨hxJ, hxa⟩
  · intro hx
    rcases hx with ⟨⟨hxI, hxna⟩, hxa⟩ | ⟨hxJ, hxa⟩
    · exact ⟨Or.inl ⟨hxI, hxna⟩, hxa⟩
    · exact ⟨Or.inr hxJ, hxa⟩

/-- The sign calculation for the Leibniz rule in case a ∈ I, a ∉ J.
    Relates the LHS sign to the RHS sign. -/
theorem leibniz_sign_eq {I J : Finset (Fin q)} {a : Fin q}
    (haI : a ∈ I) (_haJ : a ∉ J) (hIJ : I ∩ J = ∅) :
    let K := (I \ {a}) ∪ J
    ((-1 : ℤ) ^ (K.filter (· < a)).card : ℝ) * (reorderSign I J : ℝ) =
    (reorderSign (I \ {a}) J : ℝ) * ((-1 : ℤ) ^ ((I \ {a}).filter (· < a)).card : ℝ) := by
  intro K
  -- Key: K.filter(<a) = (I\{a}).filter(<a) ∪ J.filter(<a) with disjoint sets
  have hK_filter : K.filter (· < a) = (I \ {a}).filter (· < a) ∪ J.filter (· < a) :=
    filter_lt_sdiff_union hIJ
  -- The two filter sets are disjoint
  have hd : Disjoint ((I \ {a}).filter (· < a)) (J.filter (· < a)) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy heq
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hx hy
    subst heq
    have : x ∈ I ∩ J := Finset.mem_inter.mpr ⟨hx.1.1, hy.1⟩
    rw [hIJ] at this
    exact Finset.notMem_empty x this
  rw [hK_filter, Finset.card_union_of_disjoint hd]
  -- Use reorderSign_sdiff_singleton
  have _hIJ' : (I \ {a}) ∩ J = ∅ := sdiff_inter_empty_of_inter_empty hIJ
  have hsign := reorderSign_sdiff_singleton haI hIJ
  -- (-1)^(m+n) * reorderSign I J = (-1)^(m+n) * (-1)^n * reorderSign (I\{a}) J
  --                              = (-1)^(m+2n) * reorderSign (I\{a}) J
  --                              = (-1)^m * reorderSign (I\{a}) J
  -- First convert (-1)^(m+n) to (-1)^m * (-1)^n
  have hpow_add : ((-1 : ℤ) ^ ((I \ {a}).filter (· < a)).card * (-1 : ℤ) ^ (J.filter (· < a)).card : ℝ)
      = ((-1 : ℤ) ^ (((I \ {a}).filter (· < a)).card + (J.filter (· < a)).card) : ℝ) := by
    push_cast
    rw [← pow_add]
  rw [← hpow_add]
  calc ((-1 : ℤ) ^ ((I \ {a}).filter (· < a)).card * (-1 : ℤ) ^ (J.filter (· < a)).card : ℝ) *
         (reorderSign I J : ℝ)
      = ((-1 : ℤ) ^ ((I \ {a}).filter (· < a)).card * (-1 : ℤ) ^ (J.filter (· < a)).card : ℝ) *
         (((-1 : ℤ) ^ (J.filter (· < a)).card * reorderSign (I \ {a}) J : ℤ) : ℝ) := by
          rw [hsign]
    _ = ((-1 : ℤ) ^ ((I \ {a}).filter (· < a)).card : ℝ) *
         (((-1 : ℤ) ^ (J.filter (· < a)).card * (-1 : ℤ) ^ (J.filter (· < a)).card : ℤ) : ℝ) *
         (reorderSign (I \ {a}) J : ℝ) := by push_cast; ring
    _ = ((-1 : ℤ) ^ ((I \ {a}).filter (· < a)).card : ℝ) *
         (((-1 : ℤ) ^ (2 * (J.filter (· < a)).card) : ℤ) : ℝ) *
         (reorderSign (I \ {a}) J : ℝ) := by
          congr 2
          rw [← pow_add]
          ring_nf
    _ = ((-1 : ℤ) ^ ((I \ {a}).filter (· < a)).card : ℝ) * (1 : ℝ) *
         (reorderSign (I \ {a}) J : ℝ) := by
          congr 2
          have : ((-1 : ℤ) ^ (2 * (J.filter (· < a)).card) : ℤ) = 1 := by
            rw [pow_mul]; simp only [neg_one_sq, one_pow]
          simp only [this, Int.cast_one]
    _ = (reorderSign (I \ {a}) J : ℝ) * ((-1 : ℤ) ^ ((I \ {a}).filter (· < a)).card : ℝ) := by ring

/-- When a ∈ J and I ∩ J = ∅, reorderSign I J = (-1)^|I.filter(·<a)| * reorderSign I (J\{a}).
    This is because removing a from J removes inversions (i, a) for i > a in I. -/
theorem reorderSign_sdiff_singleton_right {I J : Finset (Fin q)} {a : Fin q}
    (haJ : a ∈ J) (hIJ : I ∩ J = ∅) :
    reorderSign I J = (-1 : ℤ) ^ (I.filter (a < ·)).card * reorderSign I (J \ {a}) := by
  have hIJ' : I ∩ (J \ {a}) = ∅ := inter_sdiff_empty_of_inter_empty hIJ
  simp only [reorderSign, hIJ, hIJ', ↓reduceIte]
  rw [← pow_add]
  congr 1
  -- Need: |inversions in I×J| = |I.filter(a<·)| + |inversions in I×(J\{a})|
  -- The inversions in I×J are pairs (i,j) with i ∈ I, j ∈ J, j < i
  -- Split I×J into (I×{a}) ∪ (I×(J\{a}))
  have h1 : I ×ˢ J = (I ×ˢ {a}) ∪ (I ×ˢ (J \ {a})) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_product, Finset.mem_union, Finset.mem_singleton,
               Finset.mem_sdiff]
    constructor
    · intro ⟨hxI, hyJ⟩
      by_cases hya : y = a
      · left; exact ⟨hxI, hya⟩
      · right; exact ⟨hxI, ⟨hyJ, hya⟩⟩
    · intro h
      rcases h with ⟨hxI, rfl⟩ | ⟨hxI, ⟨hyJ, _⟩⟩
      · exact ⟨hxI, haJ⟩
      · exact ⟨hxI, hyJ⟩
  -- The sets I×{a} and I×(J\{a}) are disjoint
  have hd : Disjoint (I ×ˢ {a}) (I ×ˢ (J \ {a})) := by
    rw [Finset.disjoint_iff_ne]
    intro ⟨x₁, y₁⟩ h1 ⟨x₂, y₂⟩ h2
    simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_sdiff] at h1 h2
    intro heq
    have hy : y₁ = y₂ := (Prod.mk.inj heq).2
    rw [h1.2] at hy
    exact h2.2.2 hy.symm
  rw [h1, Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd)]
  -- Inversions from I×{a}: pairs (i, a) with a < i, count = |I.filter(a<·)|
  have h2 : ((I ×ˢ {a}).filter fun p => p.2 < p.1).card = (I.filter (a < ·)).card := by
    apply Finset.card_bij (fun p _ => p.1)
    · intro ⟨x, y⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton] at hp
      simp only [Finset.mem_filter]
      exact ⟨hp.1.1, hp.1.2 ▸ hp.2⟩
    · intro ⟨x₁, y₁⟩ h₁ ⟨x₂, y₂⟩ h₂ heq
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton] at h₁ h₂
      simp only [Prod.mk.injEq]
      exact ⟨heq, h₁.1.2.trans h₂.1.2.symm⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx
      exact ⟨⟨x, a⟩, by simp [hx.1, hx.2], rfl⟩
  rw [h2]

/-- Filter of I ∪ (J \ {a}) for elements < a equals union of filters -/
theorem filter_lt_union_sdiff {I J : Finset (Fin q)} {a : Fin q}
    (_hIJ : I ∩ J = ∅) :
    (I ∪ (J \ {a})).filter (· < a) = I.filter (· < a) ∪ (J \ {a}).filter (· < a) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · intro ⟨hx, hxa⟩
    rcases hx with hxI | ⟨hxJ, hxna⟩
    · left; exact ⟨hxI, hxa⟩
    · right; exact ⟨⟨hxJ, hxna⟩, hxa⟩
  · intro hx
    rcases hx with ⟨hxI, hxa⟩ | ⟨⟨hxJ, hxna⟩, hxa⟩
    · exact ⟨Or.inl hxI, hxa⟩
    · exact ⟨Or.inr ⟨hxJ, hxna⟩, hxa⟩

/-- Filter for < a in J \ {a} equals filter in J (since a is not < a) -/
theorem filter_lt_sdiff_singleton_right {J : Finset (Fin q)} {a : Fin q} :
    (J \ {a}).filter (· < a) = J.filter (· < a) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · intro ⟨⟨hxJ, _⟩, hxa⟩
    exact ⟨hxJ, hxa⟩
  · intro ⟨hxJ, hxa⟩
    refine ⟨⟨hxJ, ?_⟩, hxa⟩
    intro hxeq
    subst hxeq
    exact absurd hxa (lt_irrefl _)

/-- The sign calculation for the Leibniz rule in case a ∉ I, a ∈ J.
    Relates the LHS sign to the RHS sign. -/
theorem leibniz_sign_eq_right {I J : Finset (Fin q)} {a : Fin q}
    (haI : a ∉ I) (_haJ : a ∈ J) (hIJ : I ∩ J = ∅) :
    let K := I ∪ (J \ {a})
    ((-1 : ℤ) ^ (K.filter (· < a)).card : ℝ) * (reorderSign I J : ℝ) =
    ((-1 : ℤ) ^ I.card : ℝ) * (reorderSign I (J \ {a}) : ℝ) *
    ((-1 : ℤ) ^ ((J \ {a}).filter (· < a)).card : ℝ) := by
  intro K
  -- K.filter(<a) = I.filter(<a) ∪ (J\{a}).filter(<a) with disjoint sets
  have hK_filter : K.filter (· < a) = I.filter (· < a) ∪ (J \ {a}).filter (· < a) :=
    filter_lt_union_sdiff hIJ
  -- The two filter sets are disjoint
  have hd : Disjoint (I.filter (· < a)) ((J \ {a}).filter (· < a)) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy heq
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hx hy
    subst heq
    have : x ∈ I ∩ J := Finset.mem_inter.mpr ⟨hx.1, hy.1.1⟩
    rw [hIJ] at this
    exact Finset.notMem_empty x this
  rw [hK_filter, Finset.card_union_of_disjoint hd]
  -- Use reorderSign_sdiff_singleton_right
  have hIJ' : I ∩ (J \ {a}) = ∅ := inter_sdiff_empty_of_inter_empty hIJ
  have hsign := reorderSign_sdiff_singleton_right _haJ hIJ
  -- The key insight: we need to relate I.filter(<a) to I.card via parity
  -- Actually, the formula involves I.filter(a<·) from reorderSign_sdiff_singleton_right
  -- We need: (-1)^|I.filter(<a)| * (-1)^|J.filter(<a)| * reorderSign I J
  --        = (-1)^|I| * reorderSign I (J\{a}) * (-1)^|(J\{a}).filter(<a)|
  -- Use: reorderSign I J = (-1)^|I.filter(a<·)| * reorderSign I (J\{a})
  -- And: |I.filter(<a)| + |I.filter(a<·)| + (1 if a ∈ I else 0) = |I|
  -- Since a ∉ I: |I.filter(<a)| + |I.filter(a<·)| = |I|
  have hI_partition : (I.filter (· < a)).card + (I.filter (a < ·)).card = I.card := by
    -- Since a ∉ I, we can partition I into {x < a} and {x > a}
    have hd' : Disjoint (I.filter (· < a)) (I.filter (a < ·)) := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy heq
      simp only [Finset.mem_filter] at hx hy
      subst heq
      exact absurd (lt_trans hx.2 hy.2) (lt_irrefl _)
    have hunion : I = I.filter (· < a) ∪ I.filter (a < ·) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hx
        by_cases hxa : x < a
        · left; exact ⟨hx, hxa⟩
        · right
          refine ⟨hx, ?_⟩
          rcases lt_trichotomy x a with hlt | heq | hgt
          · exact absurd hlt hxa
          · subst heq; exact absurd hx haI
          · exact hgt
      · intro hx
        rcases hx with ⟨hx, _⟩ | ⟨hx, _⟩ <;> exact hx
    calc (I.filter (· < a)).card + (I.filter (a < ·)).card
        = (I.filter (· < a) ∪ I.filter (a < ·)).card := (Finset.card_union_of_disjoint hd').symm
      _ = I.card := by rw [← hunion]
  -- Now compute
  have hpow_add : ((-1 : ℤ) ^ (I.filter (· < a)).card * (-1 : ℤ) ^ ((J \ {a}).filter (· < a)).card : ℝ)
      = ((-1 : ℤ) ^ ((I.filter (· < a)).card + ((J \ {a}).filter (· < a)).card) : ℝ) := by
    push_cast
    rw [← pow_add]
  rw [← hpow_add]
  -- Use filter_lt_sdiff_singleton_right to simplify (J \ {a}).filter (· < a) = J.filter (· < a)
  rw [filter_lt_sdiff_singleton_right]
  calc ((-1 : ℤ) ^ (I.filter (· < a)).card * (-1 : ℤ) ^ (J.filter (· < a)).card : ℝ) *
         (reorderSign I J : ℝ)
      = ((-1 : ℤ) ^ (I.filter (· < a)).card * (-1 : ℤ) ^ (J.filter (· < a)).card : ℝ) *
         (((-1 : ℤ) ^ (I.filter (a < ·)).card * reorderSign I (J \ {a}) : ℤ) : ℝ) := by
          rw [hsign]
    _ = ((-1 : ℤ) ^ (I.filter (· < a)).card * (-1 : ℤ) ^ (I.filter (a < ·)).card : ℝ) *
         ((-1 : ℤ) ^ (J.filter (· < a)).card : ℝ) *
         (reorderSign I (J \ {a}) : ℝ) := by push_cast; ring
    _ = ((-1 : ℤ) ^ ((I.filter (· < a)).card + (I.filter (a < ·)).card) : ℝ) *
         ((-1 : ℤ) ^ (J.filter (· < a)).card : ℝ) *
         (reorderSign I (J \ {a}) : ℝ) := by
          congr 2
          push_cast
          rw [← pow_add]
    _ = ((-1 : ℤ) ^ I.card : ℝ) *
         ((-1 : ℤ) ^ (J.filter (· < a)).card : ℝ) *
         (reorderSign I (J \ {a}) : ℝ) := by rw [hI_partition]
    _ = ((-1 : ℤ) ^ I.card : ℝ) * (reorderSign I (J \ {a}) : ℝ) *
         ((-1 : ℤ) ^ (J.filter (· < a)).card : ℝ) := by ring

/-!
## Sign cancellation for overlapping case I ∩ J = {a}
-/

/-- Key lemma: when a ∈ I, we have |I.filter(<a)| + |I.filter(a<·)| = |I| - 1.
    This is because I partitions into {x < a} ∪ {a} ∪ {x > a}. -/
theorem filter_card_partition {I : Finset (Fin q)} {a : Fin q} (ha : a ∈ I) :
    (I.filter (· < a)).card + (I.filter (a < ·)).card = I.card - 1 := by
  -- Partition I into three parts: {x < a}, {a}, {x > a}
  have hd1 : Disjoint (I.filter (· < a)) (I.filter (a < ·)) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy heq
    simp only [Finset.mem_filter] at hx hy
    subst heq
    exact absurd (lt_trans hx.2 hy.2) (lt_irrefl _)
  have ha_not_in : a ∉ I.filter (· < a) ∪ I.filter (a < ·) := by
    simp only [Finset.mem_union, Finset.mem_filter, lt_self_iff_false, and_false, or_self,
               not_false_eq_true]
  have hunion : I = I.filter (· < a) ∪ I.filter (a < ·) ∪ {a} := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hx
      rcases lt_trichotomy x a with hlt | heq | hgt
      · left; left; exact ⟨hx, hlt⟩
      · right; exact heq
      · left; right; exact ⟨hx, hgt⟩
    · intro hx
      rcases hx with (⟨hx, _⟩ | ⟨hx, _⟩) | rfl
      · exact hx
      · exact hx
      · exact ha
  have hcard_I : I.card = (I.filter (· < a) ∪ I.filter (a < ·)).card + 1 := by
    conv_lhs => rw [hunion]
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr ha_not_in)]
    simp only [Finset.card_singleton]
  calc (I.filter (· < a)).card + (I.filter (a < ·)).card
      = (I.filter (· < a) ∪ I.filter (a < ·)).card := (Finset.card_union_of_disjoint hd1).symm
    _ = I.card - 1 := by omega

/-- Sign cancellation identity when I ∩ J = {a}.
    The two terms in the Leibniz rule cancel:
    reorderSign(I\{a}, J) * (-1)^|I.filter(<a)| + (-1)^|I| * reorderSign(I, J\{a}) * (-1)^|J.filter(<a)| = 0 -/
theorem leibniz_sign_cancel {I J : Finset (Fin q)} {a : Fin q}
    (haI : a ∈ I) (haJ : a ∈ J) (hIJ : I ∩ J = {a}) :
    (reorderSign (I \ {a}) J : ℝ) * ((-1 : ℤ) ^ ((I \ {a}).filter (· < a)).card : ℝ) +
    ((-1 : ℤ) ^ I.card : ℝ) * (reorderSign I (J \ {a}) : ℝ) *
    ((-1 : ℤ) ^ ((J \ {a}).filter (· < a)).card : ℝ) = 0 := by
  -- First establish that both products have disjoint supports
  have hdisj1 : (I \ {a}) ∩ J = ∅ := by
    rw [sdiff_inter_eq_inter_sdiff, hIJ]
    simp only [Finset.sdiff_self]
  have hdisj2 : I ∩ (J \ {a}) = ∅ := by
    rw [inter_sdiff_eq_inter_sdiff, hIJ]
    simp only [Finset.sdiff_self]
  -- Simplify the filters (since a is not < a)
  rw [filter_lt_sdiff_singleton, filter_lt_sdiff_singleton_right]
  -- Let C = reorderSign (I\{a}) (J\{a})
  -- reorderSign (I\{a}) J = (-1)^|(I\{a}).filter(a<·)| * C = (-1)^|I.filter(a<·)| * C
  -- reorderSign I (J\{a}) = (-1)^|(J\{a}).filter(<a)| * C = (-1)^|J.filter(<a)| * C
  -- Term1 = reorderSign(I\{a}, J) * (-1)^|I.filter(<a)| = C * (-1)^{|I| - 1}
  -- Term2 = (-1)^|I| * reorderSign(I, J\{a}) * (-1)^|J.filter(<a)| = C * (-1)^|I|
  -- Sum = C * ((-1)^{|I|-1} + (-1)^|I|) = 0
  have hdisj3 : (I \ {a}) ∩ (J \ {a}) = ∅ := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton, Finset.notMem_empty,
               iff_false, not_and, and_imp]
    intro hxI hxa hxJ _
    have hmem : x ∈ I ∩ J := Finset.mem_inter.mpr ⟨hxI, hxJ⟩
    rw [hIJ, Finset.mem_singleton] at hmem
    exact hxa hmem
  -- Get hsign1' using reorderSign_sdiff_singleton_right
  have hsign_IaJ : reorderSign (I \ {a}) J =
      (-1 : ℤ) ^ ((I \ {a}).filter (a < ·)).card * reorderSign (I \ {a}) (J \ {a}) :=
    reorderSign_sdiff_singleton_right haJ hdisj1
  -- Get hsign2' using reorderSign_sdiff_singleton
  have hsign_IJa : reorderSign I (J \ {a}) =
      (-1 : ℤ) ^ ((J \ {a}).filter (· < a)).card * reorderSign (I \ {a}) (J \ {a}) :=
    reorderSign_sdiff_singleton haI hdisj2
  -- Simplify filters
  have hfilter1 : (I \ {a}).filter (a < ·) = I.filter (a < ·) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · intro ⟨⟨hxI, _⟩, hxa⟩; exact ⟨hxI, hxa⟩
    · intro ⟨hxI, hxa⟩
      refine ⟨⟨hxI, ?_⟩, hxa⟩
      intro hxeq; subst hxeq; exact absurd hxa (lt_irrefl _)
  have hfilter2 : (J \ {a}).filter (· < a) = J.filter (· < a) := filter_lt_sdiff_singleton_right
  rw [hfilter1] at hsign_IaJ
  rw [hfilter2] at hsign_IJa
  -- Now substitute
  let C := reorderSign (I \ {a}) (J \ {a})
  have hC1 : (reorderSign (I \ {a}) J : ℝ) = ((-1 : ℤ) ^ (I.filter (a < ·)).card : ℝ) * (C : ℝ) := by
    simp only [hsign_IaJ]; push_cast; ring
  have hC2 : (reorderSign I (J \ {a}) : ℝ) = ((-1 : ℤ) ^ (J.filter (· < a)).card : ℝ) * (C : ℝ) := by
    simp only [hsign_IJa]; push_cast; ring
  rw [hC1, hC2]
  -- Term1 = (-1)^A_I * C * (-1)^k_I = C * (-1)^(A_I + k_I) = C * (-1)^(|I|-1)
  -- Term2 = (-1)^|I| * (-1)^k_J * C * (-1)^k_J = C * (-1)^|I| * (-1)^(2k_J) = C * (-1)^|I|
  have hcard := filter_card_partition haI
  -- (-1)^(k_I + A_I) = (-1)^(|I| - 1)
  have hpow1 : ((-1 : ℤ) ^ (I.filter (· < a)).card : ℝ) * ((-1 : ℤ) ^ (I.filter (a < ·)).card : ℝ) =
      ((-1 : ℤ) ^ (I.card - 1) : ℝ) := by
    push_cast
    rw [← pow_add, hcard]
  -- (-1)^(2k_J) = 1
  have hpow2 : ((-1 : ℤ) ^ (J.filter (· < a)).card : ℝ) * ((-1 : ℤ) ^ (J.filter (· < a)).card : ℝ) =
      (1 : ℝ) := by
    push_cast
    rw [← pow_add, ← two_mul, pow_mul]
    simp only [neg_one_sq, one_pow]
  -- Combine
  calc ((-1 : ℤ) ^ (I.filter (a < ·)).card : ℝ) * (C : ℝ) *
         ((-1 : ℤ) ^ (I.filter (· < a)).card : ℝ) +
       ((-1 : ℤ) ^ I.card : ℝ) * (((-1 : ℤ) ^ (J.filter (· < a)).card : ℝ) * (C : ℝ)) *
         ((-1 : ℤ) ^ (J.filter (· < a)).card : ℝ)
      = (C : ℝ) * (((-1 : ℤ) ^ (I.filter (· < a)).card : ℝ) *
          ((-1 : ℤ) ^ (I.filter (a < ·)).card : ℝ)) +
        (C : ℝ) * ((-1 : ℤ) ^ I.card : ℝ) *
          (((-1 : ℤ) ^ (J.filter (· < a)).card : ℝ) * ((-1 : ℤ) ^ (J.filter (· < a)).card : ℝ)) := by ring
    _ = (C : ℝ) * ((-1 : ℤ) ^ (I.card - 1) : ℝ) + (C : ℝ) * ((-1 : ℤ) ^ I.card : ℝ) * 1 := by
        rw [hpow1, hpow2]
    _ = (C : ℝ) * (((-1 : ℤ) ^ (I.card - 1) : ℝ) + ((-1 : ℤ) ^ I.card : ℝ)) := by ring
    _ = (C : ℝ) * 0 := by
        congr 1
        -- (-1)^(n-1) + (-1)^n = 0 for any n ≥ 1
        have hn : 0 < I.card := Finset.card_pos.mpr ⟨a, haI⟩
        have hsub : I.card - 1 + 1 = I.card := Nat.sub_add_cancel hn
        have heq : ((-1 : ℤ) ^ I.card : ℝ) = ((-1 : ℤ) ^ (I.card - 1) : ℝ) * (-1 : ℝ) := by
          have h : ((-1 : ℤ) ^ I.card) = ((-1 : ℤ) ^ (I.card - 1)) * (-1 : ℤ) := by
            conv_lhs => rw [← hsub, pow_succ]
          exact_mod_cast h
        rw [heq]
        ring
    _ = 0 := by ring

end Supermanifolds
