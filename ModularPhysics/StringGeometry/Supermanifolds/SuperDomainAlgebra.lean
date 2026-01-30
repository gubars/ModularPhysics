/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.
-/
import ModularPhysics.StringGeometry.Supermanifolds.Supermanifolds
import ModularPhysics.StringGeometry.Supermanifolds.SuperRingCat

/-!
# SuperDomainFunction as a SuperAlgebra

This file establishes `SuperDomainFunction p q` as a proper `SuperAlgebra ℝ` instance,
connecting the coordinate-based definition to the abstract algebraic framework.

## Main Results

* `SuperDomainFunction.instRing` - Ring structure on super domain functions
* `SuperDomainFunction.instAlgebra` - ℝ-algebra structure
* `SuperDomainFunction.toSuperAlgebra` - The `SuperAlgebra ℝ` instance

## Mathematical Background

Elements of the structure sheaf of ℝ^{p|q} are:
  f(x,θ) = Σ_I f_I(x) θ^I

where I ranges over subsets of {1,...,q}. The parity of a monomial θ^I is |I| mod 2.
-/

namespace Supermanifolds

open SuperDomainFunction

variable {p q : ℕ}

/-!
## Ring Instance for SuperDomainFunction
-/

namespace SuperDomainFunction

/-- Extensionality for SuperDomainFunction -/
@[ext]
theorem ext' {f g : SuperDomainFunction p q} (h : ∀ I x, f.coefficients I x = g.coefficients I x) :
    f = g := by
  cases f; cases g
  simp only [mk.injEq]
  funext I
  exact SmoothFunction.ext (h I)

/-- Accessing coefficients of add -/
@[simp]
theorem add_coefficients (f g : SuperDomainFunction p q) (I : Finset (Fin q)) (x : Fin p → ℝ) :
    (add f g).coefficients I x = f.coefficients I x + g.coefficients I x := rfl

/-- Accessing coefficients of zero -/
@[simp]
theorem zero_coefficients (I : Finset (Fin q)) (x : Fin p → ℝ) :
    (zero : SuperDomainFunction p q).coefficients I x = 0 := rfl

/-- Accessing coefficients of neg -/
@[simp]
theorem neg_coefficients (f : SuperDomainFunction p q) (I : Finset (Fin q)) (x : Fin p → ℝ) :
    (neg f).coefficients I x = -(f.coefficients I x) := rfl

/-- Accessing coefficients of one -/
@[simp]
theorem one_coefficients (I : Finset (Fin q)) (x : Fin p → ℝ) :
    (one : SuperDomainFunction p q).coefficients I x = if I = ∅ then 1 else 0 := by
  simp only [one]; split_ifs <;> rfl

/-- Accessing coefficients of smul -/
@[simp]
theorem smul_coefficients (c : ℝ) (f : SuperDomainFunction p q) (I : Finset (Fin q)) (x : Fin p → ℝ) :
    (smul c f).coefficients I x = c * f.coefficients I x := rfl

/-- Evaluation of a finite sum of SmoothFunctions distributes -/
theorem sum_apply {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → SmoothFunction p) (x : Fin p → ℝ) :
    (s.sum f) x = s.sum fun i => (f i) x := by
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, SmoothFunction.add_apply, ih]

/-- Accessing coefficients of mul -/
theorem mul_coefficients (f g : SuperDomainFunction p q) (I : Finset (Fin q)) (x : Fin p → ℝ) :
    (mul f g).coefficients I x =
      Finset.univ.sum fun J => Finset.univ.sum fun K =>
        if J ∪ K = I ∧ J ∩ K = ∅ then reorderSign J K * f.coefficients J x * g.coefficients K x
        else 0 := by
  simp only [mul]
  rw [sum_apply, Finset.sum_congr rfl]
  intro J _
  rw [sum_apply, Finset.sum_congr rfl]
  intro K _
  split_ifs with h
  · simp only [SmoothFunction.smul_apply, SmoothFunction.mul_apply]
    ring
  · rfl

/-- Subtraction of super domain functions -/
def sub (f g : SuperDomainFunction p q) : SuperDomainFunction p q :=
  ⟨fun I => f.coefficients I - g.coefficients I⟩

@[simp]
theorem sub_coefficients (f g : SuperDomainFunction p q) (I : Finset (Fin q)) (x : Fin p → ℝ) :
    (sub f g).coefficients I x = f.coefficients I x - g.coefficients I x := rfl

instance instSub : Sub (SuperDomainFunction p q) := ⟨sub⟩

/-- Integer scalar multiplication (for AddCommGroup) -/
def zsmul' (n : ℤ) (f : SuperDomainFunction p q) : SuperDomainFunction p q :=
  ⟨fun I => n • f.coefficients I⟩

@[simp]
theorem zsmul'_coefficients (n : ℤ) (f : SuperDomainFunction p q) (I : Finset (Fin q)) (x : Fin p → ℝ) :
    (zsmul' n f).coefficients I x = n * f.coefficients I x := rfl

/-- Natural number scalar multiplication -/
def nsmul' (n : ℕ) (f : SuperDomainFunction p q) : SuperDomainFunction p q :=
  ⟨fun I => n • f.coefficients I⟩

@[simp]
theorem nsmul'_coefficients (n : ℕ) (f : SuperDomainFunction p q) (I : Finset (Fin q)) (x : Fin p → ℝ) :
    (nsmul' n f).coefficients I x = n * f.coefficients I x := rfl

instance instAddCommGroup : AddCommGroup (SuperDomainFunction p q) where
  add := add
  add_assoc f g h := by
    apply ext'; intro I x
    show (f.coefficients I x + g.coefficients I x) + h.coefficients I x =
         f.coefficients I x + (g.coefficients I x + h.coefficients I x)
    ring
  zero := zero
  zero_add f := by
    apply ext'; intro I x
    show (0 : ℝ) + f.coefficients I x = f.coefficients I x
    ring
  add_zero f := by
    apply ext'; intro I x
    show f.coefficients I x + (0 : ℝ) = f.coefficients I x
    ring
  neg := neg
  neg_add_cancel f := by
    apply ext'; intro I x
    show -(f.coefficients I x) + f.coefficients I x = (0 : ℝ)
    ring
  add_comm f g := by
    apply ext'; intro I x
    show f.coefficients I x + g.coefficients I x = g.coefficients I x + f.coefficients I x
    ring
  nsmul := nsmul'
  nsmul_zero f := by
    apply ext'; intro I x
    show (0 : ℕ) * f.coefficients I x = (0 : ℝ)
    simp
  nsmul_succ n f := by
    apply ext'; intro I x
    show (n + 1 : ℕ) * f.coefficients I x = (n : ℕ) * f.coefficients I x + f.coefficients I x
    push_cast; ring
  zsmul := zsmul'
  zsmul_zero' f := by
    apply ext'; intro I x
    show (0 : ℤ) * f.coefficients I x = (0 : ℝ)
    simp
  zsmul_succ' n f := by
    apply ext'; intro I x
    show (↑n.succ : ℝ) * f.coefficients I x = (↑n : ℝ) * f.coefficients I x + f.coefficients I x
    push_cast; ring
  zsmul_neg' n f := by
    apply ext'; intro I x
    show (↑(Int.negSucc n) : ℝ) * f.coefficients I x = -((↑n.succ : ℝ) * f.coefficients I x)
    push_cast; ring
  sub := sub
  sub_eq_add_neg f g := by
    apply ext'; intro I x
    show f.coefficients I x - g.coefficients I x = f.coefficients I x + -(g.coefficients I x)
    ring

/-- The key identity for supercommutativity:
    inversions(I,J) + inversions(J,I) = |I| * |J|
    Therefore: reorderSign I J * reorderSign J I = (-1)^{|I|*|J|} -/
theorem reorderSign_swap (I J : Finset (Fin q)) (h : I ∩ J = ∅) :
    reorderSign I J * reorderSign J I = (-1 : ℤ) ^ (I.card * J.card) := by
  simp only [reorderSign, h, Finset.inter_comm J I, ↓reduceIte]
  rw [← pow_add]
  congr 1
  -- inversions(I,J) + inversions(J,I) = |I| * |J|
  -- An inversion in (I,J) is a pair (i,j) with i∈I, j∈J, j<i
  -- An inversion in (J,I) is a pair (j,i) with j∈J, i∈I, i<j
  -- Together they count all pairs (i,j) with i∈I, j∈J (since i≠j by disjointness)
  have h1 : ((I ×ˢ J).filter fun p => p.2 < p.1).card +
            ((J ×ˢ I).filter fun p => p.2 < p.1).card =
            (I ×ˢ J).card := by
    -- The filters partition I ×ˢ J (via the bijection that swaps components)
    have hbij : ((J ×ˢ I).filter fun p => p.2 < p.1) =
                ((I ×ˢ J).filter fun p => p.1 < p.2).map
                  ⟨fun p => (p.2, p.1), fun _ _ h => Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1⟩ := by
      ext ⟨j, i⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_map,
                 Function.Embedding.coeFn_mk, Prod.exists]
      constructor
      · intro ⟨⟨hj, hi⟩, hlt⟩
        exact ⟨i, j, ⟨⟨hi, hj⟩, hlt⟩, rfl⟩
      · intro ⟨i', j', ⟨⟨hi', hj'⟩, hlt⟩, heq⟩
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hj'_eq, hi'_eq⟩ := heq
        subst hj'_eq hi'_eq
        exact ⟨⟨hj', hi'⟩, hlt⟩
    rw [hbij, Finset.card_map]
    -- Now show: filter(<) card + filter(>) card = total card
    have hpart : (I ×ˢ J).filter (fun p => p.2 < p.1) ∪ (I ×ˢ J).filter (fun p => p.1 < p.2) =
                 I ×ˢ J := by
      ext ⟨i, j⟩
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product]
      constructor
      · intro h; rcases h with ⟨⟨hi, hj⟩, _⟩ | ⟨⟨hi, hj⟩, _⟩ <;> exact ⟨hi, hj⟩
      · intro ⟨hi, hj⟩
        -- Since I ∩ J = ∅ and i ∈ I, j ∈ J, we have i ≠ j
        have hne : i ≠ j := by
          intro heq; subst heq
          have : i ∈ I ∩ J := Finset.mem_inter.mpr ⟨hi, hj⟩
          rw [h] at this; simp at this
        rcases lt_trichotomy j i with hlt | heq | hgt
        · left; exact ⟨⟨hi, hj⟩, hlt⟩
        · exact absurd heq hne.symm
        · right; exact ⟨⟨hi, hj⟩, hgt⟩
    have hdisj : Disjoint ((I ×ˢ J).filter fun p => p.2 < p.1)
                         ((I ×ˢ J).filter fun p => p.1 < p.2) := by
      rw [Finset.disjoint_filter]
      intro ⟨i, j⟩ _ hlt
      exact not_lt.mpr (le_of_lt hlt)
    rw [← Finset.card_union_of_disjoint hdisj, hpart]
  rw [h1, Finset.card_product]

/-- Supercommutativity for monomials: swapping θ^I and θ^J introduces sign (-1)^{|I||J|}.
    This is the coefficient-level version of supercommutativity. -/
theorem mul_comm_monomial (f g : SuperDomainFunction p q) (I J K : Finset (Fin q))
    (hf : ∀ I', I' ≠ I → f.coefficients I' = 0)
    (hg : ∀ J', J' ≠ J → g.coefficients J' = 0) (x : Fin p → ℝ) :
    (mul f g).coefficients K x = (-1 : ℤ) ^ (I.card * J.card) * (mul g f).coefficients K x := by
  simp only [mul_coefficients]
  -- LHS: only (I, J) contributes if I ∪ J = K and I ∩ J = ∅
  -- RHS: only (J, I) contributes with the same condition
  rw [Finset.sum_eq_single I, Finset.sum_eq_single J]
  rotate_left
  · intro J' _ hJ'; rw [hg J' hJ']; simp
  · intro h; exact absurd (Finset.mem_univ J) h
  · intro I' _ hI'; rw [Finset.sum_eq_zero]; intro J' _
    rw [hf I' hI']; simp
  · intro h; exact absurd (Finset.mem_univ I) h

  rw [Finset.sum_eq_single J, Finset.sum_eq_single I]
  rotate_left
  · intro I' _ hI'; rw [hf I' hI']; simp
  · intro h; exact absurd (Finset.mem_univ I) h
  · intro J' _ hJ'; rw [Finset.sum_eq_zero]; intro I' _
    rw [hg J' hJ']; simp
  · intro h; exact absurd (Finset.mem_univ J) h

  -- Now: single term on each side
  -- Use by_cases for clearer control
  by_cases hIJ : I ∪ J = K ∧ I ∩ J = ∅ <;> by_cases hJI : J ∪ I = K ∧ J ∩ I = ∅
  · -- Both hold: use reorderSign_swap
    simp only [hIJ, hJI, and_self, ↓reduceIte]
    obtain ⟨hIJ_u, hIJ_d⟩ := hIJ
    obtain ⟨hJI_u, hJI_d⟩ := hJI
    have hd : I ∩ J = ∅ := hIJ_d
    have hd' : J ∩ I = ∅ := by rw [Finset.inter_comm]; exact hd
    have hsign := reorderSign_swap I J hd
    -- reorderSign values are ±1 (when disjoint), so (reorderSign)^2 = 1
    have h1 : reorderSign J I * reorderSign J I = 1 := by
      simp only [reorderSign, hd', ↓reduceIte]
      have hpow : ∀ n : ℕ, ((-1 : ℤ) ^ n) * ((-1 : ℤ) ^ n) = 1 := fun n => by
        rw [← pow_add, ← two_mul]
        calc (-1 : ℤ) ^ (2 * n) = ((-1 : ℤ) ^ 2) ^ n := by rw [pow_mul]
          _ = 1 ^ n := by norm_num
          _ = 1 := one_pow n
      exact hpow _
    have hsign_eq : (reorderSign I J : ℝ) = (-1 : ℤ) ^ (I.card * J.card) * reorderSign J I := by
      have h2 : reorderSign I J = (-1 : ℤ) ^ (I.card * J.card) * reorderSign J I := by
        calc reorderSign I J = reorderSign I J * (reorderSign J I * reorderSign J I) := by rw [h1]; ring
          _ = (reorderSign I J * reorderSign J I) * reorderSign J I := by ring
          _ = (-1 : ℤ) ^ (I.card * J.card) * reorderSign J I := by rw [hsign]
      exact_mod_cast h2
    rw [hsign_eq]
    ring
  · -- hIJ but ¬hJI: impossible since conditions are symmetric
    obtain ⟨hIJ_u, hIJ_d⟩ := hIJ
    exfalso; apply hJI
    exact ⟨by rw [Finset.union_comm]; exact hIJ_u, by rw [Finset.inter_comm]; exact hIJ_d⟩
  · -- ¬hIJ but hJI: impossible
    obtain ⟨hJI_u, hJI_d⟩ := hJI
    exfalso; apply hIJ
    exact ⟨by rw [Finset.union_comm]; exact hJI_u, by rw [Finset.inter_comm]; exact hJI_d⟩
  · -- Both false
    simp only [hIJ, ↓reduceIte, hJI, mul_zero]

-- mul_assoc' is defined after reorderSign_assoc (see below)

/-- Left distributivity -/
theorem left_distrib' (f g h : SuperDomainFunction p q) : mul f (add g h) = add (mul f g) (mul f h) := by
  apply ext'; intro I x
  rw [mul_coefficients, add_coefficients, mul_coefficients, mul_coefficients]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro J _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro K _
  split_ifs with hcond
  · simp only [add, SmoothFunction.add_apply]
    ring
  · ring

/-- Right distributivity -/
theorem right_distrib' (f g h : SuperDomainFunction p q) : mul (add f g) h = add (mul f h) (mul g h) := by
  apply ext'; intro I x
  rw [mul_coefficients, add_coefficients, mul_coefficients, mul_coefficients]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro J _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro K _
  split_ifs with hcond
  · simp only [add, SmoothFunction.add_apply]
    ring
  · ring

/-- reorderSign with empty left set is 1 -/
theorem reorderSign_empty_left (I : Finset (Fin q)) : reorderSign ∅ I = 1 := by
  simp only [reorderSign, Finset.empty_inter, ↓reduceIte, Finset.empty_product,
    Finset.filter_empty, Finset.card_empty, pow_zero]

/-- reorderSign with empty right set is 1 -/
theorem reorderSign_empty_right (I : Finset (Fin q)) : reorderSign I ∅ = 1 := by
  simp only [reorderSign, Finset.inter_empty, ↓reduceIte, Finset.product_empty,
    Finset.filter_empty, Finset.card_empty, pow_zero]

/-- When sets overlap, reorderSign is 0 -/
theorem reorderSign_overlap {I J : Finset (Fin q)} (h : ¬(I ∩ J = ∅)) : reorderSign I J = 0 := by
  simp only [reorderSign, h, ↓reduceIte]

/-- Sign associativity: sign(A∪B, C) * sign(A, B) = sign(A, B∪C) * sign(B, C) for disjoint A,B,C.
    This follows from the fact that both sides count the same total number of inversions. -/
theorem reorderSign_assoc {A B C : Finset (Fin q)}
    (hAB : A ∩ B = ∅) (hBC : B ∩ C = ∅) (hAC : A ∩ C = ∅) :
    reorderSign (A ∪ B) C * reorderSign A B = reorderSign A (B ∪ C) * reorderSign B C := by
  -- Both sides count inversions in the triple (A, B, C):
  -- Type 1: (a, b) with a ∈ A, b ∈ B, b < a
  -- Type 2: (a, c) with a ∈ A, c ∈ C, c < a
  -- Type 3: (b, c) with b ∈ B, c ∈ C, c < b
  --
  -- LHS = sign(A∪B, C) * sign(A, B)
  --     = (-1)^{types 2 + 3} * (-1)^{type 1}
  --     = (-1)^{types 1 + 2 + 3}
  --
  -- RHS = sign(A, B∪C) * sign(B, C)
  --     = (-1)^{types 1 + 2} * (-1)^{type 3}
  --     = (-1)^{types 1 + 2 + 3}
  have hABC : (A ∪ B) ∩ C = ∅ := by
    rw [Finset.union_inter_distrib_right, hAC, hBC, Finset.empty_union]
  have hABC' : A ∩ (B ∪ C) = ∅ := by
    rw [Finset.inter_union_distrib_left, hAB, hAC, Finset.union_empty]
  simp only [reorderSign, hAB, hBC, hABC, hABC', ↓reduceIte]
  rw [← pow_add, ← pow_add]
  congr 1
  -- Need: |{(x,y) ∈ (A∪B)×C : y<x}| + |{(x,y) ∈ A×B : y<x}|
  --     = |{(x,y) ∈ A×(B∪C) : y<x}| + |{(x,y) ∈ B×C : y<x}|
  -- This follows from set decomposition and disjointness
  have h1 : (A ∪ B) ×ˢ C = (A ×ˢ C) ∪ (B ×ˢ C) := Finset.union_product
  have h2 : A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := Finset.product_union
  -- The pairs (A×C) and (B×C) are disjoint (first components from disjoint sets)
  have hd1 : Disjoint (A ×ˢ C) (B ×ˢ C) := by
    rw [Finset.disjoint_iff_ne]
    intro ⟨a, c₁⟩ ha ⟨b, c₂⟩ hb
    simp only [Finset.mem_product] at ha hb
    intro heq
    have hab : a = b := Prod.mk.inj heq |>.1
    subst hab
    have hmem : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨ha.1, hb.1⟩
    rw [hAB] at hmem
    simp at hmem
  -- The pairs (A×B) and (A×C) are disjoint (second components from disjoint sets)
  have hd2 : Disjoint (A ×ˢ B) (A ×ˢ C) := by
    rw [Finset.disjoint_iff_ne]
    intro ⟨a₁, b⟩ hab ⟨a₂, c⟩ hac
    simp only [Finset.mem_product] at hab hac
    intro heq
    have hbc : b = c := Prod.mk.inj heq |>.2
    subst hbc
    have hmem : b ∈ B ∩ C := Finset.mem_inter.mpr ⟨hab.2, hac.2⟩
    rw [hBC] at hmem
    simp at hmem
  -- Filtering preserves disjointness
  have hd1' : Disjoint ((A ×ˢ C).filter fun p => p.2 < p.1)
                       ((B ×ˢ C).filter fun p => p.2 < p.1) :=
    Finset.disjoint_filter_filter hd1
  have hd2' : Disjoint ((A ×ˢ B).filter fun p => p.2 < p.1)
                       ((A ×ˢ C).filter fun p => p.2 < p.1) :=
    Finset.disjoint_filter_filter hd2
  rw [h1, h2, Finset.filter_union, Finset.filter_union]
  rw [Finset.card_union_of_disjoint hd1', Finset.card_union_of_disjoint hd2']
  ring

/-- Helper: expand the 4-fold sum for LHS of associativity -/
private theorem mul_assoc_lhs_expand (f g h : SuperDomainFunction p q) (I : Finset (Fin q)) (x : Fin p → ℝ) :
    (Finset.univ.sum fun L => Finset.univ.sum fun C =>
      if L ∪ C = I ∧ L ∩ C = ∅ then
        (reorderSign L C : ℝ) * (Finset.univ.sum fun J => Finset.univ.sum fun K =>
          if J ∪ K = L ∧ J ∩ K = ∅ then reorderSign J K * f.coefficients J x * g.coefficients K x else 0)
        * h.coefficients C x
      else 0) =
    Finset.univ.sum fun L => Finset.univ.sum fun C => Finset.univ.sum fun J => Finset.univ.sum fun K =>
      if L ∪ C = I ∧ L ∩ C = ∅ ∧ J ∪ K = L ∧ J ∩ K = ∅ then
        (reorderSign L C : ℝ) * reorderSign J K * f.coefficients J x * g.coefficients K x * h.coefficients C x
      else 0 := by
  apply Finset.sum_congr rfl; intro L _
  apply Finset.sum_congr rfl; intro C _
  split_ifs with hLC
  · -- hLC holds: expand the product into the sum
    -- LHS: (sign_LC * (∑_J ∑_K ...)) * h_C
    -- Need: ∑_J ∑_K (sign_LC * sign_JK * f_J * g_K * h_C)
    calc (reorderSign L C : ℝ) * (Finset.univ.sum fun J => Finset.univ.sum fun K =>
          if J ∪ K = L ∧ J ∩ K = ∅ then reorderSign J K * f.coefficients J x * g.coefficients K x else 0)
        * h.coefficients C x
      = (Finset.univ.sum fun J => Finset.univ.sum fun K =>
          if J ∪ K = L ∧ J ∩ K = ∅ then
            (reorderSign L C : ℝ) * reorderSign J K * f.coefficients J x * g.coefficients K x else 0)
        * h.coefficients C x := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro J _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro K _
          split_ifs <;> ring
      _ = Finset.univ.sum fun J => Finset.univ.sum fun K =>
          (if J ∪ K = L ∧ J ∩ K = ∅ then
            (reorderSign L C : ℝ) * reorderSign J K * f.coefficients J x * g.coefficients K x else 0)
          * h.coefficients C x := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl; intro J _
            rw [Finset.sum_mul]
      _ = Finset.univ.sum fun J => Finset.univ.sum fun K =>
          if J ∪ K = L ∧ J ∩ K = ∅ then
            (reorderSign L C : ℝ) * reorderSign J K * f.coefficients J x * g.coefficients K x * h.coefficients C x
          else 0 := by
            apply Finset.sum_congr rfl; intro J _
            apply Finset.sum_congr rfl; intro K _
            split_ifs <;> ring
      _ = _ := by
            apply Finset.sum_congr rfl; intro J _
            apply Finset.sum_congr rfl; intro K _
            simp only [hLC, true_and]
  · -- hLC false: both sides are 0
    symm
    apply Finset.sum_eq_zero; intro J _
    apply Finset.sum_eq_zero; intro K _
    rw [if_neg]
    intro hcond
    exact hLC ⟨hcond.1, hcond.2.1⟩

/-- Helper: expand the 4-fold sum for RHS of associativity -/
private theorem mul_assoc_rhs_expand (f g h : SuperDomainFunction p q) (I : Finset (Fin q)) (x : Fin p → ℝ) :
    (Finset.univ.sum fun A => Finset.univ.sum fun N =>
      if A ∪ N = I ∧ A ∩ N = ∅ then
        (reorderSign A N : ℝ) * f.coefficients A x *
        (Finset.univ.sum fun B => Finset.univ.sum fun C =>
          if B ∪ C = N ∧ B ∩ C = ∅ then reorderSign B C * g.coefficients B x * h.coefficients C x else 0)
      else 0) =
    Finset.univ.sum fun A => Finset.univ.sum fun N => Finset.univ.sum fun B => Finset.univ.sum fun C =>
      if A ∪ N = I ∧ A ∩ N = ∅ ∧ B ∪ C = N ∧ B ∩ C = ∅ then
        (reorderSign A N : ℝ) * reorderSign B C * f.coefficients A x * g.coefficients B x * h.coefficients C x
      else 0 := by
  apply Finset.sum_congr rfl; intro A _
  apply Finset.sum_congr rfl; intro N _
  split_ifs with hAN
  · -- hAN holds: expand the product into the sum
    -- LHS: sign_AN * f_A * (∑_B ∑_C ...)
    -- Need: ∑_B ∑_C (sign_AN * sign_BC * f_A * g_B * h_C)
    calc (reorderSign A N : ℝ) * f.coefficients A x *
        (Finset.univ.sum fun B => Finset.univ.sum fun C =>
          if B ∪ C = N ∧ B ∩ C = ∅ then reorderSign B C * g.coefficients B x * h.coefficients C x else 0)
      = Finset.univ.sum fun B => Finset.univ.sum fun C =>
          (reorderSign A N : ℝ) * f.coefficients A x *
          (if B ∪ C = N ∧ B ∩ C = ∅ then reorderSign B C * g.coefficients B x * h.coefficients C x else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro B _
            rw [Finset.mul_sum]
      _ = Finset.univ.sum fun B => Finset.univ.sum fun C =>
          if B ∪ C = N ∧ B ∩ C = ∅ then
            (reorderSign A N : ℝ) * reorderSign B C * f.coefficients A x * g.coefficients B x * h.coefficients C x
          else 0 := by
            apply Finset.sum_congr rfl; intro B _
            apply Finset.sum_congr rfl; intro C _
            split_ifs <;> ring
      _ = _ := by
            apply Finset.sum_congr rfl; intro B _
            apply Finset.sum_congr rfl; intro C _
            simp only [hAN, true_and]
  · -- hAN false: both sides are 0
    symm
    apply Finset.sum_eq_zero; intro B _
    apply Finset.sum_eq_zero; intro C _
    rw [if_neg]
    intro hcond
    exact hAN ⟨hcond.1, hcond.2.1⟩

/-- Multiplication is associative.
    Both sides sum over triples (A, B, C) with A ∪ B ∪ C = I, pairwise disjoint.
    The sign identity reorderSign_assoc shows the coefficients match. -/
theorem mul_assoc' (f g h : SuperDomainFunction p q) : mul (mul f g) h = mul f (mul g h) := by
  apply ext'; intro I x
  simp only [mul_coefficients]
  rw [mul_assoc_lhs_expand, mul_assoc_rhs_expand]

  -- Define the canonical triple sum that both sides equal
  let canonicalSum :=
    Finset.univ.sum fun A => Finset.univ.sum fun B => Finset.univ.sum fun C =>
      if A ∪ B ∪ C = I ∧ A ∩ B = ∅ ∧ B ∩ C = ∅ ∧ A ∩ C = ∅ then
        (reorderSign (A ∪ B) C * reorderSign A B : ℝ) *
        f.coefficients A x * g.coefficients B x * h.coefficients C x
      else 0

  -- LHS (4-fold sum) equals canonical sum by reducing L to J ∪ K
  have lhs_eq : (Finset.univ.sum fun L => Finset.univ.sum fun C => Finset.univ.sum fun J => Finset.univ.sum fun K =>
      if L ∪ C = I ∧ L ∩ C = ∅ ∧ J ∪ K = L ∧ J ∩ K = ∅ then
        (reorderSign L C : ℝ) * reorderSign J K * f.coefficients J x * g.coefficients K x * h.coefficients C x
      else 0) = canonicalSum := by
    simp only [canonicalSum]
    -- Reorder sums: L, C, J, K -> J, K, C, L
    calc _ = Finset.univ.sum fun C => Finset.univ.sum fun L => Finset.univ.sum fun J => Finset.univ.sum fun K =>
        if L ∪ C = I ∧ L ∩ C = ∅ ∧ J ∪ K = L ∧ J ∩ K = ∅ then
          (reorderSign L C : ℝ) * reorderSign J K * f.coefficients J x * g.coefficients K x * h.coefficients C x
        else 0 := Finset.sum_comm
      _ = Finset.univ.sum fun C => Finset.univ.sum fun J => Finset.univ.sum fun L => Finset.univ.sum fun K =>
        if L ∪ C = I ∧ L ∩ C = ∅ ∧ J ∪ K = L ∧ J ∩ K = ∅ then
          (reorderSign L C : ℝ) * reorderSign J K * f.coefficients J x * g.coefficients K x * h.coefficients C x
        else 0 := by apply Finset.sum_congr rfl; intro C _; exact Finset.sum_comm
      _ = Finset.univ.sum fun C => Finset.univ.sum fun J => Finset.univ.sum fun K => Finset.univ.sum fun L =>
        if L ∪ C = I ∧ L ∩ C = ∅ ∧ J ∪ K = L ∧ J ∩ K = ∅ then
          (reorderSign L C : ℝ) * reorderSign J K * f.coefficients J x * g.coefficients K x * h.coefficients C x
        else 0 := by
          apply Finset.sum_congr rfl; intro C _
          apply Finset.sum_congr rfl; intro J _
          exact Finset.sum_comm
      _ = Finset.univ.sum fun J => Finset.univ.sum fun C => Finset.univ.sum fun K => Finset.univ.sum fun L =>
        if L ∪ C = I ∧ L ∩ C = ∅ ∧ J ∪ K = L ∧ J ∩ K = ∅ then
          (reorderSign L C : ℝ) * reorderSign J K * f.coefficients J x * g.coefficients K x * h.coefficients C x
        else 0 := Finset.sum_comm
      _ = Finset.univ.sum fun J => Finset.univ.sum fun K => Finset.univ.sum fun C => Finset.univ.sum fun L =>
        if L ∪ C = I ∧ L ∩ C = ∅ ∧ J ∪ K = L ∧ J ∩ K = ∅ then
          (reorderSign L C : ℝ) * reorderSign J K * f.coefficients J x * g.coefficients K x * h.coefficients C x
        else 0 := by apply Finset.sum_congr rfl; intro J _; exact Finset.sum_comm
      _ = Finset.univ.sum fun J => Finset.univ.sum fun K => Finset.univ.sum fun C =>
        if (J ∪ K) ∪ C = I ∧ (J ∪ K) ∩ C = ∅ ∧ J ∩ K = ∅ then
          (reorderSign (J ∪ K) C : ℝ) * reorderSign J K * f.coefficients J x * g.coefficients K x * h.coefficients C x
        else 0 := by
          apply Finset.sum_congr rfl; intro J _
          apply Finset.sum_congr rfl; intro K _
          apply Finset.sum_congr rfl; intro C _
          rw [Finset.sum_eq_single (J ∪ K)]
          rotate_left
          · intro L _ hL
            split_ifs with hcond
            · exact absurd hcond.2.2.1 (Ne.symm hL)
            · rfl
          · intro habs; exact absurd (Finset.mem_univ _) habs
          -- Now L = J ∪ K, simplify the condition
          simp only [true_and]
      _ = _ := by
          apply Finset.sum_congr rfl; intro J _
          apply Finset.sum_congr rfl; intro K _
          apply Finset.sum_congr rfl; intro C _
          -- Show conditions are equivalent
          by_cases hvalid : J ∪ K ∪ C = I ∧ J ∩ K = ∅ ∧ K ∩ C = ∅ ∧ J ∩ C = ∅
          · obtain ⟨hJKC, hJK, hKC, hJC⟩ := hvalid
            have hLC_d : (J ∪ K) ∩ C = ∅ := by
              rw [Finset.union_inter_distrib_right, hJC, hKC, Finset.empty_union]
            simp only [hJKC, hLC_d, hJK, hKC, hJC, and_self, ↓reduceIte]
          · have hLHS_false : ¬((J ∪ K) ∪ C = I ∧ (J ∪ K) ∩ C = ∅ ∧ J ∩ K = ∅) := by
              intro ⟨hU, hD, hJK⟩
              apply hvalid
              refine ⟨hU, hJK, ?_, ?_⟩
              · rw [← Finset.disjoint_iff_inter_eq_empty] at hD ⊢
                exact Finset.disjoint_of_subset_left Finset.subset_union_right hD
              · rw [← Finset.disjoint_iff_inter_eq_empty] at hD ⊢
                exact Finset.disjoint_of_subset_left Finset.subset_union_left hD
            simp only [hvalid, hLHS_false, ↓reduceIte]

  -- RHS (4-fold sum) equals canonical sum by reducing N to B ∪ C
  have rhs_eq : (Finset.univ.sum fun A => Finset.univ.sum fun N => Finset.univ.sum fun B => Finset.univ.sum fun C =>
      if A ∪ N = I ∧ A ∩ N = ∅ ∧ B ∪ C = N ∧ B ∩ C = ∅ then
        (reorderSign A N : ℝ) * reorderSign B C * f.coefficients A x * g.coefficients B x * h.coefficients C x
      else 0) = canonicalSum := by
    simp only [canonicalSum]
    apply Finset.sum_congr rfl; intro A _
    -- Reorder sums: N, B, C -> B, C, N
    calc _ = Finset.univ.sum fun B => Finset.univ.sum fun N => Finset.univ.sum fun C =>
        if A ∪ N = I ∧ A ∩ N = ∅ ∧ B ∪ C = N ∧ B ∩ C = ∅ then
          (reorderSign A N : ℝ) * reorderSign B C * f.coefficients A x * g.coefficients B x * h.coefficients C x
        else 0 := Finset.sum_comm
      _ = Finset.univ.sum fun B => Finset.univ.sum fun C => Finset.univ.sum fun N =>
        if A ∪ N = I ∧ A ∩ N = ∅ ∧ B ∪ C = N ∧ B ∩ C = ∅ then
          (reorderSign A N : ℝ) * reorderSign B C * f.coefficients A x * g.coefficients B x * h.coefficients C x
        else 0 := by apply Finset.sum_congr rfl; intro B _; exact Finset.sum_comm
      _ = Finset.univ.sum fun B => Finset.univ.sum fun C =>
        if A ∪ (B ∪ C) = I ∧ A ∩ (B ∪ C) = ∅ ∧ B ∩ C = ∅ then
          (reorderSign A (B ∪ C) : ℝ) * reorderSign B C * f.coefficients A x * g.coefficients B x * h.coefficients C x
        else 0 := by
          apply Finset.sum_congr rfl; intro B _
          apply Finset.sum_congr rfl; intro C _
          rw [Finset.sum_eq_single (B ∪ C)]
          rotate_left
          · intro N _ hN
            split_ifs with hcond
            · exact absurd hcond.2.2.1 (Ne.symm hN)
            · rfl
          · intro habs; exact absurd (Finset.mem_univ _) habs
          -- Now N = B ∪ C, simplify the condition
          simp only [true_and]
      _ = _ := by
          apply Finset.sum_congr rfl; intro B _
          apply Finset.sum_congr rfl; intro C _
          -- Show conditions are equivalent and signs match
          by_cases hvalid : A ∪ B ∪ C = I ∧ A ∩ B = ∅ ∧ B ∩ C = ∅ ∧ A ∩ C = ∅
          · obtain ⟨hABC, hAB, hBC, hAC⟩ := hvalid
            have hAN_u : A ∪ (B ∪ C) = I := by
              calc A ∪ (B ∪ C) = A ∪ B ∪ C := (Finset.union_assoc A B C).symm
                _ = I := hABC
            have hAN_d : A ∩ (B ∪ C) = ∅ := by
              rw [Finset.inter_union_distrib_left, hAB, hAC, Finset.empty_union]
            simp only [hAN_u, hAN_d, hBC, hABC, hAB, hAC, and_self, ↓reduceIte]
            -- Use reorderSign_assoc
            have hsign := reorderSign_assoc hAB hBC hAC
            calc (reorderSign A (B ∪ C) : ℝ) * reorderSign B C * f.coefficients A x * g.coefficients B x * h.coefficients C x
                = (reorderSign A (B ∪ C) * reorderSign B C : ℤ) * (f.coefficients A x * g.coefficients B x * h.coefficients C x) := by push_cast; ring
              _ = (reorderSign (A ∪ B) C * reorderSign A B : ℤ) * (f.coefficients A x * g.coefficients B x * h.coefficients C x) := by rw [← hsign]
              _ = (reorderSign (A ∪ B) C * reorderSign A B : ℝ) * f.coefficients A x * g.coefficients B x * h.coefficients C x := by push_cast; ring
          · have hRHS_false : ¬(A ∪ (B ∪ C) = I ∧ A ∩ (B ∪ C) = ∅ ∧ B ∩ C = ∅) := by
              intro ⟨hU, hD, hBC⟩
              apply hvalid
              refine ⟨?_, ?_, hBC, ?_⟩
              · calc A ∪ B ∪ C = A ∪ (B ∪ C) := Finset.union_assoc A B C
                  _ = I := hU
              · rw [← Finset.disjoint_iff_inter_eq_empty] at hD ⊢
                exact Finset.disjoint_of_subset_right Finset.subset_union_left hD
              · rw [← Finset.disjoint_iff_inter_eq_empty] at hD ⊢
                exact Finset.disjoint_of_subset_right Finset.subset_union_right hD
            simp only [hvalid, hRHS_false, ↓reduceIte]

  rw [lhs_eq, rhs_eq]

/-- One is a left identity. -/
theorem one_mul' (f : SuperDomainFunction p q) : mul one f = f := by
  apply ext'; intro I x
  rw [mul_coefficients]
  -- The only nonzero term is when J = ∅ and K = I
  rw [Finset.sum_eq_single ∅]
  · rw [Finset.sum_eq_single I]
    · simp only [Finset.empty_union, Finset.empty_inter, and_self, ↓reduceIte,
        one_coefficients, reorderSign_empty_left, Int.cast_one, one_mul]
    · intro K _ hK
      simp only [Finset.empty_union, Finset.empty_inter]
      split_ifs with h
      · exact absurd h.1 hK
      · rfl
    · intro h; exact absurd (Finset.mem_univ I) h
  · intro J _ hJ
    rw [Finset.sum_eq_zero]; intro K _
    simp only [one_coefficients, hJ, ↓reduceIte]
    split_ifs <;> ring
  · intro h; exact absurd (Finset.mem_univ ∅) h

/-- One is a right identity. -/
theorem mul_one' (f : SuperDomainFunction p q) : mul f one = f := by
  apply ext'; intro I x
  rw [mul_coefficients]
  -- The only nonzero term is when J = I and K = ∅
  rw [Finset.sum_eq_single I]
  · rw [Finset.sum_eq_single ∅]
    · simp only [Finset.union_empty, Finset.inter_empty, and_self, ↓reduceIte,
        one_coefficients, reorderSign_empty_right, Int.cast_one]
      ring
    · intro K _ hK
      -- hK : K ≠ ∅, so one.coefficients K = 0
      simp only [one_coefficients, hK, ↓reduceIte]
      -- Now: if I ∪ K = I ∧ I ∩ K = ∅ then _ * 0 else 0 = 0
      split_ifs <;> ring
    · intro h; exact absurd (Finset.mem_univ ∅) h
  · intro J _ hJ
    rw [Finset.sum_eq_zero]; intro K _
    simp only [one_coefficients]
    split_ifs with hcond hK_empty
    · -- hcond : J ∪ K = I ∧ J ∩ K = ∅, hK_empty : K = ∅
      -- With K = ∅, J ∪ ∅ = J = I, contradicting hJ
      simp only [hK_empty, Finset.union_empty, Finset.inter_empty] at hcond
      exact absurd hcond.1 hJ
    · -- hcond : J ∪ K = I ∧ J ∩ K = ∅, K ≠ ∅: gives _ * 0 = 0
      ring
    · -- ¬(J ∪ K = I ∧ J ∩ K = ∅): gives 0 = 0
      rfl
  · intro h; exact absurd (Finset.mem_univ I) h

/-- Zero times anything is zero -/
theorem zero_mul' (f : SuperDomainFunction p q) : mul zero f = zero := by
  apply ext'; intro I x
  rw [mul_coefficients, zero_coefficients]
  apply Finset.sum_eq_zero; intro J _
  apply Finset.sum_eq_zero; intro K _
  split_ifs with h
  · simp only [zero_coefficients]; ring
  · rfl

/-- Anything times zero is zero -/
theorem mul_zero' (f : SuperDomainFunction p q) : mul f zero = zero := by
  apply ext'; intro I x
  rw [mul_coefficients, zero_coefficients]
  apply Finset.sum_eq_zero; intro J _
  apply Finset.sum_eq_zero; intro K _
  split_ifs with h
  · simp only [zero_coefficients]; ring
  · rfl

/-- Power function for the ring instance -/
def npow' : ℕ → SuperDomainFunction p q → SuperDomainFunction p q
  | 0, _ => one
  | n + 1, f => mul (npow' n f) f

instance instRing : Ring (SuperDomainFunction p q) where
  mul := mul
  mul_assoc := mul_assoc'
  one := one
  one_mul := one_mul'
  mul_one := mul_one'
  left_distrib := left_distrib'
  right_distrib := right_distrib'
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  npow := npow'
  npow_zero _ := rfl
  npow_succ _ _ := rfl

/-!
## Algebra Instance
-/

/-- Helper: the toFun of algebraMap' -/
private def algebraMap'_fun (c : ℝ) : SuperDomainFunction p q :=
  ⟨fun I => if I = ∅ then SmoothFunction.const c else SmoothFunction.const 0⟩

@[simp]
private theorem algebraMap'_fun_coeffs (c : ℝ) (I : Finset (Fin q)) :
    (algebraMap'_fun c : SuperDomainFunction p q).coefficients I =
      if I = ∅ then SmoothFunction.const c else SmoothFunction.const 0 := rfl

@[simp]
private theorem algebraMap'_fun_coeffs_empty (c : ℝ) (x : Fin p → ℝ) :
    (algebraMap'_fun c : SuperDomainFunction p q).coefficients ∅ x = c := by
  simp only [algebraMap'_fun_coeffs, ↓reduceIte, SmoothFunction.const_apply]

@[simp]
private theorem algebraMap'_fun_coeffs_nonempty (c : ℝ) (I : Finset (Fin q)) (hI : I ≠ ∅) (x : Fin p → ℝ) :
    (algebraMap'_fun c : SuperDomainFunction p q).coefficients I x = 0 := by
  simp only [algebraMap'_fun_coeffs, hI, ↓reduceIte, SmoothFunction.const_apply]

/-- The algebra map from ℝ to SuperDomainFunction p q embeds constants -/
def algebraMap' : ℝ →+* SuperDomainFunction p q where
  toFun := algebraMap'_fun
  map_one' := by
    apply ext'; intro I x
    show (algebraMap'_fun 1).coefficients I x = (one : SuperDomainFunction p q).coefficients I x
    simp only [algebraMap'_fun_coeffs, SuperDomainFunction.one]
    split_ifs with h
    · simp only [SmoothFunction.const_apply, SmoothFunction.one_apply]
    · simp only [SmoothFunction.const_apply, SmoothFunction.zero_apply]
  map_mul' a b := by
    apply ext'; intro I x
    show (algebraMap'_fun (a * b)).coefficients I x =
         (mul (algebraMap'_fun a) (algebraMap'_fun b)).coefficients I x
    simp only [algebraMap'_fun_coeffs]
    rw [mul_coefficients]
    by_cases hI : I = ∅
    · subst hI
      simp only [↓reduceIte, SmoothFunction.const_apply]
      rw [Finset.sum_eq_single ∅, Finset.sum_eq_single ∅]
      · simp only [Finset.empty_union, Finset.empty_inter, and_self, ↓reduceIte,
          reorderSign, algebraMap'_fun_coeffs, SmoothFunction.const_apply]
        simp only [Finset.product_empty, Finset.filter_empty, Finset.card_empty, pow_zero,
          Int.cast_one, one_mul]
      · intro K _ hK
        simp only [Finset.empty_union, Finset.empty_inter]
        split_ifs with h
        · exact absurd h.1 hK
        · rfl
      · intro h; exact absurd (Finset.mem_univ ∅) h
      · intro J _ hJ
        rw [Finset.sum_eq_zero]; intro K _
        simp only [algebraMap'_fun_coeffs, hJ, ↓reduceIte, SmoothFunction.const_apply]
        split_ifs <;> ring
      · intro h; exact absurd (Finset.mem_univ ∅) h
    · simp only [hI, ↓reduceIte, SmoothFunction.const_apply]
      rw [Finset.sum_eq_zero]; intro J _
      rw [Finset.sum_eq_zero]; intro K _
      split_ifs with h
      · obtain ⟨h1, h2⟩ := h
        by_cases hJ : J = ∅
        · -- J = ∅, so K = I ≠ ∅, hence b's coefficient is 0
          subst hJ; simp only [Finset.empty_union] at h1
          have hK : K ≠ ∅ := by rw [h1]; exact hI
          simp only [algebraMap'_fun_coeffs, hK, ↓reduceIte, SmoothFunction.const_apply]; ring
        · -- J ≠ ∅, so a's coefficient is 0
          simp only [algebraMap'_fun_coeffs, hJ, ↓reduceIte, SmoothFunction.const_apply]; ring
      · rfl
  map_zero' := by
    apply ext'; intro I x
    show (algebraMap'_fun 0).coefficients I x = (zero : SuperDomainFunction p q).coefficients I x
    simp only [algebraMap'_fun_coeffs, SuperDomainFunction.zero]
    split_ifs with h
    · simp only [SmoothFunction.const_apply, SmoothFunction.zero_apply]
    · simp only [SmoothFunction.const_apply, SmoothFunction.zero_apply]
  map_add' a b := by
    apply ext'; intro I x
    show (algebraMap'_fun (a + b)).coefficients I x =
         (add (algebraMap'_fun a) (algebraMap'_fun b)).coefficients I x
    simp only [algebraMap'_fun_coeffs, SuperDomainFunction.add, SmoothFunction.add_apply]
    split_ifs with h
    · simp only [SmoothFunction.const_apply]
    · simp only [SmoothFunction.const_apply, add_zero]

instance instAlgebra : Algebra ℝ (SuperDomainFunction p q) where
  algebraMap := algebraMap'
  smul_def' c f := by
    -- c • f = algebraMap' c * f
    -- The only nonzero term in the product sum is (∅, I) giving c * f_I
    apply ext'; intro I x
    show (smul c f).coefficients I x = (mul (algebraMap'_fun c) f).coefficients I x
    rw [mul_coefficients]
    simp only [smul_coefficients]
    rw [Finset.sum_eq_single ∅]
    · rw [Finset.sum_eq_single I]
      · simp only [Finset.empty_union, Finset.empty_inter, and_self, ↓reduceIte,
          reorderSign_empty_left, Int.cast_one, one_mul, algebraMap'_fun_coeffs_empty]
      · intro K _ hK
        simp only [Finset.empty_union, Finset.empty_inter]
        split_ifs with h
        · exact absurd h.1 hK
        · rfl
      · intro h; exact absurd (Finset.mem_univ I) h
    · intro J _ hJ
      rw [Finset.sum_eq_zero]; intro K _
      simp only [algebraMap'_fun_coeffs, hJ, ↓reduceIte, SmoothFunction.const_apply]
      split_ifs <;> ring
    · intro h; exact absurd (Finset.mem_univ ∅) h
  commutes' c f := by
    -- algebraMap' c * f = f * algebraMap' c (commutativity with scalars)
    -- Both products equal c * f_I for each coefficient I
    apply ext'; intro I x
    show (mul (algebraMap'_fun c) f).coefficients I x = (mul f (algebraMap'_fun c)).coefficients I x
    rw [mul_coefficients, mul_coefficients]
    -- LHS: only J = ∅ contributes (algebraMap' has coefficient only at ∅)
    -- RHS: only K = ∅ contributes
    rw [Finset.sum_eq_single ∅]
    · rw [Finset.sum_eq_single I]
      -- Main term LHS: sign(∅,I) * c * f_I = c * f_I
      · rw [Finset.sum_eq_single I]
        · rw [Finset.sum_eq_single ∅]
          -- Main term RHS: sign(I,∅) * f_I * c = f_I * c = c * f_I
          · simp only [Finset.empty_union, Finset.empty_inter, and_self, ↓reduceIte,
              Finset.union_empty, Finset.inter_empty, reorderSign_empty_left,
              reorderSign_empty_right, Int.cast_one, one_mul, algebraMap'_fun_coeffs_empty]
            ring
          -- RHS: K ≠ ∅, so algebraMap' coefficient is 0
          · intro K _ hK
            simp only [algebraMap'_fun_coeffs, hK, ↓reduceIte]
            split_ifs <;> simp only [SmoothFunction.const_apply]; ring
          · intro h; exact absurd (Finset.mem_univ ∅) h
        -- RHS: J ≠ I, so the condition J ∪ K = I with K = ∅ implies J = I, contradiction
        · intro J _ hJ
          rw [Finset.sum_eq_zero]; intro K _
          simp only [algebraMap'_fun_coeffs]
          split_ifs with hcond hK_empty
          · -- condition holds and K = ∅, so J ∪ ∅ = J = I, contradiction with hJ
            rw [hK_empty, Finset.union_empty] at hcond
            exact absurd hcond.1 hJ
          · -- condition holds but K ≠ ∅, so algebraMap' K = 0
            simp only [SmoothFunction.const_apply]; ring
          · -- condition fails
            rfl
        · intro h; exact absurd (Finset.mem_univ I) h
      -- LHS: K ≠ I, so the condition ∅ ∪ K = I implies K = I, contradiction
      · intro K _ hK
        simp only [Finset.empty_union, Finset.empty_inter]
        split_ifs with h
        · exact absurd h.1 hK
        · rfl
      · intro h; exact absurd (Finset.mem_univ I) h
    -- LHS: J ≠ ∅, so algebraMap' J = 0
    · intro J _ hJ
      rw [Finset.sum_eq_zero]; intro K _
      simp only [algebraMap'_fun_coeffs, hJ, ↓reduceIte, SmoothFunction.const_apply]
      split_ifs <;> ring
    · intro h; exact absurd (Finset.mem_univ ∅) h

/-!
## SuperAlgebra Instance
-/

/-- The even submodule: functions supported on even-cardinality multi-indices -/
def evenSubmodule : Submodule ℝ (SuperDomainFunction p q) where
  carrier := { f | ∀ I, I.card % 2 = 1 → f.coefficients I = 0 }
  add_mem' {f g} hf hg I hI := by
    simp only [Set.mem_setOf_eq] at hf hg
    show (add f g).coefficients I = 0
    simp only [SuperDomainFunction.add, hf I hI, hg I hI, add_zero]
  zero_mem' I _ := rfl
  smul_mem' c f hf I hI := by
    simp only [Set.mem_setOf_eq] at hf
    show (smul c f).coefficients I = 0
    simp only [SuperDomainFunction.smul, hf I hI, smul_zero]

/-- The odd submodule: functions supported on odd-cardinality multi-indices -/
def oddSubmodule : Submodule ℝ (SuperDomainFunction p q) where
  carrier := { f | ∀ I, I.card % 2 = 0 → f.coefficients I = 0 }
  add_mem' {f g} hf hg I hI := by
    simp only [Set.mem_setOf_eq] at hf hg
    show (add f g).coefficients I = 0
    simp only [SuperDomainFunction.add, hf I hI, hg I hI, add_zero]
  zero_mem' I _ := rfl
  smul_mem' c f hf I hI := by
    simp only [Set.mem_setOf_eq] at hf
    show (smul c f).coefficients I = 0
    simp only [SuperDomainFunction.smul, hf I hI, smul_zero]

/-- Every function decomposes into even and odd parts -/
theorem direct_sum_decomp (f : SuperDomainFunction p q) :
    ∃ (f₀ : evenSubmodule (p := p) (q := q)) (f₁ : oddSubmodule (p := p) (q := q)),
    f = f₀.val + f₁.val := by
  let f_even : SuperDomainFunction p q :=
    ⟨fun I => if I.card % 2 = 0 then f.coefficients I else 0⟩
  let f_odd : SuperDomainFunction p q :=
    ⟨fun I => if I.card % 2 = 1 then f.coefficients I else 0⟩
  have h_even : f_even ∈ evenSubmodule := fun I hI => by
    simp only [f_even]
    have : I.card % 2 ≠ 0 := by omega
    simp only [this, ↓reduceIte]
  have h_odd : f_odd ∈ oddSubmodule := fun I hI => by
    simp only [f_odd]
    have : I.card % 2 ≠ 1 := by omega
    simp only [this, ↓reduceIte]
  use ⟨f_even, h_even⟩, ⟨f_odd, h_odd⟩
  apply ext'; intro I x
  show f.coefficients I x = (add f_even f_odd).coefficients I x
  rw [add_coefficients]
  simp only [f_even, f_odd]
  by_cases h : I.card % 2 = 0
  · simp only [h, ↓reduceIte, (by decide : (0 : ℕ) ≠ 1), SmoothFunction.zero_apply, add_zero]
  · have h1 : I.card % 2 = 1 := by omega
    simp only [h1, ↓reduceIte, (by decide : (1 : ℕ) ≠ 0), SmoothFunction.zero_apply, zero_add]

/-- Even times even is even -/
theorem even_mul_even' (f g : SuperDomainFunction p q)
    (hf : f ∈ evenSubmodule) (hg : g ∈ evenSubmodule) : mul f g ∈ evenSubmodule := by
  intro I hI
  apply SmoothFunction.ext; intro x
  simp only [mul_coefficients, SmoothFunction.zero_apply]
  rw [Finset.sum_eq_zero]; intro J _
  rw [Finset.sum_eq_zero]; intro K _
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have hJK : J.card + K.card = I.card := by
      rw [← h1, Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr h2)]
    by_cases hJ : J.card % 2 = 0
    · by_cases hK : K.card % 2 = 0
      · omega  -- |J| + |K| even contradicts |I| odd
      · have hK1 : K.card % 2 = 1 := by omega
        have hcoeff : g.coefficients K = 0 := hg K hK1
        simp only [hcoeff, SmoothFunction.zero_apply, mul_zero]
    · have hJ1 : J.card % 2 = 1 := by omega
      have hcoeff : f.coefficients J = 0 := hf J hJ1
      simp only [hcoeff, SmoothFunction.zero_apply]; ring
  · rfl

/-- Odd times odd is even -/
theorem odd_mul_odd' (f g : SuperDomainFunction p q)
    (hf : f ∈ oddSubmodule) (hg : g ∈ oddSubmodule) : mul f g ∈ evenSubmodule := by
  intro I hI
  apply SmoothFunction.ext; intro x
  simp only [mul_coefficients, SmoothFunction.zero_apply]
  rw [Finset.sum_eq_zero]; intro J _
  rw [Finset.sum_eq_zero]; intro K _
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have hJK : J.card + K.card = I.card := by
      rw [← h1, Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr h2)]
    by_cases hJ : J.card % 2 = 1
    · by_cases hK : K.card % 2 = 1
      · omega  -- odd + odd = even contradicts |I| odd
      · have hK0 : K.card % 2 = 0 := by omega
        have hcoeff : g.coefficients K = 0 := hg K hK0
        simp only [hcoeff, SmoothFunction.zero_apply, mul_zero]
    · have hJ0 : J.card % 2 = 0 := by omega
      have hcoeff : f.coefficients J = 0 := hf J hJ0
      simp only [hcoeff, SmoothFunction.zero_apply]; ring
  · rfl

/-- Even times odd is odd -/
theorem even_mul_odd' (f g : SuperDomainFunction p q)
    (hf : f ∈ evenSubmodule) (hg : g ∈ oddSubmodule) : mul f g ∈ oddSubmodule := by
  intro I hI
  apply SmoothFunction.ext; intro x
  simp only [mul_coefficients, SmoothFunction.zero_apply]
  rw [Finset.sum_eq_zero]; intro J _
  rw [Finset.sum_eq_zero]; intro K _
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have hJK : J.card + K.card = I.card := by
      rw [← h1, Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr h2)]
    by_cases hJ : J.card % 2 = 0
    · by_cases hK : K.card % 2 = 1
      · omega  -- even + odd = odd contradicts |I| even
      · have hK0 : K.card % 2 = 0 := by omega
        have hcoeff : g.coefficients K = 0 := hg K hK0
        simp only [hcoeff, SmoothFunction.zero_apply, mul_zero]
    · have hJ1 : J.card % 2 = 1 := by omega
      have hcoeff : f.coefficients J = 0 := hf J hJ1
      simp only [hcoeff, SmoothFunction.zero_apply]; ring
  · rfl

/-- Odd times even is odd -/
theorem odd_mul_even' (f g : SuperDomainFunction p q)
    (hf : f ∈ oddSubmodule) (hg : g ∈ evenSubmodule) : mul f g ∈ oddSubmodule := by
  intro I hI
  apply SmoothFunction.ext; intro x
  simp only [mul_coefficients, SmoothFunction.zero_apply]
  rw [Finset.sum_eq_zero]; intro J _
  rw [Finset.sum_eq_zero]; intro K _
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have hJK : J.card + K.card = I.card := by
      rw [← h1, Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr h2)]
    by_cases hJ : J.card % 2 = 1
    · by_cases hK : K.card % 2 = 0
      · omega  -- odd + even = odd contradicts |I| even
      · have hK1 : K.card % 2 = 1 := by omega
        have hcoeff : g.coefficients K = 0 := hg K hK1
        simp only [hcoeff, SmoothFunction.zero_apply, mul_zero]
    · have hJ0 : J.card % 2 = 0 := by omega
      have hcoeff : f.coefficients J = 0 := hf J hJ0
      simp only [hcoeff, SmoothFunction.zero_apply]; ring
  · rfl

/-- SuperDomainFunction as a SuperAlgebra -/
def toSuperAlgebra : SuperAlgebra ℝ where
  carrier := SuperDomainFunction p q
  ring := instRing
  algebra := instAlgebra
  even := evenSubmodule
  odd := oddSubmodule
  direct_sum := direct_sum_decomp
  even_mul_even := even_mul_even'
  odd_mul_odd := odd_mul_odd'
  even_mul_odd := even_mul_odd'
  odd_mul_even := odd_mul_even'

/-- 1 is in the even part (since 1 = f_∅ with |∅| = 0 even) -/
theorem one_mem_even : (one : SuperDomainFunction p q) ∈ evenSubmodule := by
  intro I hI
  apply SmoothFunction.ext; intro x
  simp only [SuperDomainFunction.one, SmoothFunction.zero_apply]
  have hI_ne : I ≠ ∅ := fun h => by subst h; simp at hI
  simp only [hI_ne, ↓reduceIte, SmoothFunction.zero_apply]

instance instSuperAlgebraWithOne : SuperAlgebraWithOne (toSuperAlgebra (p := p) (q := q)) where
  one_even := one_mem_even

end SuperDomainFunction

end Supermanifolds
