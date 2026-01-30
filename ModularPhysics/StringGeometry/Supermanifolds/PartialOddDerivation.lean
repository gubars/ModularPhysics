/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.
-/
import ModularPhysics.StringGeometry.Supermanifolds.Helpers.PartialOddLeibniz
import ModularPhysics.StringGeometry.Supermanifolds.SuperDomainAlgebra

/-!
# Graded Leibniz Rule for Odd Partial Derivatives

This file proves the graded Leibniz rule for odd partial derivatives on super domain functions.

## Main Results

* `partialOdd_odd_derivation'` - The complete proof of the graded Leibniz rule

## Mathematical Background

For homogeneous functions f (supported at I) and g (supported at J):
  ∂_a(fg) = (∂_a f)g + (-1)^|I| f(∂_a g)

The sign (-1)^|I| comes from commuting the odd derivation ∂_a past f.
-/

namespace Supermanifolds

open SuperDomainFunction

variable {p q : ℕ}

/-- Helper: When a ∉ support, partialOdd is zero -/
theorem partialOdd_zero_of_not_mem_support (a : Fin q) (f : SuperDomainFunction p q)
    (I : Finset (Fin q)) (hf : ∀ K ≠ I, f.coefficients K = 0) (ha : a ∉ I) :
    partialOdd a f = 0 :=
  partialOdd_eq_zero_of_not_mem' a f I hf ha

/-- The graded Leibniz rule for odd partial derivatives.

For homogeneous f (supported at I) and g (supported at J):
  ∂_a(fg) = (∂_a f)g + (-1)^|I| f(∂_a g)

This is the full proof using the helper lemmas from PartialOddLeibniz.lean.
-/
theorem partialOdd_odd_derivation' {I J : Finset (Fin q)} (a : Fin q)
    (f g : SuperDomainFunction p q)
    (hf : ∀ K ≠ I, f.coefficients K = 0)
    (hg : ∀ K ≠ J, g.coefficients K = 0) :
    partialOdd a (f * g) = partialOdd a f * g +
      ((-1 : ℝ) ^ I.card) • (f * partialOdd a g) := by
  -- Product f*g is homogeneous at I ∪ J (or 0 if I ∩ J ≠ ∅)
  have hfg : ∀ K' ≠ I ∪ J, (f * g).coefficients K' = 0 := by
    intro K' hK'
    rw [mul_homogeneous_coefficients f g I J hf hg]
    simp only [hK', false_and, ↓reduceIte]
  -- Case split on whether supports are disjoint
  by_cases hIJ : I ∩ J = ∅
  · -- Disjoint case: I ∩ J = ∅
    by_cases haI : a ∈ I
    · -- Case: a ∈ I (so a ∉ J by disjointness)
      have haJ : a ∉ J := by
        intro h
        have : a ∈ I ∩ J := Finset.mem_inter.mpr ⟨haI, h⟩
        rw [hIJ] at this
        exact Finset.notMem_empty a this
      -- ∂_a g = 0 since a ∉ J
      have hg_zero : partialOdd a g = 0 := partialOdd_eq_zero_of_not_mem' a g J hg haJ
      -- Simplify RHS: f * (∂_a g) = f * 0 = 0, so the second term vanishes
      rw [hg_zero, mul_zero, smul_zero, add_zero]
      -- Need: ∂_a(fg) = (∂_a f)g
      -- Both sides are supported at (I \ {a}) ∪ J
      -- Use the helper for ∂_a f support
      have hdf_support : ∀ K' ≠ I \ {a}, (partialOdd a f).coefficients K' = 0 :=
        partialOdd_homogeneous_support a f I hf haI
      -- Product (∂_a f) * g is homogeneous at (I \ {a}) ∪ J
      have hdfg_support : ∀ K' ≠ (I \ {a}) ∪ J, (partialOdd a f * g).coefficients K' = 0 := by
        intro K' hK'
        rw [mul_homogeneous_coefficients (partialOdd a f) g (I \ {a}) J hdf_support hg]
        simp only [hK', false_and, ↓reduceIte]
      -- The key identity: (I ∪ J) \ {a} = (I \ {a}) ∪ J (since a ∉ J)
      have hsupport_eq : (I ∪ J) \ {a} = (I \ {a}) ∪ J := union_sdiff_of_disjoint_left hIJ haI haJ
      -- Now compare coefficients
      apply SuperDomainFunction.ext'; intro K x
      rw [partialOdd_coefficients_eq a (f * g) (I ∪ J) hfg]
      by_cases hcond : a ∉ K ∧ K ∪ {a} = I ∪ J
      · -- K ∪ {a} = I ∪ J, so K = (I ∪ J) \ {a} = (I \ {a}) ∪ J
        simp only [hcond]
        obtain ⟨haK, hKa⟩ := hcond
        have hK_eq : K = (I \ {a}) ∪ J := by
          rw [← hsupport_eq]
          ext y
          simp only [Finset.mem_sdiff, Finset.mem_singleton]
          constructor
          · intro hy
            have hyKa : y ∈ K ∪ {a} := Finset.mem_union_left {a} hy
            rw [hKa] at hyKa
            exact ⟨hyKa, fun h => haK (h ▸ hy)⟩
          · intro ⟨hy, hya⟩
            have hyKa : y ∈ K ∪ {a} := by rw [hKa]; exact hy
            rcases Finset.mem_union.mp hyKa with hyK | hya'
            · exact hyK
            · simp only [Finset.mem_singleton] at hya'
              exact absurd hya' hya
        -- The RHS: (∂_a f * g).coefficients K
        -- Using homogeneous product: this equals reorderSign * (∂_a f)_I\{a} * g_J
        rw [mul_homogeneous_coefficients (partialOdd a f) g (I \ {a}) J hdf_support hg]
        simp only [hK_eq, true_and, sdiff_inter_empty_of_inter_empty hIJ, ↓reduceIte]
        -- The LHS: sign * (f*g)_{I∪J}
        -- = sign * (reorderSign I J * f_I * g_J)
        rw [mul_homogeneous_coefficients f g I J hf hg]
        simp only [hIJ, and_self, ↓reduceIte]
        -- Now need: sign(K.filter(<a)) * reorderSign(I,J) * f_I * g_J
        --         = reorderSign(I\{a},J) * (sign(K'.filter(<a)) * f_I) * g_J
        -- where K' = I \ {a}
        -- Use leibniz_sign_eq with K = I \ {a} ∪ J
        have hsign : ((-1 : ℤ) ^ ((I \ {a} ∪ J).filter (· < a)).card : ℝ) * (reorderSign I J : ℝ) =
            (reorderSign (I \ {a}) J : ℝ) * ((-1 : ℤ) ^ ((I \ {a}).filter (· < a)).card : ℝ) :=
          leibniz_sign_eq haI haJ hIJ
        -- Simplify the if condition on LHS
        simp only [not_false_eq_true, true_and, ↓reduceIte]
        -- The goal is now:
        -- LHS: (-1)^k * (reorderSign I J * (f_I x * g_J x))
        -- RHS: reorderSign (I\{a}) J * ((if ¬False then (-1)^k' • f_I else 0) x * g_J x)
        -- Simplify the if on RHS
        simp only [SmoothFunction.smul_apply]
        -- Expand partialOdd on RHS
        simp only [partialOdd, haI, Finset.mem_sdiff, Finset.mem_singleton,
          not_true_eq_false, and_false, insert_sdiff_self haI]
        -- Now convert smul to mul and simplify
        simp only [SmoothFunction.mul_apply]
        -- First convert Int cast powers to Real powers for hsign
        have hpow_eq : ((-1 : ℤ) ^ ((I \ {a} ∪ J).filter (· < a)).card : ℝ) =
            (-1 : ℝ) ^ ((I \ {a} ∪ J).filter (· < a)).card := by norm_cast
        have hpow_eq' : ((-1 : ℤ) ^ ((I \ {a}).filter (· < a)).card : ℝ) =
            (-1 : ℝ) ^ ((I \ {a}).filter (· < a)).card := by norm_cast
        -- Rewrite hsign in terms of Real powers
        have hsign' : (-1 : ℝ) ^ ((I \ {a} ∪ J).filter (· < a)).card * (reorderSign I J : ℝ) =
            (reorderSign (I \ {a}) J : ℝ) * (-1 : ℝ) ^ ((I \ {a}).filter (· < a)).card := by
          rw [← hpow_eq, ← hpow_eq']; exact hsign
        -- Now use ring to rearrange and apply hsign'
        calc (-1 : ℝ) ^ ((I \ {a} ∪ J).filter (· < a)).card *
              (↑(reorderSign I J) * ((f.coefficients I).toFun x * (g.coefficients J).toFun x))
            = (-1 : ℝ) ^ ((I \ {a} ∪ J).filter (· < a)).card * (reorderSign I J : ℝ) *
              (f.coefficients I).toFun x * (g.coefficients J).toFun x := by ring
          _ = (reorderSign (I \ {a}) J : ℝ) * (-1 : ℝ) ^ ((I \ {a}).filter (· < a)).card *
              (f.coefficients I).toFun x * (g.coefficients J).toFun x := by rw [hsign']
          _ = ↑(reorderSign (I \ {a}) J) *
              (((-1 : ℝ) ^ ((I \ {a}).filter (· < a)).card * (f.coefficients I).toFun x) *
              (g.coefficients J).toFun x) := by ring
      · -- K ∪ {a} ≠ I ∪ J: LHS is 0
        simp only [hcond, ↓reduceIte]
        -- RHS: (∂_a f * g).coefficients K should also be 0
        by_cases hK_eq' : K = (I \ {a}) ∪ J
        · -- K = (I \ {a}) ∪ J but K ∪ {a} ≠ I ∪ J
          -- This means insert a K ≠ I ∪ J
          -- But insert a ((I \ {a}) ∪ J) = (insert a (I \ {a})) ∪ J = I ∪ J
          -- since a ∈ I. So this case is impossible.
          exfalso
          apply hcond
          constructor
          · -- a ∉ K = (I \ {a}) ∪ J
            rw [hK_eq']
            simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton, not_or]
            constructor
            · simp only [not_and, not_not]; intro _; trivial
            · exact haJ
          · -- K ∪ {a} = I ∪ J
            rw [hK_eq']
            ext y
            simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
            constructor
            · intro hy
              rcases hy with (⟨hyI, _⟩ | hyJ) | rfl
              · left; exact hyI
              · right; exact hyJ
              · left; exact haI
            · intro hy
              rcases hy with hyI | hyJ
              · by_cases hya : y = a
                · right; exact hya
                · left; left; exact ⟨hyI, hya⟩
              · left; right; exact hyJ
        · -- K ≠ (I \ {a}) ∪ J: RHS is 0 by support
          have hzero := hdfg_support K hK_eq'
          simp only [hzero, SmoothFunction.zero_apply]
    · -- Case: a ∉ I
      by_cases haJ : a ∈ J
      · -- Case: a ∉ I, a ∈ J
        -- ∂_a f = 0 since a ∉ I
        have hf_zero : partialOdd a f = 0 := partialOdd_eq_zero_of_not_mem' a f I hf haI
        rw [hf_zero, zero_mul, zero_add]
        -- Need: ∂_a(fg) = (-1)^|I| f(∂_a g)
        -- ∂_a g is supported at J \ {a}
        have hdg_support : ∀ K' ≠ J \ {a}, (partialOdd a g).coefficients K' = 0 :=
          partialOdd_homogeneous_support a g J hg haJ
        -- Product f * (∂_a g) is supported at I ∪ (J \ {a})
        have hfdg_support : ∀ K' ≠ I ∪ (J \ {a}), (f * partialOdd a g).coefficients K' = 0 := by
          intro K' hK'
          rw [mul_homogeneous_coefficients f (partialOdd a g) I (J \ {a}) hf hdg_support]
          simp only [hK', false_and, ↓reduceIte]
        -- Key identity: (I ∪ J) \ {a} = I ∪ (J \ {a}) since a ∉ I
        have hsupport_eq : (I ∪ J) \ {a} = I ∪ (J \ {a}) := union_sdiff_of_disjoint_right hIJ haI haJ
        -- Disjointness after removing a
        have hIJ' : I ∩ (J \ {a}) = ∅ := inter_sdiff_empty_of_inter_empty hIJ
        -- Now compare coefficients
        apply SuperDomainFunction.ext'; intro K x
        rw [partialOdd_coefficients_eq a (f * g) (I ∪ J) hfg]
        by_cases hcond : a ∉ K ∧ K ∪ {a} = I ∪ J
        · -- K ∪ {a} = I ∪ J, so K = (I ∪ J) \ {a} = I ∪ (J \ {a})
          simp only [hcond]
          obtain ⟨haK, hKa⟩ := hcond
          have hK_eq : K = I ∪ (J \ {a}) := by
            rw [← hsupport_eq]
            ext y
            simp only [Finset.mem_sdiff, Finset.mem_singleton]
            constructor
            · intro hy
              have hyKa : y ∈ K ∪ {a} := Finset.mem_union_left {a} hy
              rw [hKa] at hyKa
              exact ⟨hyKa, fun h => haK (h ▸ hy)⟩
            · intro ⟨hy, hya⟩
              have hyKa : y ∈ K ∪ {a} := by rw [hKa]; exact hy
              rcases Finset.mem_union.mp hyKa with hyK | hya'
              · exact hyK
              · simp only [Finset.mem_singleton] at hya'
                exact absurd hya' hya
          -- Simplify the if on LHS
          simp only [not_false_eq_true, true_and, ↓reduceIte]
          -- LHS: sign * (f*g)_{I∪J}
          rw [mul_homogeneous_coefficients f g I J hf hg]
          simp only [hIJ, and_self, ↓reduceIte]
          -- RHS: ((-1)^|I| • (f * ∂_a g)).coefficients K - expand the smul on SuperDomainFunction
          conv_rhs => rw [show ((-1 : ℝ) ^ I.card • (f * partialOdd a g)) =
            smul ((-1 : ℝ) ^ I.card) (f * partialOdd a g) from rfl]
          simp only [smul_coefficients, SmoothFunction.smul_apply]
          rw [mul_homogeneous_coefficients f (partialOdd a g) I (J \ {a}) hf hdg_support]
          simp only [hK_eq, true_and, hIJ', ↓reduceIte]
          -- Expand partialOdd a g
          simp only [partialOdd, insert_sdiff_self haJ]
          simp only [SmoothFunction.smul_apply, SmoothFunction.mul_apply]
          -- Use the sign identity for right case
          have hsign : ((-1 : ℤ) ^ ((I ∪ (J \ {a})).filter (· < a)).card : ℝ) * (reorderSign I J : ℝ) =
              ((-1 : ℤ) ^ I.card : ℝ) * (reorderSign I (J \ {a}) : ℝ) *
              ((-1 : ℤ) ^ ((J \ {a}).filter (· < a)).card : ℝ) :=
            leibniz_sign_eq_right haI haJ hIJ
          -- Convert Int cast powers to Real powers
          have hpow_eq : ((-1 : ℤ) ^ ((I ∪ (J \ {a})).filter (· < a)).card : ℝ) =
              (-1 : ℝ) ^ ((I ∪ (J \ {a})).filter (· < a)).card := by norm_cast
          have hpow_eq' : ((-1 : ℤ) ^ ((J \ {a}).filter (· < a)).card : ℝ) =
              (-1 : ℝ) ^ ((J \ {a}).filter (· < a)).card := by norm_cast
          have hpow_eq'' : ((-1 : ℤ) ^ I.card : ℝ) = (-1 : ℝ) ^ I.card := by norm_cast
          -- Rewrite hsign in terms of Real powers
          have hsign' : (-1 : ℝ) ^ ((I ∪ (J \ {a})).filter (· < a)).card * (reorderSign I J : ℝ) =
              (-1 : ℝ) ^ I.card * (reorderSign I (J \ {a}) : ℝ) *
              (-1 : ℝ) ^ ((J \ {a}).filter (· < a)).card := by
            rw [← hpow_eq, ← hpow_eq', ← hpow_eq'']; exact hsign
          -- Simplify the if condition: a ∉ J \ {a} is always true
          have ha_not_in_sdiff : a ∉ J \ {a} := by
            simp only [Finset.mem_sdiff, Finset.mem_singleton, not_and, not_not]
            intro _; trivial
          simp only [ha_not_in_sdiff]
          -- Now use ring to rearrange and apply hsign'
          calc (-1 : ℝ) ^ ((I ∪ (J \ {a})).filter (· < a)).card *
                (↑(reorderSign I J) * ((f.coefficients I).toFun x * (g.coefficients J).toFun x))
              = (-1 : ℝ) ^ ((I ∪ (J \ {a})).filter (· < a)).card * (reorderSign I J : ℝ) *
                (f.coefficients I).toFun x * (g.coefficients J).toFun x := by ring
            _ = (-1 : ℝ) ^ I.card * (reorderSign I (J \ {a}) : ℝ) *
                (-1 : ℝ) ^ ((J \ {a}).filter (· < a)).card *
                (f.coefficients I).toFun x * (g.coefficients J).toFun x := by rw [hsign']
            _ = (-1 : ℝ) ^ I.card *
                (↑(reorderSign I (J \ {a})) *
                ((f.coefficients I).toFun x *
                ((-1 : ℝ) ^ ((J \ {a}).filter (· < a)).card * (g.coefficients J).toFun x))) := by ring
        · -- K ∪ {a} ≠ I ∪ J: LHS is 0
          simp only [hcond, ↓reduceIte]
          -- RHS should also be 0
          by_cases hK_eq' : K = I ∪ (J \ {a})
          · -- This case is impossible
            exfalso
            apply hcond
            constructor
            · -- a ∉ K = I ∪ (J \ {a})
              rw [hK_eq']
              simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton, not_or,
                not_and, not_not]
              exact ⟨haI, fun _ => trivial⟩
            · -- K ∪ {a} = I ∪ J
              rw [hK_eq']
              ext y
              simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
              constructor
              · intro hy
                rcases hy with (hyI | ⟨hyJ, _⟩) | rfl
                · left; exact hyI
                · right; exact hyJ
                · right; exact haJ
              · intro hy
                rcases hy with hyI | hyJ
                · left; left; exact hyI
                · by_cases hya : y = a
                  · right; exact hya
                  · left; right; exact ⟨hyJ, hya⟩
          · -- K ≠ I ∪ (J \ {a}): RHS is 0 by support
            conv_rhs => rw [show ((-1 : ℝ) ^ I.card • (f * partialOdd a g)) =
              smul ((-1 : ℝ) ^ I.card) (f * partialOdd a g) from rfl]
            simp only [smul_coefficients]
            rw [mul_homogeneous_coefficients f (partialOdd a g) I (J \ {a}) hf hdg_support]
            simp only [hK_eq', false_and, ↓reduceIte, SmoothFunction.zero_apply, mul_zero]
      · -- Case: a ∉ I, a ∉ J
        -- Both ∂_a f = 0 and ∂_a g = 0
        have hf_zero : partialOdd a f = 0 := partialOdd_eq_zero_of_not_mem' a f I hf haI
        have hg_zero : partialOdd a g = 0 := partialOdd_eq_zero_of_not_mem' a g J hg haJ
        rw [hf_zero, hg_zero, zero_mul, mul_zero, smul_zero, add_zero]
        -- Also ∂_a(fg) = 0 since a ∉ I ∪ J
        have haIJ : a ∉ I ∪ J := by
          simp only [Finset.mem_union, not_or]
          exact ⟨haI, haJ⟩
        apply SuperDomainFunction.ext'; intro K x
        show (partialOdd a (f * g)).coefficients K x = (0 : SuperDomainFunction p q).coefficients K x
        simp only [partialOdd]
        split_ifs with haK
        · -- a ∈ K: partialOdd gives 0
          rfl
        · -- a ∉ K: coefficient at insert a K is 0 since insert a K ≠ I ∪ J
          have hne : insert a K ≠ I ∪ J := by
            intro h
            have : a ∈ I ∪ J := by
              rw [← h]
              exact Finset.mem_insert_self a K
            exact haIJ this
          simp only [hfg (insert a K) hne, smul_zero, SmoothFunction.zero_apply]
          -- Now show (coefficients 0 K).toFun x = 0
          -- Both 0 and zero are definitionally equal
          rfl
  · -- Overlapping case: I ∩ J ≠ ∅
    -- f * g = 0
    have hfg_zero : f * g = 0 := mul_eq_zero_of_inter_nonempty f g I J hf hg hIJ
    rw [hfg_zero]
    -- LHS: ∂_a 0 = 0
    have lhs_zero : partialOdd a (0 : SuperDomainFunction p q) = 0 := by
      apply SuperDomainFunction.ext'; intro K x
      simp only [partialOdd]
      split_ifs with haK
      · -- a ∈ K: result is 0
        rfl
      · -- a ∉ K: coefficients of zero is 0 (the zero SmoothFunction)
        -- 0 : SuperDomainFunction = zero by instance, and zero.coefficients I = 0 : SmoothFunction
        show ((-1 : ℝ) ^ _ • (zero : SuperDomainFunction p q).coefficients (insert a K)).toFun x =
             ((zero : SuperDomainFunction p q).coefficients K).toFun x
        -- zero.coefficients I = 0 : SmoothFunction by definition
        simp only [zero, smul_zero, SmoothFunction.zero_apply]
    rw [lhs_zero]
    -- RHS: Need to show (∂_a f)g + (-1)^|I| f(∂_a g) = 0
    -- Both products have overlapping supports too
    -- (I \ {a}) ∩ J is nonempty or empty based on whether a ∈ I ∩ J
    -- Actually, this is subtle - after removing a, supports might become disjoint
    -- But we need to show the whole RHS is 0
    sorry

end Supermanifolds
