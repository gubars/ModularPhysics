import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.ZariskiTopology
import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.Core.Divisors
import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.FunctionField
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Cohomology on Algebraic Curves (Pure Algebraic Approach)

This file develops cohomology theory for algebraic curves using the Riemann-Roch space.

## Main Definitions

* `RiemannRochSpace` - The space L(D) = {f : (f) + D ≥ 0} ∪ {0}
* `RiemannRochSubmodule` - L(D) as a ℂ-submodule of K(C)

## Key Theorems (with sorrys to be proved)

* `h0_zero` - h⁰(O) = 1 (properness: regular functions on proper curves are constant)
* `h1_zero` - h¹(O) = g (algebraic definition of genus)
* `eulerChar_point_exact` - χ(D) - χ(D-p) = 1 (algebraic long exact sequence)
* `riemann_roch_algebraic` - χ(D) = deg(D) + 1 - g

## Proof Strategy (Purely Algebraic)

All theorems can be proved using purely algebraic methods:

1. **h⁰(O) = 1**: On a proper (complete) algebraic curve over an algebraically closed
   field, a rational function with no poles is regular everywhere, hence constant.
   This is the algebraic analogue of Liouville's theorem, proved via properness.

2. **h¹(O) = g**: Define genus algebraically as g := 1 - χ(O) = 1 - (h⁰(O) - h¹(O)).
   With h⁰(O) = 1, this gives h¹(O) = g by definition. Alternatively, use Serre duality
   h¹(O) = h⁰(K) and the fact that h⁰(K) = g for the canonical divisor.

3. **χ(D) - χ(D-p) = 1**: The short exact sequence of sheaves
   0 → O(D-p) → O(D) → k(p) → 0 induces a long exact sequence in algebraic
   sheaf cohomology. Since H⁰(k(p)) = k and H¹(k(p)) = 0 for a skyscraper sheaf,
   the alternating sum gives χ(D) - χ(D-p) = χ(k(p)) = 1.

## References

* Hartshorne "Algebraic Geometry" III.4, IV.1
* Silverman "The Arithmetic of Elliptic Curves" II.5
-/

namespace RiemannSurfaces.Algebraic.Cohomology

open Set Finset Classical

variable (C : AlgebraicCurve)

/-!
## The Riemann-Roch Space L(D)
-/

/-- The Riemann-Roch space L(D) as a set.
    L(D) = {f ∈ K(C) : f = 0 ∨ (f) + D ≥ 0}
    This is H⁰(C, O(D)). -/
def RiemannRochSpace (D : Core.Divisor C) : Set C.FunctionField :=
  { f | f = 0 ∨ (∀ p : C.Point, C.valuation p f + D.coeff p ≥ 0) }

/-- 0 is in L(D) -/
theorem zero_mem_RiemannRochSpace (D : Core.Divisor C) : (0 : C.FunctionField) ∈ RiemannRochSpace C D := by
  left; rfl

/-- L(D) is closed under addition -/
theorem add_mem_RiemannRochSpace (D : Core.Divisor C) {f g : C.FunctionField}
    (hf : f ∈ RiemannRochSpace C D) (hg : g ∈ RiemannRochSpace C D) :
    f + g ∈ RiemannRochSpace C D := by
  -- Handle cases based on whether f, g, or f+g is zero
  by_cases hf0 : f = 0
  · simp only [hf0, zero_add]; exact hg
  by_cases hg0 : g = 0
  · simp only [hg0, add_zero]; exact hf
  by_cases hfg : f + g = 0
  · left; exact hfg
  -- All nonzero: use ultrametric inequality
  · right
    intro p
    -- Extract the valuation bounds from hf and hg
    have hfv : C.valuation p f + D.coeff p ≥ 0 := by
      rcases hf with rfl | hf'; exact absurd rfl hf0; exact hf' p
    have hgv : C.valuation p g + D.coeff p ≥ 0 := by
      rcases hg with rfl | hg'; exact absurd rfl hg0; exact hg' p
    have hmin := C.valuation_add_min p f g hfg
    omega

/-- L(D) is closed under scalar multiplication (using field multiplication).
    Since K(C) is a ℂ-algebra, scalar multiplication c • f = (algebraMap ℂ K(C) c) * f. -/
theorem smul_mem_RiemannRochSpace [alg : FunctionFieldAlgebra C] (D : Core.Divisor C)
    {f : C.FunctionField} {c : ℂ} (hf : f ∈ RiemannRochSpace C D) :
    c • f ∈ RiemannRochSpace C D := by
  -- v(c • f) = v(algebraMap c * f) = v(algebraMap c) + v(f) = 0 + v(f) = v(f) for c ≠ 0
  -- For c = 0, c • f = 0 ∈ L(D)
  by_cases hc : c = 0
  · simp only [hc, zero_smul]; left; rfl
  by_cases hf0 : f = 0
  · simp only [hf0, smul_zero]; left; rfl
  -- Both c and f nonzero
  right
  intro p
  -- Extract the valuation bound from hf
  have hfv : C.valuation p f + D.coeff p ≥ 0 := by
    rcases hf with rfl | hf'; exact absurd rfl hf0; exact hf' p
  -- c • f = algebraMap c * f
  have hsmul : c • f = algebraMap ℂ C.FunctionField c * f := Algebra.smul_def c f
  rw [hsmul]
  have hcnz : algebraMap ℂ C.FunctionField c ≠ 0 := by
    intro heq
    simp only [map_eq_zero] at heq
    exact hc heq
  rw [C.valuation_mul p _ _ hcnz hf0, alg.valuation_algebraMap p c hc]
  simp only [zero_add]
  exact hfv

/-!
## L(D-p) ⊆ L(D): The Key Inclusion

For the point exact sequence, we need that L(D-p) is a subspace of L(D).
This follows from the fact that the condition for L(D-p) is stronger at p.
-/

/-- L(D - point(p)) ⊆ L(D).

    **Proof**: For f ∈ L(D-p):
    - At q ≠ p: condition v_q(f) ≥ -D(q) is the same since (D-p)(q) = D(q)
    - At q = p: f satisfies v_p(f) ≥ -(D(p)-1) = -D(p)+1 > -D(p)

    So L(D-p) ⊆ L(D). -/
theorem RiemannRochSpace_sub_point_subset (D : Core.Divisor C) (p : C.Point) :
    RiemannRochSpace C (D - Core.Divisor.point p) ⊆ RiemannRochSpace C D := by
  intro f hf
  simp only [RiemannRochSpace, Set.mem_setOf_eq] at hf ⊢
  rcases hf with rfl | hf_val
  · left; rfl
  · right
    intro q
    specialize hf_val q
    simp only [Core.Divisor.sub_coeff, Core.Divisor.point] at hf_val ⊢
    by_cases hqp : q = p
    · subst hqp
      simp only [if_true] at hf_val ⊢
      omega
    · simp only [if_neg hqp] at hf_val ⊢
      omega

/-- The canonical divisor K with deg(K) = 2g - 2. -/
structure CanonicalDivisor (C : Algebraic.CompactAlgebraicCurve) where
  K : Core.Divisor C.toAlgebraicCurve
  degree_eq : K.degree = (2 : ℤ) * C.genus - 2

/-!
## Cohomology Dimensions

h⁰(D) and h¹(D) are defined as dimensions of concrete vector spaces.
The finite-dimensionality theorems have sorrys - these are the actual
mathematical content that needs to be proved.
-/

/-- The FunctionFieldAlgebra instance for a CompactAlgebraicCurve -/
instance CompactAlgebraicCurve.functionFieldAlgebraInst (C : Algebraic.CompactAlgebraicCurve) :
    FunctionFieldAlgebra C.toAlgebraicCurve := C.algebraInst

/-- The Module instance on the function field from the algebra structure -/
instance CompactAlgebraicCurve.functionFieldModule (C : Algebraic.CompactAlgebraicCurve) :
    Module ℂ C.FunctionField := C.algebraInst.algebraInst.toModule

/-- L(D) as a submodule of the function field K(C).
    This uses the ℂ-algebra structure from CompactAlgebraicCurve. -/
noncomputable def RiemannRochSubmodule (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) : Submodule ℂ C.FunctionField where
  carrier := RiemannRochSpace C.toAlgebraicCurve D
  add_mem' := fun {_ _} ha hb => add_mem_RiemannRochSpace C.toAlgebraicCurve D ha hb
  zero_mem' := zero_mem_RiemannRochSpace C.toAlgebraicCurve D
  smul_mem' := fun _ {_} hf => smul_mem_RiemannRochSpace C.toAlgebraicCurve D hf

/-- L(D) is finite-dimensional (finiteness for coherent sheaves on proper curves).

    **Algebraic proof outline:**
    1. O(D) is a coherent sheaf on a proper curve C
    2. Global sections of coherent sheaves on proper schemes are finite-dimensional
    3. L(D) = H⁰(C, O(D)) is therefore finite-dimensional over the base field

    This is the algebraic version of "Cartan-Serre finiteness" - it follows from
    coherence + properness, not from analytic arguments. -/
theorem RiemannRochSubmodule_finiteDimensional (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) :
    FiniteDimensional ℂ (RiemannRochSubmodule C D) := by
  sorry

/-- L(D-p) as a submodule of L(D).
    This is the submodule inclusion used in the point exact sequence. -/
noncomputable def RiemannRochSubmodule_sub_point (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) :
    Submodule ℂ (RiemannRochSubmodule C D) :=
  Submodule.comap (RiemannRochSubmodule C D).subtype (RiemannRochSubmodule C (D - Core.Divisor.point p))

/-- The inclusion L(D-p) → L(D) is well-defined. -/
theorem RiemannRochSubmodule_sub_point_le (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) :
    RiemannRochSubmodule C (D - Core.Divisor.point p) ≤ RiemannRochSubmodule C D := by
  intro f hf
  exact RiemannRochSpace_sub_point_subset C.toAlgebraicCurve D p hf

/-- **Quotient dimension bound**: dim(L(D)/L(D-p)) ≤ 1.

    **Proof sketch**:
    The quotient is parametrized by the "leading coefficient" at p.
    If f, g ∈ L(D) have v_p(f) = v_p(g) = -D(p), then f - cg ∈ L(D-p) for suitable c.
    So the quotient embeds into ℂ (the space of leading coefficients).

    This uses `leadingCoefficientUniqueness` from CompactAlgebraicCurve:
    any two functions with the same pole order at p are proportional modulo
    functions with higher valuation. -/
theorem quotient_dim_le_one (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point)
    [FiniteDimensional ℂ (RiemannRochSubmodule C D)]
    [FiniteDimensional ℂ (RiemannRochSubmodule C (D - Core.Divisor.point p))] :
    Module.finrank ℂ (RiemannRochSubmodule C D) ≤
    Module.finrank ℂ (RiemannRochSubmodule C (D - Core.Divisor.point p)) + 1 := by
  -- The inclusion L(D-p) ≤ L(D) as submodules (viewed as a submodule of L(D))
  let W := (RiemannRochSubmodule C (D - Core.Divisor.point p)).comap
           (RiemannRochSubmodule C D).subtype

  -- W is finite-dimensional (W ⊆ L(D) which is finite-dimensional)
  haveI hW_fd : FiniteDimensional ℂ W := by
    apply Module.Finite.of_injective (W.subtype)
    exact Subtype.val_injective

  -- W ≅ L(D-p), so they have the same finrank
  have hW_eq : Module.finrank ℂ W =
      Module.finrank ℂ (RiemannRochSubmodule C (D - Core.Divisor.point p)) := by
    apply LinearEquiv.finrank_eq
    let toW : RiemannRochSubmodule C (D - Core.Divisor.point p) →ₗ[ℂ] W := {
      toFun := fun f =>
        ⟨⟨f.val, RiemannRochSubmodule_sub_point_le C D p f.property⟩, f.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
    }
    exact {
      toLinearMap := {
        toFun := fun ⟨f, hf⟩ => ⟨f.val, hf⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
      }
      invFun := toW
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
    }

  -- Use quotient dimension formula: finrank V = finrank (V/W) + finrank W
  have hdim := Submodule.finrank_quotient_add_finrank W

  suffices h : Module.finrank ℂ (RiemannRochSubmodule C D ⧸ W) ≤ 1 by omega

  -- Case 1: If W = ⊤ (i.e., L(D) = L(D-p)), quotient is trivial
  by_cases hEq : W = ⊤
  · haveI hsub : Subsingleton (RiemannRochSubmodule C D ⧸ W) :=
      Submodule.Quotient.subsingleton_iff.mpr hEq
    have : Module.finrank ℂ (RiemannRochSubmodule C D ⧸ W) = 0 :=
      Module.finrank_zero_of_subsingleton
    omega

  -- Case 2: Pick f₀ ∈ L(D) \ W and show [f₀] spans the quotient
  have hW_ne_top : ∃ x : RiemannRochSubmodule C D, x ∉ W := by
    by_contra h_all
    push_neg at h_all
    apply hEq
    ext x; constructor
    · intro _; exact Submodule.mem_top
    · intro _; exact h_all x
  obtain ⟨f₀, hf₀_not⟩ := hW_ne_top

  -- f₀ has v_p(f₀) = -D(p) exactly (not higher)
  have hf₀_val : C.valuation p f₀.val = -D.coeff p := by
    have hf₀_not' : f₀.val ∉ RiemannRochSubmodule C (D - Core.Divisor.point p) := hf₀_not
    have hf₀_D : f₀.val ∈ RiemannRochSubmodule C D := f₀.property
    -- Unfold membership in RiemannRochSubmodule
    simp only [RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
               RiemannRochSpace] at hf₀_D
    -- For hf₀_not', membership is negated
    have hf₀_not'' : ¬(f₀.val = 0 ∨ ∀ r, C.valuation r f₀.val + (D - Core.Divisor.point p).coeff r ≥ 0) := by
      intro h
      apply hf₀_not'
      simp only [RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                 RiemannRochSpace]
      exact h
    rcases hf₀_D with hf₀_zero | hf₀_D
    · exfalso; apply hf₀_not''; left; exact hf₀_zero
    · -- hf₀_not'' : ¬(f₀.val = 0 ∨ ∀ q, ...) means ¬(f₀.val = 0) ∧ ¬(∀ q, ...)
      rw [not_or] at hf₀_not''
      have ⟨_, hf₀_not_forall⟩ := hf₀_not''
      rw [not_forall] at hf₀_not_forall
      obtain ⟨q, hq⟩ := hf₀_not_forall
      rw [not_le] at hq
      simp only [Core.Divisor.sub_coeff, Core.Divisor.point] at hq
      by_cases hqp : q = p
      · simp only [hqp, if_true] at hq; have := hf₀_D p; omega
      · simp only [if_neg hqp, sub_zero] at hq; have := hf₀_D q; omega

  -- Helper: f₀ is nonzero
  have hf₀_ne : f₀.val ≠ 0 := by
    intro heq
    have hmem : f₀.val ∈ RiemannRochSubmodule C (D - Core.Divisor.point p) := by
      rw [heq]; exact zero_mem_RiemannRochSpace C.toAlgebraicCurve (D - Core.Divisor.point p)
    exact hf₀_not hmem

  -- Claim: [f₀] spans L(D)/W
  have h_span : Submodule.span ℂ ({Submodule.Quotient.mk f₀} : Set (RiemannRochSubmodule C D ⧸ W)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective W x

    by_cases hgW : g ∈ W
    · have hzero : Submodule.Quotient.mk (p := W) g = 0 := (Submodule.Quotient.mk_eq_zero W).mpr hgW
      rw [hzero]; exact zero_mem _
    · -- g ∉ W means v_p(g) = -D(p) (same as f₀)
      have hg_val : C.valuation p g.val = -D.coeff p := by
        have hg_not' : g.val ∉ RiemannRochSubmodule C (D - Core.Divisor.point p) := hgW
        have hg_D : g.val ∈ RiemannRochSubmodule C D := g.property
        simp only [RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                   RiemannRochSpace] at hg_D
        -- Convert hg_not' to a usable form
        have hg_not'' : ¬(g.val = 0 ∨ ∀ r, C.valuation r g.val + (D - Core.Divisor.point p).coeff r ≥ 0) := by
          intro h; apply hg_not'
          simp only [RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk, RiemannRochSpace]
          exact h
        rcases hg_D with hg_zero | hg_D
        · exfalso; apply hg_not''; left; exact hg_zero
        · rw [not_or] at hg_not''
          have ⟨_, hg_not_forall⟩ := hg_not''
          rw [not_forall] at hg_not_forall
          obtain ⟨q, hq⟩ := hg_not_forall
          rw [not_le] at hq
          simp only [Core.Divisor.sub_coeff, Core.Divisor.point] at hq
          by_cases hqp : q = p
          · simp only [hqp, if_true] at hq; have := hg_D p; omega
          · simp only [if_neg hqp, sub_zero] at hq; have := hg_D q; omega

      have hg_ne : g.val ≠ 0 := by
        intro heq; apply hgW
        have : g.val ∈ RiemannRochSubmodule C (D - Core.Divisor.point p) := by
          rw [heq]; exact zero_mem_RiemannRochSpace C.toAlgebraicCurve (D - Core.Divisor.point p)
        exact this

      -- Use leadingCoefficientUniquenessGeneral with swapped arguments to get g - c*f₀
      -- This works for any valuation (not just poles)
      obtain ⟨c, hc_ne, hcases⟩ := C.leadingCoefficientUniquenessGeneral p f₀.val g.val hf₀_ne hg_ne
        (by rw [hf₀_val, hg_val])

      -- g - c * f₀ ∈ L(D-p)
      have h_diff_mem : g.val - algebraMap ℂ C.FunctionField c * f₀.val ∈
          RiemannRochSubmodule C (D - Core.Divisor.point p) := by
        rcases hcases with heq | hgt
        · -- g - c*f₀ = 0
          rw [heq]; exact zero_mem_RiemannRochSpace C.toAlgebraicCurve _
        · -- v_p(g - c*f₀) > v_p(g) = -D(p), so v_p(g - c*f₀) ≥ -(D-p)(p)
          simp only [RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk, RiemannRochSpace]
          by_cases hdiff : g.val - algebraMap ℂ C.FunctionField c * f₀.val = 0
          · left; exact hdiff
          · right
            intro q
            simp only [Core.Divisor.sub_coeff, Core.Divisor.point]
            by_cases hqp : q = p
            · -- At p: v(g - c*f₀) > v(g) = -D(p), so ≥ -D(p) + 1 = -(D(p) - 1)
              simp only [hqp, if_true]; rw [hg_val] at hgt; omega
            · -- At q ≠ p: use ultrametric inequality
              simp only [if_neg hqp, sub_zero]
              -- Get bounds for g and f₀ at q
              have hg_q : C.valuation q g.val + D.coeff q ≥ 0 := by
                have hg_D : g.val ∈ RiemannRochSubmodule C D := g.property
                simp only [RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                           RiemannRochSpace] at hg_D
                rcases hg_D with hgz | hgD
                · exact absurd hgz hg_ne
                · exact hgD q
              have hf₀_q : C.valuation q f₀.val + D.coeff q ≥ 0 := by
                have hf₀_D : f₀.val ∈ RiemannRochSubmodule C D := f₀.property
                simp only [RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
                           RiemannRochSpace] at hf₀_D
                rcases hf₀_D with hf₀z | hf₀D
                · exact absurd hf₀z hf₀_ne
                · exact hf₀D q
              -- v(c * f₀) = v(f₀) since c is a nonzero constant
              have h_cf₀ : C.valuation q (algebraMap ℂ C.FunctionField c * f₀.val) =
                           C.valuation q f₀.val := by
                have hcne' : algebraMap ℂ C.FunctionField c ≠ 0 := by simp [hc_ne]
                rw [C.toAlgebraicCurve.valuation_mul q _ _ hcne' hf₀_ne,
                    C.algebraInst.valuation_algebraMap q c hc_ne]
                ring
              -- v(-x) = v(x) for nonzero x (derived from v((-1)*x) = v(-1) + v(x) = 0 + v(x))
              have hcf₀_ne : algebraMap ℂ C.FunctionField c * f₀.val ≠ 0 :=
                mul_ne_zero (by simp [hc_ne]) hf₀_ne
              have hneg_val : C.valuation q (-(algebraMap ℂ C.FunctionField c * f₀.val)) =
                              C.valuation q (algebraMap ℂ C.FunctionField c * f₀.val) := by
                -- -x = (-1) * x
                have h1 : -(algebraMap ℂ C.FunctionField c * f₀.val) =
                          algebraMap ℂ C.FunctionField (-1 : ℂ) * (algebraMap ℂ C.FunctionField c * f₀.val) := by
                  simp only [map_neg, map_one, neg_mul, one_mul]
                have hm1_ne : algebraMap ℂ C.FunctionField (-1 : ℂ) ≠ 0 := by simp
                rw [h1, C.toAlgebraicCurve.valuation_mul q _ _ hm1_ne hcf₀_ne,
                    C.algebraInst.valuation_algebraMap q (-1) (by norm_num : (-1 : ℂ) ≠ 0)]
                ring
              -- v(g - c*f₀) ≥ min(v(g), v(c*f₀)) by ultrametric inequality
              have hdiff' : g.val + (-(algebraMap ℂ C.FunctionField c * f₀.val)) ≠ 0 := by
                simp only [← sub_eq_add_neg]; exact hdiff
              have hmin := C.toAlgebraicCurve.valuation_add_min q g.val
                (-(algebraMap ℂ C.FunctionField c * f₀.val)) hdiff'
              simp only [sub_eq_add_neg]
              rw [hneg_val, h_cf₀] at hmin
              omega

      -- [g] = c • [f₀] in the quotient
      have h_diff_W : g - c • f₀ ∈ W := by
        show (g - c • f₀).val ∈ RiemannRochSubmodule C (D - Core.Divisor.point p)
        simp only [Submodule.coe_sub, Submodule.coe_smul, Algebra.smul_def]
        exact h_diff_mem

      -- Rewrite [g] as c • [f₀] using quotient properties
      have hq_eq : Submodule.Quotient.mk (p := W) g = c • Submodule.Quotient.mk (p := W) f₀ := by
        rw [← sub_eq_zero]
        -- First convert smul to mk of smul
        conv_lhs => rw [← Submodule.Quotient.mk_smul]
        rw [← Submodule.Quotient.mk_sub]
        exact (Submodule.Quotient.mk_eq_zero W).mpr h_diff_W
      rw [hq_eq]
      exact Submodule.smul_mem _ c (Submodule.subset_span rfl)

  -- Quotient is spanned by one element, so finrank ≤ 1
  -- h_span : ℂ ∙ [f₀] = ⊤, so finrank(quotient) = finrank(ℂ ∙ [f₀]) ≤ 1
  have h_eq : Module.finrank ℂ (RiemannRochSubmodule C D ⧸ W) =
              Module.finrank ℂ (Submodule.span ℂ ({Submodule.Quotient.mk f₀} :
                Set (RiemannRochSubmodule C D ⧸ W))) := by
    conv_lhs => rw [← finrank_top (R := ℂ) (M := RiemannRochSubmodule C D ⧸ W), ← h_span]
  rw [h_eq]
  -- [f₀] ≠ 0 since f₀ ∉ W
  have hf₀_ne_zero : Submodule.Quotient.mk (p := W) f₀ ≠ 0 := by
    rw [ne_eq, Submodule.Quotient.mk_eq_zero]
    exact hf₀_not
  -- Span of a nonzero singleton has finrank = 1 ≤ 1
  have h1 : Module.finrank ℂ (ℂ ∙ Submodule.Quotient.mk (p := W) f₀) = 1 :=
    finrank_span_singleton hf₀_ne_zero
  omega

/-- h⁰(D) = dim L(D).
    Properly defined as finrank of the Riemann-Roch submodule.
    If not finite-dimensional, finrank returns 0 by convention. -/
noncomputable def h0 (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) : ℕ :=
  Module.finrank ℂ (RiemannRochSubmodule C D)

/-- A proper canonical divisor with all the required properties.
    This extends CanonicalDivisor with the h⁰(K) = g property.

    **Note**: This structure only includes properties that can be proven
    from the definition of the canonical divisor. The point exact sequence
    formula (which requires Serre duality and sheaf cohomology) is stated
    as a separate theorem with a sorry. -/
structure ProperCanonicalDivisor (C : Algebraic.CompactAlgebraicCurve) extends CanonicalDivisor C where
  /-- The dimension of global sections of K equals the genus.
      This is a non-trivial theorem that requires the construction of K
      from Kähler differentials and a dimension counting argument. -/
  h0_eq_genus : h0 C K = C.genus

/-- h¹(D) = dim H¹(C, O(D)).
    Defined via Serre duality: h¹(D) = h⁰(K - D) where K is the canonical divisor.

    **Mathematical note**: The canonical divisor K is unique up to linear equivalence
    and has degree 2g - 2. The Serre duality theorem states h¹(D) = h⁰(K - D).

    For the definition, we use Classical.choice to pick a proper canonical divisor.
    The actual value is independent of the choice (up to linear equivalence). -/
noncomputable def h1 (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) : ℕ :=
  -- Use Serre duality: h¹(D) = h⁰(K - D)
  -- This requires a proper canonical divisor to exist.
  -- In a complete formalization, we would construct K from Kähler differentials.
  if h : Nonempty (ProperCanonicalDivisor C) then
    h0 C ((Classical.choice h).K - D)
  else
    0  -- Degenerate case (shouldn't happen for proper algebraic curves)

/-- Euler characteristic χ(D) = h⁰(D) - h¹(D) -/
noncomputable def eulerChar (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) : ℤ :=
  (h0 C D : ℤ) - (h1 C D : ℤ)

/-!
## Key Lemmas for Riemann-Roch

These theorems have sorrys - they represent the actual mathematical
work that needs to be done.
-/

/-- **h⁰(O) = 1**: Only constant functions have no poles.

    **Algebraic proof**:
    1. L(0) = {f ∈ K(C) : (f) ≥ 0} = {f : f has no poles}
    2. A rational function with no poles on a proper curve is regular everywhere
    3. On a proper (complete) variety over an algebraically closed field,
       a regular function is constant (this is properness, not maximum principle!)
    4. Therefore L(0) = k = ℂ, so h⁰(O) = dim L(0) = 1

    **Key point**: This uses PROPERNESS of algebraic curves, not analytic arguments. -/
theorem h0_zero (C : Algebraic.CompactAlgebraicCurve) : h0 C 0 = 1 := by
  -- h0 C 0 = finrank ℂ (RiemannRochSubmodule C 0)
  -- RiemannRochSubmodule C 0 = L(0) = {f : v_p(f) ≥ 0 for all p} ∪ {0}
  -- By regularIsConstant, this is exactly the image of ℂ under algebraMap
  unfold h0
  -- We need to show finrank ℂ (RiemannRochSubmodule C 0) = 1
  -- This follows from L(0) being isomorphic to ℂ as a ℂ-module

  -- Step 1: L(0) ⊆ constants
  have h_const : ∀ f ∈ RiemannRochSubmodule C 0, ∃ c : ℂ, f = algebraMap ℂ C.FunctionField c := by
    intro f hf
    simp only [RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
               RiemannRochSpace] at hf
    rcases hf with rfl | hf_val
    · use 0; simp only [map_zero]
    · have hf_reg : ∀ p, 0 ≤ C.valuation p f := by
        intro p; have := hf_val p; simp only [Core.Divisor.zero_coeff, add_zero] at this; exact this
      exact Algebraic.CompactAlgebraicCurve.regularIsConstant C f hf_reg

  -- Step 2: Constants ⊆ L(0)
  have h_const_mem : ∀ c : ℂ, algebraMap ℂ C.FunctionField c ∈ RiemannRochSubmodule C 0 := by
    intro c
    simp only [RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
               RiemannRochSpace]
    by_cases hc : c = 0
    · left; simp only [hc, map_zero]
    · right
      intro p
      simp only [Core.Divisor.zero_coeff, add_zero]
      exact le_of_eq (C.algebraInst.valuation_algebraMap p c hc).symm

  -- Step 3: Construct a linear equivalence L(0) ≃ₗ[ℂ] ℂ
  -- The map ℂ → L(0) given by c ↦ algebraMap c is surjective (by h_const)
  -- and injective (algebraMap is injective for field extensions)

  -- Define the linear map ℂ → L(0)
  let toL0 : ℂ →ₗ[ℂ] (RiemannRochSubmodule C 0) := {
    toFun := fun c => ⟨algebraMap ℂ C.FunctionField c, h_const_mem c⟩
    map_add' := by
      intros x y
      apply Subtype.ext
      simp only [AddMemClass.mk_add_mk, map_add]
    map_smul' := by
      intros m x
      apply Subtype.ext
      simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def, map_mul,
                 Algebra.algebraMap_self]
  }

  -- toL0 is surjective
  have h_surj : Function.Surjective toL0 := by
    intro ⟨f, hf⟩
    obtain ⟨c, hc⟩ := h_const f hf
    use c
    apply Subtype.ext
    exact hc.symm

  -- toL0 is injective (algebraMap is injective)
  have h_inj : Function.Injective toL0 := by
    intro c₁ c₂ heq
    have : (toL0 c₁).val = (toL0 c₂).val := congrArg Subtype.val heq
    exact (algebraMap ℂ C.FunctionField).injective this

  -- toL0 is a linear equivalence
  let equiv : ℂ ≃ₗ[ℂ] (RiemannRochSubmodule C 0) :=
    LinearEquiv.ofBijective toL0 ⟨h_inj, h_surj⟩

  -- finrank is preserved by linear equivalence
  rw [← LinearEquiv.finrank_eq equiv]
  -- finrank ℂ ℂ = 1
  exact Module.finrank_self ℂ

/-- **h¹(O) = g**: First cohomology dimension equals genus.

    **Algebraic definition of genus**: The genus g of an algebraic curve is defined as
    g := dim H¹(C, O_C) = h¹(O). This is the DEFINITION of genus in algebraic geometry.

    **Consistency check**: This agrees with the topological genus via:
    - Algebraic: g = h¹(O) = h⁰(K) (by Serre duality)
    - Topological: g = (first Betti number) / 2
    - GAGA theorem shows these coincide for complex algebraic curves

    **For the pure algebraic path**: If genus is defined topologically in
    `CompactAlgebraicCurve`, we need GAGA or the comparison theorem.
    If genus is defined as h¹(O), this theorem is definitional.

    **Current status**: Uses `C.genus` from CompactAlgebraicCurve structure.
    This should be defined as h¹(O) for the pure algebraic path. -/
theorem h1_zero (C : Algebraic.CompactAlgebraicCurve)
    (hK : Nonempty (ProperCanonicalDivisor C)) : h1 C 0 = C.genus := by
  -- h1 C 0 = h0 C (K - 0) = h0 C K = C.genus
  unfold h1
  simp only [dif_pos hK]
  -- K - 0 = K
  have hK0 : (Classical.choice hK).K - 0 = (Classical.choice hK).K := sub_zero _
  rw [hK0]
  exact (Classical.choice hK).h0_eq_genus

/-- **Alternating sum lemma for exact sequences**.

    For a six-term exact sequence of finite-dimensional vector spaces:
      0 → V₁ → V₂ → V₃ → V₄ → V₅ → V₆ → 0
    we have: dim V₁ - dim V₂ + dim V₃ - dim V₄ + dim V₅ - dim V₆ = 0

    This is a standard result in homological algebra (Euler-Poincaré principle). -/
theorem exact_sequence_alternating_sum
    (V₁ V₂ V₃ V₄ V₅ V₆ : Type*) [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃]
    [AddCommGroup V₄] [AddCommGroup V₅] [AddCommGroup V₆]
    [Module ℂ V₁] [Module ℂ V₂] [Module ℂ V₃] [Module ℂ V₄] [Module ℂ V₅] [Module ℂ V₆]
    [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₂] [FiniteDimensional ℂ V₃]
    [FiniteDimensional ℂ V₄] [FiniteDimensional ℂ V₅] [FiniteDimensional ℂ V₆]
    (f₁ : V₁ →ₗ[ℂ] V₂) (f₂ : V₂ →ₗ[ℂ] V₃) (f₃ : V₃ →ₗ[ℂ] V₄)
    (f₄ : V₄ →ₗ[ℂ] V₅) (f₅ : V₅ →ₗ[ℂ] V₆)
    (hinj : Function.Injective f₁) (hsurj : Function.Surjective f₅)
    (hex₂ : LinearMap.ker f₂ = LinearMap.range f₁)
    (hex₃ : LinearMap.ker f₃ = LinearMap.range f₂)
    (hex₄ : LinearMap.ker f₄ = LinearMap.range f₃)
    (hex₅ : LinearMap.ker f₅ = LinearMap.range f₄) :
    (Module.finrank ℂ V₁ : ℤ) - Module.finrank ℂ V₂ + Module.finrank ℂ V₃ -
    Module.finrank ℂ V₄ + Module.finrank ℂ V₅ - Module.finrank ℂ V₆ = 0 := by
  -- Rank-nullity: finrank V = finrank (ker f) + finrank (range f)
  -- By exactness:
  --   ker f₂ = range f₁ ≅ V₁ (since f₁ is injective)
  --   ker f₃ = range f₂
  --   ker f₄ = range f₃
  --   ker f₅ = range f₄
  --   range f₅ = V₆ (since f₅ is surjective)

  -- Let a = finrank V₁, b = finrank (range f₂), c = finrank (range f₃),
  -- d = finrank (range f₄), e = finrank V₆

  -- By rank-nullity:
  --   finrank V₂ = finrank (ker f₂) + finrank (range f₂) = a + b
  --   finrank V₃ = finrank (ker f₃) + finrank (range f₃) = b + c
  --   finrank V₄ = finrank (ker f₄) + finrank (range f₄) = c + d
  --   finrank V₅ = finrank (ker f₅) + finrank (range f₅) = d + e

  -- Alternating sum: a - (a+b) + (b+c) - (c+d) + (d+e) - e = 0

  -- Rank-nullity lemmas
  have rn₂ := Submodule.finrank_quotient_add_finrank (LinearMap.ker f₂)
  have rn₃ := Submodule.finrank_quotient_add_finrank (LinearMap.ker f₃)
  have rn₄ := Submodule.finrank_quotient_add_finrank (LinearMap.ker f₄)
  have rn₅ := Submodule.finrank_quotient_add_finrank (LinearMap.ker f₅)

  -- Convert quotient dimensions to range dimensions using quotKerEquivRange
  rw [LinearEquiv.finrank_eq f₂.quotKerEquivRange] at rn₂
  rw [LinearEquiv.finrank_eq f₃.quotKerEquivRange] at rn₃
  rw [LinearEquiv.finrank_eq f₄.quotKerEquivRange] at rn₄
  rw [LinearEquiv.finrank_eq f₅.quotKerEquivRange] at rn₅

  -- Exactness: ker = range of previous map
  have hk₂ : Module.finrank ℂ (LinearMap.ker f₂) = Module.finrank ℂ V₁ := by
    rw [hex₂]
    -- range f₁ ≅ V₁ since f₁ is injective, so V₁/ker(f₁) ≅ range(f₁) and ker(f₁) = 0
    rw [LinearEquiv.finrank_eq (LinearEquiv.ofInjective f₁ hinj)]
  have hk₃ : Module.finrank ℂ (LinearMap.ker f₃) = Module.finrank ℂ (LinearMap.range f₂) := by
    rw [hex₃]
  have hk₄ : Module.finrank ℂ (LinearMap.ker f₄) = Module.finrank ℂ (LinearMap.range f₃) := by
    rw [hex₄]
  have hk₅ : Module.finrank ℂ (LinearMap.ker f₅) = Module.finrank ℂ (LinearMap.range f₄) := by
    rw [hex₅]
  have hr₅ : Module.finrank ℂ (LinearMap.range f₅) = Module.finrank ℂ V₆ := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    exact finrank_top ℂ V₆

  -- Now the algebra
  omega

/-- **Point exact sequence**: χ(D) - χ(D - p) = 1.

    **Proof**: From the short exact sequence 0 → O(D-p) → O(D) → ℂ_p → 0, we get
    the long exact sequence in cohomology:

      0 → L(D-p) → L(D) → H⁰(ℂ_p) → H¹(D-p) → H¹(D) → H¹(ℂ_p) → 0

    where H⁰(ℂ_p) = ℂ (dimension 1) and H¹(ℂ_p) = 0 (skyscraper is acyclic).

    By the alternating sum lemma:
      h⁰(D-p) - h⁰(D) + 1 - h¹(D-p) + h¹(D) - 0 = 0

    Rearranging:
      (h⁰(D) - h¹(D)) - (h⁰(D-p) - h¹(D-p)) = 1
      χ(D) - χ(D-p) = 1 ∎

    **Infrastructure used**:
    - L(D-p) ⊆ L(D) (RiemannRochSubmodule_sub_point_le)
    - Serre duality: h¹(D) = h⁰(K-D) (definition of h1)
    - H⁰(ℂ_p) = ℂ, H¹(ℂ_p) = 0 (skyscraper sheaf properties)
    - Long exact sequence in cohomology (homological algebra) -/
theorem eulerChar_point_exact (C : Algebraic.CompactAlgebraicCurve)
    (hK : Nonempty (ProperCanonicalDivisor C))
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) :
    eulerChar C D - eulerChar C (D - Core.Divisor.point p) = 1 := by
  -- Step 1: Set up the six-term exact sequence
  -- V₁ = L(D-p), V₂ = L(D), V₃ = ℂ (H⁰ of skyscraper), V₄ = H¹(D-p), V₅ = H¹(D), V₆ = 0
  --
  -- Step 2: Apply alternating sum formula
  -- h⁰(D-p) - h⁰(D) + 1 - h¹(D-p) + h¹(D) - 0 = 0
  --
  -- Step 3: Rearrange to get χ(D) - χ(D-p) = 1
  --
  -- The key facts needed:
  -- 1. The long exact sequence exists (from short exact sequence of sheaves)
  -- 2. H⁰(ℂ_p) = ℂ has dimension 1
  -- 3. H¹(ℂ_p) = 0 (skyscraper sheaf is acyclic in degree ≥ 1)
  -- 4. All cohomology groups are finite-dimensional (Cartan-Serre)
  --
  -- These facts are proven in GAGA/Cohomology/ExactSequence.lean for the analytic case.
  -- The algebraic version uses the same argument via algebraic sheaf cohomology.
  sorry

/-- **Negative degree vanishing**: h⁰(D) = 0 when deg(D) < 0.

    **Algebraic proof**:
    1. Suppose f ∈ L(D) \ {0}, i.e., f ≠ 0 and (f) + D ≥ 0
    2. Taking degrees: deg((f) + D) ≥ 0
    3. By the degree formula: deg((f) + D) = deg((f)) + deg(D)
    4. For a principal divisor on a proper curve: deg((f)) = 0
       (this is the algebraic "argument principle" - zeros = poles)
    5. Therefore: 0 + deg(D) = deg(D) ≥ 0
    6. This contradicts deg(D) < 0, so L(D) = {0}, hence h⁰(D) = 0

    **Key fact used**: deg((f)) = 0 for f ∈ K(C)*, which follows from properness. -/
theorem h0_neg_degree (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) (hneg : D.degree < 0) : h0 C D = 0 := by
  -- h0 C D = finrank ℂ (RiemannRochSubmodule C D)
  -- We show L(D) = {0} when deg(D) < 0, hence finrank = 0

  -- Key lemma: L(D) only contains 0 when deg(D) < 0
  have h_only_zero : ∀ f ∈ RiemannRochSubmodule C D, f = 0 := by
    intro f hf
    -- Suppose f ≠ 0, derive contradiction
    by_contra hfne
    simp only [RiemannRochSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
               RiemannRochSpace] at hf
    rcases hf with rfl | hf_val
    · exact hfne rfl
    -- hf_val : ∀ p, v_p(f) + D.coeff p ≥ 0

    -- div(f) + D is effective (all coefficients ≥ 0)
    have heff : Core.Divisor.IsEffective (Core.Divisor.divOf f hfne + D) := by
      intro p
      simp only [Core.Divisor.add_coeff, Core.Divisor.divOf_coeff]
      exact hf_val p

    -- Effective divisors have non-negative degree
    have hdeg_nonneg := Core.Divisor.degree_nonneg_of_isEffective _ heff

    -- deg(div(f) + D) = deg(div(f)) + deg(D) = 0 + deg(D) = deg(D)
    have hdeg_eq : (Core.Divisor.divOf f hfne + D).degree = D.degree := by
      rw [Core.Divisor.degree_add]
      -- deg(div(f)) = orderSum f = 0 by argument principle
      rw [Core.Divisor.divOf_degree_eq_orderSum]
      rw [C.argumentPrinciple f hfne]
      ring

    -- So deg(D) ≥ 0, but we assumed deg(D) < 0
    rw [hdeg_eq] at hdeg_nonneg
    exact not_lt.mpr hdeg_nonneg hneg

  -- Now show finrank = 0 using h_only_zero
  unfold h0
  -- The submodule is {0}, so finrank = 0
  have h_eq_bot : RiemannRochSubmodule C D = ⊥ := by
    ext x
    simp only [Submodule.mem_bot]
    constructor
    · exact h_only_zero x
    · intro hx; rw [hx]; exact (RiemannRochSubmodule C D).zero_mem
  rw [h_eq_bot]
  simp only [finrank_bot]

/-- **Serre duality**: h¹(D) = h⁰(K - D).

    **Algebraic proof** (Serre's original approach):
    1. Define the residue pairing: H⁰(K-D) × H¹(D) → H¹(K) → k
       - Cup product gives H⁰(K-D) ⊗ H¹(D) → H¹(K)
       - Residue map gives H¹(K) → k (sum of residues = 0 for exact forms)
    2. Show this pairing is perfect (non-degenerate on both sides)
    3. A perfect pairing implies dim H⁰(K-D) = dim H¹(D)
    4. Therefore h¹(D) = h⁰(K - D)

    This is purely algebraic - the residue can be defined algebraically
    via Kähler differentials and the trace map. -/
theorem serre_duality (C : Algebraic.CompactAlgebraicCurve)
    (K : CanonicalDivisor C) (D : Core.Divisor C.toAlgebraicCurve) :
    h1 C D = h0 C (K.K - D) := by
  sorry

/-!
## Riemann-Roch Theorem

The main theorem follows from the lemmas above by induction.
Since the lemmas have sorrys, this theorem also effectively has sorrys.
-/

-- Helper lemmas for the induction
private theorem degree_sub_point (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) :
    (D - Core.Divisor.point p).degree = D.degree - 1 := by
  rw [Core.Divisor.sub_eq_add_neg, Core.Divisor.degree_add,
      Core.Divisor.degree_neg, Core.Divisor.degree_point]
  ring

private theorem sub_succ_smul_point (C : Algebraic.CompactAlgebraicCurve)
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) (n : ℕ) :
    D - ((n + 1 : ℕ) : ℤ) • Core.Divisor.point p =
    D - (n : ℤ) • Core.Divisor.point p - Core.Divisor.point p := by
  ext q
  simp only [Core.Divisor.sub_coeff, Core.Divisor.smul_coeff, Core.Divisor.point]
  split_ifs with hqp
  · simp only [mul_one]; omega
  · simp only [mul_zero, sub_zero]

private theorem chi_diff_nat (C : Algebraic.CompactAlgebraicCurve)
    (hK : Nonempty (ProperCanonicalDivisor C))
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) (n : ℕ) :
    eulerChar C D - eulerChar C (D - (n : ℤ) • Core.Divisor.point p) = n := by
  induction n with
  | zero =>
    have h : D - (0 : ℤ) • Core.Divisor.point p = D := by
      ext q; simp only [Core.Divisor.sub_coeff, Core.Divisor.smul_coeff, zero_mul, sub_zero]
    simp only [Nat.cast_zero, h, sub_self]
  | succ k ih =>
    rw [sub_succ_smul_point C D p k]
    let D' := D - (k : ℤ) • Core.Divisor.point p
    have hpt := eulerChar_point_exact C hK D' p
    calc eulerChar C D - eulerChar C (D' - Core.Divisor.point p)
        = (eulerChar C D - eulerChar C D') + (eulerChar C D' - eulerChar C (D' - Core.Divisor.point p)) := by ring
      _ = (k : ℤ) + 1 := by rw [ih, hpt]
      _ = (k + 1 : ℕ) := by omega

private theorem chi_diff_nat_neg (C : Algebraic.CompactAlgebraicCurve)
    (hK : Nonempty (ProperCanonicalDivisor C))
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) (n : ℕ) :
    eulerChar C D - eulerChar C (D + (n : ℤ) • Core.Divisor.point p) = -(n : ℤ) := by
  let D' := D + (n : ℤ) • Core.Divisor.point p
  have h := chi_diff_nat C hK D' p n
  have hD : D' - (n : ℤ) • Core.Divisor.point p = D := by
    ext q; simp only [Core.Divisor.sub_coeff, Core.Divisor.add_coeff,
                      Core.Divisor.smul_coeff, D']; ring
  rw [hD] at h; linarith

private theorem chi_deg_invariant_smul (C : Algebraic.CompactAlgebraicCurve)
    (hK : Nonempty (ProperCanonicalDivisor C))
    (D : Core.Divisor C.toAlgebraicCurve) (p : C.toAlgebraicCurve.Point) (n : ℤ) :
    eulerChar C D - D.degree =
    eulerChar C (D - n • Core.Divisor.point p) - (D - n • Core.Divisor.point p).degree := by
  have hdeg : (D - n • Core.Divisor.point p).degree = D.degree - n := by
    rw [Core.Divisor.sub_eq_add_neg, Core.Divisor.degree_add,
        Core.Divisor.degree_neg, Core.Divisor.degree_smul, Core.Divisor.degree_point]
    ring
  have hchi : eulerChar C D - eulerChar C (D - n • Core.Divisor.point p) = n := by
    rcases n with (m | m)
    · exact chi_diff_nat C hK D p m
    · have heq : D - Int.negSucc m • Core.Divisor.point p =
                 D + ((m + 1 : ℕ) : ℤ) • Core.Divisor.point p := by
        ext q
        simp only [Core.Divisor.sub_coeff, Core.Divisor.add_coeff,
                   Core.Divisor.smul_coeff, Int.negSucc_eq, Nat.cast_add, Nat.cast_one]
        ring
      rw [heq]
      have h := chi_diff_nat_neg C hK D p (m + 1)
      simp only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one] at h ⊢
      exact h
  omega

private theorem chi_deg_base (C : Algebraic.CompactAlgebraicCurve)
    (hK : Nonempty (ProperCanonicalDivisor C)) :
    eulerChar C 0 - (0 : Core.Divisor C.toAlgebraicCurve).degree = 1 - C.genus := by
  simp only [Core.Divisor.degree_zero, sub_zero]
  unfold eulerChar
  rw [h0_zero C, h1_zero C hK]
  ring

/-- **Riemann-Roch Theorem** for algebraic curves.

    χ(D) = deg(D) + 1 - g

    **Hypotheses**:
    - hK: A proper canonical divisor exists (with h⁰(K) = g and the pointExactFormula)

    **Proof**: The proof is by strong induction on the support cardinality of D.
    The key step uses `eulerChar_point_exact` (χ(D) - χ(D-p) = 1) derived from
    the long exact sequence in sheaf cohomology.

    **Remaining sorrys** (not used in this proof):
    - `RiemannRochSubmodule_finiteDimensional`: Cartan-Serre finiteness
    - `serre_duality`: h¹(D) = h⁰(K - D) -/
theorem riemann_roch_algebraic (C : Algebraic.CompactAlgebraicCurve)
    (hK : Nonempty (ProperCanonicalDivisor C))
    (D : Core.Divisor C.toAlgebraicCurve) :
    eulerChar C D = D.degree + 1 - C.genus := by
  suffices h : eulerChar C D - D.degree = 1 - C.genus by omega
  induction hind : D.supportCard using Nat.strong_induction_on generalizing D with
  | _ n ih =>
    by_cases hD : D = 0
    · rw [hD]; exact chi_deg_base C hK
    · obtain ⟨p, hp⟩ := Core.Divisor.exists_mem_support_of_ne_zero D hD
      simp only [Core.Divisor.support, Set.mem_setOf_eq] at hp
      let D' := D - D.coeff p • Core.Divisor.point p
      have hlt : D'.supportCard < D.supportCard :=
        Core.Divisor.supportCard_sub_coeff_point_lt D p hp
      have hinv := chi_deg_invariant_smul C hK D p (D.coeff p)
      rw [hinv]
      exact ih D'.supportCard (by rw [← hind]; exact hlt) D' rfl

end RiemannSurfaces.Algebraic.Cohomology
