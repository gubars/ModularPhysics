/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Von Neumann's Graph Theorem

This file proves von Neumann's theorem characterizing the orthogonal complement of an
operator's graph in the product Hilbert space. This is fundamental for the theory of
unbounded operators.

## Main results

* `VonNeumann.perp_snd_mem_adjDom` - Elements of graph^⊥ have second component in dom(T*)
* `VonNeumann.mem_closure_graph_of_orthogonal_adjDom` - y ⊥ dom(T*) implies (0, y) ∈ closure(graph T)

## Implementation notes

We work with WithLp 2 (H × H) to get the proper inner product space structure on the
product space. The inner product is ⟨(a,b), (c,d)⟩ = ⟨a,c⟩ + ⟨b,d⟩.

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I: Functional Analysis", Chapter VIII
* Kato, "Perturbation Theory for Linear Operators"
-/

noncomputable section

open scoped ComplexConjugate

set_option linter.unusedSectionVars false

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace VonNeumann

/-! ### The product Hilbert space -/

/-- The inner product on WithLp 2 (H × H) is the sum of component inner products -/
theorem inner_prod_eq (p q : WithLp 2 (H × H)) :
    @inner ℂ (WithLp 2 (H × H)) _ p q =
    @inner ℂ H _ p.fst q.fst + @inner ℂ H _ p.snd q.snd :=
  WithLp.prod_inner_apply p q

/-! ### Graph as a submodule of WithLp 2 (H × H) -/

/-- The graph of a linear operator as a submodule of WithLp 2 (H × H) -/
def graphLp (dom : Submodule ℂ H) (f : dom →ₗ[ℂ] H) : Submodule ℂ (WithLp 2 (H × H)) where
  carrier := { p | ∃ x : dom, p.fst = (x : H) ∧ p.snd = f x }
  add_mem' := fun {p q} hp hq => by
    obtain ⟨x, hx1, hx2⟩ := hp
    obtain ⟨y, hy1, hy2⟩ := hq
    use x + y
    constructor
    · simp only [WithLp.add_fst, Submodule.coe_add, hx1, hy1]
    · simp only [WithLp.add_snd, map_add, hx2, hy2]
  zero_mem' := by
    use 0
    simp only [WithLp.zero_fst, Submodule.coe_zero, WithLp.zero_snd, map_zero, and_self]
  smul_mem' := fun c p hp => by
    obtain ⟨x, hx1, hx2⟩ := hp
    use c • x
    constructor
    · simp only [WithLp.smul_fst, Submodule.coe_smul, hx1]
    · simp only [WithLp.smul_snd, map_smul, hx2]

/-- The adjoint domain: y such that x ↦ ⟨f x, y⟩ is bounded -/
def adjointDomain (dom : Submodule ℂ H) (f : dom →ₗ[ℂ] H) : Set H :=
  { y | ∃ C : ℝ, ∀ x : dom, ‖@inner ℂ H _ (f x) y‖ ≤ C * ‖(x : H)‖ }

/-- The adjoint domain is a submodule -/
def adjointDomainSubmodule (dom : Submodule ℂ H) (f : dom →ₗ[ℂ] H) : Submodule ℂ H where
  carrier := adjointDomain dom f
  add_mem' := fun {a b} ha hb => by
    obtain ⟨Ca, hCa⟩ := ha
    obtain ⟨Cb, hCb⟩ := hb
    use Ca + Cb
    intro x
    calc ‖@inner ℂ H _ (f x) (a + b)‖
        = ‖@inner ℂ H _ (f x) a + @inner ℂ H _ (f x) b‖ := by rw [inner_add_right]
      _ ≤ ‖@inner ℂ H _ (f x) a‖ + ‖@inner ℂ H _ (f x) b‖ := norm_add_le _ _
      _ ≤ Ca * ‖(x : H)‖ + Cb * ‖(x : H)‖ := add_le_add (hCa x) (hCb x)
      _ = (Ca + Cb) * ‖(x : H)‖ := by ring
  zero_mem' := by
    use 0
    intro x
    simp [inner_zero_right]
  smul_mem' := fun c a ha => by
    obtain ⟨Ca, hCa⟩ := ha
    use ‖c‖ * Ca
    intro x
    calc ‖@inner ℂ H _ (f x) (c • a)‖
        = ‖c * @inner ℂ H _ (f x) a‖ := by rw [inner_smul_right]
      _ = ‖c‖ * ‖@inner ℂ H _ (f x) a‖ := Complex.norm_mul c _
      _ ≤ ‖c‖ * (Ca * ‖(x : H)‖) := by apply mul_le_mul_of_nonneg_left (hCa x) (norm_nonneg _)
      _ = (‖c‖ * Ca) * ‖(x : H)‖ := by ring

/-- Characterization of the orthogonal complement of graph in WithLp 2 (H × H) -/
theorem mem_graphLp_perp_iff (dom : Submodule ℂ H) (f : dom →ₗ[ℂ] H)
    (q : WithLp 2 (H × H)) :
    q ∈ (graphLp dom f)ᗮ ↔
    ∀ x : dom, @inner ℂ H _ (x : H) q.fst + @inner ℂ H _ (f x) q.snd = 0 := by
  constructor
  · intro hq x
    have hx_in : WithLp.toLp 2 ((x : H), f x) ∈ graphLp dom f := ⟨x, rfl, rfl⟩
    have h := Submodule.inner_right_of_mem_orthogonal hx_in hq
    rw [inner_prod_eq] at h
    exact h
  · intro horth
    rw [Submodule.mem_orthogonal]
    intro p hp
    obtain ⟨x, hx1, hx2⟩ := hp
    rw [inner_prod_eq, hx1, hx2]
    exact horth x

/-- If q is in the orthogonal complement, then q.snd is in the adjoint domain -/
theorem perp_snd_mem_adjDom (dom : Submodule ℂ H) (f : dom →ₗ[ℂ] H)
    (q : WithLp 2 (H × H)) (hq : q ∈ (graphLp dom f)ᗮ) :
    q.snd ∈ adjointDomain dom f := by
  rw [mem_graphLp_perp_iff] at hq
  use ‖q.fst‖
  intro x
  have h := hq x
  -- From h: ⟨x, q.fst⟩ + ⟨f x, q.snd⟩ = 0
  -- So ⟨f x, q.snd⟩ = -⟨x, q.fst⟩
  have heq : @inner ℂ H _ (f x) q.snd = -@inner ℂ H _ (x : H) q.fst := by
    exact (add_eq_zero_iff_neg_eq.mp h).symm
  rw [heq, norm_neg]
  calc ‖@inner ℂ H _ (x : H) q.fst‖
      ≤ ‖(x : H)‖ * ‖q.fst‖ := norm_inner_le_norm _ _
    _ = ‖q.fst‖ * ‖(x : H)‖ := mul_comm _ _

/-! ### The main theorem -/

/-- Von Neumann's theorem: If y ⊥ adjointDomain, then (0, y) ∈ closure(graph) -/
theorem mem_closure_graph_of_orthogonal_adjDom (dom : Submodule ℂ H) (f : dom →ₗ[ℂ] H)
    (y : H)
    (hy : ∀ z ∈ adjointDomain dom f, @inner ℂ H _ z y = 0) :
    WithLp.toLp 2 (0, y) ∈ (graphLp dom f).topologicalClosure := by
  -- Key: (0, y) ∈ (graphLp)^⊥⊥
  -- And (graphLp)^⊥⊥ = closure(graphLp) in a Hilbert space

  have h0y_perp_perp : WithLp.toLp 2 (0, y) ∈ (graphLp dom f)ᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro q hq
    -- q ∈ (graphLp)^⊥, so q.snd ∈ adjointDomain by perp_snd_mem_adjDom
    have hq2 := perp_snd_mem_adjDom dom f q hq
    -- inner q (toLp (0, y)) = ⟨q.fst, 0⟩ + ⟨q.snd, y⟩ = ⟨q.snd, y⟩
    rw [inner_prod_eq]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd]
    rw [inner_zero_right, zero_add]
    -- y ⊥ adjointDomain, so ⟨q.snd, y⟩ = 0
    exact hy q.snd hq2

  -- Use Submodule.orthogonal_orthogonal_eq_closure
  rw [Submodule.orthogonal_orthogonal_eq_closure] at h0y_perp_perp
  exact h0y_perp_perp

/-- Corollary: y ⊥ adjointDomain implies (0, y) ∈ closure(graph) as a set in H × H -/
theorem mem_closure_graph_set_of_orthogonal_adjDom (dom : Submodule ℂ H) (f : dom →ₗ[ℂ] H)
    (y : H)
    (hy : ∀ z ∈ adjointDomain dom f, @inner ℂ H _ z y = 0) :
    (0, y) ∈ closure { p : H × H | ∃ x : dom, (x : H) = p.1 ∧ f x = p.2 } := by
  have h := mem_closure_graph_of_orthogonal_adjDom dom f y hy
  -- The topologies on WithLp 2 (H × H) and H × H are the same
  have hcont_of : Continuous (WithLp.ofLp (p := 2) : WithLp 2 (H × H) → H × H) :=
    WithLp.prod_continuous_ofLp 2 H H
  -- h : WithLp.toLp 2 (0, y) ∈ (graphLp dom f).topologicalClosure
  -- This means WithLp.toLp 2 (0, y) ∈ closure (graphLp dom f : Set _)
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at h
  -- Now h : WithLp.toLp 2 (0, y) ∈ closure (graphLp dom f : Set _)
  rw [mem_closure_iff_seq_limit] at h
  obtain ⟨seq, hseq_mem, hseq_lim⟩ := h
  rw [mem_closure_iff_seq_limit]
  use fun n => WithLp.ofLp (seq n)
  constructor
  · intro n
    obtain ⟨x, hx1, hx2⟩ := hseq_mem n
    use x
    exact ⟨hx1.symm, hx2.symm⟩
  · exact hcont_of.tendsto (WithLp.toLp 2 (0, y)) |>.comp hseq_lim

end VonNeumann
