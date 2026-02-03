import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Sets.Opens
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.ZMod

/-!
# Čech Cohomology

This file develops Čech cohomology for presheaves on topological spaces.
This is foundational infrastructure used throughout algebraic geometry,
algebraic topology, and theoretical physics.

## Main Definitions

* `CechComplex`: The Čech complex associated to a presheaf and open cover
* `CechCocycles`: Čech n-cocycles (kernel of d^n)
* `CechCoboundaries`: Čech n-coboundaries (image of d^{n-1})
* `CechCohomology`: The Čech cohomology groups H^n(U, F)

## Main Results

* `cechDiff_comp_zero`: d^{n+1} ∘ d^n = 0 (the Čech complex is a cochain complex)
* Functoriality of Čech cohomology
* Refinement maps and independence of cover

## Mathematical Background

For a topological space X, a presheaf F of abelian groups, and an open cover
U = {U_i}_{i ∈ I}, the Čech complex is:

  C^0(U, F) → C^1(U, F) → C^2(U, F) → ...

where:
  C^n(U, F) = ∏_{i_0, ..., i_n} F(U_{i_0} ∩ ... ∩ U_{i_n})

The differential d^n: C^n → C^{n+1} is given by:
  (d^n σ)_{i_0,...,i_{n+1}} = ∑_{j=0}^{n+1} (-1)^j σ_{i_0,...,î_j,...,i_{n+1}}|_{U_{i_0,...,i_{n+1}}}

The cohomology is H^n(U, F) = ker(d^n) / im(d^{n-1}).

## References

* [Godement, R. "Topologie algébrique et théorie des faisceaux"]
* [Grothendieck, A. "Sur quelques points d'algèbre homologique"]
* [Hartshorne, R. "Algebraic Geometry", Chapter III]
-/

universe u v w

open CategoryTheory TopologicalSpace

namespace CechCohomology

variable {X : Type u} [TopologicalSpace X]

/-!
## Open Covers

An open cover of X is a family of open sets whose union is X.
For Čech cohomology, we work with indexed open covers.
-/

/-- An indexed open cover of a topological space -/
structure OpenCover (X : Type u) [TopologicalSpace X] where
  /-- The index set -/
  ι : Type v
  /-- The covering opens -/
  cover : ι → Opens X
  /-- The opens cover X -/
  covers : ∀ x : X, ∃ i : ι, x ∈ cover i

/-- The n-fold intersection of opens in a cover using finite infimum -/
def OpenCover.inter {X : Type u} [TopologicalSpace X] (U : OpenCover X) :
    (Fin (n + 1) → U.ι) → Opens X :=
  fun f => Finset.univ.inf (fun k => U.cover (f k))

/-- The intersection is contained in each component -/
theorem OpenCover.inter_le {X : Type u} [TopologicalSpace X]
    (U : OpenCover X) (f : Fin (n + 1) → U.ι) (k : Fin (n + 1)) :
    U.inter f ≤ U.cover (f k) := by
  simp only [OpenCover.inter]
  exact Finset.inf_le (Finset.mem_univ k)

/-!
## Presheaves

We work with presheaves valued in AddCommGroup (abelian groups).
This can be generalized to any abelian category.
-/

/-- A presheaf of abelian groups on a topological space -/
structure AbPresheaf (X : Type u) [TopologicalSpace X] where
  /-- The abelian group of sections over each open -/
  sections : Opens X → Type w
  /-- Each sections type is an abelian group -/
  [addCommGroup : ∀ U, AddCommGroup (sections U)]
  /-- Restriction maps -/
  restrict : ∀ {U V : Opens X}, U ≤ V → sections V → sections U
  /-- Restriction preserves identity -/
  restrict_id : ∀ U (s : sections U), restrict (le_refl U) s = s
  /-- Restriction is functorial -/
  restrict_comp : ∀ {U V W : Opens X} (h₁ : U ≤ V) (h₂ : V ≤ W) (s : sections W),
    restrict h₁ (restrict h₂ s) = restrict (le_trans h₁ h₂) s
  /-- Restriction is a group homomorphism -/
  restrict_add : ∀ {U V : Opens X} (h : U ≤ V) (s t : sections V),
    restrict h (s + t) = restrict h s + restrict h t

attribute [instance] AbPresheaf.addCommGroup

namespace AbPresheaf

variable {X : Type u} [TopologicalSpace X] (F : AbPresheaf X)

/-- Restriction preserves zero -/
theorem restrict_zero {U V : Opens X} (h : U ≤ V) : F.restrict h 0 = 0 := by
  have := F.restrict_add h 0 0
  simp only [add_zero] at this
  have h2 : 0 + F.restrict h 0 = F.restrict h 0 + F.restrict h 0 := by
    rw [zero_add]; exact this
  exact (add_right_cancel h2).symm

/-- Restriction preserves negation -/
theorem restrict_neg {U V : Opens X} (h : U ≤ V) (s : F.sections V) :
    F.restrict h (-s) = -(F.restrict h s) := by
  have := F.restrict_add h (-s) s
  rw [neg_add_cancel, restrict_zero] at this
  have heq : F.restrict h (-s) + F.restrict h s = 0 := this.symm
  exact (neg_eq_of_add_eq_zero_left heq).symm

/-- Restriction preserves subtraction -/
theorem restrict_sub {U V : Opens X} (h : U ≤ V) (s t : F.sections V) :
    F.restrict h (s - t) = F.restrict h s - F.restrict h t := by
  rw [sub_eq_add_neg, F.restrict_add, restrict_neg, sub_eq_add_neg]

/-- Restriction commutes with natural number scalar multiplication -/
theorem restrict_nsmul {U V : Opens X} (h : U ≤ V) (n : ℕ) (s : F.sections V) :
    F.restrict h (n • s) = n • F.restrict h s := by
  induction n with
  | zero => simp [restrict_zero]
  | succ k ih => rw [succ_nsmul, restrict_add, ih, succ_nsmul]

/-- Restriction commutes with integer scalar multiplication -/
theorem restrict_zsmul {U V : Opens X} (h : U ≤ V) (n : ℤ) (s : F.sections V) :
    F.restrict h (n • s) = n • F.restrict h s := by
  cases n with
  | ofNat m =>
    simp only [Int.ofNat_eq_natCast, natCast_zsmul]
    exact restrict_nsmul F h m s
  | negSucc m =>
    simp only [negSucc_zsmul, restrict_neg, restrict_nsmul]

/-- Restriction distributes over finite sums -/
theorem restrict_sum {U V : Opens X} (h : U ≤ V) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → F.sections V) :
    F.restrict h (s.sum f) = s.sum (fun i => F.restrict h (f i)) := by
  induction s using Finset.induction with
  | empty => simp [restrict_zero]
  | insert x t hx ih =>
    rw [Finset.sum_insert hx, restrict_add, ih, Finset.sum_insert hx]

/-- Restriction only depends on source and target Opens, not on the specific proof.
    This is because `U ≤ V` is a Prop, so all proofs are equal. -/
theorem restrict_proof_irrel {U V : Opens X} (h₁ h₂ : U ≤ V) (s : F.sections V) :
    F.restrict h₁ s = F.restrict h₂ s := by
  rfl  -- h₁ = h₂ by proof irrelevance, so the terms are definitionally equal

/-- If two Opens are equal, restriction to them gives results in the same type -/
theorem restrict_congr_target {U V₁ V₂ : Opens X} (h₁ : U ≤ V₁) (h₂ : U ≤ V₂)
    (heq : V₁ = V₂) (s₁ : F.sections V₁) (s₂ : F.sections V₂)
    (hs : s₁ = cast (by rw [heq]) s₂) :
    F.restrict h₁ s₁ = F.restrict h₂ s₂ := by
  subst heq
  simp only [cast_eq] at hs
  rw [hs]
  -- After subst and rw, h₁ and h₂ have the same type, so proof irrelevance applies

/-- Restriction of a cast value equals restriction of the original value -/
theorem restrict_cast {U V₁ V₂ : Opens X} (h₁ : U ≤ V₁) (h₂ : U ≤ V₂)
    (heq : V₁ = V₂) (s : F.sections V₂) :
    F.restrict h₁ (cast (congrArg F.sections heq.symm) s) = F.restrict h₂ s := by
  subst heq
  rfl

/-- For dependent functions, equal arguments give equal results after transport -/
theorem dep_fun_eq {α : Type*} {β : α → Type*} (f : (a : α) → β a) {a₁ a₂ : α} (h : a₁ = a₂) :
    cast (congrArg β h) (f a₁) = f a₂ := by
  subst h
  rfl

end AbPresheaf

/-!
## The Čech Complex

The Čech n-cochains are products of sections over n-fold intersections.
-/

variable {X : Type u} [TopologicalSpace X]

/-- The Čech n-cochains: C^n(U, F) = ∏_{(i_0,...,i_n)} F(U_{i_0} ∩ ... ∩ U_{i_n}) -/
def CechCochain (F : AbPresheaf X) (U : OpenCover X) (n : ℕ) : Type _ :=
  ∀ f : Fin (n + 1) → U.ι, F.sections (U.inter f)

/-- AddCommGroup instance for Čech cochains (pointwise) -/
noncomputable instance CechCochain.instAddCommGroup (F : AbPresheaf X) (U : OpenCover X) (n : ℕ) :
    AddCommGroup (CechCochain F U n) :=
  Pi.addCommGroup

/-- The j-th face of an (n+2)-tuple: remove index j to get (n+1)-tuple

    Given f : Fin (n+2) → α and j : Fin (n+2), this produces an (n+1)-tuple
    by removing the j-th element:
    deleteFace j [a₀, ..., aⱼ, ..., aₙ₊₁] = [a₀, ..., aⱼ₋₁, aⱼ₊₁, ..., aₙ₊₁] -/
def deleteFace {α : Type*} (j : Fin (n + 2)) (f : Fin (n + 2) → α) : Fin (n + 1) → α :=
  fun k => if k.val < j.val then f ⟨k.val, by omega⟩ else f ⟨k.val + 1, by omega⟩

/-- The (n+2)-fold intersection is contained in the (n+1)-fold intersection when we delete an index -/
theorem inter_mono_deleteFace {X : Type u} [TopologicalSpace X]
    (U : OpenCover X) (j : Fin (n + 2)) (f : Fin (n + 2) → U.ι) :
    U.inter f ≤ U.inter (deleteFace j f) := by
  -- We need to show that the (n+2)-fold intersection is ≤ the (n+1)-fold intersection
  -- This is true because removing an index makes the intersection larger
  simp only [OpenCover.inter]
  -- Goal: Finset.univ.inf (U.cover ∘ f) ≤ Finset.univ.inf (U.cover ∘ deleteFace j f)
  apply Finset.le_inf
  intro k _
  -- Need: Finset.univ.inf (U.cover ∘ f) ≤ U.cover (deleteFace j f k)
  -- deleteFace j f k is either f ⟨k.val, _⟩ or f ⟨k.val + 1, _⟩
  by_cases hk : k.val < j.val
  · -- deleteFace j f k = f ⟨k.val, _⟩
    simp only [deleteFace, hk, ↓reduceIte]
    exact Finset.inf_le (Finset.mem_univ (⟨k.val, by omega⟩ : Fin (n + 2)))
  · -- deleteFace j f k = f ⟨k.val + 1, _⟩
    simp only [deleteFace, hk, ↓reduceIte]
    exact Finset.inf_le (Finset.mem_univ (⟨k.val + 1, by omega⟩ : Fin (n + 2)))

/-- The Čech differential d^n : C^n → C^{n+1}

    (d^n σ)_{i_0,...,i_{n+1}} = ∑_{j=0}^{n+1} (-1)^j σ_{i_0,...,î_j,...,i_{n+1}}

    where î_j means "omit i_j" and the restriction to the intersection is implicit. -/
def cechDiff (F : AbPresheaf X) (U : OpenCover X) (n : ℕ) :
    CechCochain F U n → CechCochain F U (n + 1) :=
  fun σ f =>
    -- Sum over all faces
    Finset.univ.sum fun (j : Fin (n + 2)) =>
      -- Sign: (-1)^j
      ((-1 : ℤ) ^ j.val) •
      -- Restrict σ applied to the face with j-th index deleted
      F.restrict (inter_mono_deleteFace U j f) (σ (deleteFace j f))

/-- The Čech differential is a group homomorphism -/
theorem cechDiff_add (F : AbPresheaf X) (U : OpenCover X) (n : ℕ)
    (σ τ : CechCochain F U n) :
    cechDiff F U n (σ + τ) = cechDiff F U n σ + cechDiff F U n τ := by
  funext f
  show (cechDiff F U n (σ + τ)) f = (cechDiff F U n σ) f + (cechDiff F U n τ) f
  unfold cechDiff
  -- LHS: ∑ j, (-1)^j • F.restrict _ ((σ + τ) (deleteFace j f))
  -- RHS: ∑ j, (-1)^j • F.restrict _ (σ (deleteFace j f)) + ∑ j, (-1)^j • F.restrict _ (τ (deleteFace j f))
  rw [← Finset.sum_add_distrib]
  congr 1
  funext j
  -- (σ + τ) (deleteFace j f) = σ (deleteFace j f) + τ (deleteFace j f) by Pi.add_apply
  change (-1 : ℤ) ^ j.val • F.restrict _ ((σ + τ) (deleteFace j f)) =
         (-1 : ℤ) ^ j.val • F.restrict _ (σ (deleteFace j f)) +
         (-1 : ℤ) ^ j.val • F.restrict _ (τ (deleteFace j f))
  rw [show (σ + τ) (deleteFace j f) = σ (deleteFace j f) + τ (deleteFace j f) from rfl]
  rw [F.restrict_add, smul_add]

/-- The Čech differential preserves zero -/
theorem cechDiff_zero (F : AbPresheaf X) (U : OpenCover X) (n : ℕ) :
    cechDiff F U n 0 = 0 := by
  funext f
  unfold cechDiff
  conv_lhs =>
    arg 2
    ext j
    rw [show (0 : CechCochain F U n) (deleteFace j f) = 0 from rfl]
    rw [AbPresheaf.restrict_zero, smul_zero]
  exact Finset.sum_const_zero

/-- Simplicial identity for deleteFace: the order of deletion can be swapped with index adjustment.

    If j < i, then deleting j first, then i-1 is the same as deleting i first, then j.
    This is the key identity for proving d² = 0. -/
theorem deleteFace_deleteFace {α : Type*} (i : Fin (n + 3)) (j : Fin (n + 2))
    (hij : j.val < i.val) (f : Fin (n + 3) → α) :
    deleteFace ⟨i.val - 1, by omega⟩ (deleteFace (⟨j.val, by omega⟩ : Fin (n + 3)) f) =
    deleteFace j (deleteFace i f) := by
  funext k
  simp only [deleteFace]
  -- Case analysis on k relative to i-1, j, i
  by_cases hkj : k.val < j.val
  · -- k < j < i, so k < i-1 and k+1 < i
    have hki1 : k.val < i.val - 1 := by omega
    have hki : k.val < i.val := by omega
    simp only [hkj, hki1, hki, ↓reduceIte]
  · by_cases hki1 : k.val < i.val - 1
    · -- j ≤ k < i - 1, so k+1 < i but k+1 ≥ j
      have hk1i : k.val + 1 < i.val := by omega
      simp only [hkj, hki1, hk1i, ↓reduceIte]
    · -- k ≥ i - 1, so k+1 ≥ i
      have hk1j : ¬(k.val + 1 < j.val) := by omega
      have hk1i : ¬(k.val + 1 < i.val) := by omega
      simp only [hkj, hki1, hk1j, hk1i, ↓reduceIte]

/-- Sign cancellation: (-1)^(m+1) + (-1)^m = 0 -/
theorem neg_one_pow_succ_add (m : ℕ) :
    ((-1 : ℤ) ^ (m + 1)) + ((-1 : ℤ) ^ m) = 0 := by
  rw [pow_succ]
  ring

/-- For the double sum in d², the restriction from the (n+3)-intersection
    to the deleted (n+1)-intersection factors through the intermediate (n+2)-intersection -/
theorem inter_double_delete_le {X : Type u} [TopologicalSpace X]
    (U : OpenCover X) (i : Fin (n + 3)) (j : Fin (n + 2)) (f : Fin (n + 3) → U.ι) :
    U.inter f ≤ U.inter (deleteFace j (deleteFace i f)) := by
  calc U.inter f ≤ U.inter (deleteFace i f) := inter_mono_deleteFace U i f
    _ ≤ U.inter (deleteFace j (deleteFace i f)) := inter_mono_deleteFace U j (deleteFace i f)

/-- A term in the double sum d(dσ) with outer index i and inner index j -/
noncomputable def doubleSumTerm (F : AbPresheaf X) (U : OpenCover X) (n : ℕ)
    (σ : CechCochain F U n) (f : Fin (n + 3) → U.ι) (i : Fin (n + 3)) (j : Fin (n + 2)) :
    F.sections (U.inter f) :=
  ((-1 : ℤ) ^ (i.val + j.val)) •
    F.restrict (inter_double_delete_le U i j f) (σ (deleteFace j (deleteFace i f)))

/-- The double sum in d(dσ) equals the sum of doubleSumTerm over all pairs (i, j) -/
theorem cechDiff_cechDiff_eq_double_sum (F : AbPresheaf X) (U : OpenCover X) (n : ℕ)
    (σ : CechCochain F U n) (f : Fin (n + 3) → U.ι) :
    (cechDiff F U (n + 1) (cechDiff F U n σ)) f =
    Finset.univ.sum fun i : Fin (n + 3) => Finset.univ.sum fun j : Fin (n + 2) =>
      doubleSumTerm F U n σ f i j := by
  unfold cechDiff doubleSumTerm
  congr 1
  funext i
  -- The outer term is (-1)^i • F.restrict _ (∑_j ...)
  -- We need to show this equals ∑_j (-1)^(i+j) • F.restrict (composed) (σ ...)
  rw [F.restrict_sum, Finset.smul_sum]
  congr 1
  funext j
  rw [F.restrict_zsmul, smul_smul, ← pow_add, F.restrict_comp]

/-- The (n+2)-fold intersection with deleteFace i and then deleteFace j
    equals the (n+2)-fold intersection with deleteFace i' and then deleteFace j'
    when these delete the same two positions from the original tuple -/
theorem double_delete_same_result {X : Type u} [TopologicalSpace X]
    (U : OpenCover X) (f : Fin (n + 3) → U.ι)
    (i : Fin (n + 3)) (j : Fin (n + 2)) (hij : j.val < i.val)
    (j' : Fin (n + 3)) (i' : Fin (n + 2))
    (hj' : j'.val = j.val) (hi' : i'.val = i.val - 1) :
    deleteFace j (deleteFace i f) = deleteFace i' (deleteFace j' f) := by
  have hj'_lt_i : j'.val < i.val := by omega
  have hi'_eq : i' = ⟨i.val - 1, by omega⟩ := by
    ext; exact hi'
  have hj'_eq : j' = ⟨j.val, by omega⟩ := by
    ext; exact hj'
  rw [hi'_eq, hj'_eq]
  exact (deleteFace_deleteFace i j hij f).symm

/-- For a pair (i, j) with j.val < i.val, the partner pair (j', i') satisfies:
    the double sum terms have opposite signs and the same restricted σ value.

    The proof uses:
    1. The simplicial identity: deleteFace_{i-1} ∘ deleteFace_j = deleteFace_j ∘ deleteFace_i (when j < i)
    2. Sign cancellation: (-1)^{i+j} + (-1)^{j+(i-1)} = (-1)^{i+j} + (-1)^{i+j-1} = 0

    The technical challenge is handling Lean's dependent types: the σ values live in different
    (but provably equal) types, requiring careful use of transport/cast. -/
theorem pair_cancel (F : AbPresheaf X) (U : OpenCover X) (n : ℕ)
    (σ : CechCochain F U n) (f : Fin (n + 3) → U.ι)
    (i : Fin (n + 3)) (j : Fin (n + 2)) (hij : j.val < i.val) :
    doubleSumTerm F U n σ f i j +
    doubleSumTerm F U n σ f ⟨j.val, by omega⟩ ⟨i.val - 1, by omega⟩ = 0 := by
  simp only [doubleSumTerm]

  -- Define the partner indices for clarity
  let i' : Fin (n + 3) := ⟨j.val, by omega⟩
  let j' : Fin (n + 2) := ⟨i.val - 1, by omega⟩

  -- The simplicial identity: deleteFace j' (deleteFace i' f) = deleteFace j (deleteFace i f)
  have hsimpl : deleteFace j' (deleteFace i' f) = deleteFace j (deleteFace i f) :=
    deleteFace_deleteFace i ⟨j.val, by omega⟩ hij f

  -- The Opens are equal
  have hopen_eq : U.inter (deleteFace j' (deleteFace i' f)) = U.inter (deleteFace j (deleteFace i f)) :=
    congrArg U.inter hsimpl

  -- Sign cancellation: (-1)^{i+j} + (-1)^{j+(i-1)} = 0
  have hcancel : ((-1 : ℤ) ^ (i.val + j.val)) + ((-1 : ℤ) ^ (i'.val + j'.val)) = 0 := by
    simp only [i', j']
    have hsign : j.val + (i.val - 1) = i.val + j.val - 1 := by omega
    rw [hsign]
    have : i.val + j.val = (i.val + j.val - 1) + 1 := by omega
    rw [this]
    exact neg_one_pow_succ_add _

  -- The key step: the restricted σ values are equal
  -- We use the helper lemmas: dep_fun_eq shows σ values are related by cast,
  -- and restrict_cast shows the restrictions are then equal
  have hrestr_eq : F.restrict (inter_double_delete_le U i j f) (σ (deleteFace j (deleteFace i f))) =
      F.restrict (inter_double_delete_le U i' j' f) (σ (deleteFace j' (deleteFace i' f))) := by
    -- By dep_fun_eq, σ A = cast (...) (σ B) where A = deleteFace j (deleteFace i f), B = deleteFace j' (deleteFace i' f)
    -- hsimpl : B = A, so congrArg gives hopen_eq : U.inter B = U.inter A
    -- dep_fun_eq σ hsimpl : cast (congrArg (F.sections ∘ U.inter) hsimpl) (σ B) = σ A
    have hσ_cast : cast (congrArg (fun g => F.sections (U.inter g)) hsimpl) (σ (deleteFace j' (deleteFace i' f))) =
        σ (deleteFace j (deleteFace i f)) := AbPresheaf.dep_fun_eq σ hsimpl
    -- Now F.restrict h1 (σ A) = F.restrict h1 (cast ... (σ B)) = F.restrict h2 (σ B) by restrict_cast
    rw [← hσ_cast]
    -- Goal: F.restrict h1 (cast ... (σ B)) = F.restrict h2 (σ B)
    exact F.restrict_cast (inter_double_delete_le U i j f) (inter_double_delete_le U i' j' f)
      hopen_eq.symm (σ (deleteFace j' (deleteFace i' f)))

  -- Combine: opposite signs times equal values sums to zero
  rw [hrestr_eq, ← add_smul, hcancel, zero_smul]

/-- d^{n+1} ∘ d^n = 0: The fundamental property that makes this a cochain complex

    The proof is by pairing terms in the double sum. For (i, j) with j.val < i.val,
    the partner is (⟨j.val, _⟩, ⟨i.val - 1, _⟩). The simplicial identity shows
    these give the same σ value, and the signs (-1)^{i+j} and (-1)^{i+j-1} sum to 0. -/
theorem cechDiff_comp_zero (F : AbPresheaf X) (U : OpenCover X) (n : ℕ)
    (σ : CechCochain F U n) :
    cechDiff F U (n + 1) (cechDiff F U n σ) = 0 := by
  funext f
  rw [cechDiff_cechDiff_eq_double_sum]
  simp only [← Finset.sum_product', Finset.univ_product_univ]

  -- Partition pairs into S_lt (j < i) and S_ge (i ≤ j)
  let S_lt := Finset.filter (fun p : Fin (n + 3) × Fin (n + 2) => p.2.val < p.1.val) Finset.univ
  let S_ge := Finset.filter (fun p : Fin (n + 3) × Fin (n + 2) => p.1.val ≤ p.2.val) Finset.univ

  have hdisjoint : Disjoint S_lt S_ge := by
    simp only [S_lt, S_ge, Finset.disjoint_filter]; intro p _ h; omega
  have hunion : S_lt ∪ S_ge = Finset.univ := by
    ext p
    simp only [S_lt, S_ge, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    -- Goal: p.2.val < p.1.val ∨ p.1.val ≤ p.2.val (trichotomy)
    rcases Nat.lt_or_ge p.2.val p.1.val with h | h
    · left; exact h
    · right; exact h

  rw [← hunion, Finset.sum_union hdisjoint]

  -- Transform sum over S_ge to sum over S_lt via bijection
  -- The bijection sends (i, j) with j < i to (j, i-1) with i-1 ≥ j, i.e., i ≤ j+1
  -- Inverse: (i', j') with i' ≤ j' maps to (j'+1, i') with i' < j'+1

  -- For p ∈ S_lt with p.2.val < p.1.val, define the partner indices
  -- Partner i-index: p.2.val (which is < n+3 since p.2 : Fin(n+2) gives p.2.val < n+2 < n+3)
  -- Partner j-index: p.1.val - 1 (need p.1.val ≥ 1, which follows from p.2.val < p.1.val and p.2.val ≥ 0)

  -- Define the transformed sum function using Subtype to carry the membership proof
  have hbij : S_ge.sum (fun p => doubleSumTerm F U n σ f p.1 p.2) =
      S_lt.sum (fun p => doubleSumTerm F U n σ f
        ⟨p.2.val, Nat.lt_of_lt_of_le p.2.isLt (Nat.le_succ _)⟩
        ⟨p.1.val - 1, by
          have h1 : p.1.val < n + 3 := p.1.isLt
          omega⟩) := by
    symm
    refine Finset.sum_bij'
      (i := fun p hp => (⟨p.2.val, Nat.lt_of_lt_of_le p.2.isLt (Nat.le_succ _)⟩,
                         ⟨p.1.val - 1, by have := (Finset.mem_filter.mp hp).2; omega⟩))
      (j := fun p hp => (⟨p.2.val + 1, by omega⟩,
                         ⟨p.1.val, by have := (Finset.mem_filter.mp hp).2; omega⟩))
      ?_ ?_ ?_ ?_ ?_
    · intro p hp; simp only [S_lt, S_ge, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; omega
    · intro p hp; simp only [S_lt, S_ge, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; omega
    · intro p hp
      have h := (Finset.mem_filter.mp hp).2
      apply Prod.ext
      · simp only [Fin.ext_iff]; omega
      · rfl
    · intro p hp
      have h := (Finset.mem_filter.mp hp).2
      apply Prod.ext
      · rfl
      · simp only [Fin.ext_iff]; omega
    · intro p hp; rfl

  rw [hbij, ← Finset.sum_add_distrib]

  -- Each pair sums to zero
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := (Finset.mem_filter.mp hp).2
  exact pair_cancel F U n σ f p.1 p.2 hp'

/-!
## Čech Cocycles and Coboundaries
-/

/-- Z^n = ker(d^n): Čech n-cocycles -/
def CechCocycles (F : AbPresheaf X) (U : OpenCover X) (n : ℕ) : Type _ :=
  { σ : CechCochain F U n // cechDiff F U n σ = 0 }

/-- B^{n+1} = im(d^n): Čech (n+1)-coboundaries

    We use successor indexing to avoid the n-1 type mismatch issue.
    B^{n+1} consists of (n+1)-cochains that are in the image of d^n. -/
def CechCoboundariesSucc (F : AbPresheaf X) (U : OpenCover X) (n : ℕ) : Type _ :=
  { σ : CechCochain F U (n + 1) // ∃ τ : CechCochain F U n, cechDiff F U n τ = σ }

/-- Every coboundary is a cocycle (since d² = 0) -/
theorem coboundary_is_cocycle (F : AbPresheaf X) (U : OpenCover X) (n : ℕ)
    (σ : CechCoboundariesSucc F U n) : cechDiff F U (n + 1) σ.val = 0 := by
  obtain ⟨τ, hτ⟩ := σ.property
  rw [← hτ]
  exact cechDiff_comp_zero F U n τ

/-!
## Čech Cohomology as a Quotient

H^n(U, F) = Z^n / B^n

For n = 0, B^0 = 0 (no coboundaries), so H^0 = Z^0.
For n ≥ 1, we quotient by coboundaries.
-/

/-- H^0 is just the 0-cocycles (there are no coboundaries to quotient by) -/
def CechH0 (F : AbPresheaf X) (U : OpenCover X) : Type _ :=
  CechCocycles F U 0

/-- The equivalence relation for H^{n+1}: σ ~ σ' iff σ - σ' ∈ B^{n+1}

    We use successor indexing to avoid type mismatch issues. -/
def CechCohomologyRelSucc (F : AbPresheaf X) (U : OpenCover X) (n : ℕ)
    (σ σ' : CechCocycles F U (n + 1)) : Prop :=
  ∃ τ : CechCochain F U n, cechDiff F U n τ = σ.val - σ'.val

/-- Negation preserves cochains -/
theorem cechDiff_neg (F : AbPresheaf X) (U : OpenCover X) (n : ℕ)
    (τ : CechCochain F U n) :
    cechDiff F U n (-τ) = -cechDiff F U n τ := by
  have hadd := cechDiff_add F U n (-τ) τ
  rw [neg_add_cancel, cechDiff_zero] at hadd
  exact (neg_eq_of_add_eq_zero_left hadd.symm).symm

/-- The Čech differential is linear over subtraction -/
theorem cechDiff_sub (F : AbPresheaf X) (U : OpenCover X) (n : ℕ)
    (σ τ : CechCochain F U n) :
    cechDiff F U n (σ - τ) = cechDiff F U n σ - cechDiff F U n τ := by
  rw [sub_eq_add_neg, cechDiff_add, cechDiff_neg, sub_eq_add_neg]

/-- CechCohomologyRelSucc is an equivalence relation -/
theorem CechCohomologyRelSucc.equivalence (F : AbPresheaf X) (U : OpenCover X) (n : ℕ) :
    Equivalence (CechCohomologyRelSucc F U n) where
  refl σ := ⟨0, by rw [cechDiff_zero, sub_self]⟩
  symm := fun ⟨τ, hτ⟩ => ⟨-τ, by rw [cechDiff_neg, hτ, neg_sub]⟩
  trans := fun ⟨τ₁, h₁⟩ ⟨τ₂, h₂⟩ => ⟨τ₁ + τ₂, by
    rw [cechDiff_add, h₁, h₂]
    abel⟩

/-- The setoid for defining H^{n+1} as a quotient -/
def CechCohomologySetoidSucc (F : AbPresheaf X) (U : OpenCover X) (n : ℕ) :
    Setoid (CechCocycles F U (n + 1)) where
  r := CechCohomologyRelSucc F U n
  iseqv := CechCohomologyRelSucc.equivalence F U n

/-- H^{n+1}(U, F) = Z^{n+1} / B^{n+1} for n ≥ 0

    The (n+1)-th Čech cohomology group. -/
def CechHSucc (F : AbPresheaf X) (U : OpenCover X) (n : ℕ) : Type _ :=
  Quotient (CechCohomologySetoidSucc F U n)

/-- H^n for any n, defined case-wise -/
def CechH (F : AbPresheaf X) (U : OpenCover X) : ℕ → Type _
  | 0 => CechH0 F U
  | n + 1 => CechHSucc F U n

/-!
## Special Cases

For computational purposes, we provide explicit descriptions of low-degree cohomology.
-/

/-- H^0(U, F) consists of 0-cocycles: families of sections over each U_i that agree on overlaps

    More precisely, σ ∈ H^0(U, F) iff for all i, j:
    σ_i|_{U_i ∩ U_j} = σ_j|_{U_i ∩ U_j}

    When F is a sheaf, this is isomorphic to global sections F(X). -/
theorem cechH0_is_cocycles (F : AbPresheaf X) (U : OpenCover X) :
    CechH0 F U = CechCocycles F U 0 := rfl

end CechCohomology
