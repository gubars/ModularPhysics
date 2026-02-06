/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Sheaves.Coherent
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

-- Note: OModuleCast.lean provides `OModule.doubleFace_restriction_eq` which can be used
-- to fix the sorry in `pair_cancel`. However, we need to avoid circular imports,
-- so the lemma is reproven inline here.

/-!
# Čech Cohomology for Algebraic Curves

This file develops Čech cohomology for algebraic curves from scratch using
purely scheme-theoretic methods. No derived functor machinery is assumed.

## Main Definitions

* `OpenCover` - An open cover of a scheme
* `CechCochain` - n-cochains for a sheaf with respect to an open cover
* `cechDifferential` - The Čech differential d : Cⁿ → Cⁿ⁺¹
* `CechCocycles` - Cocycles ker(d)
* `CechCoboundaries` - Coboundaries im(d)
* `CechCohomology` - Čech cohomology Ȟⁿ = Zⁿ/Bⁿ

## Main Results

* `cechDifferential_sq_zero` - d² = 0
* `CechCohomology_addCommGroup` - Čech cohomology forms an abelian group

## Design

We work with finite open covers and explicit products of sections over
intersections. For curves, any open cover can be refined to an affine cover,
and Čech cohomology with respect to affine covers computes sheaf cohomology.

## References

* Hartshorne, "Algebraic Geometry", Chapter III.4 (Čech Cohomology)
* Stacks Project, Tag 01ED (Čech Cohomology)
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

namespace RiemannSurfaces.SchemeTheoretic

/-!
## Open Covers

An open cover of a scheme X is a collection of open subsets whose union is X.
-/

/-- An open cover of a scheme. -/
structure OpenCover (X : Scheme) where
  /-- Index set for the cover -/
  I : Type*
  /-- The open subsets forming the cover -/
  U : I → Opens X.carrier
  /-- The cover property: every point lies in some U_i -/
  covers : ∀ x : X.carrier, ∃ i : I, x ∈ U i

/-- A finite open cover. -/
structure FiniteOpenCover (X : Scheme) extends OpenCover X where
  /-- The index set is finite -/
  finite : Finite I

variable {X : Scheme}

/-- Intersection of opens in a cover indexed by a finite set of indices.
    For indices σ : Fin n → I, returns ⋂_{j ∈ Fin n} U(σ j). -/
noncomputable def OpenCover.intersection (𝒰 : OpenCover X) {n : ℕ} (σ : Fin n → 𝒰.I) : Opens X.carrier :=
  if _ : n = 0 then ⊤
  else ⨅ j : Fin n, 𝒰.U (σ j)

/-- The intersection is contained in each U(σ j). -/
theorem OpenCover.intersection_le (𝒰 : OpenCover X) {n : ℕ} (hn : n ≠ 0) (σ : Fin n → 𝒰.I) (j : Fin n) :
    𝒰.intersection σ ≤ 𝒰.U (σ j) := by
  unfold intersection
  simp only [hn, ↓reduceDIte]
  exact iInf_le (fun j => 𝒰.U (σ j)) j

/-!
## Čech Cochains

For a presheaf F and an open cover 𝒰, an n-cochain assigns to each
n-simplex σ = (i₀, ..., iₙ) an element of F(U_{i₀} ∩ ... ∩ U_{iₙ}).
-/

/-- The type of n-cochains for a presheaf F with respect to an open cover 𝒰.

    An n-cochain assigns to each (n+1)-tuple of indices an element of the
    sections over the corresponding intersection. -/
noncomputable def CechCochain (F : OModule X) (𝒰 : OpenCover X) (n : ℕ) : Type _ :=
  (σ : Fin (n + 1) → 𝒰.I) → F.val.obj (Opposite.op (𝒰.intersection σ))

variable (F : OModule X) (𝒰 : OpenCover X)

/-- CechCochain forms an additive group using Pi structure. -/
noncomputable instance CechCochain.addCommGroup : AddCommGroup (CechCochain F 𝒰 n) :=
  Pi.addCommGroup

/-!
## The Čech Differential

The differential d : Cⁿ → Cⁿ⁺¹ is defined by the alternating sum:
  (df)(i₀, ..., iₙ₊₁) = Σⱼ (-1)ʲ ρ(f(i₀, ..., îⱼ, ..., iₙ₊₁))
where ρ is the restriction map and îⱼ means omit the j-th index.
-/

/-- Face map: delete the j-th index from a function Fin (n+2) → I.
    δʲ : (Fin (n+2) → I) → (Fin (n+1) → I) -/
def faceMap {I : Type*} (j : Fin (n + 2)) : (Fin (n + 2) → I) → (Fin (n + 1) → I) :=
  fun σ k => if k.val < j.val then σ ⟨k.val, Nat.lt_of_lt_of_le k.isLt (Nat.le_succ _)⟩
             else σ ⟨k.val + 1, Nat.add_lt_add_right k.isLt 1⟩

/-- The intersection for (n+2)-simplex is contained in the intersection for
    any face (n+1-simplex). -/
theorem intersection_face_le (𝒰 : OpenCover X) {n : ℕ} (σ : Fin (n + 2) → 𝒰.I) (j : Fin (n + 2)) :
    𝒰.intersection σ ≤ 𝒰.intersection (faceMap j σ) := by
  -- The full intersection is contained in each face intersection
  -- because removing one term from the intersection makes it larger
  unfold OpenCover.intersection
  simp only [Nat.add_one_ne_zero, ↓reduceDIte]
  -- Goal: ⨅ i, 𝒰.U (σ i) ≤ ⨅ k, 𝒰.U (faceMap j σ k)
  -- Suffices to show: ∀ k, (⨅ i, 𝒰.U (σ i)) ≤ 𝒰.U (faceMap j σ k)
  apply le_iInf
  intro k
  -- Need: ⨅ i, 𝒰.U (σ i) ≤ 𝒰.U (faceMap j σ k)
  -- faceMap j σ k = σ(k) if k < j, else σ(k+1)
  -- Either way, it's σ of some index, so we use iInf_le
  simp only [faceMap]
  split_ifs with h
  · -- Case k < j: faceMap j σ k = σ ⟨k, ...⟩
    exact iInf_le (fun i => 𝒰.U (σ i)) ⟨k.val, Nat.lt_of_lt_of_le k.isLt (Nat.le_succ _)⟩
  · -- Case k ≥ j: faceMap j σ k = σ ⟨k+1, ...⟩
    exact iInf_le (fun i => 𝒰.U (σ i)) ⟨k.val + 1, Nat.add_lt_add_right k.isLt 1⟩

/-- Restriction map from the face intersection to the full (n+2)-simplex intersection. -/
noncomputable def restrictionToFace (F : OModule X) (𝒰 : OpenCover X) {n : ℕ}
    (σ : Fin (n + 2) → 𝒰.I) (j : Fin (n + 2)) :
    F.val.obj (Opposite.op (𝒰.intersection (faceMap j σ))) →
    F.val.obj (Opposite.op (𝒰.intersection σ)) :=
  F.val.map (homOfLE (intersection_face_le 𝒰 σ j)).op

/-- The Čech differential d : Cⁿ → Cⁿ⁺¹.

    For a cochain c ∈ Cⁿ, the differential (dc)(σ) for σ : Fin (n+2) → I is
    the alternating sum Σⱼ (-1)ʲ ρⱼ(c(δʲσ)) where:
    - δʲσ is the j-th face (delete j from σ)
    - ρⱼ is restriction from the face intersection to the full intersection

    Since F.val.obj _ is a module, we can take the alternating sum. -/
noncomputable def cechDifferential (F : OModule X) (𝒰 : OpenCover X) (n : ℕ) :
    CechCochain F 𝒰 n → CechCochain F 𝒰 (n + 1) := fun c σ =>
  ∑ j : Fin (n + 2), (-1 : ℤ)^(j.val) • restrictionToFace F 𝒰 σ j (c (faceMap j σ))

/-- The differential as an additive group homomorphism. -/
noncomputable def cechDifferentialHom (F : OModule X) (𝒰 : OpenCover X) (n : ℕ) :
    CechCochain F 𝒰 n →+ CechCochain F 𝒰 (n + 1) where
  toFun := cechDifferential F 𝒰 n
  map_zero' := by
    -- Zero cochain maps to zero
    funext σ
    simp only [cechDifferential]
    -- Each term in the sum is (-1)^j • ρ(0) = (-1)^j • 0 = 0
    apply Finset.sum_eq_zero
    intro j _
    -- 0 (faceMap j σ) = 0 since 0 is the zero function
    rw [show (0 : CechCochain F 𝒰 n) (faceMap j σ) = 0 from rfl]
    -- restrictionToFace is F.val.map which preserves 0 (module hom maps 0 to 0)
    simp only [restrictionToFace, map_zero, smul_zero]
  map_add' := fun c₁ c₂ => by
    -- Differential is additive
    funext σ
    simp only [cechDifferential]
    -- Unfold the RHS: (d c₁ + d c₂)(σ) = d c₁ σ + d c₂ σ
    rw [show (cechDifferential F 𝒰 n c₁ + cechDifferential F 𝒰 n c₂) σ =
            cechDifferential F 𝒰 n c₁ σ + cechDifferential F 𝒰 n c₂ σ from rfl]
    simp only [cechDifferential]
    -- Now both sides are sums, use sum_add_distrib
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    -- Need: (-1)^j • ρ((c₁+c₂)(σ')) = (-1)^j • ρ(c₁(σ')) + (-1)^j • ρ(c₂(σ'))
    rw [show (c₁ + c₂) (faceMap j σ) = c₁ (faceMap j σ) + c₂ (faceMap j σ) from rfl]
    -- restrictionToFace is F.val.map which preserves addition (module hom is additive)
    simp only [restrictionToFace, map_add, smul_add]

/-!
## Properties of the Differential
-/

/-- Simplicial identity: composing face maps in different orders.

    For i < j: δⁱ ∘ δʲ = δʲ⁻¹ ∘ δⁱ (after adjusting indices)

    This is the key identity for proving d² = 0.
    The precise statement for face maps: if we delete index i first then j,
    it's the same as deleting (j-1) first then i, when i < j.

    More precisely, for σ : Fin (n+3) → I:
    - δⁱ(δʲ(σ)) removes j from σ, then removes i from the result
    - δʲ⁻¹(δⁱ(σ)) removes i from σ, then removes j-1 from the result
    These are equal when i < j because removing i shifts j down by 1. -/
theorem faceMap_simplicial {I : Type*} {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 3))
    (hij : i.val < j.val) (σ : Fin (n + 3) → I) :
    faceMap i (faceMap ⟨j.val, by omega⟩ σ) =
    faceMap ⟨j.val - 1, by omega⟩ (faceMap ⟨i.val, by omega⟩ σ) := by
  -- The simplicial identity follows from case analysis on index positions
  -- LHS: first delete j from σ, then delete i from result
  -- RHS: first delete i from σ, then delete (j-1) from result
  -- Since i < j, after deleting i, the position j becomes j-1
  funext k
  simp only [faceMap]
  -- Case analysis on k relative to i and j-1
  -- After split_ifs, we need to show σ applied to equal Fin elements are equal
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  all_goals first | rfl | (congr 1; ext; omega)

/-- Alternative simplicial identity: for the proof of d² = 0, we need this form.
    When j < i (as natural numbers), δʲ(δⁱσ) = δⁱ⁻¹(δʲσ).

    This is the form needed for pairing terms in the double sum. -/
theorem faceMap_simplicial' {I : Type*} {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2))
    (hij : j.val < i.val) (σ : Fin (n + 3) → I) :
    faceMap j (faceMap i σ) =
    faceMap ⟨i.val - 1, by omega⟩ (faceMap ⟨j.val, by omega⟩ σ) := by
  -- Use the original simplicial identity with appropriate index adjustments
  have hj' : (⟨j.val, by omega⟩ : Fin (n + 2)).val < i.val := hij
  have heq := faceMap_simplicial (⟨j.val, by omega⟩ : Fin (n + 2)) i hj' σ
  simp only at heq
  exact heq

/-- Sign cancellation lemma: (-1)^{i+j} + (-1)^{j+(i-1)} = 0 when i ≥ 1. -/
theorem sign_cancel (i j : ℕ) (hi : i ≥ 1) :
    ((-1 : ℤ)^(i + j)) + ((-1 : ℤ)^(j + (i - 1))) = 0 := by
  have h : j + (i - 1) = i + j - 1 := by omega
  rw [h]
  have h2 : i + j = (i + j - 1) + 1 := by omega
  conv_lhs => arg 1; rw [h2, pow_succ]
  -- Now have: (-1)^(i+j-1) * -1 + (-1)^(i+j-1) = 0
  ring

/-- The intersection after two face maps is ≤ the original intersection. -/
theorem intersection_double_face_le (𝒰 : OpenCover X) {n : ℕ} (σ : Fin (n + 3) → 𝒰.I)
    (i : Fin (n + 3)) (j : Fin (n + 2)) :
    𝒰.intersection σ ≤ 𝒰.intersection (faceMap j (faceMap i σ)) := by
  calc 𝒰.intersection σ ≤ 𝒰.intersection (faceMap i σ) := intersection_face_le 𝒰 σ i
    _ ≤ 𝒰.intersection (faceMap j (faceMap i σ)) := intersection_face_le 𝒰 (faceMap i σ) j

/-- Restriction commutes with integer scalar multiplication. -/
theorem restrict_zsmul (F : OModule X) {U V : Opens X.carrier} (h : U ≤ V)
    (n : ℤ) (x : F.val.obj (Opposite.op V)) :
    F.val.map (homOfLE h).op (n • x) = n • F.val.map (homOfLE h).op x := by
  rw [map_zsmul]

/-- Restriction commutes with sums. -/
theorem restrict_sum (F : OModule X) {U V : Opens X.carrier} (h : U ≤ V)
    {ι : Type*} (s : Finset ι) (f : ι → F.val.obj (Opposite.op V)) :
    F.val.map (homOfLE h).op (∑ i ∈ s, f i) = ∑ i ∈ s, F.val.map (homOfLE h).op (f i) := by
  rw [map_sum]

/-- A term in the double sum d(dc)(σ) for the pair (i, j). -/
noncomputable def doubleSumTerm (F : OModule X) (𝒰 : OpenCover X) (n : ℕ)
    (c : CechCochain F 𝒰 n) (σ : Fin (n + 3) → 𝒰.I) (i : Fin (n + 3)) (j : Fin (n + 2)) :
    F.val.obj (Opposite.op (𝒰.intersection σ)) :=
  ((-1 : ℤ)^(i.val + j.val)) •
    F.val.map (homOfLE (intersection_double_face_le 𝒰 σ i j)).op
      (c (faceMap j (faceMap i σ)))

/-- The double sum in d(dc)(σ) equals the sum of doubleSumTerm over all pairs (i, j). -/
theorem cechDifferential_cechDifferential_eq_double_sum (F : OModule X) (𝒰 : OpenCover X) (n : ℕ)
    (c : CechCochain F 𝒰 n) (σ : Fin (n + 3) → 𝒰.I) :
    (cechDifferential F 𝒰 (n + 1) (cechDifferential F 𝒰 n c)) σ =
    ∑ i : Fin (n + 3), ∑ j : Fin (n + 2), doubleSumTerm F 𝒰 n c σ i j := by
  simp only [cechDifferential, doubleSumTerm, restrictionToFace]
  congr 1
  funext i
  -- The outer term is (-1)^i • F.val.map ... (∑ⱼ ...)
  -- First push the map through the sum
  rw [map_sum]
  -- Then push the scalar through the sum
  rw [Finset.smul_sum]
  congr 1
  funext j
  -- For each j, we have (-1)^i • F.val.map ρᵢ ((-1)^j • F.val.map ρⱼ (c ...))
  rw [map_zsmul, smul_smul]
  -- Convert (-1)^i * (-1)^j to (-1)^(i+j)
  have hpow : ((-1 : ℤ)^(i.val)) * ((-1 : ℤ)^(j.val)) = (-1 : ℤ)^(i.val + j.val) := by
    rw [← pow_add]
  rw [hpow]
  congr 1
  -- The restrictions compose: F.val.map h1 (F.val.map h2 x) = F.val.map (h2 ≫ h1) x
  -- In the opposite category, h1.op ≫ h2.op corresponds to (h2 ≫ h1) in the original
  -- Use functoriality: F.val.map (f ≫ g) = F.val.map f ≫ F.val.map g
  have hcomp : (homOfLE (intersection_face_le 𝒰 (faceMap i σ) j)).op ≫
      (homOfLE (intersection_face_le 𝒰 σ i)).op =
      (homOfLE (intersection_double_face_le 𝒰 σ i j)).op := rfl
  rw [← hcomp, F.val.map_comp]
  rfl

/-- Paired terms in the double sum cancel.
    For (i, j) with j.val < i.val, the partner (j', i-1) has opposite sign
    and the same face (by simplicial identity). -/
theorem pair_cancel (F : OModule X) (𝒰 : OpenCover X) (n : ℕ)
    (c : CechCochain F 𝒰 n) (σ : Fin (n + 3) → 𝒰.I)
    (i : Fin (n + 3)) (j : Fin (n + 2)) (hij : j.val < i.val) :
    doubleSumTerm F 𝒰 n c σ i j +
    doubleSumTerm F 𝒰 n c σ ⟨j.val, by omega⟩ ⟨i.val - 1, by omega⟩ = 0 := by
  simp only [doubleSumTerm]

  -- Define partner indices
  let i' : Fin (n + 3) := ⟨j.val, by omega⟩
  let j' : Fin (n + 2) := ⟨i.val - 1, by omega⟩

  -- The simplicial identity gives us that the faces are equal
  have hsimpl : faceMap j (faceMap i σ) = faceMap j' (faceMap i' σ) := by
    exact faceMap_simplicial' i j hij σ

  -- Therefore the intersections are equal
  have hopen_eq : 𝒰.intersection (faceMap j (faceMap i σ)) =
      𝒰.intersection (faceMap j' (faceMap i' σ)) := congrArg 𝒰.intersection hsimpl

  -- Sign cancellation: (-1)^{i+j} + (-1)^{j+(i-1)} = 0
  have hsign : ((-1 : ℤ)^(i.val + j.val)) + ((-1 : ℤ)^(i'.val + j'.val)) = 0 := by
    simp only [i', j']
    -- i'.val = j.val and j'.val = i.val - 1
    -- So we need: (-1)^{i+j} + (-1)^{j+(i-1)} = 0
    have hsum : j.val + (i.val - 1) = i.val + j.val - 1 := by omega
    rw [hsum]
    -- (-1)^{i+j} = (-1)^{(i+j-1)+1} = (-1)^{i+j-1} * (-1)
    have hsucc : i.val + j.val = (i.val + j.val - 1) + 1 := by omega
    have hlhs : ((-1 : ℤ)^(i.val + j.val)) = ((-1 : ℤ)^(i.val + j.val - 1) * (-1)) := by
      conv_lhs => rw [hsucc, pow_succ]
    rw [hlhs]
    ring

  -- The restricted values are equal because:
  -- 1. The faces are equal (hsimpl): faceMap j (faceMap i σ) = faceMap j' (faceMap i' σ)
  -- 2. When we substitute the face equality, c applied to equal faces gives equal values
  -- 3. The restriction maps through equal Opens (by hopen_eq) give equal results
  have hval_eq : F.val.map (homOfLE (intersection_double_face_le 𝒰 σ i j)).op
        (c (faceMap j (faceMap i σ))) =
      F.val.map (homOfLE (intersection_double_face_le 𝒰 σ i' j')).op
        (c (faceMap j' (faceMap i' σ))) := by
    -- Helper: when faces are equal, the restricted c-values are equal
    -- We abstract to make face a free variable so subst works
    have helper : ∀ (f₁ f₂ : Fin (n+1) → 𝒰.I) (hf : f₁ = f₂)
        (h₁ : 𝒰.intersection σ ≤ 𝒰.intersection f₁)
        (h₂ : 𝒰.intersection σ ≤ 𝒰.intersection f₂),
        F.val.map (homOfLE h₁).op (c f₁) = F.val.map (homOfLE h₂).op (c f₂) := by
      intro f₁ f₂ hf h₁ h₂
      subst hf
      rfl
    exact helper _ _ hsimpl _ _

  rw [hval_eq, ← add_smul, hsign, zero_smul]

/-- The fundamental property: d² = 0.

    **Proof strategy:**
    Expand d²c(σ) = Σᵢ Σⱼ (-1)^{i+j} ρᵢⱼ(c(δʲ(δⁱσ)))

    The terms pair up via the simplicial identity `faceMap_simplicial`:
    For j.val < i.val: δʲ(δⁱσ) = δⁱ⁻¹(δʲσ)

    The bijection pairs (i, j) with j < i to (j', i-1) where j'.val = j.val:
    - Same face by simplicial identity
    - Signs: (-1)^{i+j} and (-1)^{j+(i-1)} = -(-1)^{i+j} (opposite)

    Therefore all terms cancel. -/
theorem cechDifferential_sq_zero (F : OModule X) (𝒰 : OpenCover X) (n : ℕ)
    (c : CechCochain F 𝒰 n) :
    cechDifferential F 𝒰 (n + 1) (cechDifferential F 𝒰 n c) = 0 := by
  -- Standard simplicial argument using faceMap_simplicial
  -- Terms in the double sum pair with opposite signs and same faces
  funext σ
  rw [cechDifferential_cechDifferential_eq_double_sum]
  simp only [← Finset.sum_product', Finset.univ_product_univ]

  -- Partition pairs into S_lt (j < i) and S_ge (i ≤ j)
  let S_lt := Finset.filter (fun p : Fin (n + 3) × Fin (n + 2) => p.2.val < p.1.val) Finset.univ
  let S_ge := Finset.filter (fun p : Fin (n + 3) × Fin (n + 2) => p.1.val ≤ p.2.val) Finset.univ

  have hdisjoint : Disjoint S_lt S_ge := by
    simp only [S_lt, S_ge, Finset.disjoint_filter]; intro p _ h; omega
  have hunion : S_lt ∪ S_ge = Finset.univ := by
    ext p
    simp only [S_lt, S_ge, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    omega

  rw [← hunion, Finset.sum_union hdisjoint]

  -- Transform sum over S_ge to sum over S_lt via bijection
  -- The bijection: (i, j) with j < i ↔ (j, i-1) with i-1 ≥ j
  have hbij : S_ge.sum (fun p => doubleSumTerm F 𝒰 n c σ p.1 p.2) =
      S_lt.sum (fun p => doubleSumTerm F 𝒰 n c σ
        ⟨p.2.val, Nat.lt_of_lt_of_le p.2.isLt (Nat.le_succ _)⟩
        ⟨p.1.val - 1, by
          have h1 := p.1.isLt  -- p.1.val < n + 3
          have h2 := p.2.isLt  -- p.2.val < n + 2
          omega⟩) := by
    symm
    refine Finset.sum_bij'
      (i := fun p hp => (⟨p.2.val, Nat.lt_of_lt_of_le p.2.isLt (Nat.le_succ _)⟩,
                         ⟨p.1.val - 1, by
                           have h := (Finset.mem_filter.mp hp).2
                           have h1 := p.1.isLt
                           omega⟩))
      (j := fun p hp => (⟨p.2.val + 1, by
                           have h := (Finset.mem_filter.mp hp).2
                           have h2 := p.2.isLt
                           omega⟩,
                         ⟨p.1.val, by
                           have h := (Finset.mem_filter.mp hp).2
                           have h1 := p.1.isLt
                           omega⟩))
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
  exact pair_cancel F 𝒰 n c σ p.1 p.2 hp'

/-!
## Čech Cohomology

The Čech cohomology groups are defined as the homology of the Čech complex:
  Ȟⁿ(𝒰, F) = ker(dⁿ) / im(dⁿ⁻¹)
-/

/-- Čech n-cocycles: cochains c with dc = 0. -/
noncomputable def CechCocycles (F : OModule X) (𝒰 : OpenCover X) (n : ℕ) :
    AddSubgroup (CechCochain F 𝒰 n) :=
  (cechDifferentialHom F 𝒰 n).ker

/-- Čech n-coboundaries for n ≥ 1: image of d^{n-1}. -/
noncomputable def CechCoboundariesSucc (F : OModule X) (𝒰 : OpenCover X) (n : ℕ) :
    AddSubgroup (CechCochain F 𝒰 (n + 1)) :=
  (cechDifferentialHom F 𝒰 n).range

/-- Čech 0-coboundaries: just {0}. -/
noncomputable def CechCoboundaries0 (F : OModule X) (𝒰 : OpenCover X) :
    AddSubgroup (CechCochain F 𝒰 0) :=
  ⊥

/-- Coboundaries in degree n+1 are cocycles (uses d² = 0). -/
theorem coboundariesSucc_le_cocycles (F : OModule X) (𝒰 : OpenCover X) (n : ℕ) :
    CechCoboundariesSucc F 𝒰 n ≤ CechCocycles F 𝒰 (n + 1) := by
  intro c hc
  simp only [CechCoboundariesSucc, AddMonoidHom.mem_range] at hc
  obtain ⟨c', rfl⟩ := hc
  simp only [CechCocycles, AddMonoidHom.mem_ker, cechDifferentialHom]
  exact cechDifferential_sq_zero F 𝒰 n c'

/-- Čech cohomology in degree 0: H⁰ = Z⁰ (no coboundaries). -/
noncomputable def CechCohomology0 (F : OModule X) (𝒰 : OpenCover X) : Type _ :=
  CechCocycles F 𝒰 0

/-- Čech cohomology in degree n+1: Hⁿ⁺¹ = Zⁿ⁺¹ / Bⁿ⁺¹. -/
noncomputable def CechCohomologySucc (F : OModule X) (𝒰 : OpenCover X) (n : ℕ) : Type _ :=
  (CechCocycles F 𝒰 (n + 1)) ⧸
    AddSubgroup.comap (CechCocycles F 𝒰 (n + 1)).subtype (CechCoboundariesSucc F 𝒰 n)

/-- Čech cohomology: unified definition. -/
noncomputable def CechCohomology (F : OModule X) (𝒰 : OpenCover X) : ℕ → Type _
  | 0 => CechCohomology0 F 𝒰
  | n + 1 => CechCohomologySucc F 𝒰 n

/-- Čech cohomology H⁰ is an additive group. -/
noncomputable instance CechCohomology0.addCommGroup (F : OModule X) (𝒰 : OpenCover X) :
    AddCommGroup (CechCohomology0 F 𝒰) :=
  inferInstanceAs (AddCommGroup (CechCocycles F 𝒰 0))

/-- Čech cohomology Hⁿ⁺¹ is an additive group. -/
noncomputable instance CechCohomologySucc.addCommGroup (F : OModule X) (𝒰 : OpenCover X) (n : ℕ) :
    AddCommGroup (CechCohomologySucc F 𝒰 n) :=
  QuotientAddGroup.Quotient.addCommGroup _

/-!
## Cohomology of Curves

For algebraic curves, we define sheaf cohomology using Čech cohomology
with respect to a standard affine cover.
-/

variable (C : AlgebraicCurve)

/-- The standard affine cover of an algebraic curve.

    This uses Mathlib's affineCover for schemes. -/
noncomputable def standardAffineCover : OpenCover C.toScheme where
  I := C.toScheme.affineCover.I₀
  U := fun i => (C.toScheme.affineCover.f i).opensRange
  covers := fun x => by
    -- The affine cover covers the scheme
    -- Use the idx function to get the index for point x
    exact ⟨C.toScheme.affineCover.idx x, C.toScheme.affineCover.covers x⟩

/-- Čech cohomology of a sheaf on a curve with respect to the standard affine cover. -/
noncomputable def CechCohomologyCurve (F : OModule C.toScheme) (n : ℕ) : Type _ :=
  CechCohomology F (standardAffineCover C) n

end RiemannSurfaces.SchemeTheoretic
