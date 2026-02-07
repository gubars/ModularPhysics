/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Cohomology.CechComplex
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Flasque Sheaves

This file develops the theory of flasque (flabby) sheaves, which are
sheaves for which all restriction maps are surjective.

## Main Definitions

* `IsFlasque` - A sheaf is flasque if restriction maps are surjective

## Main Results

* `flasque_H1_zero` - Flasque sheaves have H¹ = 0

## Application

The main application is proving that skyscraper sheaves k_p are flasque,
which implies h¹(k_p) = 0 - a key ingredient in the Riemann-Roch proof.

## References

* Hartshorne, "Algebraic Geometry", Chapter III, Exercise 2.3
* Stacks Project, Tag 01EW (Flasque Sheaves)
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace RiemannSurfaces.SchemeTheoretic

variable {X : Scheme}

/-!
## Open Cover Lemmas
-/

/-- The union of all opens in a cover equals the whole space. -/
theorem OpenCover.iSup_eq_top (𝒰 : OpenCover X) : ⨆ i : 𝒰.I, 𝒰.U i = ⊤ := by
  ext x
  constructor
  · intro _; trivial
  · intro _; exact Opens.mem_iSup.mpr (𝒰.covers x)

/-- Restriction maps compose: restricting from W to V then to U is the same as
    restricting directly from W to U. Works at the element level. -/
theorem OModule.map_comp_apply {X : Scheme} (F : OModule X) {U V W : Opens X.carrier}
    (h₁ : U ≤ V) (h₂ : V ≤ W) (s : F.val.obj (Opposite.op W)) :
    F.val.map (homOfLE h₁).op (F.val.map (homOfLE h₂).op s) =
    F.val.map (homOfLE (le_trans h₁ h₂)).op s := by
  -- Work at the presheaf (AddCommGrpCat) level via .hom where composition is rfl:
  -- presheaf_map_apply_coe : (M.presheaf.map f).hom x = M.map f x := rfl
  -- AddCommGrpCat.hom_comp : (f ≫ g).hom = g.hom.comp f.hom := rfl
  -- Together: g.hom (f.hom x) = (f ≫ g).hom x (all rfl)
  show (F.val.presheaf.map (homOfLE h₂).op ≫ F.val.presheaf.map (homOfLE h₁).op).hom s =
    (F.val.presheaf.map (homOfLE (le_trans h₁ h₂)).op).hom s
  rw [← F.val.presheaf.map_comp]
  exact congrArg (fun m => (F.val.presheaf.map m).hom s) (Subsingleton.elim _ _)

/-!
## Flasque Sheaves

A sheaf F is flasque (or flabby) if for every open U ⊆ V, the restriction
map F(V) → F(U) is surjective. Equivalently, every section over an open
set can be extended to the whole space.
-/

/-- A presheaf is flasque if all restriction maps are surjective.

    **Flasque sheaves have trivial Čech cohomology in positive degrees.**
    This is because any cocycle can be "extended" step by step to become
    a coboundary. -/
class IsFlasque (F : OModule X) : Prop where
  /-- Restriction maps are surjective. -/
  restriction_surjective : ∀ (U V : Opens X.carrier) (hUV : U ≤ V),
    Function.Surjective (F.val.map (homOfLE hUV).op)

/-- A flasque sheaf has sections that extend.
    Given a section s ∈ F(U), there exists a section t ∈ F(V) with t|_U = s. -/
theorem IsFlasque.extend_section (F : OModule X) [IsFlasque F]
    (U V : Opens X.carrier) (hUV : U ≤ V) (s : F.val.obj (Opposite.op U)) :
    ∃ t : F.val.obj (Opposite.op V), F.val.map (homOfLE hUV).op t = s :=
  IsFlasque.restriction_surjective U V hUV s

/-!
## Flasque Sheaves are Acyclic

The main theorem: flasque sheaves have trivial Čech cohomology in positive degrees.
-/

/-!
### Cocycle Condition

The cocycle condition in explicit form for 1-cocycles.
-/

/-- For a 1-cocycle, the differential vanishes at each 2-simplex. -/
theorem cocycle_at_simplex (F : OModule X) (𝒰 : OpenCover X)
    (c : CechCocycles F 𝒰 1) (σ : Fin 3 → 𝒰.I) :
    (cechDifferential F 𝒰 1 c.val) σ = 0 := by
  -- c is in CechCocycles = ker(d¹), so dc = 0
  have h : cechDifferential F 𝒰 1 c.val = 0 := c.property
  -- Evaluate at σ
  exact congrFun h σ

/-!
### Infrastructure for flasque_H1_zero

The proof of H¹ = 0 for flasque sheaves requires careful handling of
the cocycle condition and the flasque extension property.
-/

/-- The 1-cocycle condition in explicit form.

    For σ = (i₀, i₁, i₂), the cocycle condition says:
    c(i₁,i₂)|_{triple} - c(i₀,i₂)|_{triple} + c(i₀,i₁)|_{triple} = 0

    This is the key constraint that makes the construction work. -/
theorem cocycle_explicit (F : OModule X) (𝒰 : OpenCover X)
    (c : CechCocycles F 𝒰 1) (i₀ i₁ i₂ : 𝒰.I) :
    let σ : Fin 3 → 𝒰.I := ![i₀, i₁, i₂]
    -- The three face contributions sum to zero:
    -- c(i₁,i₂) - c(i₀,i₂) + c(i₀,i₁) = 0 (all restricted to triple)
    (cechDifferential F 𝒰 1 c.val) σ = 0 :=
  cocycle_at_simplex F 𝒰 c _

/-- For flasque sheaves, sections can be extended from any open to any larger open.
    This is the key property used in constructing the primitive. -/
theorem flasque_extend (F : OModule X) [IsFlasque F] (U V : Opens X.carrier) (hUV : U ≤ V)
    (s : F.val.obj (Opposite.op U)) :
    ∃ t : F.val.obj (Opposite.op V), F.val.map (homOfLE hUV).op t = s :=
  IsFlasque.restriction_surjective U V hUV s

/-- The d⁰ differential applied to a 0-cochain b at a 1-simplex σ = (i, j).

    (d⁰b)(i,j) = b(j)|_{U_i∩U_j} - b(i)|_{U_i∩U_j}

    This formula makes explicit what db = c means: for each pair (i,j),
    the difference of restrictions equals c(i,j). -/
theorem d0_explicit (F : OModule X) (𝒰 : OpenCover X)
    (b : CechCochain F 𝒰 0) (i j : 𝒰.I) :
    let σ : Fin 2 → 𝒰.I := ![i, j]
    (cechDifferential F 𝒰 0 b) σ =
      restrictionToFace F 𝒰 σ 0 (b (faceMap 0 σ)) -
      restrictionToFace F 𝒰 σ 1 (b (faceMap 1 σ)) := by
  simp only [cechDifferential]
  -- Sum over j : Fin 2 with alternating signs
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one]
  -- (-1)^1 = -1
  norm_num
  -- Now we have: term0 + (-term1) = term0 - term1
  rw [sub_eq_add_neg]

/-!
### Infrastructure for Transfinite Induction Proof

The proof of H¹ = 0 for flasque sheaves uses:
1. A well-ordering on the index set 𝒰.I
2. Transfinite induction to construct the primitive b
3. Sheaf gluing to combine compatible sections at each step
4. Flasqueness to extend sections to larger opens
5. The cocycle condition for compatibility verification
-/

/-- The intersection of a 1-simplex (single index) is just the single open set.
    This identifies F(𝒰.intersection σ) with F(𝒰.U (σ 0)) for σ : Fin 1 → 𝒰.I. -/
theorem intersection_eq_single (𝒰 : OpenCover X) (σ : Fin 1 → 𝒰.I) :
    𝒰.intersection σ = 𝒰.U (σ 0) := by
  unfold OpenCover.intersection
  simp only [show (1 : ℕ) ≠ 0 from one_ne_zero, ↓reduceDIte]
  have h : (fun j : Fin 1 => 𝒰.U (σ j)) = fun _ => 𝒰.U (σ 0) := by
    funext j; exact congr_arg (𝒰.U ∘ σ) (Subsingleton.elim j 0)
  rw [h, iInf_const]

/-- Sheaf gluing for O_X-modules: compatible sections over an open cover can be glued.

    This is the gluing axiom for sheaves: given sections s_i ∈ F(V_i) that agree
    on overlaps (s_i|_{V_i ∩ V_j} = s_j|_{V_i ∩ V_j}), there exists a section
    s ∈ F(⋃ V_i) with s|_{V_i} = s_i.

    F is a SheafOfModules, so this follows from F.isSheaf which encodes the
    sheaf condition. In Mathlib, the concrete gluing axiom is
    `Sheaf.existsUnique_gluing'` in `Topology.Sheaves.SheafCondition.UniqueGluing`. -/
theorem OModule.glue_sections {X : Scheme} (F : OModule X)
    {ι : Type*} (V : ι → Opens X.carrier)
    (sf : ∀ i : ι, F.val.obj (Opposite.op (V i)))
    (compat : ∀ i j : ι,
      F.val.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (sf i) =
      F.val.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (sf j)) :
    ∃ s : F.val.obj (Opposite.op (⨆ i, V i)),
      ∀ i : ι, F.val.map (homOfLE (le_iSup V i)).op s = sf i := by
  -- Construct the TopCat.Sheaf of abelian groups from F
  let F_sheaf : TopCat.Sheaf Ab X.carrier := ⟨F.val.presheaf, F.isSheaf⟩
  -- Bridge the compatibility condition to Mathlib's IsCompatible form
  -- Note: infLELeft = homOfLE inf_le_left by LE.le.hom = homOfLE (definitional)
  -- and presheaf_map_apply_coe is rfl, so F.val.presheaf.map and F.val.map agree on elements
  have hcompat : TopCat.Presheaf.IsCompatible F.val.presheaf V sf := by
    intro i j
    exact compat i j
  -- Apply the sheaf gluing theorem (U = V family, result at iSup V)
  -- leSupr V i = homOfLE (le_iSup V i) definitionally
  obtain ⟨s, hs, _⟩ := F_sheaf.existsUnique_gluing V sf hcompat
  exact ⟨s, hs⟩

/-- Flasque sheaves have H¹ = 0.

    **Proof by transfinite induction (Godement/Hartshorne):**

    Well-order 𝒰.I. Construct b(α) ∈ F(U_α) by well-founded recursion:

    **Base:** b(min) = 0 ∈ F(U_min).

    **Step α:** Given b(β) for all β < α with the induction hypothesis
      ∀ β₁ β₂ < α, b(β₂)|_{U_{β₁} ∩ U_{β₂}} - b(β₁)|_{U_{β₁} ∩ U_{β₂}} = c(β₁, β₂),
    define for each β < α:
      s_β := c(β, α) + b(β)|_{U_β ∩ U_α} ∈ F(U_β ∩ U_α)

    **Compatibility:** For β₁, β₂ < α, on U_{β₁} ∩ U_{β₂} ∩ U_α:
      s_{β₁} - s_{β₂} = c(β₁, α) + b(β₁) - c(β₂, α) - b(β₂)
                        = c(β₁, α) - c(β₂, α) + c(β₁, β₂)   (by IH)
                        = 0                                      (by cocycle condition)

    **Glue:** The compatible {s_β} glue to a section on ⋃_{β<α} (U_β ∩ U_α).
    **Extend:** By flasqueness, extend to b(α) ∈ F(U_α).

    **Verification:** For any β < α: b(α)|_{U_β ∩ U_α} - b(β)|_{U_β ∩ U_α} = c(β,α)
    by construction. For α < β: follows from the IH at step β.
    Cocycle antisymmetry c(β,α) = -c(α,β) handles the sign. -/
theorem flasque_H1_zero (F : OModule X) [IsFlasque F] (𝒰 : OpenCover X) :
    ∀ c : CechCocycles F 𝒰 1, ∃ b : CechCochain F 𝒰 0,
      cechDifferential F 𝒰 0 b = c.val := by
  intro c
  have hcoc : cechDifferential F 𝒰 1 c.val = 0 := c.property
  classical
  -- Handle the empty cover case (no indices means cochains are over empty domain)
  by_cases hne : Nonempty 𝒰.I
  swap
  · refine ⟨fun σ => absurd ⟨σ 0⟩ hne, funext fun σ => absurd ⟨σ 0⟩ hne⟩
  · -- Step 1: Well-order the index set
    letI : LinearOrder 𝒰.I := WellOrderingRel.isWellOrder.linearOrder
    -- Step 2: Construct b_aux : (i : 𝒰.I) → F(U_i) by well-founded recursion.
    --
    -- At step α, given b(β) for all β < α satisfying the IH:
    --   ∀ β₁ β₂ < α, b(β₂)|_{U_{β₁} ∩ U_{β₂}} - b(β₁)|_{U_{β₁} ∩ U_{β₂}} = c(β₁, β₂)
    --
    -- For each β < α, define s_β = c(β, α) + b(β)|_{U_β ∩ U_α} ∈ F(U_β ∩ U_α).
    -- These are compatible on overlaps by the cocycle condition + IH.
    -- Glue via OModule.glue_sections, then extend by IsFlasque.extend_section.
    --
    -- Step 3: Convert b_aux to CechCochain format (via intersection_eq_single)
    -- and verify d⁰b = c.val pointwise:
    --   For σ = ![i,j] with i < j: follows from IH at step j
    --   For σ = ![i,j] with i > j: follows from IH at step i + cocycle antisymmetry
    --   For σ = ![i,i]: both sides are 0
    --
    -- The sheaf gluing step uses OModule.glue_sections (which derives from
    -- the sheaf condition built into SheafOfModules).
    sorry

/-- Flasque sheaves have Hⁿ⁺¹ = 0 for all n ≥ 0. -/
theorem flasque_acyclic_succ (F : OModule X) [IsFlasque F] (𝒰 : OpenCover X) (n : ℕ) :
    ∀ c : CechCocycles F 𝒰 (n + 1), ∃ b : CechCochain F 𝒰 n,
      cechDifferential F 𝒰 n b = c.val := by
  -- General case follows from the same principle as H¹
  sorry

/-!
## Skyscraper Sheaves are Flasque

A skyscraper sheaf k_p is supported only at the point p, so restriction
maps are either identities (if p is in both opens) or zero maps.
In either case, they are surjective.
-/

/-
Note on skyscraper modules:

A proper definition would use Mathlib's skyscraper presheaf construction
or be defined via pushforward along the closed immersion {p} → X.
The skyscraperModule is defined in Skyscraper.lean.

Skyscraper sheaves are flasque because:

For a skyscraper sheaf k_p:
- k_p(U) = κ(p) if p ∈ U
- k_p(U) = 0 if p ∉ U

The restriction map k_p(V) → k_p(U) for U ⊆ V is:
- Identity κ(p) → κ(p) if p ∈ U (hence p ∈ V)
- The unique map κ(p) → 0 if p ∉ U, p ∈ V
- The zero map 0 → 0 if p ∉ V (hence p ∉ U)

All these maps are surjective.

The theorem skyscraper_isFlasque will be proven in Skyscraper.lean
once skyscraperModule is properly defined.
-/

end RiemannSurfaces.SchemeTheoretic
