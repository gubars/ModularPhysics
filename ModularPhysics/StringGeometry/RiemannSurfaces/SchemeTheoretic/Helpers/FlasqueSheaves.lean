/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Cohomology.CechComplex

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

/-- Flasque sheaves have H¹ = 0.

    **Proof strategy:**
    Let c be a 1-cocycle: for σ : Fin 2 → 𝒰.I, c(σ) ∈ F(U_{σ0} ∩ U_{σ1}).
    The cocycle condition says: for any σ : Fin 3 → 𝒰.I,
      c(δ⁰σ) - c(δ¹σ) + c(δ²σ) = 0 in F(U_{σ0} ∩ U_{σ1} ∩ U_{σ2})

    We construct b : CechCochain F 𝒰 0, i.e., b(i) ∈ F(U_i) for each i,
    such that db = c, i.e., b(σ1)|_{U_{σ0}∩U_{σ1}} - b(σ0)|_{U_{σ0}∩U_{σ1}} = c(σ).

    **Construction (requires Choice):**
    1. Choose a well-ordering on 𝒰.I
    2. For the first index i₀, set b(i₀) = 0
    3. For each i > i₀, the cocycle condition forces the values of b(i) on overlaps.
       Use flasqueness to extend to all of U_i.
    4. Verify using the cocycle condition that this is consistent.

    **Why it works:**
    The key is that on U_i ∩ U_j ∩ U_k, the cocycle condition gives:
      c_{jk} - c_{ik} + c_{ij} = 0
    So if we've defined b_j and b_k with the right properties, then
    the required value for b_i on U_i ∩ U_j equals the required value on U_i ∩ U_k.

    **Mathematical status:**
    This is a classical result in sheaf theory. The proof is somewhat technical
    and requires well-founded induction over 𝒰.I. We mark it as sorry for now
    and note that it's a standard result used throughout algebraic geometry. -/
theorem flasque_H1_zero (F : OModule X) [IsFlasque F] (𝒰 : OpenCover X) :
    ∀ c : CechCocycles F 𝒰 1, ∃ b : CechCochain F 𝒰 0,
      cechDifferential F 𝒰 0 b = c.val := by
  intro c
  -- The cocycle condition: c is in the kernel of d¹
  have hcoc : cechDifferential F 𝒰 1 c.val = 0 := c.property
  -- The construction uses:
  -- 1. Well-ordering on 𝒰.I
  -- 2. Transfinite induction to define b(i) for each i
  -- 3. Flasqueness to extend local sections to U_i
  -- 4. Cocycle condition to verify consistency
  classical
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
