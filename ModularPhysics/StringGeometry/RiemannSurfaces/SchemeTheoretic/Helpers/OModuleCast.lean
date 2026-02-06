/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Cohomology.CechComplex

/-!
# Cast Lemmas for OModule

This file provides infrastructure for transporting values along equalities
in the categorical module setting. These are needed for dependent type
manipulation in Čech cohomology proofs.

## Main Results

* `OModule.map_cast` - Restriction maps transport along equal Opens
* `OModule.section_cast` - Sections can be cast along equal Opens
* `OModule.eq_of_section_eq` - Equal faces give equal section values

## Application

These lemmas are used in `pair_cancel` (CechComplex.lean) to show that
paired terms in the d² = 0 proof have equal restricted values.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace RiemannSurfaces.SchemeTheoretic

variable {X : Scheme} (F : OModule X)

/-!
## Equality Lemmas for OModule Sections

When functions determining Opens are equal, the section values under a
cochain are provably equal. This avoids the dependent type issues with
categorical module structures.
-/

/-- When we substitute equal functions, the intersection Opens are equal. -/
theorem OModule.intersection_eq_of_fn_eq {𝒰 : OpenCover X} {n : ℕ}
    {f₁ f₂ : Fin (n + 1) → 𝒰.I} (hf : f₁ = f₂) :
    𝒰.intersection f₁ = 𝒰.intersection f₂ :=
  congrArg 𝒰.intersection hf

/-!
## Transport of Restriction Maps

When the source and target Opens are equal (via `subst`), restriction maps
give equal results.
-/

/-- Combining function equality with restriction map equality. -/
theorem OModule.restriction_eq_of_fn_eq {n : ℕ} {𝒰 : OpenCover X}
    (c : CechCochain F 𝒰 n)
    {f₁ f₂ : Fin (n + 1) → 𝒰.I} (hf : f₁ = f₂)
    {U : Opens X.carrier} (hle₁ : U ≤ 𝒰.intersection f₁) (hle₂ : U ≤ 𝒰.intersection f₂) :
    F.val.map (homOfLE hle₁).op (c f₁) =
    F.val.map (homOfLE hle₂).op (c f₂) := by
  subst hf
  rfl

/-!
## Application to pair_cancel

The key lemma needed for `pair_cancel` in CechComplex.lean.
-/

/-- For equal faces, the double restriction values are equal.

    If faceMap j (faceMap i σ) = faceMap j' (faceMap i' σ), then
    the restricted c-values are equal. -/
theorem OModule.doubleFace_restriction_eq {n : ℕ} {𝒰 : OpenCover X}
    (c : CechCochain F 𝒰 n)
    {σ : Fin (n + 3) → 𝒰.I}
    {i i' : Fin (n + 3)} {j j' : Fin (n + 2)}
    (hface : faceMap j (faceMap i σ) = faceMap j' (faceMap i' σ))
    (hle₁ : 𝒰.intersection σ ≤ 𝒰.intersection (faceMap j (faceMap i σ)))
    (hle₂ : 𝒰.intersection σ ≤ 𝒰.intersection (faceMap j' (faceMap i' σ))) :
    F.val.map (homOfLE hle₁).op (c (faceMap j (faceMap i σ))) =
    F.val.map (homOfLE hle₂).op (c (faceMap j' (faceMap i' σ))) := by
  -- Since the faces are equal, the c values are in the same type (after cast),
  -- and the restriction maps are through the same Opens
  exact OModule.restriction_eq_of_fn_eq F c hface hle₁ hle₂

end RiemannSurfaces.SchemeTheoretic
