/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Cohomology.SheafCohomology
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Helpers.FlasqueSheaves

/-!
# Skyscraper Sheaves on Algebraic Curves

This file defines skyscraper sheaves at closed points of algebraic curves.
These are fundamental for the Riemann-Roch theorem, as they satisfy χ(k_p) = 1.

## Main Definitions

* `skyscraperSheaf` - The skyscraper sheaf k_p at a point p
* `skyscraperSheaf_isCoherent` - k_p is coherent

## Main Results

* `h0_skyscraper` - h⁰(k_p) = 1
* `h1_skyscraper` - h¹(k_p) = 0
* `euler_char_skyscraper` - χ(k_p) = 1

## Scheme-Theoretic Construction

The skyscraper sheaf k_p at a closed point p is defined as:
- k_p(U) = κ(p) if p ∈ U, else 0
- where κ(p) is the residue field at p

For curves over ℂ, κ(p) ≅ ℂ by the `residueFieldIsComplex` axiom.

## References

* Hartshorne, "Algebraic Geometry", Chapter II, Exercise 1.17
* Stacks Project, Tag 0080 (Skyscraper sheaves)
-/

open AlgebraicGeometry CategoryTheory

namespace RiemannSurfaces.SchemeTheoretic

variable (C : AlgebraicCurve)

/-!
## Skyscraper Sheaf Definition

The skyscraper sheaf at a point p has stalk κ(p) at p and 0 elsewhere.
For curves over ℂ, κ(p) ≅ ℂ.
-/

/-- The underlying O_C-module for the skyscraper sheaf at point p.

    **Scheme-theoretic definition:**
    The skyscraper sheaf k_p is the pushforward of the residue field κ(p)
    along the inclusion {p} → C.

    For a closed point p on a curve C over ℂ:
    - κ(p) = C.toScheme.residueField p ≅ ℂ (by residueFieldIsComplex)
    - k_p(U) = κ(p) if p ∈ U, else 0
    - The O_C-module structure: f · v = f(p) · v for f ∈ O_C(U), v ∈ κ(p)

    **Construction outline:**
    1. Define the presheaf of abelian groups: U ↦ κ(p) if p ∈ U, else 0
    2. Give it O_C-module structure via evalAtPoint (from SkyscraperInfrastructure)
    3. Show the sheaf condition holds (trivially, since sections glue uniquely)
    4. Package as SheafOfModules C.toScheme.ringCatSheaf

    The key tool is `TopCat.Presheaf.skyscraperPresheaf` from Mathlib which
    constructs the underlying presheaf. The O_C-module structure uses
    `residueFieldModule` from SkyscraperInfrastructure.

    TODO: Requires developing infrastructure for:
    - Presheaf of modules structure on skyscraper presheaf
    - Verifying the sheaf condition for modules
    - Interfacing with Mathlib's SheafOfModules API -/
noncomputable def skyscraperModule (p : C.PointType) : OModule C.toScheme := by
  -- The mathematical content is standard:
  -- skyscraper(p, κ(p)) as an O_C-module sheaf
  -- Sections: k_p(U) = κ(p) if p ∈ U, else 0
  -- Module action: f · v = evaluation(f)(p) · v
  sorry

/-- The skyscraper sheaf at p is coherent.

    **Proof sketch:**
    k_p is supported on a single point, which makes it automatically
    finitely generated as an O_C-module. On each affine chart,
    the module of sections is either κ(p) ≅ ℂ (1-dimensional) or 0. -/
instance skyscraperModule_isCoherent (p : C.PointType) :
    IsCoherent C.toScheme (skyscraperModule C p) where
  locallyPresentable := fun i => ⟨Iso.refl _⟩
  locallyFinitelyGenerated := fun i => sorry
    -- The sections are either κ(p) (1-dim) or 0, both finitely generated

/-- The skyscraper sheaf k_p at a closed point p.

    This is the coherent sheaf with:
    - Stalk at p: κ(p) ≅ ℂ
    - Stalk at q ≠ p: 0 -/
noncomputable def skyscraperSheaf (p : C.PointType) : CoherentSheaf C where
  toModule := skyscraperModule C p
  isCoherent := skyscraperModule_isCoherent C p

namespace SkyscraperSheaf

variable {C}
variable (p : C.PointType)

/-!
## Stalk Properties

The defining property of skyscraper sheaves: concentrated at a single point.
-/

/-- The stalk of k_p at p is the residue field κ(p).

    For curves over ℂ, this is isomorphic to ℂ.

    **Mathematical content:**
    The stalk (k_p)_p ≅ κ(p) as an abelian group. -/
theorem stalk_at_point :
    Nonempty (C.toScheme.presheaf.stalk p ≅ C.toScheme.presheaf.stalk p) := by
  -- TODO: Express the actual isomorphism (k_p)_p ≅ κ(p)
  -- This requires infrastructure for stalks of skyscraper sheaves
  exact ⟨Iso.refl _⟩

/-- The stalk of k_p at any other point q ≠ p is zero.

    **Mathematical content:**
    (k_p)_q = 0 for q ≠ p. -/
theorem stalk_away (q : C.PointType) (hpq : p ≠ q) :
    -- The stalk at q is the initial/terminal object (zero in Ab)
    Nonempty (Limits.IsInitial (C.toScheme.presheaf.stalk q)) ∨
    Nonempty (Limits.IsTerminal (C.toScheme.presheaf.stalk q)) := by
  -- TODO: Express that (k_p)_q = 0 for the skyscraper module
  sorry

/-!
## Global Sections

k_p has exactly one global section (the identity element of κ(p)).
-/

/-- Global sections of k_p form a 1-dimensional ℂ-vector space.

    **Proof:**
    Γ(C, k_p) = k_p(C) = κ(p) ≅ ℂ (since p is a closed point on a proper curve).

    **Mathematical content:**
    The global sections Γ(C, k_p) is 1-dimensional over ℂ. -/
theorem globalSections_dim :
    -- Γ(C, k_p) ≅ κ(p) as modules
    -- For now, express that the global sections module is isomorphic to itself
    -- (placeholder for the actual 1-dimensionality statement)
    Nonempty ((skyscraperModule C p).val.obj (Opposite.op ⊤) ≅
              (skyscraperModule C p).val.obj (Opposite.op ⊤)) := by
  exact ⟨Iso.refl _⟩

end SkyscraperSheaf

/-!
## Cohomology of Skyscraper Sheaves

The key fact for Riemann-Roch: skyscraper sheaves have Euler characteristic 1.
-/

/-- h⁰(k_p) = 1.

    **Proof:**
    H⁰(C, k_p) = Γ(C, k_p) = κ(p) ≅ ℂ, which is 1-dimensional. -/
theorem h0_skyscraper (C : ProperCurve) (p : C.toAlgebraicCurve.PointType) :
    h_i C 0 (skyscraperSheaf C.toAlgebraicCurve p) = 1 := by
  sorry

/-- h¹(k_p) = 0 (skyscraper sheaves are acyclic).

    **Proof:**
    This follows from the fact that k_p is a flasque (flabby) sheaf:
    - k_p is supported on a single point
    - Restriction maps are either identity or zero-to-zero
    - Flasque sheaves have vanishing higher cohomology

    Alternatively, use the fact that any sheaf supported on a 0-dimensional
    subset has H^i = 0 for i ≥ 1 (cohomological dimension bound). -/
theorem h1_skyscraper (C : ProperCurve) (p : C.toAlgebraicCurve.PointType) :
    h_i C 1 (skyscraperSheaf C.toAlgebraicCurve p) = 0 := by
  sorry

/-- χ(k_p) = 1.

    **Proof:**
    χ(k_p) = h⁰(k_p) - h¹(k_p) = 1 - 0 = 1.

    This is the key fact used in the inductive proof of Riemann-Roch. -/
theorem euler_char_skyscraper (C : ProperCurve) (p : C.toAlgebraicCurve.PointType) :
    EulerChar C (skyscraperSheaf C.toAlgebraicCurve p) = 1 := by
  unfold EulerChar
  rw [h0_skyscraper C p, h1_skyscraper C p]
  norm_num

/-!
## Skyscraper Sheaves are Flasque

This is the key property that implies H¹ = 0.
-/

/-- Skyscraper sheaves are flasque.

    **Proof:**
    For a skyscraper sheaf k_p:
    - k_p(U) = κ(p) if p ∈ U, else 0

    The restriction map k_p(V) → k_p(U) for U ⊆ V is:
    - Identity κ(p) → κ(p) if p ∈ U (hence p ∈ V)
    - The unique map κ(p) → 0 if p ∉ U, p ∈ V
    - The zero map 0 → 0 if p ∉ V

    All these maps are surjective. -/
instance skyscraperModule_isFlasque (p : C.PointType) :
    IsFlasque (skyscraperModule C p) where
  restriction_surjective := fun U V hUV => by
    -- By case analysis on whether p ∈ U
    sorry

end RiemannSurfaces.SchemeTheoretic
