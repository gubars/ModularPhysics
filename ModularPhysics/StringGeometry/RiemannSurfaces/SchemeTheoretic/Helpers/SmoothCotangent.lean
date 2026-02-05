/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Helpers.NoetherianStalks

/-!
# Cotangent Space Dimension for Smooth Curves

This file proves that for a smooth projective curve C over ℂ, the cotangent space
at each point has dimension 1 over the residue field.

## Main Results

* `SmoothProjectiveCurve.cotangent_finrank_eq_one` - dim(m/m²) = 1 at each point

## Mathematical Background

For a smooth curve C over ℂ:
1. The cotangent space m_p/m_p² at a point p measures the "tangent directions"
2. Smoothness implies the cotangent space dimension equals the relative dimension
3. For a curve, the relative dimension is 1
4. Therefore dim(m_p/m_p²) = 1

This is the key connection between smoothness and the DVR structure.

## References

* Mathlib.RingTheory.Ideal.Cotangent
* Hartshorne, "Algebraic Geometry", Chapter II.8 (Differentials)
-/

open AlgebraicGeometry CategoryTheory

namespace RiemannSurfaces.SchemeTheoretic

namespace SmoothProjectiveCurve

variable (C : SmoothProjectiveCurve)

/-!
## Cotangent Space Setup

The cotangent space of a local ring R is m/m² where m is the maximal ideal.
-/

/-- The residue field of the stalk at a point. -/
noncomputable def stalkResidueField (x : C.PointType) :=
  IsLocalRing.ResidueField (C.StalkType x)

/-- The residue field is a field. -/
noncomputable instance stalkResidueFieldField (x : C.PointType) :
    Field (C.stalkResidueField x) :=
  inferInstanceAs (Field (IsLocalRing.ResidueField (C.StalkType x)))

/-- The cotangent space of the stalk at a point. -/
noncomputable def stalkCotangentSpace (x : C.PointType) :=
  IsLocalRing.CotangentSpace (C.StalkType x)

/-- The cotangent space is an additive comm group. -/
noncomputable instance stalkCotangentSpaceAddCommGroup (x : C.PointType) :
    AddCommGroup (C.stalkCotangentSpace x) :=
  inferInstanceAs (AddCommGroup (IsLocalRing.CotangentSpace (C.StalkType x)))

/-- The cotangent space is a module over the residue field. -/
noncomputable instance cotangentSpaceModule (x : C.PointType) :
    Module (C.stalkResidueField x) (C.stalkCotangentSpace x) :=
  inferInstanceAs (Module (IsLocalRing.ResidueField (C.StalkType x))
    (IsLocalRing.CotangentSpace (C.StalkType x)))

/-!
## Main Theorem: Cotangent Dimension = 1

For a smooth curve, the cotangent space has dimension 1.
-/

/-- The cotangent space at each point has dimension 1 over the residue field.

    **Mathematical content:**
    For a smooth scheme X → S of relative dimension d, the cotangent space
    at each point x has dimension d over the residue field κ(x).

    For our curve C → Spec ℂ:
    - `IsSmoothOfRelativeDimension 1 structureMorphism` encodes that C is a smooth curve
    - At each point x, the Kähler differentials Ω[S/R] have rank 1 locally
    - The cotangent space m_x/m_x² is the fiber of the cotangent sheaf at x
    - Therefore dim_{κ(x)}(m_x/m_x²) = 1

    **Required Infrastructure (not yet in Mathlib):**
    1. `IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` gives rank Ω[S/R] = 1
    2. Need: Localization of Kähler differentials: Ω[S/R]_𝔭 ≃ Ω[S_𝔭/R]
    3. Need: Cotangent exact sequence: Ω[S/R] ⊗ κ(𝔭) → m/m² → 0 with m/m² ≃ fiber
    4. Need: For smooth over alg closed field, the above map is an isomorphism

    **References:** SGA 1, Chapter II, Proposition 4.10; Hartshorne IV.1 -/
theorem cotangent_finrank_eq_one (x : C.PointType) :
    Module.finrank (C.stalkResidueField x) (C.stalkCotangentSpace x) = 1 := by
  -- The proof chain:
  -- 1. IsSmoothOfRelativeDimension 1 gives Locally (IsStandardSmoothOfRelativeDimension 1)
  --    on affine opens
  -- 2. IsStandardSmoothOfRelativeDimension 1 implies rank Ω[S/R] = 1
  -- 3. Stalks of Ω form the cotangent sheaf; at closed points over alg closed field,
  --    fiber = m/m²
  -- 4. Free module of rank 1 tensored with residue field gives dim 1
  --
  -- Missing Mathlib infrastructure: connection between scheme-level differential forms
  -- and local cotangent spaces at stalks
  sorry

end SmoothProjectiveCurve

end RiemannSurfaces.SchemeTheoretic
