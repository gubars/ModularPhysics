/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Helpers.SmoothCotangent

/-!
# Stalks of Smooth Curves are DVRs

This file proves that stalks of smooth projective curves over ℂ are discrete valuation rings.

## Main Results

* `SmoothProjectiveCurve.stalkIsDVR` - Stalks are DVRs

## Proof Strategy

The proof uses the TFAE characterization of DVRs from Mathlib:
- `IsLocalRing.finrank_CotangentSpace_eq_one_iff`: For a Noetherian local domain R,
  R is a DVR ↔ dim(m/m²) = 1

We combine:
1. `stalkIsNoetherianRing` - stalks are Noetherian (from `NoetherianStalks.lean`)
2. `stalkIsDomain` - stalks are domains (from integrality of the scheme)
3. `stalkIsLocalRing` - stalks are local (schemes are locally ringed)
4. `cotangent_finrank_eq_one` - dim(m/m²) = 1 (from smoothness)

## References

* Mathlib.RingTheory.DiscreteValuationRing.TFAE
* Hartshorne, "Algebraic Geometry", Chapter II.6
-/

open AlgebraicGeometry CategoryTheory

namespace RiemannSurfaces.SchemeTheoretic

namespace SmoothProjectiveCurve

variable (C : SmoothProjectiveCurve)

/-!
## Main Theorem: Stalks are DVRs

This combines all the helper results to prove the DVR structure.
-/

/-- Stalks of smooth projective curves are discrete valuation rings.

    **Mathematical content:**
    For a smooth curve C over ℂ, at each point p:
    - The stalk O_{C,p} is a Noetherian local domain
    - The cotangent space m_p/m_p² has dimension 1
    - By the TFAE characterization, this implies O_{C,p} is a DVR

    **Proof structure:**
    Uses `IsLocalRing.finrank_CotangentSpace_eq_one_iff` which states:
    For a Noetherian local domain R: R is a DVR ↔ finrank(m/m²) = 1

    We have:
    - `[IsNoetherianRing R]` from `NoetherianStalks.stalkIsNoetherianRing`
    - `[IsLocalRing R]` from scheme stalks being local rings
    - `[IsDomain R]` from `Basic.stalkIsDomain`
    - `finrank = 1` from `SmoothCotangent.cotangent_finrank_eq_one`

    This is a PROPER THEOREM using Mathlib's TFAE characterization. -/
theorem stalkIsDVR (x : C.PointType) : IsDiscreteValuationRing (C.StalkType x) := by
  -- Gather the required instances
  haveI h_noeth : IsNoetherianRing (C.StalkType x) := C.stalkIsNoetherianRing x
  haveI h_local : IsLocalRing (C.StalkType x) := C.stalkIsLocalRing x
  haveI h_domain : IsDomain (C.StalkType x) := C.stalkIsDomain x
  -- Use the TFAE characterization: finrank = 1 ↔ DVR
  rw [← IsLocalRing.finrank_CotangentSpace_eq_one_iff]
  -- Prove finrank = 1 from smoothness
  exact C.cotangent_finrank_eq_one x

end SmoothProjectiveCurve

end RiemannSurfaces.SchemeTheoretic
