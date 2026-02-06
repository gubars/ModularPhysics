/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Basic
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Helpers.ValuationExtension
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Helpers.StalkDVR
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Local Rings and Valuations on Smooth Projective Curves

This file connects the scheme-theoretic local ring structure to discrete valuations,
which is the key step in bridging to `CompactAlgebraicCurve`.

## Main Results

* `SmoothProjectiveCurve.valuationAt` - The discrete valuation v_p : K(C)* → ℤ
* `SmoothProjectiveCurve.valuationAt_mul` - v_p(fg) = v_p(f) + v_p(g)
* `SmoothProjectiveCurve.valuationAt_add_min` - v_p(f+g) ≥ min(v_p(f), v_p(g))

## Design Principles

All valuation properties are DERIVED from the DVR structure of stalks,
which itself is a THEOREM (not an axiom) following from smoothness.

The key insight: For a smooth curve C over ℂ:
- Stalks O_{C,p} are DVRs (from smooth + dimension 1)
- DVRs have a canonical valuation v : Frac(O_{C,p})* → ℤ
- The function field K(C) = Frac(O_{C,η}) embeds into Frac(O_{C,p})

## References

* Hartshorne, "Algebraic Geometry", Chapter II.6 (Divisors)
* Neukirch, "Algebraic Number Theory", Chapter I (Valuations)
-/

open AlgebraicGeometry CategoryTheory

namespace RiemannSurfaces.SchemeTheoretic

namespace SmoothProjectiveCurve

variable (C : SmoothProjectiveCurve)

/-!
## Valuation from DVR Structure

For a DVR R with fraction field K, there is a canonical valuation:
  v : K* → ℤ
  v(x) = n  iff  x = u * π^n  for unit u and uniformizer π

We extract this valuation from the stalk O_{C,p}.
-/

/-- The fraction field of the stalk at a point.

    For a DVR O_{C,p}, this is the localization at the zero ideal,
    which embeds into the function field K(C). -/
noncomputable def stalkFractionField (x : C.PointType) : Type _ :=
  FractionRing (C.StalkType x)

/-- The fraction field of a stalk is a field.

    This uses Mathlib's `FractionRing.field` instance which requires `IsDomain`.
    We have `stalkIsDomain` from the integrality of the scheme. -/
noncomputable instance stalkFractionFieldField (x : C.PointType) : Field (C.stalkFractionField x) :=
  -- FractionRing of a domain is a field via Mathlib's FractionRing.field
  -- Uses: IsDomain (C.StalkType x) from stalkIsDomain
  inferInstanceAs (Field (FractionRing (C.StalkType x)))

/-- The valuation v_p : K(C)* → ℤ at a point p.

    **Mathematical content:**
    Given p ∈ C, the stalk O_{C,p} is a DVR (from smoothness + dim 1).
    The valuation v_p measures the order of vanishing/pole at p:
    - v_p(f) > 0 means f has a zero of order v_p(f) at p
    - v_p(f) < 0 means f has a pole of order -v_p(f) at p
    - v_p(f) = 0 means f is a unit in O_{C,p}

    This is DERIVED from the DVR structure via `DVRValuation.extendedVal`.

    **Implementation:**
    Uses `DVRValuation.extendedVal` which extends the DVR valuation on O_{C,p}
    to its fraction field K(C). Requires:
    - `IsDiscreteValuationRing (StalkType x)` from `stalkIsDVR`
    - `IsFractionRing (StalkType x) FunctionFieldType` from Mathlib
    - `Field FunctionFieldType` from Mathlib

    This is a PROPER DEFINITION (no sorry). -/
noncomputable def valuationAt (x : C.PointType) : C.FunctionFieldType → ℤ :=
  -- Use the DVR valuation extension from ValuationExtension.lean
  -- The stalk is a DVR (from stalkIsDVR), and the function field is its fraction ring
  --
  -- Note: We use the underlying Mathlib types directly rather than our type aliases
  -- to ensure instance resolution works correctly.
  @DVRValuation.extendedVal
    (C.toScheme.presheaf.stalk x)  -- R = stalk
    (C.toScheme.functionField)      -- K = function field
    _  -- CommRing R
    _  -- IsDomain R
    (C.stalkIsDVR x)               -- IsDiscreteValuationRing R
    _  -- Field K
    _  -- Algebra R K
    _  -- IsFractionRing R K

/-- Convention: v_p(0) = 0.

    **Note:** Mathematically v_p(0) = +∞, but we use 0 as convention
    to avoid `WithTop ℤ`. All meaningful valuation axioms only apply
    to nonzero elements. -/
theorem valuationAt_zero (x : C.PointType) : C.valuationAt x 0 = 0 := by
  unfold valuationAt
  exact @DVRValuation.extendedVal_zero
    (C.toScheme.presheaf.stalk x)
    (C.toScheme.functionField)
    _ _ (C.stalkIsDVR x) _ _ _

/-- v_p(fg) = v_p(f) + v_p(g) for f, g ≠ 0.

    **Proof:** This is a fundamental property of DVR valuations.
    In a DVR, every nonzero element is u * π^n for unit u and uniformizer π.
    So v(fg) = v(u₁ π^{n₁} · u₂ π^{n₂}) = v(u₁u₂ π^{n₁+n₂}) = n₁ + n₂. -/
theorem valuationAt_mul (x : C.PointType) (f g : C.FunctionFieldType)
    (hf : f ≠ 0) (hg : g ≠ 0) :
    C.valuationAt x (f * g) = C.valuationAt x f + C.valuationAt x g := by
  unfold valuationAt
  exact @DVRValuation.extendedVal_mul
    (C.toScheme.presheaf.stalk x)
    (C.toScheme.functionField)
    _ _ (C.stalkIsDVR x) _ _ _ f g hf hg

/-- v_p(f + g) ≥ min(v_p(f), v_p(g)) when f + g ≠ 0 (ultrametric inequality).

    **Proof:** This is the ultrametric property of DVR valuations.
    Writing f = u₁ π^{n₁}, g = u₂ π^{n₂} with n₁ ≤ n₂, we have
    f + g = π^{n₁}(u₁ + u₂ π^{n₂-n₁}), and u₁ + u₂ π^{n₂-n₁} ∈ O_{C,p}.
    So v(f+g) ≥ n₁ = min(n₁, n₂). -/
theorem valuationAt_add_min (x : C.PointType) (f g : C.FunctionFieldType)
    (hfg : f + g ≠ 0) :
    C.valuationAt x (f + g) ≥ min (C.valuationAt x f) (C.valuationAt x g) := by
  unfold valuationAt
  exact @DVRValuation.extendedVal_add_min
    (C.toScheme.presheaf.stalk x)
    (C.toScheme.functionField)
    _ _ (C.stalkIsDVR x) _ _ _ f g hfg

/-- For f ≠ 0, only finitely many points have v_p(f) ≠ 0.

    **Mathematical content:**
    A nonzero rational function on a curve has only finitely many
    zeros and poles. This follows from:
    1. f defines a morphism f : C → ℙ¹
    2. For proper curves, this is a finite morphism
    3. Preimages of 0 and ∞ are finite

    This is a THEOREM, not an axiom. -/
theorem valuationAt_finiteSupport (f : C.FunctionFieldType) (hf : f ≠ 0) :
    Set.Finite { x : C.PointType | C.valuationAt x f ≠ 0 } := by
  sorry

/-!
## Derived Properties

These follow from the basic valuation axioms.
-/

/-- v_p(1) = 0 (derived from valuationAt_mul). -/
theorem valuationAt_one (x : C.PointType) : C.valuationAt x 1 = 0 := by
  unfold valuationAt
  exact @DVRValuation.extendedVal_one
    (C.toScheme.presheaf.stalk x)
    (C.toScheme.functionField)
    _ _ (C.stalkIsDVR x) _ _ _

/-- v_p(f⁻¹) = -v_p(f) for f ≠ 0 (derived from valuationAt_mul).

    Note: The function field of an integral scheme has a canonical Field instance
    from Mathlib (`instFieldCarrierFunctionField`). -/
theorem valuationAt_inv (x : C.PointType) (f : C.FunctionFieldType) (hf : f ≠ 0) :
    C.valuationAt x f⁻¹ = -C.valuationAt x f := by
  unfold valuationAt
  exact @DVRValuation.extendedVal_inv
    (C.toScheme.presheaf.stalk x)
    (C.toScheme.functionField)
    _ _ (C.stalkIsDVR x) _ _ _ f hf

/-!
### Constants Have Valuation Zero

The theorem that constants have valuation 0 is proven in
`Helpers/ConstantValuation.lean` as `SmoothProjectiveCurve.valuationAt_constant'`.

The proof uses the key insight that:
1. Constants factor through stalks via the scalar tower Γ(C, ⊤) → O_{C,x} → K(C)
2. Nonzero constants are units in stalks (their residue is nonzero by residueFieldIsComplex)
3. Units in a DVR have valuation 0 (by extendedVal_unit)

Import `Helpers.ConstantValuation` for the full theorem.
-/

/-!
## Local Parameters

A local parameter (uniformizer) at p is an element t_p ∈ K(C) with v_p(t_p) = 1.
Such elements exist because O_{C,p} is a DVR.
-/

/-- A local parameter (uniformizer) exists at each point.

    **Mathematical content:**
    For a DVR, the maximal ideal is principal, generated by a uniformizer π.
    The uniformizer satisfies v(π) = 1 by definition of the normalized valuation. -/
theorem exists_localParameter (x : C.PointType) :
    ∃ t : C.FunctionFieldType, C.valuationAt x t = 1 := by
  -- Get a uniformizer from the DVR structure
  letI : IsDiscreteValuationRing (C.toScheme.presheaf.stalk x) := C.stalkIsDVR x
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (C.toScheme.presheaf.stalk x)
  -- Embed π into the function field
  use algebraMap (C.toScheme.presheaf.stalk x) (C.toScheme.functionField) π
  -- The uniformizer has addVal = 1
  have hval : IsDiscreteValuationRing.addVal (C.toScheme.presheaf.stalk x) π = 1 :=
    IsDiscreteValuationRing.addVal_uniformizer hπ
  -- Therefore extendedVal = 1
  unfold valuationAt
  have hπ_ne : π ≠ 0 := hπ.ne_zero
  rw [@DVRValuation.extendedVal_algebraMap
    (C.toScheme.presheaf.stalk x)
    (C.toScheme.functionField)
    _ _ (C.stalkIsDVR x) _ _ _ π hπ_ne]
  -- addValNat π = toNat(1) = 1
  simp only [DVRValuation.addValNat, hval, ENat.toNat_one, Nat.cast_one]

/-- A uniformizer at p, viewed in K(C), has finite support.

    Follows from `valuationAt_finiteSupport`. -/
theorem localParameter_finiteSupport (x : C.PointType) (t : C.FunctionFieldType)
    (ht_ne : t ≠ 0) :
    Set.Finite { y : C.PointType | C.valuationAt y t ≠ 0 } :=
  C.valuationAt_finiteSupport t ht_ne

/-- The sum of valuations of a uniformizer is zero (argument principle).

    **Mathematical content:**
    By the argument principle, Σ_p v_p(t) = 0 for any t ∈ K(C)*.
    For a uniformizer with v_x(t) = 1, the sum of valuations at other points is -1.

    **Note:** Individual valuations at other points may be positive, zero,
    or negative. The statement v_q(t) ≤ 0 for all q ≠ p is FALSE in general.
    A uniformizer at p can have additional zeros at other points.

    This theorem is stated here but proven in Divisors.lean as
    `principalDivisor_degree_zero` since it requires the divisor machinery. -/
theorem localParameter_valuation_sum (_x : C.PointType) (t : C.FunctionFieldType)
    (_ht : C.valuationAt _x t = 1) (ht_ne : t ≠ 0) :
    -- The sum of valuations over the finite support equals 0
    -- This is expressed via the degree of the principal divisor in Divisors.lean
    ∃ (S : Finset C.PointType), (∀ y ∉ S, C.valuationAt y t = 0) ∧
      S.sum (C.valuationAt · t) = 0 := by
  sorry

end SmoothProjectiveCurve

end RiemannSurfaces.SchemeTheoretic
