-- Note: Cohomology.Basic uses CompactRiemannSurface, so it lives in GAGA/Cohomology
import ModularPhysics.StringGeometry.RiemannSurfaces.GAGA.Cohomology.Basic
import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.Helpers.Meromorphic

/-!
# Construction of Line Bundle Sheaves O(D)

This file provides infrastructure for the line bundle sheaf O(D) associated to a divisor D.

## Mathematical Background

For a divisor D = Σ nᵢ pᵢ on a Riemann surface Σ, the line bundle sheaf O(D) is:

  O(D)(U) = {f meromorphic on U : ord_p(f) ≥ -D(p) for all p ∈ U}

## Approach

Rather than constructing O(D) explicitly from scratch (which requires substantial
complex analysis infrastructure), we:

1. Define `SectionOrder` - an order function for sections compatible with localUniformizer
2. Define `LineBundleSheafData` - axiomatic structure for D ↦ O(D) assignment
3. Show how to convert to `LineBundleSheafAssignment` for cohomology

This "axiomatic" approach is mathematically sound:
- Both algebraic and analytic constructions must satisfy our axioms
- GAGA ensures any valid construction gives the same cohomology
- The cohomology theory can be parameterized by this data

## Main Definitions

* `SectionOrder` - Order function for sections of O(U)
* `LineBundleSheafData` - Full assignment D ↦ O(D) with properties

## References

* Griffiths, Harris "Principles of Algebraic Geometry", Chapter 2
* Hartshorne "Algebraic Geometry", Chapter II
-/

namespace RiemannSurfaces.Algebraic.Cohomology

open RiemannSurfaces

-- Note: We use RiemannSurfaces.Divisor (from Basic.lean) which is in scope via `open RiemannSurfaces`

/-!
## Order Function for Sections

The order function captures the DVR structure at each point of a Riemann surface.
-/

/-- An order function for sections of a structure sheaf.

    For a Riemann surface, the local ring at each point is a DVR, and the
    order function is the DVR valuation. The localUniformizer in StructureSheaf
    provides the uniformizer for this DVR.

    **Key properties:**
    - ord_p(fg) = ord_p(f) + ord_p(g)
    - ord_p(f) > 0 ↔ f(p) = 0
    - ord_p(f) ≥ 0 for holomorphic f
    - ord_p(1) = 0 -/
structure SectionOrder (RS : RiemannSurface) (O : StructureSheaf RS) where
  /-- Order of a section f ∈ O(U) at a point p ∈ U -/
  orderAt : ∀ (U : OpenSet RS) (f : O.sections U) (p : RS.carrier), p ∈ U.carrier → ℤ

  /-- Order is non-negative for holomorphic functions -/
  orderAt_nonneg : ∀ U f p hp, 0 ≤ orderAt U f p hp

  /-- Order of 1 is 0 at all points -/
  orderAt_one : ∀ U p hp, orderAt U 1 p hp = 0

  /-- Order of product is sum of orders: ord(fg) = ord(f) + ord(g) -/
  orderAt_mul : ∀ U f g p hp,
    orderAt U (f * g) p hp = orderAt U f p hp + orderAt U g p hp

  /-- Positive order iff value is zero: ord_p(f) > 0 ↔ f(p) = 0 -/
  orderAt_pos_iff : ∀ U f p hp,
    0 < orderAt U f p hp ↔ O.evalAt U p hp f = 0

  /-- Order is 0 for nonzero constants -/
  orderAt_algebraMap : ∀ U p hp c, c ≠ 0 →
    orderAt U (algebraMap ℂ (O.sections U) c) p hp = 0

  /-- Compatibility with restrictions -/
  orderAt_restrict : ∀ {U V : OpenSet RS} (h : U ≤ V) f p (hpU : p ∈ U.carrier),
    orderAt U (O.restrict h f) p hpU = orderAt V f p (h hpU)

namespace SectionOrder

variable {RS : RiemannSurface} {O : StructureSheaf RS}

/-- Order of 0 is positive (actually +∞, but we just need > 0) -/
theorem orderAt_zero_pos (ord : SectionOrder RS O) (U : OpenSet RS) (p : RS.carrier)
    (hp : p ∈ U.carrier) : 0 < ord.orderAt U 0 p hp := by
  rw [ord.orderAt_pos_iff]
  simp only [map_zero]

/-- A section with order 0 is nonvanishing -/
theorem orderAt_zero_iff_ne (ord : SectionOrder RS O) (U : OpenSet RS) (f : O.sections U)
    (p : RS.carrier) (hp : p ∈ U.carrier) :
    ord.orderAt U f p hp = 0 ↔ O.evalAt U p hp f ≠ 0 := by
  constructor
  · intro h hcontra
    have hpos : 0 < ord.orderAt U f p hp := (ord.orderAt_pos_iff U f p hp).mpr hcontra
    omega
  · intro h
    have hnpos : ¬(0 < ord.orderAt U f p hp) := by
      intro hpos
      exact h ((ord.orderAt_pos_iff U f p hp).mp hpos)
    have hnonneg := ord.orderAt_nonneg U f p hp
    omega

end SectionOrder

/-!
## Line Bundle Sheaf Data

The full structure for line bundle assignments D ↦ O(D).
-/

/-- Complete data for line bundle sheaves.

    This packages:
    - A section order function (from localUniformizer)
    - The sheaf O(D) for each divisor D
    - Key properties like O(0) = O

    Taking this as input to cohomology theory is mathematically sound because:
    1. Any concrete construction (algebraic or analytic) must satisfy these properties
    2. GAGA ensures algebraic and analytic give the same answer for compact surfaces
    3. The cohomology theory depends only on these abstract properties -/
structure LineBundleSheafData (RS : RiemannSurface) (O : StructureSheaf RS) where
  /-- The order function for sections -/
  sectionOrder : SectionOrder RS O

  /-- The sheaf O(D) for each divisor D -/
  sheafOf : (D : Divisor RS) → LineBundleSheaf RS O D

  /-- O(0) is canonically isomorphic to the structure sheaf O.
      For each open U, sections of O(0) over U are identified with O(U). -/
  zero_eq_structure : ∀ U, Nonempty ((sheafOf 0).sections U ≃+ O.sections U)

  /-- The isomorphism O(0)(U) ≃ O(U) is compatible with the O(U)-module structure.
      This ensures the isomorphism is an O(U)-module isomorphism, not just additive. -/
  zero_eq_structure_module : ∀ U,
    ∃ (φ : (sheafOf 0).sections U ≃+ O.sections U),
      ∀ (f : O.sections U) (s : (sheafOf 0).sections U), φ (f • s) = f * φ s

namespace LineBundleSheafData

variable {RS : RiemannSurface} {O : StructureSheaf RS}

/-- Convert to LineBundleSheafAssignment for use in cohomology theory.

    **Note:** We assume sheafOf 0 corresponds to the structure sheaf O.
    This is the case for properly constructed LineBundleSheafData. -/
noncomputable def toAssignment (data : LineBundleSheafData RS O) :
    LineBundleSheafAssignment RS O where
  sheafOf := fun D => (data.sheafOf D).toCoherentSheaf

/-- Global sections of O(D) -/
def H0 (data : LineBundleSheafData RS O) (D : Divisor RS) : Type* :=
  (data.sheafOf D).sections OpenSet.univ

end LineBundleSheafData

/-!
## Existence from localUniformizer

We outline how SectionOrder can be constructed from StructureSheaf.localUniformizer.
The full construction requires DVR theory.
-/

/-- Existence of section order from localUniformizer.

    The localUniformizer at each point p provides a local coordinate z with z(p) = 0
    and the property that every f with f(p) = 0 is divisible by z. This makes the
    local ring O_{Σ,p} a DVR with uniformizer z.

    The order function is then defined recursively:
    - If f(p) ≠ 0: ord_p(f) = 0
    - If f(p) = 0: f = z · g, so ord_p(f) = 1 + ord_p(g)

    This construction requires:
    1. DVR theory (Mathlib has this)
    2. Extension to meromorphic functions (for O(D) with D < 0)
    3. Careful handling of open sets vs. germs

    We axiomatize the result rather than constructing it explicitly. -/
theorem exists_sectionOrder_from_uniformizer (RS : RiemannSurface) (O : StructureSheaf RS) :
    ∃ (ord : SectionOrder RS O), True := by
  -- The construction uses O.localUniformizer
  -- For now we leave this as sorry; the main point is the structure exists
  sorry

/-!
## Notes on Full Construction

To fully construct LineBundleSheafData requires:

### 1. Section Order Construction

From localUniformizer, define:
```
ord_p(f) = sup { n : ∃ g, f = z^n · g in O_p }
```
where z is the localUniformizer at p and O_p is the germ.

This is well-defined because O_p is a DVR.

### 2. O(D) Sections Construction

Define O(D)(U) as the set of meromorphic functions f on U with:
```
ord_p(f) ≥ -D(p) for all p ∈ U
```

This requires extending from holomorphic to meromorphic, which can be done via:
- The function field K(Σ) of the Riemann surface
- Local description: f is a ratio g/h of holomorphic functions

### 3. Line Bundle Structure

Show O(D)(U) is:
- An O(U)-module (via f · s for f ∈ O(U), s ∈ O(D)(U))
- Locally free of rank 1: near p, O(D) ≅ O via s ↦ z^{D(p)} · s

### 4. Sheaf Axioms

Verify locality and gluing for the O(D) construction.

---

For Riemann-Roch, we can use LineBundleSheafData axiomatically because:
- Riemann-Roch only needs formal properties of cohomology
- The cohomological properties follow from the abstract structure
- GAGA guarantees any concrete construction gives the same result
-/

end RiemannSurfaces.Algebraic.Cohomology
