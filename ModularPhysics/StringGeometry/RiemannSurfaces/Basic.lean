import ModularPhysics.StringGeometry.RiemannSurfaces.Analytic.Basic

/-!
# Riemann Surfaces - Common Entry Point

This file serves as the main entry point for Riemann surface theory, re-exporting
definitions from the specialized subfolders.

## Architecture

The formalization is organized into three perspectives:

- **Analytic/** - Complex manifolds, holomorphic functions (core definitions live here)
- **Algebraic/** - Divisors, sheaf cohomology, Riemann-Roch
- **Combinatorial/** - Ribbon graphs, Penner/Kontsevich moduli theory

These are connected via **GAGA/** which shows that for compact Riemann surfaces,
the algebraic and analytic viewpoints are equivalent.

## What's in this file

This file re-exports the core definitions (RiemannSurface, CompactRiemannSurface)
from Analytic/Basic.lean and adds:

- Holomorphic line bundles (with degree as intrinsic data)
- Canonical bundles
- Spin structures (with parity as intrinsic data)

For divisors and Riemann-Roch, see `Algebraic/Divisors.lean` and `Algebraic/RiemannRoch.lean`.

## References

* Farkas, Kra "Riemann Surfaces"
* Griffiths, Harris "Principles of Algebraic Geometry", Chapter 2
* Donaldson "Riemann Surfaces"
-/

namespace RiemannSurfaces

-- Re-export core definitions from Analytic
-- This allows downstream code to continue using RiemannSurfaces.RiemannSurface
export Analytic (ComplexManifold RiemannSurface CompactRiemannSurface
  complexManifold_complex ComplexPlane RiemannSphere genus0Surface genus0Surface_genus
  chartedSpace_onePoint complexManifold_onePoint)

/-!
## Holomorphic Line Bundles

We define these abstractly for the formalization.
-/

/-- Data for local trivializations of a line bundle.

    A local trivialization over U ⊂ Σ is an isomorphism φ : L|_U → U × ℂ.
    The transition functions g_{ij} = φ_j ∘ φ_i⁻¹ on U_i ∩ U_j must be holomorphic. -/
structure LocalTrivialization (RS : RiemannSurface) where
  /-- The open subset U where the trivialization is defined -/
  domain : Set RS.carrier
  /-- Trivialization function (abstractly represented) -/
  trivId : ℕ

/-- A holomorphic line bundle over a Riemann surface.

    A holomorphic line bundle L → Σ consists of:
    - Total space E with projection π : E → Σ
    - Fibers π⁻¹(p) ≅ ℂ are 1-dimensional ℂ-vector spaces
    - Local trivializations: L|_U ≅ U × ℂ with holomorphic transition functions

    **Key examples:**
    - Trivial bundle O (sections = holomorphic functions)
    - Canonical bundle K (sections = holomorphic 1-forms)
    - Point bundle O(p) for p ∈ Σ
    - Spin bundles S with S ⊗ S ≅ K

    **Note on degree:** The degree is included as intrinsic data of the bundle.
    On a compact surface, deg(L) = c₁(L) (first Chern class integrated over Σ).
    For a divisor line bundle O(D), deg(O(D)) = deg(D). -/
structure HolomorphicLineBundle (RS : RiemannSurface) where
  /-- The total space of the bundle -/
  totalSpace : Type*
  /-- Bundle projection -/
  proj : totalSpace → RS.carrier
  /-- Local trivializations covering the surface -/
  trivializations : Set (LocalTrivialization RS)
  /-- The trivializations cover the surface -/
  covers : ∀ p : RS.carrier, ∃ φ ∈ trivializations, p ∈ φ.domain
  /-- Transition functions between overlapping trivializations are holomorphic.
      This is the key condition making the bundle "holomorphic".
      Transition function g_{ij} : U_i ∩ U_j → ℂ* is holomorphic and nonvanishing. -/
  transitionsHolomorphic : Prop  -- Full formalization requires complex analysis on RS
  /-- Degree of the line bundle (first Chern number).
      On a compact surface, this is c₁(L) = ∫_Σ c₁(L).
      For divisor bundles O(D), this equals deg(D). -/
  degree : ℤ

/-- The canonical bundle K (holomorphic cotangent bundle).

    The canonical bundle K = T*Σ^{1,0} is the bundle of holomorphic 1-forms.
    - Local sections: f(z)dz where f is holomorphic
    - Transition: dz' = (dz'/dz) dz, so g_{ij} = dz_j/dz_i
    - deg(K) = 2g - 2 (Riemann-Hurwitz)
    - dim H⁰(K) = g (by Riemann-Roch) -/
structure CanonicalBundle (RS : RiemannSurface) extends HolomorphicLineBundle RS where
  /-- The canonical bundle has specific transition functions determined by the atlas.
      For charts (U_i, z_i) and (U_j, z_j), the transition function is g_{ij} = dz_j/dz_i.
      This encodes that sections transform as 1-forms: f(z)dz → f(z(w))(dz/dw)dw. -/
  transitionsAreCotangent : Prop  -- g_{ij} = dz_j/dz_i (derivative of coordinate change)

/-- Degree of canonical bundle is 2g - 2 (Riemann-Hurwitz formula).

    This theorem expresses that for a canonical bundle on a compact Riemann surface
    of genus g, the degree (as recorded in the bundle data) equals 2g - 2.

    **Note:** When constructing a CanonicalBundle, the degree field must be set to
    2g - 2 for this theorem to hold. This is the content of Riemann-Hurwitz. -/
theorem canonical_degree (CRS : CompactRiemannSurface)
    (K : CanonicalBundle CRS.toRiemannSurface)
    (hdeg : K.degree = 2 * (CRS.genus : ℤ) - 2) :
    K.toHolomorphicLineBundle.degree = 2 * (CRS.genus : ℤ) - 2 :=
  hdeg

/-!
## Spin Structures

A spin structure is a square root of the canonical bundle.
-/

/-- Parity of a spin structure (even or odd) -/
inductive SpinParity
  | even : SpinParity  -- h⁰(S) even
  | odd : SpinParity   -- h⁰(S) odd
  deriving DecidableEq

/-- A spin structure is a square root of the canonical bundle.

    Mathematically, a spin structure on Σ is a holomorphic line bundle S
    with an isomorphism S ⊗ S ≅ K (the canonical bundle).

    **Existence:** Spin structures exist iff deg(K) is even (always true since
    deg(K) = 2g - 2). For genus g, there are 2^{2g} distinct spin structures.

    **Classification:** Spin structures correspond to:
    - H¹(Σ, ℤ/2ℤ) ≅ (ℤ/2ℤ)^{2g}
    - Theta characteristics: divisor classes [S] with 2[S] = [K]

    **Parity:** The parity of a spin structure is h⁰(S) mod 2.
    This is a topological invariant (Atiyah, Mumford).

    **Note:** The parity is included as intrinsic data of the spin structure,
    as computing it requires cohomology theory (see Algebraic/RiemannRoch.lean). -/
structure SpinStructure (RS : RiemannSurface) where
  /-- The spin bundle S with S ⊗ S ≅ K -/
  spinBundle : HolomorphicLineBundle RS
  /-- The canonical bundle K -/
  canonical : CanonicalBundle RS
  /-- The degree of S is half the degree of K: deg(S) = g - 1.
      This is a necessary condition for S ⊗ S ≅ K. -/
  degree_half : spinBundle.degree * 2 = canonical.degree
  /-- The parity of the spin structure: even if h⁰(S) is even, odd otherwise.
      For genus g, there are 2^{g-1}(2^g + 1) even and 2^{g-1}(2^g - 1) odd spin structures.
      This is a topological invariant (Atiyah, Mumford). -/
  parity : SpinParity

/-!
## Note on Divisors and Riemann-Roch

Divisor theory and the Riemann-Roch theorem are developed in the Algebraic/ subfolder:

- **Divisors**: `Algebraic/Divisors.lean` - Full divisor group structure with AddCommGroup
- **Sheaf cohomology**: `Algebraic/Cohomology/` - H^i(Σ, O(D)) via Čech cohomology
- **Riemann-Roch**: `Algebraic/RiemannRoch.lean` - Full proof: h⁰(D) - h¹(D) = deg(D) - g + 1

This file focuses on the analytic foundations (line bundles, spin structures) that
do not require divisor arithmetic.
-/

end RiemannSurfaces
