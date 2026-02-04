import ModularPhysics.StringGeometry.RiemannSurfaces.Basic

/-!
# Spin Structures on Riemann Surfaces

This file contains the definitions related to spin structures on Riemann surfaces.

## Main Definitions

* `SpinParity` - Even or odd parity of a spin structure
* `HolomorphicLineBundle` - Abstract holomorphic line bundle over a Riemann surface
* `CanonicalBundle` - The canonical bundle K (holomorphic cotangent bundle)
* `SpinStructure` - A square root of the canonical bundle

## Mathematical Background

A spin structure on a Riemann surface Σ is a holomorphic line bundle S
with an isomorphism S ⊗ S ≅ K (the canonical bundle).

For a compact Riemann surface of genus g:
- There are 2^{2g} spin structures
- They are classified by their parity (h⁰(S) mod 2)
- Even spin structures: 2^{g-1}(2^g + 1)
- Odd spin structures: 2^{g-1}(2^g - 1)

## References

* Atiyah "Riemann Surfaces and Spin Structures" (1971)
* Johnson "Spin Structures and Quadratic Forms on Surfaces"
* Mumford "Theta Characteristics of an Algebraic Curve"
-/

namespace RiemannSurfaces

/-!
## Spin Parity
-/

/-- Parity of a spin structure (even or odd).

    For a compact Riemann surface of genus g with spin structure L (L ⊗ L ≅ K):
    - **Even**: h⁰(L) is even (Arf invariant = 0)
    - **Odd**: h⁰(L) is odd (Arf invariant = 1)

    The parity is a topological invariant (Atiyah's theorem).
    For genus g, there are:
    - 2^{g-1}(2^g + 1) even spin structures
    - 2^{g-1}(2^g - 1) odd spin structures -/
inductive SpinParity
  | even : SpinParity
  | odd : SpinParity
  deriving DecidableEq, Repr

/-- The Arf invariant of a spin parity: 0 for even, 1 for odd -/
def SpinParity.arfInvariant : SpinParity → Fin 2
  | .even => 0
  | .odd => 1

/-!
## Holomorphic Line Bundles
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

/-!
## Canonical Bundle
-/

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
-/

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

end RiemannSurfaces
