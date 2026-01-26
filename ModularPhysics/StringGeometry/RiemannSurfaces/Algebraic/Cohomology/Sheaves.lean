import ModularPhysics.StringGeometry.RiemannSurfaces.Basic
import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.Divisors
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Sheaves on Riemann Surfaces

This file develops the theory of coherent sheaves on Riemann surfaces, particularly
the structure sheaf O and line bundle sheaves O(D).

## Relationship to Other Files

- **This file (Cohomology/Sheaves.lean)**: Sheaves on **individual** Riemann surfaces Σ.
  Used for Riemann-Roch theorem: H^i(Σ, O(D)).

- **VectorBundles.lean**: Bundles over the **moduli space** M_{g,n}.
  Used for intersection theory: Hodge bundle E, ψ-classes, λ-classes.

- **Divisors.lean**: Defines `Divisor` structure used to parameterize line bundles O(D).

The distinction: here we fix a single curve Σ and study sheaves on it;
VectorBundles.lean studies how these structures vary over the moduli space.

## Mathematical Background

On a Riemann surface Σ, we have:

1. **Structure sheaf O**: The sheaf of holomorphic functions
   - O(U) = {holomorphic f : U → ℂ}
   - This is a sheaf of ℂ-algebras

2. **Line bundle sheaves O(D)**: For a divisor D
   - O(D)(U) = {meromorphic f on U : (f)|_U + D|_U ≥ 0}
   - These are invertible O-modules (rank 1 locally free)

3. **Coherent sheaves**: Finite type O-modules with finite presentation
   - On curves, coherent = locally free ⊕ torsion

## Main Definitions

* `StructureSheaf` - The sheaf O of holomorphic functions
* `LineBundleSheaf` - The sheaf O(D) for a divisor D
* `CoherentSheaf` - Category of coherent O-modules

## References

* Hartshorne "Algebraic Geometry" Ch II
* Griffiths, Harris "Principles of Algebraic Geometry"
-/

namespace RiemannSurfaces.Algebraic.Cohomology

open CategoryTheory RiemannSurfaces

/-!
## The Site Structure

A Riemann surface has a natural site structure given by the open cover topology.
-/

/-- The category of open sets of a Riemann surface, ordered by inclusion.
    This forms a small category that serves as the site for sheaves. -/
structure OpenSet (RS : RiemannSurface) where
  /-- The underlying set -/
  carrier : Set RS.carrier
  /-- It is open -/
  isOpen : @IsOpen RS.carrier RS.topology carrier

namespace OpenSet

variable {RS : RiemannSurface}

instance : LE (OpenSet RS) where
  le U V := U.carrier ⊆ V.carrier

instance : Preorder (OpenSet RS) where
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ := Set.Subset.trans

/-- The whole space as an open set -/
def univ : OpenSet RS where
  carrier := Set.univ
  isOpen := @isOpen_univ RS.carrier RS.topology

/-- The empty set -/
def empty : OpenSet RS where
  carrier := ∅
  isOpen := @isOpen_empty RS.carrier RS.topology

/-- Intersection of open sets -/
def inter (U V : OpenSet RS) : OpenSet RS where
  carrier := U.carrier ∩ V.carrier
  isOpen := @IsOpen.inter RS.carrier RS.topology _ _ U.isOpen V.isOpen

/-- Union of a family of open sets -/
def union {ι : Type*} (U : ι → OpenSet RS) : OpenSet RS where
  carrier := ⋃ i, (U i).carrier
  isOpen := RS.topology.isOpen_sUnion (Set.range fun i => (U i).carrier)
    (by rintro _ ⟨i, rfl⟩; exact (U i).isOpen)

/-- A family of open sets covers U if their union contains U -/
def isCover {ι : Type*} (cover : ι → OpenSet RS) (U : OpenSet RS) : Prop :=
  U.carrier ⊆ (union cover).carrier

end OpenSet

/-!
## Structure Sheaf

The structure sheaf O assigns to each open set U the ring of holomorphic functions on U.
-/

/-- The structure sheaf O of a Riemann surface.

    O(U) = {holomorphic functions f : U → ℂ}

    This is a sheaf of ℂ-algebras. The sheaf axioms are:
    - Locality: if f|_{U_i} = 0 for all i, then f = 0
    - Gluing: if f_i ∈ O(U_i) agree on overlaps, they glue to f ∈ O(⋃U_i)

    **Implementation**: We represent O abstractly as a structure carrying
    the assignment of rings to open sets. The actual ring of holomorphic
    functions requires complex analysis infrastructure. -/
structure StructureSheaf (RS : RiemannSurface) where
  /-- Sections over an open set (abstractly, this is the ring O(U)) -/
  sections : OpenSet RS → Type*
  /-- Each section space is a ℂ-algebra -/
  [algebraStructure : ∀ U, CommRing (sections U)]
  /-- Restriction maps -/
  restrict : ∀ {U V : OpenSet RS}, U ≤ V → sections V → sections U
  /-- Restriction is a ring homomorphism: preserves addition -/
  restrict_add : ∀ {U V : OpenSet RS} (h : U ≤ V) (s t : sections V),
    restrict h (s + t) = restrict h s + restrict h t
  /-- Restriction is a ring homomorphism: preserves multiplication -/
  restrict_mul : ∀ {U V : OpenSet RS} (h : U ≤ V) (s t : sections V),
    restrict h (s * t) = restrict h s * restrict h t
  /-- Restriction is a ring homomorphism: preserves one -/
  restrict_one : ∀ {U V : OpenSet RS} (h : U ≤ V), restrict h 1 = 1
  /-- Restriction is functorial: id -/
  restrict_id : ∀ U (s : sections U), restrict (le_refl U) s = s
  /-- Restriction is functorial: composition -/
  restrict_comp : ∀ {U V W : OpenSet RS} (hUV : U ≤ V) (hVW : V ≤ W) (s : sections W),
    restrict hUV (restrict hVW s) = restrict (le_trans hUV hVW) s
  /-- **Sheaf axiom: Locality** - A section is determined by its restrictions.
      If s, t ∈ O(U) satisfy s|_V = t|_V for all V ⊆ U, then s = t. -/
  locality : ∀ {U : OpenSet RS} (s t : sections U),
    (∀ V : OpenSet RS, ∀ h : V ≤ U, restrict h s = restrict h t) → s = t
  /-- **Sheaf axiom: Gluing** - Compatible local sections glue to a global one.

      Given an open cover {U_i} of U and sections s_i ∈ O(U_i) that are compatible
      (meaning s_i|_{U_i ∩ U_j} = s_j|_{U_i ∩ U_j} for all i,j), there exists a unique
      section s ∈ O(U) with s|_{U_i} = s_i for all i. -/
  gluing : ∀ {ι : Type*} {U : OpenSet RS} (cover : ι → OpenSet RS),
    -- The cover covers U
    OpenSet.isCover cover U →
    -- Each cover element is contained in U
    (∀ i, (cover i) ≤ U) →
    -- Given a family of local sections
    ∀ (family : ∀ i, sections (cover i)),
    -- That are compatible on overlaps
    (∀ i j, ∀ h1 : (cover i).inter (cover j) ≤ cover i,
            ∀ h2 : (cover i).inter (cover j) ≤ cover j,
            restrict h1 (family i) = restrict h2 (family j)) →
    -- There exists a global section restricting to each local section
    ∃ (s : sections U), ∀ i, ∀ h : cover i ≤ U, restrict h s = family i

attribute [instance] StructureSheaf.algebraStructure

namespace StructureSheaf

variable {RS : RiemannSurface}

/-- Global sections H⁰(Σ, O) = O(Σ) -/
def globalSections (O : StructureSheaf RS) : Type* := O.sections OpenSet.univ

/-- Global sections form a ℂ-algebra -/
instance (O : StructureSheaf RS) : CommRing O.globalSections := O.algebraStructure _

end StructureSheaf

/-!
## Line Bundle Sheaves O(D)

For a divisor D, the sheaf O(D) consists of meromorphic functions with poles bounded by D.
-/

/-- The line bundle sheaf O(D) associated to a divisor D, with respect to a structure sheaf O.

    O(D)(U) = {f meromorphic on U : (f)|_U + D|_U ≥ 0}
            = {f : poles of f on U are bounded by D}

    Key properties:
    - O(0) = O (the structure sheaf)
    - O(D + E) ≅ O(D) ⊗_O O(E)
    - O(D) is an invertible O-module (locally free of rank 1)

    **Cohomology**: H^i(Σ, O(D)) are the key objects for Riemann-Roch.

    **O(U)-module structure**: Line bundles are O-modules that are locally free of rank 1.
    Each L(U) is an O(U)-module, and locally L(U) ≃ O(U) as O(U)-modules. -/
structure LineBundleSheaf (RS : RiemannSurface) (O : StructureSheaf RS) (D : Divisor RS) where
  /-- Sections over an open set -/
  sections : OpenSet RS → Type*
  /-- Each section space is an additive commutative group -/
  [addCommGroup : ∀ U, AddCommGroup (sections U)]
  /-- Each section space is an O(U)-module -/
  [module : ∀ U, Module (O.sections U) (sections U)]
  /-- Restriction maps (additive group homomorphisms) -/
  restrict : ∀ {U V : OpenSet RS}, U ≤ V → sections V → sections U
  /-- Restriction is O(V)-linear: (f · s)|_U = f|_U · s|_U -/
  restrict_smul : ∀ {U V : OpenSet RS} (h : U ≤ V) (f : O.sections V) (s : sections V),
    restrict h (f • s) = O.restrict h f • restrict h s
  /-- Restriction preserves addition -/
  restrict_add : ∀ {U V : OpenSet RS} (h : U ≤ V) (s t : sections V),
    restrict h (s + t) = restrict h s + restrict h t
  /-- Restriction is functorial: id -/
  restrict_id : ∀ U (s : sections U), restrict (le_refl U) s = s
  /-- Restriction is functorial: composition -/
  restrict_comp : ∀ {U V W : OpenSet RS} (hUV : U ≤ V) (hVW : V ≤ W) (s : sections W),
    restrict hUV (restrict hVW s) = restrict (le_trans hUV hVW) s
  /-- **Sheaf axiom: Locality** - A section is determined by its local restrictions. -/
  locality : ∀ {U : OpenSet RS} (s t : sections U),
    (∀ V : OpenSet RS, ∀ h : V ≤ U, restrict h s = restrict h t) → s = t
  /-- **Sheaf axiom: Gluing** - Compatible local sections glue to a global section. -/
  gluing : ∀ {ι : Type*} {U : OpenSet RS} (cover : ι → OpenSet RS),
    OpenSet.isCover cover U →
    (∀ i, (cover i) ≤ U) →
    ∀ (family : ∀ i, sections (cover i)),
    (∀ i j, ∀ h1 : (cover i).inter (cover j) ≤ cover i,
            ∀ h2 : (cover i).inter (cover j) ≤ cover j,
            restrict h1 (family i) = restrict h2 (family j)) →
    ∃ (s : sections U), ∀ i, ∀ h : cover i ≤ U, restrict h s = family i
  /-- Locally free of rank 1: each point has a neighborhood V where sections form a free
      O(V)-module of rank 1. Moreover, this triviality propagates to all smaller opens U ⊆ V
      containing p (a consequence of the sheaf structure).

      **Local trivialization**: On a trivializing open U, L(U) ≃ O(U) as O(U)-modules.
      We represent this as an additive group isomorphism that is compatible with scaling. -/
  locallyTrivial : ∀ (p : RS.carrier), ∃ (V : OpenSet RS), p ∈ V.carrier ∧
    ∀ (U : OpenSet RS), U ≤ V → p ∈ U.carrier →
      ∃ (φ : sections U ≃+ O.sections U),
        ∀ (f : O.sections U) (s : sections U), φ (f • s) = f * φ s

attribute [instance] LineBundleSheaf.addCommGroup LineBundleSheaf.module

namespace LineBundleSheaf

variable {RS : RiemannSurface} {O : StructureSheaf RS} {D : Divisor RS}

/-- Global sections H⁰(Σ, O(D)) -/
def H0 (L : LineBundleSheaf RS O D) : Type* := L.sections OpenSet.univ

/-- The Riemann-Roch space L(D) = H⁰(Σ, O(D)) -/
abbrev RiemannRochSpace (L : LineBundleSheaf RS O D) := L.H0

end LineBundleSheaf

/-!
## Canonical Sheaf

The canonical sheaf K = Ω¹ is the sheaf of holomorphic 1-forms.
-/

/-- The canonical sheaf K (sheaf of holomorphic 1-forms).

    K(U) = {holomorphic 1-forms on U}

    In local coordinates z: sections are f(z)dz where f is holomorphic.
    This is O(K) where K is the canonical divisor.

    Key properties:
    - K is a line bundle (locally free of rank 1)
    - deg(K) = 2g - 2 (for a compact surface of genus g)
    - H⁰(K) = g (dimension of holomorphic 1-forms = genus) -/
structure CanonicalSheaf (RS : RiemannSurface) (O : StructureSheaf RS) where
  /-- The canonical divisor K -/
  canonicalDivisor : Divisor RS
  /-- The underlying line bundle sheaf O(K) -/
  toLineBundleSheaf : LineBundleSheaf RS O canonicalDivisor
  /-- The degree of K is 2g - 2 (for compact surfaces) -/
  degree_eq : ∀ (CRS : CompactRiemannSurface), RS = CRS.toRiemannSurface →
    canonicalDivisor.degree = 2 * (CRS.genus : ℤ) - 2

/-!
## Category of Coherent Sheaves

Coherent sheaves form an abelian category, which is essential for cohomology.
-/

/-- A coherent sheaf on a Riemann surface with respect to a structure sheaf O.

    A coherent O-module F is:
    1. A sheaf of O-modules: each F(U) is an O(U)-module, satisfying sheaf axioms
    2. Of finite type: locally generated by finitely many sections
    3. Finitely presented: kernel of any finite surjection O^n → F is also finite type

    On a curve, every coherent sheaf decomposes as:
    F = (locally free part) ⊕ (torsion part)

    **Key theorem**: The category of coherent sheaves is abelian.

    **O(U)-module structure**: Each F(U) is a module over the ring O(U) of holomorphic
    functions on U. The module action f · s for f ∈ O(U), s ∈ F(U) represents
    pointwise multiplication of a section by a holomorphic function.

    **Compatibility with restrictions**: For V ⊆ U, the restriction F(U) → F(V)
    is O(U)-linear, where O(U) acts on F(V) via the restriction O(U) → O(V). -/
structure CoherentSheaf (RS : RiemannSurface) (O : StructureSheaf RS) where
  /-- Sections over an open set -/
  sections : OpenSet RS → Type*
  /-- Each section space is an additive group -/
  [addCommGroup : ∀ U, AddCommGroup (sections U)]
  /-- Each section space is an O(U)-module (module over holomorphic functions) -/
  [module : ∀ U, Module (O.sections U) (sections U)]
  /-- Restriction maps (additive group homomorphisms) -/
  restrict : ∀ {U V : OpenSet RS}, U ≤ V → sections V → sections U
  /-- Restriction is O(V)-linear: (f · s)|_U = f|_U · s|_U -/
  restrict_smul : ∀ {U V : OpenSet RS} (h : U ≤ V) (f : O.sections V) (s : sections V),
    restrict h (f • s) = O.restrict h f • restrict h s
  /-- Restriction preserves addition -/
  restrict_add : ∀ {U V : OpenSet RS} (h : U ≤ V) (s t : sections V),
    restrict h (s + t) = restrict h s + restrict h t
  /-- Restriction is functorial: id -/
  restrict_id : ∀ U (s : sections U), restrict (le_refl U) s = s
  /-- Restriction is functorial: composition -/
  restrict_comp : ∀ {U V W : OpenSet RS} (hUV : U ≤ V) (hVW : V ≤ W) (s : sections W),
    restrict hUV (restrict hVW s) = restrict (le_trans hUV hVW) s
  /-- **Sheaf axiom: Locality** - A section is determined by its local restrictions.
      If s, t ∈ F(U) agree on all elements of an open cover, then s = t.

      More precisely: if {Uᵢ} covers U and s|_{Uᵢ} = t|_{Uᵢ} for all i, then s = t. -/
  locality : ∀ {U : OpenSet RS} (s t : sections U),
    (∀ V : OpenSet RS, ∀ h : V ≤ U, restrict h s = restrict h t) → s = t
  /-- **Sheaf axiom: Gluing** - Compatible local sections glue to a global section.

      Given an open cover {Uᵢ} of U and sections sᵢ ∈ F(Uᵢ) that agree on overlaps
      (i.e., sᵢ|_{Uᵢ ∩ Uⱼ} = sⱼ|_{Uᵢ ∩ Uⱼ}), there exists s ∈ F(U) with s|_{Uᵢ} = sᵢ. -/
  gluing : ∀ {ι : Type*} {U : OpenSet RS} (cover : ι → OpenSet RS),
    -- The cover covers U
    OpenSet.isCover cover U →
    -- Each cover element is contained in U
    (∀ i, (cover i) ≤ U) →
    -- Given a family of local sections
    ∀ (family : ∀ i, sections (cover i)),
    -- That are compatible on overlaps
    (∀ i j, ∀ h1 : (cover i).inter (cover j) ≤ cover i,
            ∀ h2 : (cover i).inter (cover j) ≤ cover j,
            restrict h1 (family i) = restrict h2 (family j)) →
    -- There exists a global section restricting to each local section
    ∃ (s : sections U), ∀ i, ∀ h : cover i ≤ U, restrict h s = family i
  /-- **Finite type**: Locally finitely generated as an O-module.

      At each point p, there exists a neighborhood U and finitely many generators
      e₁, ..., eₙ ∈ F(U) such that the O(U)-linear map O(U)^n → F(U) sending
      (f₁, ..., fₙ) ↦ Σᵢ fᵢ · eᵢ is surjective.

      We record: the open U, the number n of generators, and the generators themselves.
      Surjectivity is encoded by requiring every section is an O(U)-linear combination. -/
  finiteType : ∀ (p : RS.carrier), ∃ (U : OpenSet RS) (n : ℕ),
    p ∈ U.carrier ∧
    -- n generators exist
    ∃ (generators : Fin n → sections U),
    -- Every section is an O(U)-linear combination of generators
    ∀ s : sections U, ∃ (coeffs : Fin n → O.sections U), s = ∑ i, coeffs i • generators i
  /-- **Finite presentation**: The kernel of the generating map is finitely generated.

      Given n generators, there exist m relations (syzygies) r₁, ..., rₘ where
      each rⱼ = (rⱼ₁, ..., rⱼₙ) ∈ O(U)^n satisfies Σᵢ rⱼᵢ · eᵢ = 0.
      These relations generate the kernel of the generating map.

      We record: the number m of relations, and the relation vectors.

      **Kernel generation**: Any syzygy c = (c₁, ..., cₙ) with Σᵢ cᵢ · eᵢ = 0
      is an O(U)-linear combination of the given relations:
        cᵢ = Σⱼ aⱼ · rⱼᵢ  for some coefficients a₁, ..., aₘ ∈ O(U) -/
  finitePresentation : ∀ (p : RS.carrier), ∃ (U : OpenSet RS) (n m : ℕ),
    p ∈ U.carrier ∧
    -- n generators and m relations exist
    ∃ (generators : Fin n → sections U) (relations : Fin m → (Fin n → O.sections U)),
    -- Each relation gives zero: Σᵢ rⱼᵢ · eᵢ = 0
    (∀ j : Fin m, ∑ i, relations j i • generators i = 0) ∧
    -- The relations generate the kernel: any syzygy is an O(U)-linear combination of relations
    (∀ (c : Fin n → O.sections U), (∑ i, c i • generators i = 0) →
      ∃ (a : Fin m → O.sections U), ∀ i, c i = ∑ j, a j * relations j i)

attribute [instance] CoherentSheaf.addCommGroup CoherentSheaf.module

/-- Line bundle sheaves are coherent O-modules.

    **Proof outline**: A line bundle L is locally free of rank 1, meaning:
    - Locally, L(U) ≃ O(U) as O(U)-modules
    - This gives 1 generator (the preimage of 1 under the trivialization)
    - No relations (free module of rank 1) -/
noncomputable def LineBundleSheaf.toCoherentSheaf {RS : RiemannSurface} {O : StructureSheaf RS}
    {D : Divisor RS} (L : LineBundleSheaf RS O D) : CoherentSheaf RS O where
  sections := L.sections
  addCommGroup := L.addCommGroup
  module := L.module
  restrict := L.restrict
  restrict_smul := L.restrict_smul
  restrict_add := L.restrict_add
  restrict_id := L.restrict_id
  restrict_comp := L.restrict_comp
  locality := L.locality
  gluing := L.gluing
  finiteType := fun p =>
    -- Use locallyTrivial to get a trivializing neighborhood
    let ⟨V, hpV, htriv⟩ := L.locallyTrivial p
    -- Get the trivialization φ : L(V) ≃+ O(V) for V itself
    let ⟨φ, hφ⟩ := htriv V (le_refl V) hpV
    -- The generator is e = φ⁻¹(1) ∈ L(V)
    let e : L.sections V := φ.symm 1
    ⟨V, 1, hpV,
      ⟨fun _ => e,
      -- Every section s is s = f · e where f = φ(s) ∈ O(V)
      fun s =>
        let f : O.sections V := φ s
        ⟨fun _ => f, by
          simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
          -- Need: s = f • e = f • φ⁻¹(1)
          -- By the trivialization property: φ(f • e) = f * φ(e) = f * 1 = f
          -- So φ⁻¹(f) = f • e (since φ is an isomorphism)
          -- And f = φ(s), so φ⁻¹(φ(s)) = s = f • e
          have h1 : φ (f • e) = f * φ e := hφ f e
          have h2 : φ e = 1 := φ.apply_symm_apply 1
          rw [h2, mul_one] at h1
          -- Now h1 : φ (f • e) = f, and f = φ s, so φ (f • e) = φ s
          -- By injectivity of φ: f • e = s
          have h3 : φ (f • e) = φ s := h1
          exact (φ.injective h3).symm⟩⟩⟩
  finitePresentation := fun p =>
    let ⟨V, hpV, htriv⟩ := L.locallyTrivial p
    let ⟨φ, hφ⟩ := htriv V (le_refl V) hpV
    let e : L.sections V := φ.symm 1
    -- Line bundles are free of rank 1, so 0 relations
    ⟨V, 1, 0, hpV,
      ⟨fun _ => e,
       finZeroElim,  -- no relations
       finZeroElim,  -- trivially satisfied
       -- Kernel generation: if f • e = 0, then f = 0
       fun c hc => by
         simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at hc
         -- hc : c 0 • e = 0
         -- Apply trivialization: φ(c 0 • e) = c 0 * φ(e) = c 0 * 1 = c 0
         -- And φ(0) = 0, so c 0 = 0
         have h1 : φ (c 0 • e) = c 0 * φ e := hφ (c 0) e
         have h2 : φ e = 1 := φ.apply_symm_apply 1
         rw [h2, mul_one] at h1
         have h3 : φ (c 0 • e) = 0 := by rw [hc]; exact φ.map_zero
         have h4 : c 0 = 0 := by rw [h1] at h3; exact h3
         exact ⟨finZeroElim, fun i => by fin_cases i; simp [h4]⟩⟩⟩

/-!
## Tensor Products and Duality

Operations on line bundles corresponding to divisor arithmetic.
-/

/-!
## Tensor Products and Duality

Operations on line bundles corresponding to divisor arithmetic.

**Note**: The full tensor product L_D ⊗_O L_E and dual L* constructions require
the O(U)-module tensor product L_D(U) ⊗_{O(U)} L_E(U), which is more complex
than the ℂ-tensor product. For curves, these give line bundles:
- O(D) ⊗_O O(E) ≅ O(D + E)
- O(D)* = Hom_O(O(D), O) ≅ O(-D)

These constructions are defined in a more abstract setting where we track
divisors and their arithmetic, leaving the explicit O-module tensor for
further development.
-/

end RiemannSurfaces.Algebraic.Cohomology
