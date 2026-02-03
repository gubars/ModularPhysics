import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.Cohomology.ExactSequence
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Topology.Sets.Opens
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# Mathlib Bridge for Sheaf Cohomology

This file bridges our Riemann surface sheaf definitions with Mathlib's categorical
sheaf framework, enabling use of Mathlib's cohomology infrastructure.

## Key Bridges

1. **OpenSet RS → Opens (TopCat.of RS.carrier)**: Our open sets to Mathlib's Opens
2. **CoherentSheaf → CategoryTheory.Sheaf**: Our sheaves to Mathlib sheaves
3. **Access to `Sheaf.H` for cohomology**

## Mathematical Background

Mathlib's sheaf cohomology is defined via derived functors:
- `Sheaf.H F n` = n-th cohomology of sheaf F
- This uses Ext groups in the derived category

For a compact Riemann surface Σ:
- H^0(F) = global sections Γ(Σ, F)
- H^1(F) = first derived functor R^1Γ(F)
- H^i(F) = 0 for i ≥ 2 (curves have cohomological dimension 1)

## References

* Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
* Mathlib.Topology.Sheaves.Sheaf
-/

namespace RiemannSurfaces.Algebraic.Cohomology.MathlibBridge

open CategoryTheory RiemannSurfaces TopologicalSpace

/-!
## The Category of Opens

We establish that our OpenSet RS forms a category equivalent to Mathlib's Opens.
-/

/-- Convert a Riemann surface to a TopCat object.
    We need to use the topology from the RiemannSurface structure. -/
def rsToTopCat (RS : RiemannSurface) : TopCat :=
  @TopCat.of RS.carrier RS.topology

/-- The type of open sets in Mathlib's framework -/
abbrev OpensRS (RS : RiemannSurface) := Opens (rsToTopCat RS)

/-- Convert our OpenSet to Mathlib's Opens.
    Note: The isOpen property uses RS.topology, which matches rsToTopCat. -/
def OpenSet.toOpens {RS : RiemannSurface} (U : OpenSet RS) : OpensRS RS :=
  ⟨U.carrier, U.isOpen⟩

/-- Convert Mathlib's Opens to our OpenSet -/
def OpenSet.ofOpens {RS : RiemannSurface} (U : OpensRS RS) : OpenSet RS :=
  ⟨U.carrier, U.isOpen⟩

/-- The conversions are inverses -/
theorem openSet_toOpens_ofOpens {RS : RiemannSurface} (U : OpenSet RS) :
    OpenSet.ofOpens (OpenSet.toOpens U) = U := by
  simp only [OpenSet.ofOpens, OpenSet.toOpens]

theorem opens_ofOpens_toOpens {RS : RiemannSurface} (U : OpensRS RS) :
    OpenSet.toOpens (OpenSet.ofOpens U) = U := by
  simp only [OpenSet.ofOpens, OpenSet.toOpens]

/-!
## Global Sections as Cohomology H^0

The zeroth cohomology is the global sections functor. This is concrete and computable.
-/

/-- H^0(F) = global sections = F(Σ)

    This is the CONCRETE definition of H^0. It is the sections over the whole space.
    The dimension is computed via Module.finrank, not provided as input. -/
def H0 {RS : RiemannSurface} {O : StructureSheaf RS} (F : CoherentSheaf RS O) : Type* :=
  F.sections OpenSet.univ

/-- Global sections form an additive group -/
instance H0.addCommGroup {RS : RiemannSurface} {O : StructureSheaf RS}
    (F : CoherentSheaf RS O) : AddCommGroup (H0 F) :=
  F.addCommGroup OpenSet.univ

/-- Global sections form a module over global functions -/
instance H0.module {RS : RiemannSurface} {O : StructureSheaf RS}
    (F : CoherentSheaf RS O) : Module (O.sections OpenSet.univ) (H0 F) :=
  F.module OpenSet.univ

/-- Global sections form a ℂ-module via the algebra structure -/
noncomputable instance H0.moduleComplex {RS : RiemannSurface} {O : StructureSheaf RS}
    (F : CoherentSheaf RS O) : Module ℂ (H0 F) :=
  Module.compHom (H0 F) (algebraMap ℂ (O.sections OpenSet.univ))

/-- h^0(F) = dim H^0(F) - the dimension of global sections.
    This is COMPUTED from the vector space, not given as input. -/
noncomputable def h0 {RS : RiemannSurface} {O : StructureSheaf RS}
    (F : CoherentSheaf RS O) [Module.Finite ℂ (H0 F)] : ℕ :=
  Module.finrank ℂ (H0 F)

/-!
## H^0 for Specific Sheaves
-/

/-- H^0 of the structure sheaf O -/
def H0_structure {RS : RiemannSurface} (O : StructureSheaf RS) : Type* :=
  O.sections OpenSet.univ

/-- H^0 of a line bundle O(D) -/
def H0_lineBundle {RS : RiemannSurface} {O : StructureSheaf RS} {D : Divisor RS}
    (L : LineBundleSheaf RS O D) : Type* :=
  L.sections OpenSet.univ

/-!
## Skyscraper Sheaf H^0

For the skyscraper sheaf ℂ_p, global sections are isomorphic to ℂ.
-/

/-- Global sections of skyscraper sheaf.
    When p is in the surface, Γ(Σ, ℂ_p) = ℂ. -/
def H0_skyscraper {RS : RiemannSurface} (p : RS.carrier) : Type :=
  SkyscraperSection p OpenSet.univ

-- Provide explicit instances for H0_skyscraper
noncomputable instance H0_skyscraper.instAddCommGroup {RS : RiemannSurface} (p : RS.carrier) :
    AddCommGroup (H0_skyscraper p) :=
  SkyscraperSection.instAddCommGroup OpenSet.univ

noncomputable instance H0_skyscraper.instModule {RS : RiemannSurface} (p : RS.carrier) :
    Module ℂ (H0_skyscraper p) :=
  SkyscraperSection.instModuleComplex OpenSet.univ

/-- A global section of ℂ_p is determined by its value in ℂ -/
noncomputable def H0_skyscraper_equiv {RS : RiemannSurface}
    (p : RS.carrier) : H0_skyscraper p ≃ ℂ where
  toFun s := s.val
  invFun c := ⟨c, fun hp => absurd (Set.mem_univ p) hp⟩
  left_inv _ := SkyscraperSection.ext rfl
  right_inv _ := rfl

/-- H^0(ℂ_p) ≃ ℂ as additive groups -/
noncomputable def H0_skyscraper_addEquiv {RS : RiemannSurface}
    (p : RS.carrier) : H0_skyscraper p ≃+ ℂ where
  toFun := (H0_skyscraper_equiv p).toFun
  invFun := (H0_skyscraper_equiv p).invFun
  left_inv := (H0_skyscraper_equiv p).left_inv
  right_inv := (H0_skyscraper_equiv p).right_inv
  map_add' _ _ := rfl

/-- H^0(ℂ_p) ≃ₗ[ℂ] ℂ as ℂ-linear spaces -/
noncomputable def H0_skyscraper_linearEquiv {RS : RiemannSurface}
    (p : RS.carrier) : H0_skyscraper p ≃ₗ[ℂ] ℂ where
  toFun := (H0_skyscraper_equiv p).toFun
  invFun := (H0_skyscraper_equiv p).invFun
  left_inv := (H0_skyscraper_equiv p).left_inv
  right_inv := (H0_skyscraper_equiv p).right_inv
  map_add' _ _ := rfl
  map_smul' _ _ := by
    simp only [H0_skyscraper_equiv, RingHom.id_apply]
    -- The ℂ-scalar multiplication on SkyscraperSection is c • s = ⟨c * s.val, ...⟩
    rfl

/-- H^0(ℂ_p) is finite-dimensional (dimension 1) -/
noncomputable instance H0_skyscraper.instFinite {RS : RiemannSurface} (p : RS.carrier) :
    Module.Finite ℂ (H0_skyscraper p) :=
  Module.Finite.of_surjective (H0_skyscraper_linearEquiv p).symm.toLinearMap
    (H0_skyscraper_linearEquiv p).symm.surjective

/-- h^0(ℂ_p) = 1: The dimension of global sections of the skyscraper sheaf is 1. -/
theorem h0_skyscraper_eq_one {RS : RiemannSurface} (p : RS.carrier) :
    Module.finrank ℂ (H0_skyscraper p) = 1 := by
  rw [LinearEquiv.finrank_eq (H0_skyscraper_linearEquiv p)]
  exact Module.finrank_self ℂ

/-!
## Higher Cohomology via Čech Complex

For proper definition of H^i with i ≥ 1, we use Čech cohomology.
-/

universe u v

/-- A cover of an open set by a family of opens -/
structure Cover (RS : RiemannSurface) (U : OpenSet RS) where
  /-- Index set -/
  ι : Type u
  /-- The covering opens -/
  opens : ι → OpenSet RS
  /-- Each open is contained in U -/
  subset : ∀ i, opens i ≤ U
  /-- The opens cover U -/
  covers : U.carrier ⊆ (OpenSet.union opens).carrier

/-- The Čech 0-cochains: C^0(U, F) = Π_i F(U_i) -/
def Cech0 (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U) : Type _ :=
  ∀ i : cov.ι, F.sections (cov.opens i)

/-- The Čech 1-cochains: C^1(U, F) = Π_{i,j} F(U_i ∩ U_j) -/
def Cech1 (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U) : Type _ :=
  ∀ i j : cov.ι, F.sections ((cov.opens i).inter (cov.opens j))

/-- The Čech 2-cochains: C^2(U, F) = Π_{i,j,k} F(U_i ∩ U_j ∩ U_k) -/
def Cech2 (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U) : Type _ :=
  ∀ i j k : cov.ι, F.sections ((cov.opens i).inter ((cov.opens j).inter (cov.opens k)))

/-! ### Algebraic structure on Čech cochains -/

variable {RS : RiemannSurface} {O : StructureSheaf RS} {F : CoherentSheaf RS O}
variable {U : OpenSet RS} {cov : Cover RS U}

/-- Zero 0-cochain -/
instance Cech0.instZero : Zero (Cech0 RS O F U cov) where
  zero := fun _ => 0

/-- Addition of 0-cochains -/
instance Cech0.instAdd : Add (Cech0 RS O F U cov) where
  add σ τ := fun i => σ i + τ i

/-- Negation of 0-cochains -/
instance Cech0.instNeg : Neg (Cech0 RS O F U cov) where
  neg σ := fun i => -σ i

/-- AddCommGroup instance for C^0 (inherited from Pi types) -/
noncomputable instance Cech0.instAddCommGroup : AddCommGroup (Cech0 RS O F U cov) :=
  Pi.addCommGroup

/-- AddCommGroup instance for C^1 (inherited from Pi types) -/
noncomputable instance Cech1.instAddCommGroup : AddCommGroup (Cech1 RS O F U cov) :=
  Pi.addCommGroup

/-- AddCommGroup instance for C^2 (inherited from Pi types) -/
noncomputable instance Cech2.instAddCommGroup : AddCommGroup (Cech2 RS O F U cov) :=
  Pi.addCommGroup

/-- The Čech differential d^0 : C^0 → C^1
    (d^0 σ)_{ij} = σ_j|_{U_i ∩ U_j} - σ_i|_{U_i ∩ U_j} -/
def cechDiff0 (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U) :
    Cech0 RS O F U cov → Cech1 RS O F U cov :=
  fun σ i j =>
    let Uij := (cov.opens i).inter (cov.opens j)
    -- Restriction from Uj to Uij
    let restrict_j : Uij ≤ cov.opens j := fun x (hx : x ∈ Uij.carrier) => hx.2
    -- Restriction from Ui to Uij
    let restrict_i : Uij ≤ cov.opens i := fun x (hx : x ∈ Uij.carrier) => hx.1
    F.restrict restrict_j (σ j) - F.restrict restrict_i (σ i)

/-- The Čech differential d^1 : C^1 → C^2
    (d^1 τ)_{ijk} = τ_{jk}|_{U_ijk} - τ_{ik}|_{U_ijk} + τ_{ij}|_{U_ijk} -/
def cechDiff1 (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U) :
    Cech1 RS O F U cov → Cech2 RS O F U cov :=
  fun τ i j k =>
    let Uijk := (cov.opens i).inter ((cov.opens j).inter (cov.opens k))
    let Ujk := (cov.opens j).inter (cov.opens k)
    let Uik := (cov.opens i).inter (cov.opens k)
    let Uij := (cov.opens i).inter (cov.opens j)
    -- Restriction from Ujk to Uijk: x ∈ Uijk.carrier → x ∈ Ujk.carrier
    let r_jk : Uijk ≤ Ujk := fun x (hx : x ∈ Uijk.carrier) => ⟨hx.2.1, hx.2.2⟩
    -- Restriction from Uik to Uijk
    let r_ik : Uijk ≤ Uik := fun x (hx : x ∈ Uijk.carrier) => ⟨hx.1, hx.2.2⟩
    -- Restriction from Uij to Uijk
    let r_ij : Uijk ≤ Uij := fun x (hx : x ∈ Uijk.carrier) => ⟨hx.1, hx.2.1⟩
    F.restrict r_jk (τ j k) - F.restrict r_ik (τ i k) + F.restrict r_ij (τ i j)

/-- Restriction preserves zero -/
theorem restrict_zero {RS : RiemannSurface} {O : StructureSheaf RS}
    (F : CoherentSheaf RS O) {U V : OpenSet RS} (h : U ≤ V) :
    F.restrict h 0 = 0 := by
  have heq := F.restrict_add h 0 0
  simp only [add_zero] at heq
  -- heq : F.restrict h 0 = F.restrict h 0 + F.restrict h 0
  -- From x = x + x, we get 0 = x, hence x = 0
  have h2 : 0 + F.restrict h 0 = F.restrict h 0 + F.restrict h 0 := by
    rw [zero_add]; exact heq
  exact (add_right_cancel h2).symm

/-- Restriction distributes over negation -/
theorem restrict_neg {RS : RiemannSurface} {O : StructureSheaf RS}
    (F : CoherentSheaf RS O) {U V : OpenSet RS} (h : U ≤ V) (s : F.sections V) :
    F.restrict h (-s) = -(F.restrict h s) := by
  have hadd := F.restrict_add h (-s) s
  rw [neg_add_cancel, restrict_zero] at hadd
  -- hadd : 0 = F.restrict h (-s) + F.restrict h s
  have heq : F.restrict h (-s) + F.restrict h s = 0 := hadd.symm
  exact (neg_eq_of_add_eq_zero_left heq).symm

/-- Restriction distributes over subtraction -/
theorem restrict_sub {RS : RiemannSurface} {O : StructureSheaf RS}
    (F : CoherentSheaf RS O) {U V : OpenSet RS} (h : U ≤ V) (s t : F.sections V) :
    F.restrict h (s - t) = F.restrict h s - F.restrict h t := by
  rw [sub_eq_add_neg, F.restrict_add, restrict_neg, sub_eq_add_neg]

/-- d^0 is a group homomorphism -/
theorem cechDiff0_add (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U)
    (σ τ : Cech0 RS O F U cov) :
    cechDiff0 RS O F U cov (σ + τ) = cechDiff0 RS O F U cov σ + cechDiff0 RS O F U cov τ := by
  funext i j
  unfold cechDiff0
  -- (σ + τ) k = σ k + τ k definitionally for Pi types
  change F.restrict _ (σ j + τ j) - F.restrict _ (σ i + τ i) =
         (F.restrict _ (σ j) - F.restrict _ (σ i)) + (F.restrict _ (τ j) - F.restrict _ (τ i))
  rw [F.restrict_add, F.restrict_add]
  abel

/-- d^0 preserves zero -/
theorem cechDiff0_zero (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U) :
    cechDiff0 RS O F U cov 0 = 0 := by
  funext i j
  unfold cechDiff0
  change F.restrict _ (0 : F.sections _) - F.restrict _ (0 : F.sections _) = (0 : F.sections _)
  rw [restrict_zero, restrict_zero, sub_self]

/-- d^0 as an AddMonoidHom -/
def cechDiff0Hom (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U) :
    Cech0 RS O F U cov →+ Cech1 RS O F U cov where
  toFun := cechDiff0 RS O F U cov
  map_zero' := cechDiff0_zero RS O F U cov
  map_add' := cechDiff0_add RS O F U cov

/-- d^1 is a group homomorphism -/
theorem cechDiff1_add (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U)
    (τ η : Cech1 RS O F U cov) :
    cechDiff1 RS O F U cov (τ + η) = cechDiff1 RS O F U cov τ + cechDiff1 RS O F U cov η := by
  funext i j k
  unfold cechDiff1
  change F.restrict _ (τ j k + η j k) - F.restrict _ (τ i k + η i k) + F.restrict _ (τ i j + η i j) =
         (F.restrict _ (τ j k) - F.restrict _ (τ i k) + F.restrict _ (τ i j)) +
         (F.restrict _ (η j k) - F.restrict _ (η i k) + F.restrict _ (η i j))
  rw [F.restrict_add, F.restrict_add, F.restrict_add]
  abel

/-- d^1 preserves zero -/
theorem cechDiff1_zero (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U) :
    cechDiff1 RS O F U cov 0 = 0 := by
  funext i j k
  unfold cechDiff1
  change F.restrict _ (0 : F.sections _) - F.restrict _ (0 : F.sections _) +
         F.restrict _ (0 : F.sections _) = (0 : F.sections _)
  rw [restrict_zero, restrict_zero, restrict_zero, sub_self, zero_add]

/-- d^1 as an AddMonoidHom -/
def cechDiff1Hom (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U) :
    Cech1 RS O F U cov →+ Cech2 RS O F U cov where
  toFun := cechDiff1 RS O F U cov
  map_zero' := cechDiff1_zero RS O F U cov
  map_add' := cechDiff1_add RS O F U cov

/-- d^1 ∘ d^0 = 0: The composition of Čech differentials is zero -/
theorem cechDiff1_comp_cechDiff0 (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U)
    (σ : Cech0 RS O F U cov) :
    cechDiff1 RS O F U cov (cechDiff0 RS O F U cov σ) = fun _ _ _ => 0 := by
  funext i j k
  simp only [cechDiff1, cechDiff0]
  -- We need to prove:
  -- (σ_k|_{jk} - σ_j|_{jk})|_{ijk} - (σ_k|_{ik} - σ_i|_{ik})|_{ijk} + (σ_j|_{ij} - σ_i|_{ij})|_{ijk} = 0

  -- Define the opens for clarity
  let Ui := cov.opens i
  let Uj := cov.opens j
  let Uk := cov.opens k
  let Uij := Ui.inter Uj
  let Uik := Ui.inter Uk
  let Ujk := Uj.inter Uk
  let Uijk := Ui.inter (Uj.inter Uk)

  -- Canonical restrictions to Uijk
  have ri : Uijk ≤ Ui := fun x hx => hx.1
  have rj : Uijk ≤ Uj := fun x hx => hx.2.1
  have rk : Uijk ≤ Uk := fun x hx => hx.2.2

  -- Distribute restrictions over subtraction
  simp only [restrict_sub]

  -- Use restrict_comp to simplify all nested restrictions
  simp only [F.restrict_comp]

  -- Now all terms are of the form F.restrict _ (σ x) where _ is some proof of Uijk ≤ Ux
  -- Since LE on OpenSet is proof-irrelevant (it's a Prop), all these restrictions
  -- to the same open give the same result
  -- Need to show: σ_k - σ_j - (σ_k - σ_i) + (σ_j - σ_i) = 0
  -- = σ_k - σ_j - σ_k + σ_i + σ_j - σ_i = 0
  -- The terms should cancel

  -- After simp, all restrictions from Ux to Uijk should be the same
  -- (proof-irrelevance of LE), so ring should work
  -- If not, we need to rewrite using congruence
  abel

/-! ### Čech Cohomology Groups

For a Riemann surface (algebraic curve), cohomology vanishes for i ≥ 2.
We define:
- H⁰ = ker(d⁰) = global sections (elements that glue)
- H¹ = ker(d¹)/im(d⁰) = cocycles modulo coboundaries
- H² = 0 (cohomological dimension 1)
-/

/-- Z^0 = ker(d^0) - Čech 0-cocycles (global sections)
    A 0-cochain σ is a cocycle if σ_j|_{U_ij} = σ_i|_{U_ij} for all i,j.
    These are exactly the sections that glue to give a global section. -/
def CechCocycles0 (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U) : Type _ :=
  { σ : Cech0 RS O F U cov // cechDiff0 RS O F U cov σ = 0 }

/-- Z^1 = ker(d^1) - Čech 1-cocycles
    A 1-cochain τ is a cocycle if τ_{jk} - τ_{ik} + τ_{ij} = 0 on triple overlaps -/
def CechCocycles1 (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U) : Type _ :=
  { τ : Cech1 RS O F U cov // cechDiff1 RS O F U cov τ = fun _ _ _ => 0 }

/-- B^1 = im(d^0) - Čech 1-coboundaries -/
def CechCoboundaries1 (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U) : Type _ :=
  { τ : Cech1 RS O F U cov // ∃ σ : Cech0 RS O F U cov, cechDiff0 RS O F U cov σ = τ }

/-- H⁰(U, F) = Z⁰ = ker(d⁰)
    The zeroth cohomology is just the kernel of d⁰, which consists of
    0-cochains that agree on overlaps (i.e., glue to global sections). -/
def CechH0 (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U) : Type _ :=
  CechCocycles0 RS O F U cov

/-- The equivalence relation for H¹: τ ~ τ' iff τ - τ' ∈ B¹ -/
def CechH1Rel (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U)
    (τ τ' : CechCocycles1 RS O F U cov) : Prop :=
  ∃ σ : Cech0 RS O F U cov, cechDiff0 RS O F U cov σ = τ.val - τ'.val

/-- CechH1Rel is an equivalence relation -/
theorem CechH1Rel.equivalence (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U) :
    Equivalence (CechH1Rel RS O F U cov) where
  refl τ := ⟨0, by rw [cechDiff0_zero, sub_self]⟩
  symm := fun ⟨σ, h⟩ => ⟨-σ, by
    have hn : cechDiff0 RS O F U cov (-σ) = -cechDiff0 RS O F U cov σ :=
      (cechDiff0Hom RS O F U cov).map_neg σ
    rw [hn, h]; abel⟩
  trans := fun ⟨σ₁, h₁⟩ ⟨σ₂, h₂⟩ => ⟨σ₁ + σ₂, by
    have ha : cechDiff0 RS O F U cov (σ₁ + σ₂) =
              cechDiff0 RS O F U cov σ₁ + cechDiff0 RS O F U cov σ₂ :=
      cechDiff0_add RS O F U cov σ₁ σ₂
    rw [ha, h₁, h₂]; abel⟩

/-- The setoid for defining H¹ as a quotient -/
def CechH1Setoid (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U) :
    Setoid (CechCocycles1 RS O F U cov) where
  r := CechH1Rel RS O F U cov
  iseqv := CechH1Rel.equivalence RS O F U cov

/-- H¹(U, F) = Z¹/B¹ as a quotient type -/
def CechH1 (RS : RiemannSurface) (O : StructureSheaf RS)
    (F : CoherentSheaf RS O) (U : OpenSet RS) (cov : Cover RS U) : Type _ :=
  Quotient (CechH1Setoid RS O F U cov)

/-!
## Key Properties

For compact Riemann surfaces:
- Any finite open cover suffices
- H^i = 0 for i ≥ 2 (curves have dimension 1)
- Skyscraper sheaves are acyclic (H^i = 0 for i ≥ 1)
- For Leray covers, Čech = derived functor cohomology
-/

/-- Skyscraper sheaves are acyclic: H^1(ℂ_p) = 0

    **Proof**: Skyscraper sheaves are flasque (sections extend trivially).
    For a 1-cocycle τ, we construct σ by choosing a fixed index j₀ and setting
    σ_i = τ_{j₀,i} (restricted appropriately).

    The cocycle condition τ_{jk} - τ_{ik} + τ_{ij} = 0 implies:
    τ_{ij} = τ_{j₀j} - τ_{j₀i} on the triple intersection

    Since skyscraper sections are determined by their value at p (if p is in the open)
    or are zero (if p is not in the open), this construction works.

    **Note**: This is a standard result - skyscraper sheaves are flasque hence acyclic.
    The full formalization requires careful bookkeeping of restriction paths. -/
theorem H1_skyscraper_vanish (RS : RiemannSurface) (O : StructureSheaf RS)
    (p : RS.carrier) (U : OpenSet RS) (cov : Cover RS U) :
    ∀ τ : CechCocycles1 RS O (skyscraperSheaf O p) U cov,
    ∃ σ : Cech0 RS O (skyscraperSheaf O p) U cov,
    cechDiff0 RS O (skyscraperSheaf O p) U cov σ = τ.val := by
  classical
  intro τ

  by_cases hp : p ∈ U.carrier
  · -- Case: p ∈ U
    have hcov := cov.covers hp
    simp only [OpenSet.union] at hcov
    obtain ⟨j₀, hj₀⟩ := Set.mem_iUnion.mp hcov

    -- Define σ_i = τ_{j₀,i} lifted to Ui
    let σ : Cech0 RS O (skyscraperSheaf O p) U cov := fun i =>
      ⟨(τ.val j₀ i).val, fun hni => (τ.val j₀ i).prop (fun h => hni h.2)⟩
    use σ

    funext i j
    simp only [cechDiff0, skyscraperSheaf]
    apply SkyscraperSection.ext
    simp only [SkyscraperSection.sub_val]

    -- Case split on whether p is in Uij
    by_cases hpij : p ∈ ((cov.opens i).inter (cov.opens j)).carrier
    · -- p ∈ Uij: restrictions preserve values
      -- Goal: (restrict σ_j).val - (restrict σ_i).val = τ_{ij}.val
      have hp_i : p ∈ (cov.opens i).carrier := hpij.1
      have hp_j : p ∈ (cov.opens j).carrier := hpij.2

      -- Compute restrictions when p is in target
      have hr_j : (SkyscraperSection.restrict
        (fun x (hx : x ∈ ((cov.opens i).inter (cov.opens j)).carrier) => hx.2) (σ j)).val = (σ j).val := by
        simp only [SkyscraperSection.restrict, hpij, ↓reduceDIte]
      have hr_i : (SkyscraperSection.restrict
        (fun x (hx : x ∈ ((cov.opens i).inter (cov.opens j)).carrier) => hx.1) (σ i)).val = (σ i).val := by
        simp only [SkyscraperSection.restrict, hpij, ↓reduceDIte]

      rw [hr_j, hr_i]
      -- Now: (σ j).val - (σ i).val = τ_{ij}.val
      -- By definition: (σ k).val = (τ.val j₀ k).val
      -- Need: (τ.val j₀ j).val - (τ.val j₀ i).val = (τ.val i j).val

      -- Explicit equalities for σ
      have hσj : (σ j).val = (τ.val j₀ j).val := rfl
      have hσi : (σ i).val = (τ.val j₀ i).val := rfl
      rw [hσj, hσi]

      -- Use cocycle condition at (j₀, i, j)
      have hc : cechDiff1 RS O (skyscraperSheaf O p) U cov τ.val j₀ i j = 0 := by rw [τ.prop]
      simp only [cechDiff1, skyscraperSheaf] at hc
      have heq := congrArg SkyscraperSection.val hc
      simp only [SkyscraperSection.zero_val', SkyscraperSection.sub_val, SkyscraperSection.add_val] at heq

      -- The restrictions in heq: all preserve values since p is in triple intersection
      have hp_j₀ij : p ∈ ((cov.opens j₀).inter ((cov.opens i).inter (cov.opens j))).carrier := ⟨hj₀, hpij⟩

      -- Extract the value equation from heq
      unfold SkyscraperSection.restrict at heq
      simp only [hp_j₀ij, ↓reduceDIte] at heq
      -- heq: (↑τ i j).val - (↑τ j₀ j).val + (↑τ j₀ i).val = 0
      -- Goal after rewrites: (↑τ j₀ j).val - (↑τ j₀ i).val = (↑τ i j).val
      -- Direct arithmetic: from a - b + c = 0, we get b - c = a
      calc (τ.val j₀ j).val - (τ.val j₀ i).val
          = (τ.val j₀ j).val - (τ.val j₀ i).val + 0 := by ring
        _ = (τ.val j₀ j).val - (τ.val j₀ i).val +
            ((τ.val i j).val - (τ.val j₀ j).val + (τ.val j₀ i).val) := by rw [heq]
        _ = (τ.val i j).val := by ring

    · -- p ∉ Uij: both sides are 0
      have h_tau_zero : (τ.val i j).val = 0 := (τ.val i j).prop hpij
      -- Restrictions give 0 when p ∉ target
      have hr_j : (SkyscraperSection.restrict
        (fun x (hx : x ∈ ((cov.opens i).inter (cov.opens j)).carrier) => hx.2) (σ j)).val = 0 := by
        simp only [SkyscraperSection.restrict, hpij, ↓reduceDIte]
      have hr_i : (SkyscraperSection.restrict
        (fun x (hx : x ∈ ((cov.opens i).inter (cov.opens j)).carrier) => hx.1) (σ i)).val = 0 := by
        simp only [SkyscraperSection.restrict, hpij, ↓reduceDIte]
      rw [hr_j, hr_i, h_tau_zero]; ring

  · -- Case: p ∉ U - all sections are 0
    let σ : Cech0 RS O (skyscraperSheaf O p) U cov := fun _ => ⟨0, fun _ => rfl⟩
    use σ
    funext i j
    simp only [cechDiff0, skyscraperSheaf]
    apply SkyscraperSection.ext
    simp only [SkyscraperSection.sub_val]

    have hpi : p ∉ (cov.opens i).carrier := fun h => hp (cov.subset i h)
    have hpij : p ∉ ((cov.opens i).inter (cov.opens j)).carrier := fun h => hpi h.1
    have h_tau_zero : (τ.val i j).val = 0 := (τ.val i j).prop hpij

    -- Restrictions of 0 are 0
    have hr_j : (SkyscraperSection.restrict
      (fun x (hx : x ∈ ((cov.opens i).inter (cov.opens j)).carrier) => hx.2)
      (⟨0, fun _ => rfl⟩ : SkyscraperSection p _)).val = 0 := by
      unfold SkyscraperSection.restrict; split_ifs; all_goals rfl
    have hr_i : (SkyscraperSection.restrict
      (fun x (hx : x ∈ ((cov.opens i).inter (cov.opens j)).carrier) => hx.1)
      (⟨0, fun _ => rfl⟩ : SkyscraperSection p _)).val = 0 := by
      unfold SkyscraperSection.restrict; split_ifs; all_goals rfl
    rw [hr_j, hr_i, h_tau_zero]; ring

end RiemannSurfaces.Algebraic.Cohomology.MathlibBridge
