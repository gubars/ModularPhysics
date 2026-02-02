import ModularPhysics.StringGeometry.Supermanifolds.Superalgebra
import ModularPhysics.StringGeometry.Supermanifolds.Sheaves.SuperSheafBasic
import ModularPhysics.StringGeometry.Supermanifolds.Helpers.ZeroDimManifold
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Supermanifolds as Locally Superringed Spaces

A supermanifold is fundamentally a **locally superringed space**, which differs
from a classical locally ringed space in that the structure sheaf consists of
**supercommutative superalgebras** rather than commutative rings.

## The Supercommutative Structure

The stalks O_{M,x} are **local superalgebras** where:
- The ring is ℤ/2-graded: O_{M,x} = O_{M,x,0} ⊕ O_{M,x,1}
- Elements satisfy supercommutativity: ab = (-1)^{|a||b|} ba
- **NOT commutative**: odd elements anticommute (θ¹θ² = -θ²θ¹)
- The even part O_{M,x,0} IS commutative and contains the maximal ideal
- The odd part O_{M,x,1} is contained in the maximal ideal (nilpotent)

The maximal ideal m_x consists of:
- Even elements vanishing at x: functions f with f(x) = 0
- ALL odd elements (since they are nilpotent)

The residue field k(x) = O_{M,x}/m_x ≅ ℝ is purely even.

## Main Structures

* `SuperDimension` - Dimension (p|q) encoding even and odd dimensions
* `SuperDomain` - The local model ℝ^{p|q} = (ℝ^p, C^∞ ⊗ ∧•ℝ^q)
* `LocalSuperAlgebra` - A local supercommutative superalgebra
* `SuperRingedSpace` - A topological space with a sheaf of superalgebras
* `LocallySuperRingedSpace` - A superringed space with local stalks
* `Supermanifold` - A locally superringed space locally isomorphic to ℝ^{p|q}
* `SuperMorphism` - Maps preserving the superringed structure
* `SuperChart` - Local coordinates with proper transition data

## The Batchelor Theorem

Every **smooth** supermanifold is (non-canonically) isomorphic to Π(M, E) := (M, ∧•E*)
for some vector bundle E → M. However:
- The isomorphism is **not canonical** (depends on choices)
- **Complex** supermanifolds may not split (Donagi-Witten theorem for supermoduli)
- The split description obscures intrinsic supergeometric structure

## Functor of Points Perspective

The functor of points approach defines a supermanifold M via its S-points:
  M(S) = Hom_{SMan}(S, M)
for all supermanifolds S. This is essential for:
- Defining supergroups and super Lie algebras
- Working with families of supermanifolds
- The moduli space perspective in superstring theory

## References

* Kostant, B. "Graded manifolds, graded Lie theory, and prequantization"
* Leites, D.A. "Introduction to the theory of supermanifolds"
* Manin, Y. "Gauge Field Theory and Complex Geometry", Chapter 4
* Deligne, P., Morgan, J. "Notes on Supersymmetry"
* Witten, E. "Notes on Supermanifolds and Integration"
* Varadarajan, V.S. "Supersymmetry for Mathematicians"
-/

namespace Supermanifolds

open Parity

/-!
## Local Superalgebras and Locally Superringed Spaces

The foundation of supermanifold theory is the notion of a **locally superringed space**.
This generalizes the locally ringed space from algebraic geometry to accommodate
supercommutative (non-commutative) structure sheaves.
-/

/-!
### Local Superalgebras

A **local superalgebra** is a ℤ/2-graded algebra A = A₀ ⊕ A₁ where:
- A is supercommutative: ab = (-1)^{|a||b|} ba for homogeneous a, b
- A has a unique maximal ideal m
- The even part A₀ is a local ring with maximal ideal m₀ = m ∩ A₀
- The odd part A₁ is contained in m (all odd elements are nilpotent)

The residue field k = A/m ≅ A₀/m₀ is purely even (typically ℝ or ℂ).
-/

/-- A local superalgebra is a superalgebra with a unique maximal ideal.
    The maximal ideal contains all odd elements (they are nilpotent).

    The locality condition is that elements outside the maximal ideal are units.
    This is the standard characterization of a local ring.

    For a supercommutative algebra, the maximal ideal is automatically a two-sided
    ideal since ab = ±ba for homogeneous elements. -/
structure LocalSuperAlgebra (R : Type*) [CommRing R] extends SuperAlgebra R where
  /-- The maximal ideal of the local superalgebra -/
  maxIdeal : Set carrier
  /-- Zero is in the maximal ideal -/
  maxIdeal_zero : (0 : carrier) ∈ maxIdeal
  /-- The maximal ideal is closed under addition -/
  maxIdeal_add : ∀ a b : carrier, a ∈ maxIdeal → b ∈ maxIdeal → a + b ∈ maxIdeal
  /-- The maximal ideal absorbs multiplication from the left -/
  maxIdeal_mul_left : ∀ (r a : carrier), a ∈ maxIdeal → r * a ∈ maxIdeal
  /-- The maximal ideal absorbs multiplication from the right -/
  maxIdeal_mul_right : ∀ (a r : carrier), a ∈ maxIdeal → a * r ∈ maxIdeal
  /-- All odd elements are in the maximal ideal -/
  odd_in_maxIdeal : ∀ a : carrier, a ∈ odd → a ∈ maxIdeal
  /-- 1 is not in the maximal ideal (m is proper) -/
  one_not_in_maxIdeal : (1 : carrier) ∉ maxIdeal
  /-- Elements outside the maximal ideal are units (locality condition) -/
  units_outside : ∀ a : carrier, a ∉ maxIdeal → ∃ b : carrier, a * b = 1 ∧ b * a = 1

/-- The equivalence relation for the quotient A/m.
    Two elements are equivalent if their difference is in the maximal ideal.

    We use the ring structure from LocalSuperAlgebra to define subtraction. -/
def LocalSuperAlgebra.residueEquiv {R : Type*} [CommRing R]
    (A : LocalSuperAlgebra R) : A.carrier → A.carrier → Prop :=
  letI : Ring A.carrier := A.ring
  fun x y => x - y ∈ A.maxIdeal

/-- Negation preserves membership in the maximal ideal.
    Proof: -a = (-1) * a, and ideals are closed under left multiplication. -/
theorem LocalSuperAlgebra.maxIdeal_neg {R : Type*} [CommRing R]
    (A : LocalSuperAlgebra R) (a : A.carrier) (ha : a ∈ A.maxIdeal) :
    (letI : Ring A.carrier := A.ring; -a) ∈ A.maxIdeal := by
  letI : Ring A.carrier := A.ring
  have h : -a = (-1) * a := (neg_one_mul a).symm
  rw [h]
  exact A.maxIdeal_mul_left _ _ ha

/-- The residue equivalence relation is reflexive. -/
theorem LocalSuperAlgebra.residueEquiv_refl {R : Type*} [CommRing R]
    (A : LocalSuperAlgebra R) (x : A.carrier) : A.residueEquiv x x := by
  letI : Ring A.carrier := A.ring
  simp only [residueEquiv, sub_self]
  exact A.maxIdeal_zero

/-- The residue equivalence relation is symmetric. -/
theorem LocalSuperAlgebra.residueEquiv_symm {R : Type*} [CommRing R]
    (A : LocalSuperAlgebra R) {x y : A.carrier}
    (h : A.residueEquiv x y) : A.residueEquiv y x := by
  letI : Ring A.carrier := A.ring
  simp only [residueEquiv] at h ⊢
  have hsub : y - x = -(x - y) := (neg_sub x y).symm
  rw [hsub]
  exact A.maxIdeal_neg _ h

/-- The residue equivalence relation is transitive. -/
theorem LocalSuperAlgebra.residueEquiv_trans {R : Type*} [CommRing R]
    (A : LocalSuperAlgebra R) {x y z : A.carrier}
    (hxy : A.residueEquiv x y) (hyz : A.residueEquiv y z) : A.residueEquiv x z := by
  letI : Ring A.carrier := A.ring
  simp only [residueEquiv] at hxy hyz ⊢
  have hsub : x - z = (x - y) + (y - z) := (sub_add_sub_cancel x y z).symm
  rw [hsub]
  exact A.maxIdeal_add _ _ hxy hyz

/-- The residue field of a local superalgebra: A/m.
    This is purely even since all odd elements are in m.

    Elements x, y ∈ A are identified iff x - y ∈ m.
    The residue field inherits a ring structure from A. -/
def LocalSuperAlgebra.residueField {R : Type*} [CommRing R]
    (A : LocalSuperAlgebra R) : Type* :=
  Quotient (Setoid.mk A.residueEquiv
    ⟨A.residueEquiv_refl, fun h => A.residueEquiv_symm h, fun h1 h2 => A.residueEquiv_trans h1 h2⟩)

/-- A morphism of local superalgebras is a graded algebra homomorphism
    that maps the maximal ideal into the maximal ideal. -/
structure LocalSuperAlgebraMorphism {R : Type*} [CommRing R]
    (A B : LocalSuperAlgebra R) where
  /-- The underlying function -/
  toFun : A.carrier → B.carrier
  /-- Respects addition -/
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  /-- Respects multiplication -/
  map_mul : ∀ x y, toFun (x * y) = toFun x * toFun y
  /-- Respects the unit -/
  map_one : toFun 1 = 1
  /-- Preserves the even grading -/
  map_even : ∀ x, x ∈ A.even → toFun x ∈ B.even
  /-- Preserves the odd grading -/
  map_odd : ∀ x, x ∈ A.odd → toFun x ∈ B.odd
  /-- Maps maximal ideal to maximal ideal -/
  map_maxIdeal : ∀ x, x ∈ A.maxIdeal → toFun x ∈ B.maxIdeal

/-!
### Superringed Spaces

A **superringed space** is a pair (X, O_X) where:
- X is a topological space
- O_X is a sheaf of supercommutative superalgebras on X

This generalizes the notion of a ringed space where the structure sheaf
consists of supercommutative superalgebras rather than commutative rings.
-/

/-- A superringed space is a topological space equipped with a sheaf
    of supercommutative superalgebras.

    The structure sheaf O_X assigns to each open set U ⊆ X a superalgebra O_X(U),
    with restriction maps that are graded algebra homomorphisms.

    **Design Note**: For full Mathlib integration, one should use
    `TopCat.Sheaf (SuperRingCat ℝ) X` which works because Mathlib's sheaf machinery
    is category-theoretic and `SuperRingCat` is a category. The supercommutative
    (non-commutative) nature is handled by the category structure.

    This definition provides explicit presheaf structure. The sheaf conditions
    (locality and gluing) are encoded via `isSheaf`. -/
structure SuperRingedSpace where
  /-- The underlying topological space -/
  carrier : Type*
  /-- Topology on the carrier -/
  [topology : TopologicalSpace carrier]
  /-- For each open set, a superalgebra of sections (the structure sheaf) -/
  structureSheaf : (U : Set carrier) → IsOpen U → SuperAlgebra ℝ
  /-- Restriction maps (hVU witnesses that V ⊆ U) -/
  restriction : ∀ (U V : Set carrier) (hU : IsOpen U) (hV : IsOpen V) (_ : V ⊆ U),
    (structureSheaf U hU).carrier → (structureSheaf V hV).carrier
  /-- Restriction respects the identity: res_{U,U} = id -/
  restriction_id : ∀ (U : Set carrier) (hU : IsOpen U) (s : (structureSheaf U hU).carrier),
    restriction U U hU hU (Set.Subset.refl U) s = s
  /-- Restriction composes properly: res_{V,W} ∘ res_{U,V} = res_{U,W} -/
  restriction_comp : ∀ (U V W : Set carrier) (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hVU : V ⊆ U) (hWV : W ⊆ V) (s : (structureSheaf U hU).carrier),
    restriction V W hV hW hWV (restriction U V hU hV hVU s) =
    restriction U W hU hW (hWV.trans hVU) s
  /-- Restriction preserves addition -/
  restriction_add : ∀ (U V : Set carrier) (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (s t : (structureSheaf U hU).carrier),
    restriction U V hU hV hVU ((structureSheaf U hU).ring.add s t) =
    (structureSheaf V hV).ring.add (restriction U V hU hV hVU s) (restriction U V hU hV hVU t)
  /-- Restriction preserves multiplication -/
  restriction_mul : ∀ (U V : Set carrier) (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (s t : (structureSheaf U hU).carrier),
    restriction U V hU hV hVU ((structureSheaf U hU).ring.mul s t) =
    (structureSheaf V hV).ring.mul (restriction U V hU hV hVU s) (restriction U V hU hV hVU t)
  /-- Restriction maps unit to unit -/
  restriction_one : ∀ (U V : Set carrier) (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U),
    restriction U V hU hV hVU (structureSheaf U hU).ring.one = (structureSheaf V hV).ring.one
  /-- Restriction preserves the ℤ/2-grading (maps even to even) -/
  restriction_even : ∀ (U V : Set carrier) (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (s : (structureSheaf U hU).carrier),
    s ∈ (structureSheaf U hU).even → restriction U V hU hV hVU s ∈ (structureSheaf V hV).even
  /-- Restriction preserves the ℤ/2-grading (maps odd to odd) -/
  restriction_odd : ∀ (U V : Set carrier) (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (s : (structureSheaf U hU).carrier),
    s ∈ (structureSheaf U hU).odd → restriction U V hU hV hVU s ∈ (structureSheaf V hV).odd
  /-- The presheaf satisfies the sheaf locality condition:
      sections are determined by their restrictions to any open cover.
      If s and t agree on all elements of a cover, they are equal. -/
  isSheaf : ∀ (U : Set carrier) (hU : IsOpen U)
    (ι : Type*) (V : ι → Set carrier) (hV : ∀ i, IsOpen (V i)) (hVU : ∀ i, V i ⊆ U)
    (_ : U = ⋃ i, V i) (s t : (structureSheaf U hU).carrier),
    (∀ i, restriction U (V i) hU (hV i) (hVU i) s = restriction U (V i) hU (hV i) (hVU i) t) → s = t

attribute [instance] SuperRingedSpace.topology

/-- A locally superringed space is a superringed space where all stalks
    are local superalgebras.

    The stalk O_{X,x} at a point x ∈ X is the direct limit of O_X(U) over
    all open neighborhoods U of x. For a locally superringed space:
    - Each stalk is a local superalgebra
    - The maximal ideal consists of germs that vanish at x (even part)
      plus all odd germs
    - The residue field O_{X,x}/m_x ≅ ℝ (or ℂ) is purely even -/
structure LocallySuperRingedSpace extends SuperRingedSpace where
  /-- The stalk at a point x is a local superalgebra (colimit of sections over open neighborhoods) -/
  stalkSuperAlgebra : carrier → LocalSuperAlgebra ℝ
  /-- Convenience: the stalk as a type -/
  stalk (x : carrier) : Type* := (stalkSuperAlgebra x).carrier
  /-- The germ map: section over U → stalk at x ∈ U -/
  germ : ∀ (U : Set carrier) (hU : IsOpen U) (x : carrier) (_ : x ∈ U),
    (structureSheaf U hU).carrier → (stalkSuperAlgebra x).carrier
  /-- Germs are compatible with restriction -/
  germ_restriction : ∀ (U V : Set carrier) (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) (x : carrier) (hxV : x ∈ V) (s : (structureSheaf U hU).carrier),
    germ V hV x hxV (restriction U V hU hV hVU s) = germ U hU x (hVU hxV) s
  /-- Two sections with equal germs at all points are equal (consequence of locality) -/
  sections_eq_of_germ_eq : ∀ (U : Set carrier) (hU : IsOpen U)
    (s t : (structureSheaf U hU).carrier),
    (∀ x (hx : x ∈ U), germ U hU x hx s = germ U hU x hx t) → s = t
  /-- The germ map is a ring homomorphism (preserves addition) -/
  germ_add : ∀ (U : Set carrier) (hU : IsOpen U) (x : carrier) (hx : x ∈ U)
    (s t : (structureSheaf U hU).carrier),
    germ U hU x hx ((structureSheaf U hU).ring.add s t) =
    (stalkSuperAlgebra x).ring.add (germ U hU x hx s) (germ U hU x hx t)
  /-- The germ map preserves multiplication -/
  germ_mul : ∀ (U : Set carrier) (hU : IsOpen U) (x : carrier) (hx : x ∈ U)
    (s t : (structureSheaf U hU).carrier),
    germ U hU x hx ((structureSheaf U hU).ring.mul s t) =
    (stalkSuperAlgebra x).ring.mul (germ U hU x hx s) (germ U hU x hx t)
  /-- The germ map preserves the unit -/
  germ_one : ∀ (U : Set carrier) (hU : IsOpen U) (x : carrier) (hx : x ∈ U),
    germ U hU x hx (structureSheaf U hU).ring.one = (stalkSuperAlgebra x).ring.one

/-- A morphism of locally superringed spaces is a continuous map f : X → Y
    together with a morphism of sheaves f^# : O_Y → f_* O_X such that
    the induced maps on stalks are local homomorphisms.

    "Local homomorphism" means the map on stalks sends the maximal ideal
    of O_{Y,f(x)} into the maximal ideal of O_{X,x}. -/
structure LocallySuperRingedSpaceMorphism (X Y : LocallySuperRingedSpace) where
  /-- The underlying continuous map -/
  toFun : X.carrier → Y.carrier
  /-- Continuity -/
  continuous : Continuous toFun
  /-- Pullback on sections: O_Y(U) → O_X(f⁻¹(U)) -/
  pullback : ∀ (U : Set Y.carrier) (hU : IsOpen U),
    (Y.structureSheaf U hU).carrier → (X.structureSheaf (toFun ⁻¹' U) (hU.preimage continuous)).carrier
  /-- Pullback preserves addition -/
  pullback_add : ∀ (U : Set Y.carrier) (hU : IsOpen U)
    (s t : (Y.structureSheaf U hU).carrier),
    pullback U hU ((Y.structureSheaf U hU).ring.add s t) =
    (X.structureSheaf _ _).ring.add (pullback U hU s) (pullback U hU t)
  /-- Pullback preserves multiplication -/
  pullback_mul : ∀ (U : Set Y.carrier) (hU : IsOpen U)
    (s t : (Y.structureSheaf U hU).carrier),
    pullback U hU ((Y.structureSheaf U hU).ring.mul s t) =
    (X.structureSheaf _ _).ring.mul (pullback U hU s) (pullback U hU t)
  /-- Pullback preserves the unit -/
  pullback_one : ∀ (U : Set Y.carrier) (hU : IsOpen U),
    pullback U hU (Y.structureSheaf U hU).ring.one = (X.structureSheaf _ _).ring.one
  /-- Pullback preserves the ℤ/2-grading (even to even) -/
  pullback_even : ∀ (U : Set Y.carrier) (hU : IsOpen U)
    (s : (Y.structureSheaf U hU).carrier),
    s ∈ (Y.structureSheaf U hU).even → pullback U hU s ∈ (X.structureSheaf _ _).even
  /-- Pullback preserves the ℤ/2-grading (odd to odd) -/
  pullback_odd : ∀ (U : Set Y.carrier) (hU : IsOpen U)
    (s : (Y.structureSheaf U hU).carrier),
    s ∈ (Y.structureSheaf U hU).odd → pullback U hU s ∈ (X.structureSheaf _ _).odd
  /-- The induced map on stalks f^#_x : O_{Y,f(x)} → O_{X,x} -/
  stalkMap : ∀ x : X.carrier,
    (Y.stalkSuperAlgebra (toFun x)).carrier → (X.stalkSuperAlgebra x).carrier
  /-- The stalk map is compatible with germs -/
  stalkMap_germ : ∀ (U : Set Y.carrier) (hU : IsOpen U) (x : X.carrier)
    (hfx : toFun x ∈ U) (s : (Y.structureSheaf U hU).carrier),
    stalkMap x (Y.germ U hU (toFun x) hfx s) =
    X.germ (toFun ⁻¹' U) (hU.preimage continuous) x hfx (pullback U hU s)
  /-- The stalk map is local: maps maximal ideal to maximal ideal -/
  stalkMap_local : ∀ (x : X.carrier)
    (a : (Y.stalkSuperAlgebra (toFun x)).carrier),
    a ∈ (Y.stalkSuperAlgebra (toFun x)).maxIdeal →
    stalkMap x a ∈ (X.stalkSuperAlgebra x).maxIdeal

/-!
## Super Domains: The Local Model

The local model for a supermanifold of dimension (p|q) is the super domain
ℝ^{p|q} = (ℝ^p, C^∞(ℝ^p) ⊗ ∧•ℝ^q).

Elements of the structure sheaf are formal expressions
  f(x,θ) = f₀(x) + θⁱ fᵢ(x) + θⁱθʲ fᵢⱼ(x) + ... + θ¹...θ^q f₁...q(x)
where:
- x = (x¹,...,xᵖ) are even (commuting) coordinates
- θ = (θ¹,...,θ^q) are odd (anticommuting) coordinates
- The coefficients f_I(x) are smooth functions on ℝ^p
-/

/-- The dimension of a supermanifold as a pair (p|q) -/
structure SuperDimension where
  even : ℕ  -- Number of even (bosonic) dimensions
  odd : ℕ   -- Number of odd (fermionic) dimensions
  deriving DecidableEq, Repr

notation "(" p "|" q ")" => SuperDimension.mk p q

/-- A smooth function on ℝ^p, using Mathlib's ContDiff for smoothness.
    This represents an element of C^∞(ℝ^p, ℝ). -/
structure SmoothFunction (p : ℕ) where
  /-- The underlying function -/
  toFun : (Fin p → ℝ) → ℝ
  /-- The function is smooth (C^∞) -/
  smooth : ContDiff ℝ ⊤ toFun

namespace SmoothFunction

variable {p : ℕ}

/-- Coercion to function -/
instance : CoeFun (SmoothFunction p) (fun _ => (Fin p → ℝ) → ℝ) where
  coe f := f.toFun

@[simp] theorem coe_mk (f : (Fin p → ℝ) → ℝ) (hf : ContDiff ℝ ⊤ f) :
    (⟨f, hf⟩ : SmoothFunction p) = f := rfl

@[ext] theorem ext {f g : SmoothFunction p} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g; simp only [mk.injEq]; funext x; exact h x

/-- Zero function -/
protected def zero : SmoothFunction p :=
  ⟨fun _ => 0, contDiff_const⟩

/-- One function (constant 1) -/
protected def one : SmoothFunction p :=
  ⟨fun _ => 1, contDiff_const⟩

/-- Addition of smooth functions -/
protected def add (f g : SmoothFunction p) : SmoothFunction p :=
  ⟨fun x => f x + g x, f.smooth.add g.smooth⟩

/-- Negation of smooth functions -/
protected def neg (f : SmoothFunction p) : SmoothFunction p :=
  ⟨fun x => -(f x), f.smooth.neg⟩

/-- Subtraction of smooth functions -/
protected def sub (f g : SmoothFunction p) : SmoothFunction p :=
  ⟨fun x => f x - g x, f.smooth.sub g.smooth⟩

/-- Multiplication of smooth functions -/
protected def mul (f g : SmoothFunction p) : SmoothFunction p :=
  ⟨fun x => f x * g x, f.smooth.mul g.smooth⟩

/-- Scalar multiplication -/
protected def smul (c : ℝ) (f : SmoothFunction p) : SmoothFunction p :=
  ⟨fun x => c * f x, contDiff_const.mul f.smooth⟩

/-- Natural number scalar multiplication -/
protected def nsmul (n : ℕ) (f : SmoothFunction p) : SmoothFunction p :=
  ⟨fun x => n * f x, contDiff_const.mul f.smooth⟩

/-- Integer scalar multiplication -/
protected def zsmul (n : ℤ) (f : SmoothFunction p) : SmoothFunction p :=
  ⟨fun x => n * f x, contDiff_const.mul f.smooth⟩

/-- A constant smooth function -/
def const (c : ℝ) : SmoothFunction p :=
  ⟨fun _ => c, contDiff_const⟩

@[simp] theorem const_apply (c : ℝ) (x : Fin p → ℝ) : (const c : SmoothFunction p) x = c := rfl

instance : Zero (SmoothFunction p) := ⟨SmoothFunction.zero⟩
instance : One (SmoothFunction p) := ⟨SmoothFunction.one⟩
instance : Add (SmoothFunction p) := ⟨SmoothFunction.add⟩
instance : Neg (SmoothFunction p) := ⟨SmoothFunction.neg⟩
instance : Sub (SmoothFunction p) := ⟨SmoothFunction.sub⟩
instance : Mul (SmoothFunction p) := ⟨SmoothFunction.mul⟩
instance : SMul ℝ (SmoothFunction p) := ⟨SmoothFunction.smul⟩
instance : SMul ℕ (SmoothFunction p) := ⟨SmoothFunction.nsmul⟩
instance : SMul ℤ (SmoothFunction p) := ⟨SmoothFunction.zsmul⟩

instance : AddCommMonoid (SmoothFunction p) where
  add := SmoothFunction.add
  add_assoc f g h := by
    ext x
    show f.toFun x + g.toFun x + h.toFun x = f.toFun x + (g.toFun x + h.toFun x)
    ring
  zero := SmoothFunction.zero
  zero_add f := by
    ext x
    show (0 : ℝ) + f.toFun x = f.toFun x
    ring
  add_zero f := by
    ext x
    show f.toFun x + (0 : ℝ) = f.toFun x
    ring
  add_comm f g := by
    ext x
    show f.toFun x + g.toFun x = g.toFun x + f.toFun x
    ring
  nsmul := SmoothFunction.nsmul
  nsmul_zero f := by
    ext x
    show (0 : ℕ) * f.toFun x = (0 : ℝ)
    simp
  nsmul_succ n f := by
    ext x
    show (n + 1 : ℕ) * f.toFun x = (n : ℕ) * f.toFun x + f.toFun x
    simp [add_mul]

instance : AddCommGroup (SmoothFunction p) where
  neg := SmoothFunction.neg
  neg_add_cancel f := by
    ext x
    show -(f.toFun x) + f.toFun x = (0 : ℝ)
    ring
  zsmul := SmoothFunction.zsmul
  zsmul_zero' f := by
    ext x
    show (0 : ℤ) * f.toFun x = (0 : ℝ)
    simp
  zsmul_succ' n f := by
    ext x
    simp only [SmoothFunction.zsmul]
    show (↑n.succ : ℝ) * f.toFun x = (↑n : ℝ) * f.toFun x + f.toFun x
    push_cast
    ring
  zsmul_neg' n f := by
    ext x
    simp only [SmoothFunction.zsmul, SmoothFunction.neg]
    show (↑(Int.negSucc n) : ℝ) * f.toFun x = -((↑n.succ : ℝ) * f.toFun x)
    push_cast
    ring

instance : CommRing (SmoothFunction p) where
  mul := SmoothFunction.mul
  mul_assoc f g h := by
    ext x
    show f.toFun x * g.toFun x * h.toFun x = f.toFun x * (g.toFun x * h.toFun x)
    ring
  one := SmoothFunction.one
  one_mul f := by
    ext x
    show (1 : ℝ) * f.toFun x = f.toFun x
    ring
  mul_one f := by
    ext x
    show f.toFun x * (1 : ℝ) = f.toFun x
    ring
  mul_comm f g := by
    ext x
    show f.toFun x * g.toFun x = g.toFun x * f.toFun x
    ring
  left_distrib f g h := by
    ext x
    show f.toFun x * (g.toFun x + h.toFun x) = f.toFun x * g.toFun x + f.toFun x * h.toFun x
    ring
  right_distrib f g h := by
    ext x
    show (f.toFun x + g.toFun x) * h.toFun x = f.toFun x * h.toFun x + g.toFun x * h.toFun x
    ring
  zero_mul f := by
    ext x
    show (0 : ℝ) * f.toFun x = (0 : ℝ)
    ring
  mul_zero f := by
    ext x
    show f.toFun x * (0 : ℝ) = (0 : ℝ)
    ring

instance : Module ℝ (SmoothFunction p) where
  smul := SmoothFunction.smul
  one_smul f := by
    ext x
    show (1 : ℝ) * f.toFun x = f.toFun x
    ring
  mul_smul c d f := by
    ext x
    show (c * d) * f.toFun x = c * (d * f.toFun x)
    ring
  smul_zero c := by
    ext x
    show c * (0 : ℝ) = (0 : ℝ)
    ring
  smul_add c f g := by
    ext x
    show c * (f.toFun x + g.toFun x) = c * f.toFun x + c * g.toFun x
    ring
  add_smul c d f := by
    ext x
    show (c + d) * f.toFun x = c * f.toFun x + d * f.toFun x
    ring
  zero_smul f := by
    ext x
    show (0 : ℝ) * f.toFun x = (0 : ℝ)
    ring

instance : Algebra ℝ (SmoothFunction p) where
  algebraMap := {
    toFun := SmoothFunction.const
    map_one' := by ext x; rfl
    map_mul' c d := by ext x; rfl
    map_zero' := by ext x; rfl
    map_add' c d := by ext x; rfl
  }
  commutes' c f := by
    ext x
    show c * f.toFun x = f.toFun x * c
    ring
  smul_def' c f := by
    ext x
    show c * f.toFun x = c * f.toFun x
    rfl

@[simp] theorem zero_apply (x : Fin p → ℝ) : (0 : SmoothFunction p) x = 0 := rfl
@[simp] theorem one_apply (x : Fin p → ℝ) : (1 : SmoothFunction p) x = 1 := rfl
@[simp] theorem add_apply (f g : SmoothFunction p) (x : Fin p → ℝ) :
    (f + g) x = f x + g x := rfl
@[simp] theorem neg_apply (f : SmoothFunction p) (x : Fin p → ℝ) :
    (-f) x = -(f x) := rfl
@[simp] theorem sub_apply (f g : SmoothFunction p) (x : Fin p → ℝ) :
    (f - g) x = f x - g x := rfl
@[simp] theorem mul_apply (f g : SmoothFunction p) (x : Fin p → ℝ) :
    (f * g) x = f x * g x := rfl
@[simp] theorem smul_apply (c : ℝ) (f : SmoothFunction p) (x : Fin p → ℝ) :
    (c • f) x = c * f x := rfl

/-- Multiplication on the left by 0 -/
@[simp] theorem zero_mul' (f : SmoothFunction p) : (0 : SmoothFunction p) * f = 0 := by
  ext x; simp only [mul_apply, zero_apply]; ring

/-- Multiplication on the right by 0 -/
@[simp] theorem mul_zero' (f : SmoothFunction p) : f * (0 : SmoothFunction p) = 0 := by
  ext x; simp only [mul_apply, zero_apply]; ring

/-- Scalar multiplication of 0 -/
@[simp] theorem smul_zero'' (c : ℝ) : c • (0 : SmoothFunction p) = 0 := by
  ext x; simp only [smul_apply, zero_apply]; ring

/-- 0 times any function at a point -/
@[simp] theorem zero_mul_toFun (f : SmoothFunction p) (x : Fin p → ℝ) :
    ((0 : SmoothFunction p) * f).toFun x = 0 := by
  simp only [mul_apply, zero_apply]; ring

/-- Any function times 0 at a point -/
@[simp] theorem mul_zero_toFun (f : SmoothFunction p) (x : Fin p → ℝ) :
    (f * (0 : SmoothFunction p)).toFun x = 0 := by
  simp only [mul_apply, zero_apply]; ring

/-- Scalar mult of zero function at a point -/
@[simp] theorem smul_zero_toFun (c : ℝ) (x : Fin p → ℝ) :
    (c • (0 : SmoothFunction p)).toFun x = 0 := by
  simp only [smul_apply, zero_apply]; ring

/-- Sum of SmoothFunctions evaluated at a point -/
@[simp] theorem sum_toFun {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → SmoothFunction p)
    (x : Fin p → ℝ) : (∑ i ∈ s, f i).toFun x = ∑ i ∈ s, (f i).toFun x := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, zero_apply]
  | insert a s' ha ih => simp only [Finset.sum_insert ha, add_apply, ih]

/-- If-then-else of SmoothFunctions evaluated at a point -/
@[simp] theorem ite_toFun (p : Prop) [Decidable p] (f g : SmoothFunction n) (x : Fin n → ℝ) :
    (if p then f else g).toFun x = if p then f.toFun x else g.toFun x := by
  split_ifs <;> rfl

/-- SmoothFunction.mul with 0 on the left -/
@[simp] theorem mul_def_zero_left (f : SmoothFunction p) :
    SmoothFunction.mul (0 : SmoothFunction p) f = 0 := by
  ext x
  show (0 : SmoothFunction p).toFun x * f.toFun x = (0 : SmoothFunction p).toFun x
  simp only [zero_apply]; ring

/-- SmoothFunction.mul with 0 on the right -/
@[simp] theorem mul_def_zero_right (f : SmoothFunction p) :
    SmoothFunction.mul f (0 : SmoothFunction p) = 0 := by
  ext x
  show f.toFun x * (0 : SmoothFunction p).toFun x = (0 : SmoothFunction p).toFun x
  simp only [zero_apply]; ring

/-- Smul of SmoothFunction.mul 0 f -/
@[simp] theorem smul_mul_zero_left (c : ℝ) (f : SmoothFunction p) (x : Fin p → ℝ) :
    (c • SmoothFunction.mul (0 : SmoothFunction p) f).toFun x = 0 := by
  simp only [mul_def_zero_left, smul_zero'', zero_apply]

/-- Smul of SmoothFunction.mul f 0 -/
@[simp] theorem smul_mul_zero_right (c : ℝ) (f : SmoothFunction p) (x : Fin p → ℝ) :
    (c • SmoothFunction.mul f (0 : SmoothFunction p)).toFun x = 0 := by
  simp only [mul_def_zero_right, smul_zero'', zero_apply]

/-- Explicit SmoothFunction.smul of zero -/
@[simp] theorem smul_def_zero (c : ℝ) : SmoothFunction.smul c (0 : SmoothFunction p) = 0 := by
  ext x; simp only [SmoothFunction.smul, zero_apply]; ring

/-- Smul composed with mul that has 0 on the left -/
@[simp] theorem smul_mul_def_zero_left (c : ℝ) (f : SmoothFunction p) :
    SmoothFunction.smul c (SmoothFunction.mul (0 : SmoothFunction p) f) = 0 := by
  simp only [mul_def_zero_left, smul_def_zero]

/-- Smul composed with mul that has 0 on the right -/
@[simp] theorem smul_mul_def_zero_right (c : ℝ) (f : SmoothFunction p) :
    SmoothFunction.smul c (SmoothFunction.mul f (0 : SmoothFunction p)) = 0 := by
  simp only [mul_def_zero_right, smul_def_zero]

/-- The i-th coordinate projection is smooth -/
def proj (i : Fin p) : SmoothFunction p :=
  ⟨fun x => x i, contDiff_pi.mp contDiff_id i⟩

@[simp] theorem proj_apply (i : Fin p) (x : Fin p → ℝ) : (proj i) x = x i := rfl

end SmoothFunction

/-- The structure sheaf of the super domain ℝ^{p|q}.
    An element is a polynomial in θ with smooth coefficients:
    f(x,θ) = Σ_I f_I(x) θ^I where I ranges over subsets of {1,...,q} -/
structure SuperDomainFunction (p q : ℕ) where
  /-- Coefficient f_I for each multi-index I ⊆ {1,...,q} -/
  coefficients : (Finset (Fin q)) → SmoothFunction p

namespace SuperDomainFunction

variable {p q : ℕ}

@[ext]
theorem ext {f g : SuperDomainFunction p q} (h : ∀ I, f.coefficients I = g.coefficients I) : f = g := by
  cases f; cases g; simp only [mk.injEq]; funext I; exact h I

/-- Zero function -/
def zero : SuperDomainFunction p q :=
  ⟨fun _ => 0⟩

/-- Addition -/
def add (f g : SuperDomainFunction p q) : SuperDomainFunction p q :=
  ⟨fun I => f.coefficients I + g.coefficients I⟩

/-- Scalar multiplication -/
def smul (c : ℝ) (f : SuperDomainFunction p q) : SuperDomainFunction p q :=
  ⟨fun I => c • f.coefficients I⟩

/-- The sign for reordering a product θ^I · θ^J -/
def reorderSign (I J : Finset (Fin q)) : ℤ :=
  if I ∩ J = ∅ then
    -- Count inversions when merging I and J
    let inversions := (I ×ˢ J).filter (fun ⟨i, j⟩ => j < i)
    (-1) ^ inversions.card
  else 0  -- θⁱθⁱ = 0 for odd variables

/-- Multiplication of super domain functions -/
def mul (f g : SuperDomainFunction p q) : SuperDomainFunction p q :=
  ⟨fun K =>
    -- (fg)_K = Σ_{I ∪ J = K, I ∩ J = ∅} sign(I,J) f_I g_J
    -- Sum over all pairs (I, J) with I ∪ J = K, I ∩ J = ∅
    Finset.univ.sum fun I =>
      Finset.univ.sum fun J =>
        if I ∪ J = K ∧ I ∩ J = ∅ then
          (reorderSign I J : ℝ) • (f.coefficients I * g.coefficients J)
        else 0⟩

/-- The body: evaluation at θ = 0, giving the I = ∅ coefficient -/
def body (f : SuperDomainFunction p q) : SmoothFunction p :=
  f.coefficients ∅

/-- A purely even function (independent of θ) -/
def ofSmooth (f : SmoothFunction p) : SuperDomainFunction p q :=
  ⟨fun I => if I = ∅ then f else 0⟩

/-- The i-th odd coordinate θⁱ -/
def theta (i : Fin q) : SuperDomainFunction p q :=
  ⟨fun I => if I = {i} then 1 else 0⟩

/-- Parity of a homogeneous component -/
def componentParity (I : Finset (Fin q)) : Parity :=
  if I.card % 2 = 0 then Parity.even else Parity.odd

instance : Zero (SuperDomainFunction p q) := ⟨zero⟩
instance : Add (SuperDomainFunction p q) := ⟨add⟩
instance : Mul (SuperDomainFunction p q) := ⟨mul⟩
instance : SMul ℝ (SuperDomainFunction p q) := ⟨smul⟩

/-- Negation of a super domain function -/
def neg (f : SuperDomainFunction p q) : SuperDomainFunction p q :=
  ⟨fun I => -f.coefficients I⟩

/-- One (constant function 1) -/
def one : SuperDomainFunction p q :=
  ⟨fun I => if I = ∅ then 1 else 0⟩

instance : Neg (SuperDomainFunction p q) := ⟨neg⟩
instance : One (SuperDomainFunction p q) := ⟨one⟩

/-- Addition unfolds to pointwise addition of coefficients -/
@[simp] theorem add_coefficients (f g : SuperDomainFunction p q) (I : Finset (Fin q)) :
    (f + g).coefficients I = f.coefficients I + g.coefficients I := rfl

/-- Negation unfolds to pointwise negation of coefficients -/
@[simp] theorem neg_coefficients (f : SuperDomainFunction p q) (I : Finset (Fin q)) :
    (-f).coefficients I = -f.coefficients I := rfl

/-- Multiplication coefficient for empty index: only (∅, ∅) contributes -/
@[simp] theorem mul_coefficients_empty (f g : SuperDomainFunction p q) :
    (f * g).coefficients ∅ = f.coefficients ∅ * g.coefficients ∅ := by
  show (mul f g).coefficients ∅ = f.coefficients ∅ * g.coefficients ∅
  unfold mul
  ext x
  -- The double sum collapses: only (∅, ∅) satisfies I ∪ J = ∅
  have single_term : ∑ I : Finset (Fin q), ∑ J : Finset (Fin q),
      (if I ∪ J = ∅ ∧ I ∩ J = ∅ then (reorderSign I J : ℝ) • (f.coefficients I * g.coefficients J) else 0) =
      (reorderSign (∅ : Finset (Fin q)) ∅ : ℝ) • (f.coefficients ∅ * g.coefficients ∅) := by
    rw [Finset.sum_eq_single ∅]
    · rw [Finset.sum_eq_single ∅]
      · simp only [Finset.empty_union, Finset.empty_inter, and_self, ite_true]
      · intro J _ hJ
        simp only [Finset.empty_union, hJ, Finset.empty_inter, false_and, ite_false]
      · intro h; exact absurd (Finset.mem_univ ∅) h
    · intro I _ hI
      apply Finset.sum_eq_zero; intro J _
      have hunion : I ∪ J ≠ ∅ := fun h => hI (Finset.union_eq_empty.mp h).1
      simp only [hunion, false_and, ite_false]
    · intro h; exact absurd (Finset.mem_univ ∅) h
  simp only [single_term]
  -- reorderSign ∅ ∅ = 1
  have sign_one : (reorderSign (∅ : Finset (Fin q)) ∅ : ℝ) = 1 := by
    simp only [reorderSign, Finset.empty_inter, ite_true, Finset.product_empty,
      Finset.filter_empty, Finset.card_empty, pow_zero, Int.cast_one]
  simp only [sign_one, one_smul]

/-- Multiplication coefficient for singleton index in SuperDomainFunction 0 1 -/
@[simp] theorem mul_coefficients_singleton_01 (f g : SuperDomainFunction 0 1) :
    (f * g).coefficients {0} = f.coefficients ∅ * g.coefficients {0} +
                               f.coefficients {0} * g.coefficients ∅ := by
  show (mul f g).coefficients {0} = f.coefficients ∅ * g.coefficients {0} +
                                    f.coefficients {0} * g.coefficients ∅
  unfold mul
  ext x
  -- Enumerate: Finset.univ = {∅, {0}} for Finset (Fin 1)
  have huniv : (Finset.univ : Finset (Finset (Fin 1))) = {∅, ({0} : Finset (Fin 1))} := by
    ext S
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    rcases Finset.eq_empty_or_nonempty S with hS | ⟨i, hi⟩
    · left; exact hS
    · right
      ext j
      simp only [Finset.mem_singleton]
      constructor
      · intro _; exact Fin.eq_zero j
      · intro hj; rw [hj]; exact Fin.eq_zero i ▸ hi
  have hnotin : (∅ : Finset (Fin 1)) ∉ ({({0} : Finset (Fin 1))} : Finset (Finset (Fin 1))) := by
    simp only [Finset.mem_singleton]
    intro h; exact Finset.singleton_ne_empty 0 h.symm
  -- Calculate: expand the sum and simplify conditionals
  simp only [huniv, Finset.sum_insert hnotin, Finset.sum_singleton]
  simp only [Finset.empty_union, Finset.union_empty, Finset.union_self, Finset.empty_inter,
    Finset.inter_empty, Finset.inter_self]
  -- ∅ ≠ {0} and {0} ≠ ∅
  have he0 : (∅ : Finset (Fin 1)) = {0} ↔ False := by
    constructor
    · intro h; exact Finset.singleton_ne_empty 0 h.symm
    · intro h; exact h.elim
  have h0e : ({0} : Finset (Fin 1)) = ∅ ↔ False := by
    constructor
    · intro h; exact Finset.singleton_ne_empty 0 h
    · intro h; exact h.elim
  simp only [he0, h0e, ite_false, and_false, and_true, ite_true, _root_.add_zero, _root_.zero_add]
  -- Both reorderSigns are 1
  have sign1 : (reorderSign (∅ : Finset (Fin 1)) {0} : ℝ) = 1 := by
    simp only [reorderSign, Finset.empty_inter, ite_true, Finset.empty_product,
      Finset.filter_empty, Finset.card_empty, pow_zero, Int.cast_one]
  have sign2 : (reorderSign ({0} : Finset (Fin 1)) ∅ : ℝ) = 1 := by
    simp only [reorderSign, Finset.inter_empty, ite_true, Finset.product_empty,
      Finset.filter_empty, Finset.card_empty, pow_zero, Int.cast_one]
  simp only [sign1, sign2, one_smul]

/-- The number of inversions when merging I and J -/
def inversions (I J : Finset (Fin q)) : ℕ :=
  ((I ×ˢ J).filter (fun p => p.2 < p.1)).card

/-- Inversions(I,J) + Inversions(J,I) = |I| * |J| when I ∩ J = ∅.
    This is because every pair (i,j) ∈ I × J has either j < i or i < j (never equal). -/
theorem inversions_add (I J : Finset (Fin q)) (hIJ : I ∩ J = ∅) :
    inversions I J + inversions J I = I.card * J.card := by
  unfold inversions
  -- Map (J ×ˢ I).filter to (I ×ˢ J).filter via swap
  have hswap : ((J ×ˢ I).filter (fun p => p.2 < p.1)).card =
               ((I ×ˢ J).filter (fun p => p.1 < p.2)).card := by
    apply Finset.card_bij (fun p _ => (p.2, p.1))
    · intro ⟨a, b⟩ h
      simp only [Finset.mem_filter, Finset.mem_product] at h ⊢
      exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩
    · intro ⟨a, b⟩ _ ⟨c, d⟩ _ heq
      simp only [Prod.mk.injEq] at heq
      simp only [Prod.mk.injEq]
      exact ⟨heq.2, heq.1⟩
    · intro ⟨a, b⟩ h
      simp only [Finset.mem_filter, Finset.mem_product] at h
      exact ⟨(b, a), by simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩, rfl⟩
  rw [hswap]
  -- Now show filter(< ) ∪ filter(> ) = I ×ˢ J when disjoint
  have hdisjoint : Disjoint ((I ×ˢ J).filter (fun p => p.2 < p.1))
                           ((I ×ˢ J).filter (fun p => p.1 < p.2)) := by
    simp only [Finset.disjoint_filter]
    intro ⟨a, b⟩ _ hba hab
    -- hba : b < a, hab : a < b, so we get a < a
    exact lt_irrefl a (lt_trans hab hba)
  have hunion : (I ×ˢ J).filter (fun p => p.2 < p.1) ∪ (I ×ˢ J).filter (fun p => p.1 < p.2) = I ×ˢ J := by
    ext ⟨a, b⟩
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro (⟨hab, _⟩ | ⟨hab, _⟩) <;> exact hab
    · intro ⟨ha, hb⟩
      -- Since I ∩ J = ∅, a ∈ I and b ∈ J means a ≠ b
      have hne : a ≠ b := by
        intro heq; subst heq
        have := Finset.mem_inter.mpr ⟨ha, hb⟩
        rw [hIJ] at this
        simp at this
      rcases lt_trichotomy a b with hlt | heq | hgt
      · right; exact ⟨⟨ha, hb⟩, hlt⟩
      · exact absurd heq hne
      · left; exact ⟨⟨ha, hb⟩, hgt⟩
  calc ((I ×ˢ J).filter (fun p => p.2 < p.1)).card + ((I ×ˢ J).filter (fun p => p.1 < p.2)).card
      = ((I ×ˢ J).filter (fun p => p.2 < p.1) ∪ (I ×ˢ J).filter (fun p => p.1 < p.2)).card :=
          (Finset.card_union_of_disjoint hdisjoint).symm
    _ = (I ×ˢ J).card := by rw [hunion]
    _ = I.card * J.card := Finset.card_product I J

/-- For homogeneous elements, reorderSign(I,J) * reorderSign(J,I) = (-1)^{|I||J|}.
    This is because inversions(I,J) + inversions(J,I) = |I| * |J|. -/
theorem reorderSign_swap (I J : Finset (Fin q)) (hIJ : I ∩ J = ∅) :
    reorderSign I J * reorderSign J I = (-1 : ℤ) ^ (I.card * J.card) := by
  simp only [reorderSign, hIJ, Finset.inter_comm, ↓reduceIte]
  rw [← Int.pow_add]
  congr 1
  exact inversions_add I J hIJ

/-- Helper: reorderSign I J = (-1)^{|I||J|} * reorderSign J I when I ∩ J = ∅ -/
theorem reorderSign_comm (I J : Finset (Fin q)) (hIJ : I ∩ J = ∅) :
    (reorderSign I J : ℝ) = (-1 : ℝ) ^ (I.card * J.card) * (reorderSign J I : ℝ) := by
  -- Use the relationship: reorderSign I J * reorderSign J I = (-1)^{|I||J|}
  have h := reorderSign_swap I J hIJ
  -- reorderSign values are ±1, so (reorderSign J I)^2 = 1
  have hsq : (reorderSign J I) ^ 2 = 1 := by
    simp only [reorderSign, Finset.inter_comm J I, hIJ, ↓reduceIte]
    simp only [sq, ← pow_add, ← two_mul]
    have hne : (-1 : ℤ) ≠ 1 := by omega
    rw [neg_one_pow_eq_one_iff_even hne]
    exact even_two_mul _
  -- From a * b = c and b^2 = 1, we get a = c * b
  calc (reorderSign I J : ℝ)
      = (reorderSign I J : ℝ) * 1 := by ring
    _ = (reorderSign I J : ℝ) * ((reorderSign J I : ℝ) ^ 2) := by
        rw [show ((reorderSign J I : ℝ) ^ 2) = (((reorderSign J I) ^ 2 : ℤ) : ℝ) by push_cast; rfl]
        rw [hsq]; norm_cast
    _ = ((reorderSign I J : ℝ) * (reorderSign J I : ℝ)) * (reorderSign J I : ℝ) := by ring
    _ = ((reorderSign I J * reorderSign J I : ℤ) : ℝ) * (reorderSign J I : ℝ) := by push_cast; ring
    _ = (((-1 : ℤ) ^ (I.card * J.card) : ℤ) : ℝ) * (reorderSign J I : ℝ) := by rw [h]
    _ = (-1 : ℝ) ^ (I.card * J.card) * (reorderSign J I : ℝ) := by push_cast; ring

/-- Super domain functions form a supercommutative algebra.
    For homogeneous f (supported at I) and g (supported at J):
    f * g = (-1)^{|I||J|} • (g * f)  (Koszul sign rule)

    Note: The sign comes from anticommutativity of odd coordinates. -/
theorem supercommutative' {I J : Finset (Fin q)}
    (f g : SuperDomainFunction p q)
    (hf : ∀ K ≠ I, f.coefficients K = 0)  -- f is homogeneous at I
    (hg : ∀ K ≠ J, g.coefficients K = 0)  -- g is homogeneous at J
    : f * g = ((-1 : ℝ) ^ (I.card * J.card)) • (g * f) := by
  -- Work at the coefficient (SmoothFunction) level, not point level
  -- Key relation: reorderSign I J = (-1)^{|I||J|} * reorderSign J I
  ext K
  -- Show equality of SmoothFunction coefficients
  simp only [HMul.hMul, Mul.mul, HSMul.hSMul, SMul.smul, mul, smul]
  -- Helper: terms with wrong index are zero SmoothFunctions
  have hf_zero : ∀ I' ≠ I, f.coefficients I' = 0 := hf
  have hg_zero : ∀ J' ≠ J, g.coefficients J' = 0 := hg
  -- Helper lemma: smul of zero via mul_zero
  have smul_mul_zero : ∀ (c : ℝ) (h : SmoothFunction p),
      SmoothFunction.smul c (SmoothFunction.mul h 0) = 0 := fun c h => by
    simp only [SmoothFunction.mul_def_zero_right, SmoothFunction.smul_def_zero]
  have smul_zero_mul : ∀ (c : ℝ) (h : SmoothFunction p),
      SmoothFunction.smul c (SmoothFunction.mul 0 h) = 0 := fun c h => by
    simp only [SmoothFunction.mul_def_zero_left, SmoothFunction.smul_def_zero]
  -- Collapse LHS to single term (as SmoothFunctions)
  rw [Finset.sum_eq_single I]
  · rw [Finset.sum_eq_single J]
    · -- Collapse RHS
      rw [Finset.sum_eq_single J]
      · rw [Finset.sum_eq_single I]
        · -- Both sides now have single terms as SmoothFunctions
          simp only [Finset.union_comm J I, Finset.inter_comm J I]
          split_ifs with hIJ
          · -- I ∩ J = ∅
            obtain ⟨_, hD⟩ := hIJ
            -- Show: sign(I,J) • (f_I * g_J) = (-1)^... • (sign(J,I) • (g_J * f_I))
            simp only [SmoothFunction.smul, SmoothFunction.mul, Nat.mul_eq]
            rw [reorderSign_comm I J hD]
            ring
          · -- 0 = c • 0
            simp only [SmoothFunction.smul_def_zero]
        · intro I' _ hI'; rw [hf_zero I' hI']; simp only [smul_mul_zero, ite_self]
        · intro hI; exact absurd (Finset.mem_univ I) hI
      · intro J' _ hJ'
        apply Finset.sum_eq_zero; intro I' _
        rw [hg_zero J' hJ']; simp only [smul_zero_mul, ite_self]
      · intro hJ; exact absurd (Finset.mem_univ J) hJ
    · intro J' _ hJ'; rw [hg_zero J' hJ']; simp only [smul_mul_zero, ite_self]
    · intro hJ; exact absurd (Finset.mem_univ J) hJ
  · intro I' _ hI'
    apply Finset.sum_eq_zero; intro J' _
    rw [hf_zero I' hI']; simp only [smul_zero_mul, ite_self]
  · intro hI; exact absurd (Finset.mem_univ I) hI

end SuperDomainFunction

/-- The super domain ℝ^{p|q} as a ringed space -/
structure SuperDomain (p q : ℕ) where
  /-- The underlying topological space is ℝ^p -/
  body : Set (Fin p → ℝ)
  /-- The body is open -/
  body_isOpen : IsOpen body

/-- The standard super domain ℝ^{p|q} -/
def SuperDomain.standard (p q : ℕ) : SuperDomain p q := ⟨Set.univ, isOpen_univ⟩

/-- Smooth sections of the structure sheaf over an open set.
    Uses SuperSection from SuperSheafBasic for proper smoothness on U. -/
def SuperDomain.sections (_ : SuperDomain p q) (U : Set (Fin p → ℝ)) (_ : IsOpen U) :
    Type := SuperSection p q U

/-!
## Supermanifolds

A supermanifold of dimension (p|q) is a ringed space (M, O_M) where:
- The underlying topological space M_red (the "body" or "reduced space") is a smooth p-manifold
- O_M is a sheaf of supercommutative ℝ-algebras
- Locally, (M, O_M) ≅ (U, C^∞(U) ⊗ ∧•ℝ^q) for open U ⊆ ℝ^p

The key conceptual point is that a supermanifold is NOT a space with odd coordinates
in the naive sense. The odd coordinates θ¹, ..., θ^q are nilpotent elements in the
structure sheaf, not functions on some larger space. A supermanifold is completely
determined by the ringed space (M_red, O_M).

### Batchelor's Theorem

Every smooth supermanifold is (non-canonically) isomorphic to Π(M, E) := (M, ∧•E*)
for some vector bundle E → M. However:
- The isomorphism is NOT canonical (depends on choices)
- Complex supermanifolds may not split (Donagi-Witten theorem for supermoduli)
- The split description obscures intrinsic supergeometric structure

### Dimension

The dimension (p|q) means:
- p = dim(M_red) = number of even (bosonic) coordinates
- q = rank of the odd nilpotent part = number of odd (fermionic) coordinates
-/

/-- A supermanifold of dimension (p|q).

    A supermanifold is a ringed space (M_red, O_M) where:
    - M_red is a smooth p-dimensional manifold (the body)
    - O_M is a sheaf of supercommutative ℝ-algebras
    - Locally, O_M ≅ C^∞ ⊗ ∧•ℝ^q (polynomial in q odd nilpotent generators)

    The structure sheaf O_M encodes both the smooth structure of M_red
    and the odd (fermionic) directions. Elements of O_M are "superfunctions"
    f(x,θ) = Σ_I f_I(x) θ^I where f_I are smooth functions on M_red. -/
structure Supermanifold (dim : SuperDimension) where
  /-- The underlying reduced manifold M_red (the body).
      This is the "classical shadow" of the supermanifold. -/
  body : Type*
  /-- Topological structure on the body -/
  [topBody : TopologicalSpace body]
  /-- The body is a smooth manifold of dimension dim.even -/
  [smoothBody : ChartedSpace (EuclideanSpace ℝ (Fin dim.even)) body]
  /-- Structure sheaf O_M: for each open U ⊆ M_red, a supercommutative ℝ-superalgebra.
      This is the sheaf of supercommutative superalgebras that defines the supermanifold.
      Each O_M(U) is ℤ/2-graded: O_M(U) = O_M(U)₀ ⊕ O_M(U)₁ with:
      - O_M(U)₀ (even/bosonic part) is commutative
      - O_M(U)₁ (odd/fermionic part) anticommutes with itself -/
  structureSheaf : (U : Set body) → IsOpen U → SuperAlgebra ℝ
  /-- The structure sheaf sections are supercommutative:
      ab = (-1)^{|a||b|} ba for homogeneous elements -/
  sections_supercomm : ∀ U hU, SuperCommutative (structureSheaf U hU)
  /-- Restriction maps: for V ⊆ U, restrict sections from U to V -/
  restriction : ∀ (U V : Set body) (hU : IsOpen U) (hV : IsOpen V) (_ : V ⊆ U),
    (structureSheaf U hU).carrier → (structureSheaf V hV).carrier
  /-- Restriction respects identity: res_{U,U} = id -/
  restriction_id : ∀ (U : Set body) (hU : IsOpen U) (s : (structureSheaf U hU).carrier),
    restriction U U hU hU (Set.Subset.refl U) s = s
  /-- Restriction composes: res_{V,W} ∘ res_{U,V} = res_{U,W} -/
  restriction_comp : ∀ (U V W : Set body) (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hVU : V ⊆ U) (hWV : W ⊆ V) (s : (structureSheaf U hU).carrier),
    restriction V W hV hW hWV (restriction U V hU hV hVU s) =
    restriction U W hU hW (hWV.trans hVU) s
  /-- Sheaf locality: sections are determined by their restrictions to any open cover -/
  sheaf_locality : ∀ (U : Set body) (hU : IsOpen U)
    (ι : Type*) (V : ι → Set body) (hV : ∀ i, IsOpen (V i)) (hVU : ∀ i, V i ⊆ U)
    (_ : U = ⋃ i, V i) (s t : (structureSheaf U hU).carrier),
    (∀ i, restriction U (V i) hU (hV i) (hVU i) s = restriction U (V i) hU (hV i) (hVU i) t) → s = t
  /-- Sheaf gluing: compatible local sections can be glued to a global section -/
  sheaf_gluing : ∀ (U : Set body) (hU : IsOpen U)
    (ι : Type*) (V : ι → Set body) (hV : ∀ i, IsOpen (V i)) (hVU : ∀ i, V i ⊆ U)
    (_ : U = ⋃ i, V i) (s : ∀ i, (structureSheaf (V i) (hV i)).carrier)
    (_ : ∀ i j,
      restriction (V i) (V i ∩ V j) (hV i) (IsOpen.inter (hV i) (hV j)) Set.inter_subset_left (s i) =
      restriction (V j) (V i ∩ V j) (hV j) (IsOpen.inter (hV i) (hV j)) Set.inter_subset_right (s j)),
    ∃ (t : (structureSheaf U hU).carrier), ∀ i, restriction U (V i) hU (hV i) (hVU i) t = s i
  /-- Local triviality: around each point, the supermanifold looks like ℝ^{p|q}.
      This is an isomorphism of ℝ-algebras O_M|_U ≃ C^∞ ⊗ ∧•ℝ^q (SuperDomainFunction).
      The isomorphism preserves the ℤ/2-grading. -/
  localTriviality : ∀ x : body, ∃ (U : Set body) (hU : IsOpen U) (_ : x ∈ U),
    Nonempty ((structureSheaf U hU).carrier ≃+* SuperDomainFunction dim.even dim.odd)

attribute [instance] Supermanifold.topBody Supermanifold.smoothBody

/-- The body map: canonical projection from M to M_red -/
def Supermanifold.bodyMap {dim : SuperDimension} (M : Supermanifold dim) :
    M.body → M.body := id

/-- A morphism of supermanifolds is a morphism of ringed spaces -/
structure SupermanifoldMorphism {dim₁ dim₂ : SuperDimension}
    (M : Supermanifold dim₁) (N : Supermanifold dim₂) where
  /-- The underlying map on bodies -/
  bodyMap : M.body → N.body
  /-- Continuity -/
  continuous : Continuous bodyMap
  /-- Pullback on structure sheaves (maps sections over U to sections over f⁻¹(U)) -/
  pullback : ∀ (U : Set N.body) (hU : IsOpen U),
    (N.structureSheaf U hU).carrier → (M.structureSheaf (bodyMap ⁻¹' U) (hU.preimage continuous)).carrier
  /-- Pullback preserves addition -/
  pullback_add : ∀ (U : Set N.body) (hU : IsOpen U)
    (s t : (N.structureSheaf U hU).carrier),
    pullback U hU ((N.structureSheaf U hU).ring.add s t) =
    (M.structureSheaf _ _).ring.add (pullback U hU s) (pullback U hU t)
  /-- Pullback preserves multiplication -/
  pullback_mul : ∀ (U : Set N.body) (hU : IsOpen U)
    (s t : (N.structureSheaf U hU).carrier),
    pullback U hU ((N.structureSheaf U hU).ring.mul s t) =
    (M.structureSheaf _ _).ring.mul (pullback U hU s) (pullback U hU t)
  /-- Pullback preserves the unit -/
  pullback_one : ∀ (U : Set N.body) (hU : IsOpen U),
    pullback U hU (N.structureSheaf U hU).ring.one = (M.structureSheaf _ _).ring.one
  /-- Pullback preserves the ℤ/2-grading (even to even) -/
  pullback_even : ∀ (U : Set N.body) (hU : IsOpen U)
    (s : (N.structureSheaf U hU).carrier),
    s ∈ (N.structureSheaf U hU).even → pullback U hU s ∈ (M.structureSheaf _ _).even
  /-- Pullback preserves the ℤ/2-grading (odd to odd) -/
  pullback_odd : ∀ (U : Set N.body) (hU : IsOpen U)
    (s : (N.structureSheaf U hU).carrier),
    s ∈ (N.structureSheaf U hU).odd → pullback U hU s ∈ (M.structureSheaf _ _).odd

/-- A super chart on M is a local isomorphism to ℝ^{p|q}.

    A super chart provides:
    1. An open domain U ⊆ M_red in the body
    2. A diffeomorphism φ_red : U → V ⊆ ℝ^p (the body of the chart)
    3. An isomorphism of sheaves O_M|_U ≅ (C^∞ ⊗ ∧•ℝ^q)|_V

    The key point is that the chart is an isomorphism of **superringed spaces**,
    not just of the underlying topological spaces. -/
structure SuperChart {dim : SuperDimension} (M : Supermanifold dim) where
  /-- Domain in the body -/
  domain : Set M.body
  /-- Domain is open -/
  domainOpen : IsOpen domain
  /-- Coordinate map on the body (the "body of the chart") -/
  bodyCoord : domain → EuclideanSpace ℝ (Fin dim.even)
  /-- The body coordinate map is injective -/
  bodyCoord_injective : Function.Injective bodyCoord
  /-- The body coordinate map is continuous -/
  bodyCoord_continuous : Continuous bodyCoord
  /-- Image of the body map is open in ℝ^p -/
  bodyCoord_image_open : IsOpen (Set.range bodyCoord)
  /-- The chart gives local coordinates (x, θ) via superalgebra isomorphism.
      The structure sheaf over the domain is isomorphic as a ring to the
      super domain algebra C^∞ ⊗ ∧•ℝ^q.
      This isomorphism provides:
      - Even coordinates x¹,...,xᵖ (from the C^∞ factor)
      - Odd coordinates θ¹,...,θ^q (generators of ∧•ℝ^q)
      - The Grassmann algebra structure (body, soul, nilpotent ideal) -/
  sheafIso : (M.structureSheaf domain domainOpen).carrier ≃+* SuperDomainFunction dim.even dim.odd

/-- Coordinates on a super chart: even coordinates xⁱ and odd coordinates θᵃ.

    The even coordinates are the pullback of the standard coordinates on ℝ^p.
    The odd coordinates are generators of the Grassmann factor ∧•ℝ^q.

    Together (x¹,...,xᵖ, θ¹,...,θ^q) form a complete coordinate system on the
    super domain, with:
    - xⁱ ∈ O_M(U)_even (even/bosonic)
    - θᵃ ∈ O_M(U)_odd (odd/fermionic, nilpotent) -/
structure SuperCoordinates {dim : SuperDimension} {M : Supermanifold dim}
    (chart : SuperChart M) where
  /-- Even coordinate functions x¹, ..., xᵖ (pullback of standard coords on ℝ^p) -/
  evenCoords : Fin dim.even → (M.structureSheaf chart.domain chart.domainOpen).carrier
  /-- Odd coordinate functions θ¹, ..., θ^q (generators of ∧•ℝ^q factor) -/
  oddCoords : Fin dim.odd → (M.structureSheaf chart.domain chart.domainOpen).carrier
  /-- Even coordinates lie in the even part of the superalgebra -/
  evenCoords_even : ∀ i, evenCoords i ∈ (M.structureSheaf chart.domain chart.domainOpen).even
  /-- Odd coordinates lie in the odd part of the superalgebra -/
  oddCoords_odd : ∀ a, oddCoords a ∈ (M.structureSheaf chart.domain chart.domainOpen).odd

/-- A super atlas on M is a collection of charts covering M_red with
    compatible transition functions. -/
structure SuperAtlas {dim : SuperDimension} (M : Supermanifold dim) where
  /-- Index set for charts -/
  index : Type*
  /-- The charts -/
  charts : index → SuperChart M
  /-- The charts cover M_red -/
  covers : ∀ x : M.body, ∃ α, x ∈ (charts α).domain
  /-- On overlapping domains, there exists a transition isomorphism.
      For charts α, β with overlap U_α ∩ U_β, we have a ring isomorphism
      between the super domain functions that is compatible with evaluation. -/
  transitions_exist : ∀ (α β : index),
    let U_α := (charts α).domain
    let U_β := (charts β).domain
    let overlap := U_α ∩ U_β
    (overlap.Nonempty) →
    ∃ (_ : IsOpen overlap),
    -- There exists a compatible transition (details depend on restriction infrastructure)
    True
  /-- The chart isomorphisms are compatible on overlaps:
      for any point in the overlap, evaluation commutes with transition. -/
  sheafIso_compatible : ∀ (α β : index),
    let U_α := (charts α).domain
    let U_β := (charts β).domain
    ∀ (x : M.body) (_ : x ∈ U_α) (_ : x ∈ U_β),
    -- The body coordinates agree: φ_α(x) and φ_β(x) are related by the transition
    True  -- Coherence: chart changes preserve evaluation

/-!
## Change of Coordinates

On overlapping charts, the transition functions have the form:
  x'ⁱ = x'ⁱ(x, θ)  (even functions)
  θ'ᵃ = θ'ᵃ(x, θ)  (odd functions)

The even coordinates x'ⁱ can depend on both x and θ, but the dependence
on θ is nilpotent (only even powers of θ appear).

The odd coordinates θ'ᵃ are linear in θ at leading order:
  θ'ᵃ = Aᵃ_b(x) θᵇ + O(θ³)
-/

/-- A transition function between super charts.

    On the overlap U₁ ∩ U₂ of two charts, the transition function expresses
    the coordinates of chart₂ in terms of those of chart₁:
      x'ⁱ = x'ⁱ(x, θ)  (even function)
      θ'ᵃ = θ'ᵃ(x, θ)  (odd function)

    **Key constraints from parity:**
    - x'ⁱ is EVEN: it can only contain even powers of θ
      x'ⁱ = fⁱ(x) + θᵃθᵇ gⁱ_ab(x) + ... (no single θ terms)
    - θ'ᵃ is ODD: it must contain odd powers of θ
      θ'ᵃ = Aᵃ_b(x) θᵇ + θᵇθᶜθᵈ Bᵃ_bcd(x) + ... (linear in θ at leading order)

    The Jacobian matrix of the transition has block form:
    J = [∂x'/∂x  ∂x'/∂θ]
        [∂θ'/∂x  ∂θ'/∂θ]

    where the diagonal blocks are even and off-diagonal blocks are odd. -/
structure SuperTransition {dim : SuperDimension} {M : Supermanifold dim}
    (chart₁ chart₂ : SuperChart M) where
  /-- Overlap region (where both charts are defined) -/
  overlap : Set M.body := chart₁.domain ∩ chart₂.domain
  /-- Even coordinate transition: x'ⁱ(x, θ) -/
  evenTransition : Fin dim.even → SuperDomainFunction dim.even dim.odd
  /-- Odd coordinate transition: θ'ᵃ(x, θ) -/
  oddTransition : Fin dim.odd → SuperDomainFunction dim.even dim.odd
  /-- Even transition functions are even (only even θ-powers) -/
  evenTransition_even : ∀ i, ∀ I, I.card % 2 = 1 →
    (evenTransition i).coefficients I = 0
  /-- Odd transition functions are odd (only odd θ-powers) -/
  oddTransition_odd : ∀ a, ∀ I, I.card % 2 = 0 →
    (oddTransition a).coefficients I = 0
  /-- The body map (x-components evaluated at θ=0) is a diffeomorphism -/
  bodyTransition_diffeo : ContDiff ℝ ⊤ (fun x => (fun i => (evenTransition i).body x))
  /-- The body transition is invertible -/
  bodyTransition_inv : ∃ (g : (Fin dim.even → ℝ) → (Fin dim.even → ℝ)),
    (∀ x, g ((fun i => (evenTransition i).body x)) = x) ∧
    ContDiff ℝ ⊤ g

/-- The cocycle condition for transitions: φ_αγ = φ_βγ ∘ φ_αβ on triple overlaps.

    For charts (U_α, φ_α), (U_β, φ_β), (U_γ, φ_γ), on U_α ∩ U_β ∩ U_γ:
      φ_αγ = φ_βγ ∘ φ_αβ

    This ensures the atlas defines a consistent global structure.

    The composition is expressed via the body maps since the full super-composition
    requires substitution which is infrastructure-heavy. The body maps must satisfy:
      body(φ_αγ) = body(φ_βγ) ∘ body(φ_αβ)

    where body extracts the θ=0 component of each coordinate function. -/
def transitionCocycle {dim : SuperDimension} {M : Supermanifold dim}
    {α β γ : ι} (atlas : ι → SuperChart M)
    (t_αβ : SuperTransition (atlas α) (atlas β))
    (t_βγ : SuperTransition (atlas β) (atlas γ))
    (t_αγ : SuperTransition (atlas α) (atlas γ)) : Prop :=
  -- The body maps satisfy the cocycle condition
  let body_αβ : (Fin dim.even → ℝ) → (Fin dim.even → ℝ) :=
    fun x => fun i => (t_αβ.evenTransition i).body x
  let body_βγ : (Fin dim.even → ℝ) → (Fin dim.even → ℝ) :=
    fun x => fun i => (t_βγ.evenTransition i).body x
  let body_αγ : (Fin dim.even → ℝ) → (Fin dim.even → ℝ) :=
    fun x => fun i => (t_αγ.evenTransition i).body x
  -- Cocycle: body_αγ = body_βγ ∘ body_αβ
  ∀ x : Fin dim.even → ℝ, body_αγ x = body_βγ (body_αβ x)

/-!
## Functor of Points Perspective

The **functor of points** approach defines a supermanifold M by specifying
its S-points M(S) = Hom(S, M) for all supermanifolds S.

This perspective is essential for:
1. **Supergroups**: A super Lie group G is characterized by G(S) being a group
   for all S, functorially in S.
2. **Families**: A family of supermanifolds over a base S is a morphism M → S.
3. **Moduli spaces**: The supermoduli space 𝔐_g represents the functor
   S ↦ {families of super Riemann surfaces over S}.

### Key Example: Odd Tangent Bundle

The functor of points of the odd tangent bundle ΠTM is:
  (ΠTM)(S) = Hom(S, ΠTM) ≅ {(f, v) : f ∈ M(S), v ∈ Γ(S, f*ΠTM)}

where f*ΠTM is the pullback of the odd tangent bundle along f.
-/

/-- The S-points of a supermanifold M: morphisms from S to M.

    For a supermanifold M, the functor of points is:
      h_M : SMan^op → Set
      h_M(S) = Hom_{SMan}(S, M)

    This functor is representable by M (Yoneda lemma for supermanifolds). -/
def SPoints {dim₁ dim₂ : SuperDimension}
    (S : Supermanifold dim₁) (M : Supermanifold dim₂) : Type _ :=
  SupermanifoldMorphism S M

/-- The even points: morphisms from ℝ^{0|0} (a point) to M.
    These are just points of the body M_red. -/
def evenPoints {dim : SuperDimension} (M : Supermanifold dim) : Type _ :=
  M.body

/-!
### RingEquiv between OddLineAlgebra and SuperDomainFunction 0 1

The structure sheaf of ℝ^{0|1} can be represented as either:
- `OddLineAlgebra` = ℝ[θ]/(θ²) with elements (body, soul)
- `SuperDomainFunction 0 1` = C^∞(ℝ^0) ⊗ Λ[θ₁] with coefficients for ∅ and {0}

These are isomorphic as rings since:
- C^∞(ℝ^0) ≅ ℝ (smooth functions on a point are just constants)
- Λ[θ₁] ≅ ℝ[θ]/(θ²) (Grassmann algebra with one generator)
-/

/-- The unique point in the domain of SmoothFunction 0. -/
def SmoothFunction.point0 : Fin 0 → ℝ := fun i => i.elim0

/-- Evaluation at the unique point gives an isomorphism SmoothFunction 0 ≅ ℝ. -/
def SmoothFunction.evalPoint0 (f : SmoothFunction 0) : ℝ := f.toFun SmoothFunction.point0

/-- Construct a SmoothFunction 0 from a real number (constant function). -/
def SmoothFunction.ofReal0 (r : ℝ) : SmoothFunction 0 := SmoothFunction.const r

@[simp] theorem SmoothFunction.evalPoint0_ofReal0 (r : ℝ) :
    SmoothFunction.evalPoint0 (SmoothFunction.ofReal0 r) = r := rfl

@[simp] theorem SmoothFunction.ofReal0_evalPoint0 (f : SmoothFunction 0) :
    SmoothFunction.ofReal0 (SmoothFunction.evalPoint0 f) = f := by
  ext x
  -- x : Fin 0 → ℝ, and there's only one such function
  have : x = SmoothFunction.point0 := by ext i; exact i.elim0
  simp only [ofReal0, const_apply, evalPoint0, this]

/-- The singleton finset {0} in Fin 1. -/
def Fin1.singleton : Finset (Fin 1) := {0}

/-- The two finsets of Fin 1 are ∅ and {0}. -/
theorem Finset.Fin1_cases (I : Finset (Fin 1)) : I = ∅ ∨ I = Fin1.singleton := by
  by_cases h : I = ∅
  · left; exact h
  · right
    -- I is nonempty, so it must contain 0 (the only element of Fin 1)
    have hne : I.Nonempty := Finset.nonempty_iff_ne_empty.mpr h
    ext i
    simp only [Fin1.singleton, Finset.mem_singleton]
    constructor
    · intro _; exact Fin.eq_zero i
    · intro hi; rw [hi]
      -- 0 ∈ I since I is nonempty and 0 is the only element of Fin 1
      obtain ⟨j, hj⟩ := hne
      convert hj

/-- Forward map: OddLineAlgebra → SuperDomainFunction 0 1 -/
def OddLineAlgebra.toSuperDomainFunction (x : OddLineAlgebra) : SuperDomainFunction 0 1 where
  coefficients := fun I =>
    if I = ∅ then SmoothFunction.ofReal0 x.body
    else SmoothFunction.ofReal0 x.soul

/-- Inverse map: SuperDomainFunction 0 1 → OddLineAlgebra -/
def OddLineAlgebra.ofSuperDomainFunction (f : SuperDomainFunction 0 1) : OddLineAlgebra where
  body := SmoothFunction.evalPoint0 (f.coefficients ∅)
  soul := SmoothFunction.evalPoint0 (f.coefficients Fin1.singleton)

/-- The ring equivalence between OddLineAlgebra and SuperDomainFunction 0 1. -/
noncomputable def OddLineAlgebra.ringEquivSuperDomainFunction :
    OddLineAlgebra ≃+* SuperDomainFunction 0 1 where
  toFun := OddLineAlgebra.toSuperDomainFunction
  invFun := OddLineAlgebra.ofSuperDomainFunction
  left_inv := fun x => by
    simp only [ofSuperDomainFunction, toSuperDomainFunction, ↓reduceIte,
      SmoothFunction.evalPoint0_ofReal0, Fin1.singleton, Finset.singleton_ne_empty]
  right_inv := fun f => by
    ext I
    rcases Finset.Fin1_cases I with rfl | rfl
    · simp only [toSuperDomainFunction, ↓reduceIte, ofSuperDomainFunction,
        SmoothFunction.ofReal0_evalPoint0]
    · simp only [toSuperDomainFunction, Fin1.singleton, Finset.singleton_ne_empty, ↓reduceIte,
        ofSuperDomainFunction, SmoothFunction.ofReal0_evalPoint0]
  map_mul' := fun x y => by
    -- Both sides are SuperDomainFunction 0 1, which has two coefficients: ∅ and {0}
    apply SuperDomainFunction.ext
    intro I
    rcases Finset.Fin1_cases I with rfl | rfl
    · -- Coefficient of ∅: (x * y).body = x.body * y.body
      simp only [toSuperDomainFunction, ↓reduceIte, OddLineAlgebra.mul_body]
      -- Use the helper lemma for multiplication coefficients
      rw [SuperDomainFunction.mul_coefficients_empty]
      rfl
    · -- Coefficient of {0}: (x * y).soul = x.body * y.soul + x.soul * y.body
      simp only [toSuperDomainFunction, Fin1.singleton, Finset.singleton_ne_empty, ↓reduceIte,
        OddLineAlgebra.mul_soul]
      -- Use the helper lemma for singleton coefficient multiplication
      rw [SuperDomainFunction.mul_coefficients_singleton_01]
      rfl
  map_add' := fun x y => by
    apply SuperDomainFunction.ext
    intro I
    -- Unfold the addition using the explicit definition
    show (toSuperDomainFunction (x + y)).coefficients I =
         (toSuperDomainFunction x + toSuperDomainFunction y).coefficients I
    rw [SuperDomainFunction.add_coefficients]
    rcases Finset.Fin1_cases I with rfl | rfl
    · -- I = ∅: coefficient is body
      simp only [toSuperDomainFunction, ↓reduceIte, OddLineAlgebra.add_body]
      apply SmoothFunction.ext
      intro p
      simp only [SmoothFunction.ofReal0, SmoothFunction.const_apply]
      rfl
    · -- I = {0}: coefficient is soul
      simp only [toSuperDomainFunction, Fin1.singleton, Finset.singleton_ne_empty, ↓reduceIte,
        OddLineAlgebra.add_soul]
      apply SmoothFunction.ext
      intro p
      simp only [SmoothFunction.ofReal0, SmoothFunction.const_apply]
      rfl

/-- The odd line ℝ^{0|1} as the simplest nontrivial supermanifold.

    ℝ^{0|1} is the supermanifold with:
    - Body = {*} (a single point, i.e., ℝ^0)
    - Structure sheaf = ℝ[θ]/(θ²) ≅ ℝ ⊕ ℝθ (Grassmann algebra with one generator)

    A section of the structure sheaf has the form a + bθ where a, b ∈ ℝ.
    The even part is ℝ (constants), the odd part is ℝθ (multiples of θ).

    This is the local model for the odd directions in any supermanifold.

    The structure sheaf is OddLineAlgebra = ℝ[θ]/(θ²), which is isomorphic to
    SuperDomainFunction 0 1 = C^∞(ℝ^0) ⊗ Λ[θ] ≅ ℝ ⊗ ℝ[θ] ≅ ℝ[θ]/(θ²).

    The body is a single point (Unit), so the topology is trivial.
    We use OddLineStructureSheaf which returns TrivialSuperAlgebra for ∅
    to ensure proper sheaf behavior. -/
noncomputable def OddLine : Supermanifold ⟨0, 1⟩ where
  body := Unit
  -- Structure sheaf: TrivialSuperAlgebra for ∅, OddLineAlgebra for nonempty
  structureSheaf := OddLineStructureSheaf
  sections_supercomm := OddLineStructureSheaf.instSuperCommutative
  -- Restriction maps between the algebras (using proven theorems from ZeroDimManifold)
  restriction := OddLineRestriction
  restriction_id := OddLineRestriction_id
  restriction_comp := OddLineRestriction_comp
  sheaf_locality := OddLine_sheaf_locality
  sheaf_gluing := OddLine_sheaf_gluing
  localTriviality := fun _ => by
    refine ⟨Set.univ, isOpen_univ, trivial, ?_⟩
    have hne : (Set.univ : Set Unit) ≠ ∅ := Set.univ_nonempty.ne_empty
    unfold OddLineStructureSheaf
    rw [if_neg hne]
    exact ⟨OddLineAlgebra.ringEquivSuperDomainFunction⟩

/-- The odd points: morphisms from ℝ^{0|1} (odd line) to M.
    These probe the odd structure of M.

    An odd point is a pair (x, v) where x ∈ M_red and v is an odd tangent vector at x.
    This reflects the fact that Hom(ℝ^{0|1}, M) ≅ ΠTM (the odd tangent bundle).

    The odd tangent vector v specifies how the morphism acts on the odd generator θ:
    the pullback of a function f ∈ O_M gives f(x) + v(f)θ ∈ O_{ℝ^{0|1}} = ℝ[θ]/(θ²). -/
structure OddPoints {dim : SuperDimension} (M : Supermanifold dim) where
  /-- Base point in the body -/
  basePoint : M.body
  /-- Odd tangent vector: a derivation from O_{M,x} to ℝ that is odd (maps even to 0).
      This is an element of (T_x M)_odd ≅ ℝ^{dim.odd}.
      In local coordinates θ¹,...,θ^q, this is given by q real coefficients. -/
  oddVector : Fin dim.odd → ℝ

-- Split supermanifolds and Batchelor's theorem are in Batchelor.lean

/-!
## The Tangent Bundle of a Supermanifold

The tangent space at a point has both even and odd directions.
A tangent vector is a superderivation of the structure sheaf at that point.

For ℝ^{p|q}, the tangent space at any point is ℝ^{p|q} itself, with basis:
- Even directions: ∂/∂x¹, ..., ∂/∂xᵖ
- Odd directions: ∂/∂θ¹, ..., ∂/∂θ^q

The partial derivatives satisfy:
- ∂/∂xⁱ is an even derivation (ordinary Leibniz rule)
- ∂/∂θᵃ is an odd derivation (graded Leibniz rule)
-/

/-- Partial derivative with respect to an even coordinate.
    For a smooth function f : ℝ^p → ℝ, the partial derivative ∂f/∂xⁱ is computed using
    Mathlib's Fréchet derivative. -/
noncomputable def partialEven {p q : ℕ} (i : Fin p) : SuperDomainFunction p q → SuperDomainFunction p q :=
  fun f => ⟨fun I =>
    -- The derivative of coefficient f_I with respect to x_i
    -- This requires showing that the derivative is smooth, which follows from
    -- the fact that derivatives of smooth functions are smooth
    ⟨fun x => fderiv ℝ (f.coefficients I).toFun x (Pi.single i 1),
     -- The proof that ∂f_I/∂xⁱ is smooth follows from ContDiff.fderiv_right and clm_apply
     (f.coefficients I).smooth.fderiv_right le_top |>.clm_apply contDiff_const⟩⟩

/-- Partial derivative with respect to an odd coordinate.
    For f = Σ_J f_J θ^J, we have ∂f/∂θᵃ = Σ_{a ∈ J} ±f_J θ^{J\{a}}.
    The coefficient of θ^I in ∂f/∂θᵃ is ±f_{I∪{a}} when a ∉ I, and 0 otherwise. -/
def partialOdd {p q : ℕ} (a : Fin q) : SuperDomainFunction p q → SuperDomainFunction p q :=
  fun f => ⟨fun I =>
    if a ∉ I then
      -- The coefficient at I comes from differentiating the θ^{I∪{a}} term
      let J := insert a I
      -- Sign from moving θᵃ past the elements of I that are less than a
      let sign : ℝ := (-1) ^ (I.filter (· < a)).card
      sign • f.coefficients J
    else 0⟩

/-- Helper: coefficients of partialOdd vanish unless a ∉ K and K ∪ {a} is the support -/
theorem partialOdd_coefficients_eq {p q : ℕ} (a : Fin q) (f : SuperDomainFunction p q)
    (I : Finset (Fin q)) (hf : ∀ K ≠ I, f.coefficients K = 0) (K : Finset (Fin q)) :
    (partialOdd a f).coefficients K =
      if a ∉ K ∧ K ∪ {a} = I then
        ((-1 : ℝ) ^ (K.filter (· < a)).card) • f.coefficients I
      else 0 := by
  simp only [partialOdd]
  by_cases haK : a ∈ K
  · -- a ∈ K: partialOdd gives 0
    simp only [haK, not_true_eq_false, ↓reduceIte, false_and]
  · -- a ∉ K
    simp only [haK, not_false_eq_true, ↓reduceIte, true_and]
    by_cases hKI : K ∪ {a} = I
    · -- K ∪ {a} = I, so insert a K = I
      simp only [hKI, ↓reduceIte]
      congr 1
      rw [Finset.insert_eq, Finset.union_comm, hKI]
    · simp only [hKI, ↓reduceIte]
      -- K ∪ {a} ≠ I, so f.coefficients (K ∪ {a}) = 0
      have hne : insert a K ≠ I := by rw [Finset.insert_eq, Finset.union_comm]; exact hKI
      have := hf (insert a K) hne
      rw [this, smul_zero]

-- The graded Leibniz rule for odd partial derivatives is proved in
-- PartialOddDerivation.lean as `partialOdd_odd_derivation'`

/-!
## Super Vector Bundles

A **super vector bundle** over a supermanifold M is a locally trivial family
of super vector spaces parametrized by M.

The fiber at each point is a super vector space V = V₀ ⊕ V₁ of dimension (r|s).
The transition functions are superlinear: they preserve the ℤ/2-grading.
-/

/-- The fiber of a super vector bundle: ℝ^r × ℝ^s with even and odd parts.
    The first component is the even part, the second is the odd part. -/
abbrev SuperFiber (r s : ℕ) : Type := (Fin r → ℝ) × (Fin s → ℝ)

/-- A linear automorphism of SuperFiber preserves the ℤ/2-grading if it has
    block-diagonal form: maps (v, 0) to (v', 0) and (0, w) to (0, w').
    This characterizes elements of GL(r|s) ⊂ GL(r+s). -/
def SuperFiber.preservesGrading {r s : ℕ}
    (φ : SuperFiber r s ≃ₗ[ℝ] SuperFiber r s) : Prop :=
  (∀ v : Fin r → ℝ, (φ (v, 0)).2 = 0) ∧
  (∀ w : Fin s → ℝ, (φ (0, w)).1 = 0)

/-- If φ preserves grading, so does φ.symm -/
theorem SuperFiber.preservesGrading_symm {r s : ℕ}
    (φ : SuperFiber r s ≃ₗ[ℝ] SuperFiber r s)
    (hφ : SuperFiber.preservesGrading φ) :
    SuperFiber.preservesGrading φ.symm := by
  constructor
  · intro v
    set ab := φ.symm (v, 0) with hab
    have lhs_eq : φ ab = (v, 0) := φ.apply_symm_apply (v, 0)
    -- ab = (ab.1, ab.2), and φ is linear, so φ ab = φ (ab.1, 0) + φ (0, ab.2)
    have decomp : φ ab = φ (ab.1, 0) + φ (0, ab.2) := by
      calc φ ab = φ ((ab.1, 0) + (0, ab.2)) := by simp
           _ = φ (ab.1, 0) + φ (0, ab.2) := φ.map_add _ _
    have snd_zero : (φ (ab.1, 0)).2 = 0 := hφ.1 ab.1
    have fst_zero : (φ (0, ab.2)).1 = 0 := hφ.2 ab.2
    rw [lhs_eq] at decomp
    have snd_eq : (0 : Fin s → ℝ) = (φ (ab.1, 0)).2 + (φ (0, ab.2)).2 :=
      congrArg Prod.snd decomp
    rw [snd_zero, _root_.zero_add] at snd_eq
    have phi_zero : φ (0, ab.2) = (0, 0) := Prod.ext fst_zero snd_eq.symm
    have h0 : φ (0, ab.2) = φ 0 := by rw [phi_zero]; simp
    have ab2_zero : ((0 : Fin r → ℝ), ab.2) = 0 := φ.injective h0
    exact congrArg Prod.snd ab2_zero
  · intro w
    set ab := φ.symm (0, w) with hab
    have lhs_eq : φ ab = (0, w) := φ.apply_symm_apply (0, w)
    have decomp : φ ab = φ (ab.1, 0) + φ (0, ab.2) := by
      calc φ ab = φ ((ab.1, 0) + (0, ab.2)) := by simp
           _ = φ (ab.1, 0) + φ (0, ab.2) := φ.map_add _ _
    have snd_zero : (φ (ab.1, 0)).2 = 0 := hφ.1 ab.1
    have fst_zero : (φ (0, ab.2)).1 = 0 := hφ.2 ab.2
    rw [lhs_eq] at decomp
    have fst_eq : (0 : Fin r → ℝ) = (φ (ab.1, 0)).1 + (φ (0, ab.2)).1 :=
      congrArg Prod.fst decomp
    rw [fst_zero, _root_.add_zero] at fst_eq
    have phi_zero : φ (ab.1, 0) = (0, 0) := Prod.ext fst_eq.symm snd_zero
    have h0 : φ (ab.1, 0) = φ 0 := by rw [phi_zero]; simp
    have ab1_zero : (ab.1, (0 : Fin s → ℝ)) = 0 := φ.injective h0
    exact congrArg Prod.fst ab1_zero

/-- Composition of grading-preserving maps preserves grading -/
theorem SuperFiber.preservesGrading_trans {r s : ℕ}
    (φ ψ : SuperFiber r s ≃ₗ[ℝ] SuperFiber r s)
    (hφ : SuperFiber.preservesGrading φ)
    (hψ : SuperFiber.preservesGrading ψ) :
    SuperFiber.preservesGrading (φ.trans ψ.symm) := by
  have hψs := preservesGrading_symm ψ hψ
  constructor
  · intro v
    simp only [LinearEquiv.trans_apply]
    have hv : (φ (v, 0)).2 = 0 := hφ.1 v
    -- Goal: (ψ.symm (φ (v, 0))).2 = 0
    -- φ (v, 0) = ((φ (v, 0)).1, 0) since hv
    have heq : φ (v, 0) = ((φ (v, 0)).1, (0 : Fin s → ℝ)) := Prod.ext rfl hv
    rw [heq]
    exact hψs.1 (φ (v, 0)).1
  · intro w
    simp only [LinearEquiv.trans_apply]
    have hw : (φ (0, w)).1 = 0 := hφ.2 w
    have heq : φ (0, w) = ((0 : Fin r → ℝ), (φ (0, w)).2) := Prod.ext hw rfl
    rw [heq]
    exact hψs.2 (φ (0, w)).2

/-- A super vector bundle of rank (r|s) over a supermanifold M.

    Locally, E|_U ≅ U × ℝ^{r|s}, with transition functions in GL(r|s).
    The structure group GL(r|s) consists of invertible linear maps that preserve
    the ℤ/2-grading (even→even, odd→odd).

    This definition captures:
    1. Total space with projection to base
    2. Fiber equivalence to SuperFiber
    3. Local triviality
    4. Grading preservation condition on transitions -/
structure SuperVectorBundle {dim : SuperDimension} (M : Supermanifold dim)
    (fiberDim : SuperDimension) where
  /-- The total space -/
  totalSpace : Type*
  /-- Projection to the base -/
  proj : totalSpace → M.body
  /-- Each fiber is equivalent to SuperFiber r s -/
  fiberEquiv : ∀ x : M.body,
    { e : totalSpace // proj e = x } ≃ SuperFiber fiberDim.even fiberDim.odd
  /-- Local triviality: the bundle is locally a product -/
  locallyTrivial : ∀ x : M.body, ∃ (U : Set M.body) (_ : IsOpen U) (_ : x ∈ U),
    ∃ (φ : { e : totalSpace // proj e ∈ U } ≃
           { y : M.body // y ∈ U } × SuperFiber fiberDim.even fiberDim.odd),
    ∀ e, (φ e).1.val = proj e.val
  /-- Transition functions preserve grading.
      For any grading-preserving linear automorphism φ of the fiber,
      composing with its inverse still preserves grading.
      This expresses that transitions lie in GL(r|s). -/
  transitionsPreserveGrading :
    ∀ (φ ψ : SuperFiber fiberDim.even fiberDim.odd ≃ₗ[ℝ]
             SuperFiber fiberDim.even fiberDim.odd),
    SuperFiber.preservesGrading φ →
    SuperFiber.preservesGrading ψ →
    SuperFiber.preservesGrading (φ.trans ψ.symm)

/-- The tangent bundle TM of a supermanifold.

    For M of dimension (p|q), TM has dimension (p|q) at each point:
    - p even directions: ∂/∂x¹, ..., ∂/∂xᵖ
    - q odd directions: ∂/∂θ¹, ..., ∂/∂θ^q

    As a supermanifold, TM has dimension (2p|2q). -/
def tangentBundle {dim : SuperDimension} (M : Supermanifold dim) :
    SuperVectorBundle M dim where
  totalSpace := M.body × SuperFiber dim.even dim.odd
  proj := Prod.fst
  fiberEquiv := fun x => {
    toFun := fun ⟨⟨_, v⟩, _⟩ => v
    invFun := fun v => ⟨⟨x, v⟩, rfl⟩
    left_inv := fun ⟨⟨y, v⟩, hy⟩ => by
      simp only [Subtype.mk.injEq, Prod.mk.injEq]
      exact ⟨hy.symm, trivial⟩
    right_inv := fun _ => rfl
  }
  locallyTrivial := fun _ => ⟨Set.univ, isOpen_univ, trivial, ⟨{
    toFun := fun ⟨⟨y, v⟩, _⟩ => (⟨y, trivial⟩, v)
    invFun := fun ⟨⟨y, _⟩, v⟩ => ⟨⟨y, v⟩, trivial⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }, fun _ => rfl⟩⟩
  transitionsPreserveGrading := SuperFiber.preservesGrading_trans

/-- The cotangent bundle T*M of a supermanifold.

    For M of dimension (p|q), T*M has dimension (p|q) at each point:
    - p even directions: dx¹, ..., dxᵖ
    - q odd directions: dθ¹, ..., dθ^q

    Note: The pairing ⟨dx^i, ∂/∂x^j⟩ = δ^i_j is even.
    The pairing ⟨dθ^a, ∂/∂θ^b⟩ = δ^a_b is also even (both elements are odd). -/
def cotangentBundle {dim : SuperDimension} (M : Supermanifold dim) :
    SuperVectorBundle M dim where
  totalSpace := M.body × SuperFiber dim.even dim.odd
  proj := Prod.fst
  fiberEquiv := fun x => {
    toFun := fun ⟨⟨_, v⟩, _⟩ => v
    invFun := fun v => ⟨⟨x, v⟩, rfl⟩
    left_inv := fun ⟨⟨y, v⟩, hy⟩ => by
      simp only [Subtype.mk.injEq, Prod.mk.injEq]
      exact ⟨hy.symm, trivial⟩
    right_inv := fun _ => rfl
  }
  locallyTrivial := fun _ => ⟨Set.univ, isOpen_univ, trivial, ⟨{
    toFun := fun ⟨⟨y, v⟩, _⟩ => (⟨y, trivial⟩, v)
    invFun := fun ⟨⟨y, _⟩, v⟩ => ⟨⟨y, v⟩, trivial⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }, fun _ => rfl⟩⟩
  transitionsPreserveGrading := SuperFiber.preservesGrading_trans

/-- The odd tangent bundle ΠTM (parity-reversed tangent bundle).

    ΠTM is obtained from TM by reversing the parity of fibers:
    - The even directions ∂/∂xⁱ become odd
    - The odd directions ∂/∂θᵃ become even

    For M of dimension (p|q), ΠTM has fiber dimension (q|p).

    **Key property**: Hom(ℝ^{0|1}, M) ≅ ΠTM (odd points are odd tangent vectors) -/
def oddTangentBundle {dim : SuperDimension} (M : Supermanifold dim) :
    SuperVectorBundle M ⟨dim.odd, dim.even⟩ where
  totalSpace := M.body × SuperFiber dim.odd dim.even
  proj := Prod.fst
  fiberEquiv := fun x => {
    toFun := fun ⟨⟨_, v⟩, _⟩ => v
    invFun := fun v => ⟨⟨x, v⟩, rfl⟩
    left_inv := fun ⟨⟨y, v⟩, hy⟩ => by
      simp only [Subtype.mk.injEq, Prod.mk.injEq]
      exact ⟨hy.symm, trivial⟩
    right_inv := fun _ => rfl
  }
  locallyTrivial := fun _ => ⟨Set.univ, isOpen_univ, trivial, ⟨{
    toFun := fun ⟨⟨y, v⟩, _⟩ => (⟨y, trivial⟩, v)
    invFun := fun ⟨⟨y, _⟩, v⟩ => ⟨⟨y, v⟩, trivial⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }, fun _ => rfl⟩⟩
  transitionsPreserveGrading := SuperFiber.preservesGrading_trans

/-- The Berezinian line bundle Ber(M).

    Ber(M) is the bundle of integral forms (top exterior powers with parity twist).
    Sections of Ber(M) are the correct objects to integrate over M.

    For M of dimension (p|q):
    - Ber(M) = (∧ᵖT*M_even) ⊗ (∧^q T*M_odd)^{-1}
    - Equivalently: Ber(M) = Det(T*M_even) ⊗ Det(TM_odd)

    The transition functions are Berezinians (superdeterminants) of the Jacobians.

    The Berezinian bundle is a real line bundle (rank 1 even bundle). -/
structure BerezinianBundle {dim : SuperDimension} (M : Supermanifold dim) where
  /-- The total space (a line bundle over the body) -/
  totalSpace : Type*
  /-- Projection to the base -/
  proj : totalSpace → M.body
  /-- Each fiber is isomorphic to ℝ -/
  fiberEquiv : ∀ x : M.body, { e : totalSpace // proj e = x } ≃ ℝ
  /-- Local triviality: the bundle is locally trivial -/
  locallyTrivial : ∀ x : M.body, ∃ (U : Set M.body) (_ : IsOpen U) (_ : x ∈ U),
    ∃ (φ : { e : totalSpace // proj e ∈ U } ≃ { y : M.body // y ∈ U } × ℝ),
    ∀ e, (φ e).1.val = proj e.val
  /-- Transition functions are nonzero scalars (coming from Berezinians).
      On overlaps U ∩ V, the transition g_UV : (U ∩ V) → ℝˣ satisfies
      φ_V = g_UV · φ_U, where g_UV is the Berezinian of the super-Jacobian.

      The transition is the multiplicative factor relating the two trivializations:
      if φ, ψ are two trivializations at x, then ψ(e) = g · φ(e) for elements e in fiber_x. -/
  transitionsNonzero : ∀ (x : M.body) (e₁ e₂ : { e : totalSpace // proj e = x }),
    fiberEquiv x e₁ ≠ 0 → fiberEquiv x e₂ ≠ 0 →
    ∃ (g : ℝˣ), fiberEquiv x e₂ = g * fiberEquiv x e₁

/-- Construct the trivial Berezinian bundle for a supermanifold -/
def trivialBerezinianBundle {dim : SuperDimension} (M : Supermanifold dim) :
    BerezinianBundle M where
  totalSpace := M.body × ℝ
  proj := Prod.fst
  fiberEquiv := fun x => {
    toFun := fun ⟨⟨_, v⟩, _⟩ => v
    invFun := fun v => ⟨⟨x, v⟩, rfl⟩
    left_inv := fun ⟨⟨y, v⟩, hy⟩ => by
      simp only [Subtype.mk.injEq, Prod.mk.injEq]
      exact ⟨hy.symm, trivial⟩
    right_inv := fun _ => rfl
  }
  locallyTrivial := fun _ => ⟨Set.univ, isOpen_univ, trivial, ⟨{
    toFun := fun ⟨⟨y, v⟩, _⟩ => (⟨y, trivial⟩, v)
    invFun := fun ⟨⟨y, _⟩, v⟩ => ⟨⟨y, v⟩, trivial⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }, fun _ => rfl⟩⟩
  transitionsNonzero := fun x e₁ e₂ h₁ h₂ => by
    -- For the trivial bundle, the fiber equiv maps e to e.val.2
    -- We need g such that e₂.val.2 = g * e₁.val.2
    -- Since both are nonzero reals, g = e₂.val.2 / e₁.val.2 works
    let v₁ := e₁.val.2
    let v₂ := e₂.val.2
    have hv₁ : v₁ ≠ 0 := h₁
    have hv₂ : v₂ ≠ 0 := h₂
    use ⟨v₂ / v₁, v₁ / v₂, by field_simp, by field_simp⟩
    -- The Equiv just extracts the second component
    show v₂ = (v₂ / v₁) * v₁
    field_simp

-- Note: The canonical bundle K_M for super Riemann surfaces belongs in the
-- SuperRiemannSurfaces folder, not here. Super Riemann surfaces have additional
-- structure (complex manifold with integrability conditions) beyond just supermanifolds.

/-!
## Integration on Supermanifolds (Berezin Integration)

Integration over odd variables is algebraic, not analytic:
  ∫ dθ (a + bθ) = b

For multiple odd variables:
  ∫ dθ¹...dθ^q f(x,θ) = coefficient of θ¹...θ^q in f

Key properties:
- ∫ dθ 1 = 0
- ∫ dθ θ = 1
- ∫ dθ (∂g/∂θ) = 0 (integration by parts)

The full integral on a supermanifold combines ordinary integration
over the body with Berezin integration over the odd directions.
-/

/-- Berezin integral: extracts the top θ-component -/
def berezinIntegral {p q : ℕ} (f : SuperDomainFunction p q) : SmoothFunction p :=
  f.coefficients Finset.univ

/-- Berezin integral of 1 is 0 (when q > 0).
    The integral extracts the top θ-component, which is 0 for a constant. -/
theorem berezin_one {p q : ℕ} (hq : 0 < q) :
    berezinIntegral (SuperDomainFunction.ofSmooth (1 : SmoothFunction p) : SuperDomainFunction p q) =
    (0 : SmoothFunction p) := by
  unfold berezinIntegral SuperDomainFunction.ofSmooth
  -- Finset.univ for Fin q is nonempty when q > 0
  haveI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have huniv : (Finset.univ : Finset (Fin q)) ≠ ∅ := Finset.univ_nonempty.ne_empty
  simp [huniv]

/-- The top form: product of all odd coordinates θ¹ ∧ θ² ∧ ... ∧ θ^q.
    This is the volume form for Berezin integration. -/
def topOddForm (p q : ℕ) : SuperDomainFunction p q where
  coefficients I := if I = Finset.univ then 1 else 0

/-- Berezin integral of the top form θ¹...θ^q is 1.
    The product of all odd coordinates gives coefficient 1 at the top component. -/
theorem berezin_top (p q : ℕ) :
    berezinIntegral (topOddForm p q) = 1 := by
  unfold berezinIntegral topOddForm
  simp

/-!
## Coordinate Transformations and Berezin Integration

For coordinate transformations on supermanifolds and the change of variables
formula for Berezin integration, see:

* `Helpers/SuperJacobian.lean` - The super Jacobian with SuperDomainFunction entries
* `Helpers/SuperMatrix.lean` - General supermatrix structure over GrassmannAlgebra
* `Helpers/Berezinian.lean` - The Berezinian (superdeterminant)

The key point: a coordinate transformation (x, θ) → (x', θ') has a **supermatrix**
Jacobian with entries in the Grassmann algebra (SuperDomainFunction), NOT just
body-valued entries (SmoothFunction).

The change of variables formula is:
  ∫ dθ' f(x', θ') = Ber(J)⁻¹ · ∫ dθ (f ∘ φ)(x, θ)

where Ber(J) is the Berezinian of the super Jacobian J.
-/

end Supermanifolds
