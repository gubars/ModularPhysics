/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Logic.Unique
import Mathlib.Logic.IsEmpty
import ModularPhysics.StringGeometry.Supermanifolds.Superalgebra

/-!
# Zero-Dimensional Manifolds

This file provides infrastructure for 0-dimensional manifolds, which are
essential for defining the supermanifold ℝ^{0|1} (the odd line).

## Main Results

* `instUniqueEuclideanSpaceFinZero` - EuclideanSpace ℝ (Fin 0) is a singleton
* `instChartedSpaceUnitEuclideanSpaceFinZero` - Unit is a 0-dimensional manifold
* `OddLineAlgebra` - The algebra ℝ[θ]/(θ²) for the structure sheaf of ℝ^{0|1}

## Mathematical Background

ℝ^{0|1} is the supermanifold with:
- Body = {*} (a single point, i.e., ℝ^0)
- Structure sheaf = ℝ[θ]/(θ²) ≅ ℝ ⊕ ℝθ (Grassmann algebra with one generator)

This is the local model for odd directions in supermanifold theory.
-/

namespace Supermanifolds

open scoped Topology Manifold

/-!
## EuclideanSpace ℝ (Fin 0) as a Singleton

EuclideanSpace ℝ (Fin 0) = PiLp 2 (fun _ : Fin 0 => ℝ) is a singleton since
Fin 0 is empty and the only function from the empty type is the empty function.
-/

/-- EuclideanSpace ℝ (Fin 0) is a singleton (isomorphic to Unit).
    This follows from the fact that it's PiLp 2 over an empty index set, and
    Fin 0 is empty, so functions from it are unique. -/
instance instUniqueEuclideanSpaceFinZero : Unique (EuclideanSpace ℝ (Fin 0)) :=
  inferInstance  -- Infers from Pi.uniqueOfIsEmpty

/-- The unique element of EuclideanSpace ℝ (Fin 0). -/
def EuclideanSpace.origin : EuclideanSpace ℝ (Fin 0) := default

/-- Any element of EuclideanSpace ℝ (Fin 0) equals the origin. -/
theorem EuclideanSpace.eq_origin (x : EuclideanSpace ℝ (Fin 0)) : x = EuclideanSpace.origin :=
  Subsingleton.elim x EuclideanSpace.origin

/-!
## Homeomorphism between Unit and EuclideanSpace ℝ (Fin 0)
-/

/-- The unique map from Unit to EuclideanSpace ℝ (Fin 0). -/
def unitToEuclideanFinZero : Unit → EuclideanSpace ℝ (Fin 0) := fun _ => EuclideanSpace.origin

/-- The unique map from EuclideanSpace ℝ (Fin 0) to Unit. -/
def euclideanFinZeroToUnit : EuclideanSpace ℝ (Fin 0) → Unit := fun _ => ()

theorem unitToEuclideanFinZero_continuous : Continuous unitToEuclideanFinZero :=
  continuous_const

theorem euclideanFinZeroToUnit_continuous : Continuous euclideanFinZeroToUnit :=
  continuous_const

/-- Unit and EuclideanSpace ℝ (Fin 0) are homeomorphic. -/
def unitHomeomorphEuclideanFinZero : Unit ≃ₜ EuclideanSpace ℝ (Fin 0) where
  toFun := unitToEuclideanFinZero
  invFun := euclideanFinZeroToUnit
  left_inv := fun _ => rfl
  right_inv := fun x => (EuclideanSpace.eq_origin x).symm
  continuous_toFun := unitToEuclideanFinZero_continuous
  continuous_invFun := euclideanFinZeroToUnit_continuous

/-!
## ChartedSpace Instance for Unit as a 0-Dimensional Manifold
-/

/-- The chart for Unit as a 0-dimensional manifold. -/
def unitChart : OpenPartialHomeomorph Unit (EuclideanSpace ℝ (Fin 0)) :=
  unitHomeomorphEuclideanFinZero.toOpenPartialHomeomorph

/-- Unit is a charted space over EuclideanSpace ℝ (Fin 0), making it a 0-dimensional manifold. -/
instance instChartedSpaceUnitEuclideanSpaceFinZero :
    ChartedSpace (EuclideanSpace ℝ (Fin 0)) Unit where
  atlas := {unitChart}
  chartAt := fun _ => unitChart
  mem_chart_source := fun _ => by simp [unitChart, Homeomorph.toOpenPartialHomeomorph]
  chart_mem_atlas := fun _ => Set.mem_singleton _

/-- Unit is a smooth manifold of dimension 0. -/
instance instIsManifoldUnitFinZero :
    IsManifold (𝓡 0) ⊤ Unit where
  compatible := by
    intro e e' he he'
    -- Both e and e' are unitChart since atlas = {unitChart}
    have he_eq : e = unitChart := Set.mem_singleton_iff.mp he
    have he'_eq : e' = unitChart := Set.mem_singleton_iff.mp he'
    rw [he_eq, he'_eq]
    constructor
    · apply contDiffOn_const
    · apply contDiffOn_const

/-!
## The Odd Line Algebra ℝ[θ]/(θ²)

The structure sheaf of ℝ^{0|1} on any open set is ℝ[θ]/(θ²),
the algebra of dual numbers over ℝ.
-/

/-- The algebra ℝ[θ]/(θ²), also known as the dual numbers.
    Elements have the form a + bθ where a, b ∈ ℝ and θ² = 0.

    This is the structure sheaf of ℝ^{0|1} over any open set. -/
structure OddLineAlgebra where
  /-- The body (even) component: coefficient of 1 -/
  body : ℝ
  /-- The soul (odd) component: coefficient of θ -/
  soul : ℝ

namespace OddLineAlgebra

/-- Extensionality for OddLineAlgebra. -/
@[ext]
theorem ext {x y : OddLineAlgebra} (hbody : x.body = y.body) (hsoul : x.soul = y.soul) :
    x = y := by
  cases x; cases y; simp only [mk.injEq]; exact ⟨hbody, hsoul⟩

instance : Zero OddLineAlgebra := ⟨⟨0, 0⟩⟩
instance : One OddLineAlgebra := ⟨⟨1, 0⟩⟩
instance : Inhabited OddLineAlgebra := ⟨0⟩

@[simp] theorem zero_body : (0 : OddLineAlgebra).body = 0 := rfl
@[simp] theorem zero_soul : (0 : OddLineAlgebra).soul = 0 := rfl
@[simp] theorem one_body : (1 : OddLineAlgebra).body = 1 := rfl
@[simp] theorem one_soul : (1 : OddLineAlgebra).soul = 0 := rfl

instance : Add OddLineAlgebra := ⟨fun x y => ⟨x.body + y.body, x.soul + y.soul⟩⟩

@[simp] theorem add_body (x y : OddLineAlgebra) : (x + y).body = x.body + y.body := rfl
@[simp] theorem add_soul (x y : OddLineAlgebra) : (x + y).soul = x.soul + y.soul := rfl

instance : Neg OddLineAlgebra := ⟨fun x => ⟨-x.body, -x.soul⟩⟩

@[simp] theorem neg_body (x : OddLineAlgebra) : (-x).body = -x.body := rfl
@[simp] theorem neg_soul (x : OddLineAlgebra) : (-x).soul = -x.soul := rfl

instance : Sub OddLineAlgebra := ⟨fun x y => ⟨x.body - y.body, x.soul - y.soul⟩⟩

/-- Multiplication in ℝ[θ]/(θ²): (a + bθ)(c + dθ) = ac + (ad + bc)θ since θ² = 0 -/
instance : Mul OddLineAlgebra := ⟨fun x y =>
  ⟨x.body * y.body, x.body * y.soul + x.soul * y.body⟩⟩

@[simp] theorem mul_body (x y : OddLineAlgebra) : (x * y).body = x.body * y.body := rfl
@[simp] theorem mul_soul (x y : OddLineAlgebra) :
    (x * y).soul = x.body * y.soul + x.soul * y.body := rfl

/-- Scalar multiplication by ℝ. -/
instance : SMul ℝ OddLineAlgebra := ⟨fun c x => ⟨c * x.body, c * x.soul⟩⟩

@[simp] theorem smul_body (c : ℝ) (x : OddLineAlgebra) : (c • x).body = c * x.body := rfl
@[simp] theorem smul_soul (c : ℝ) (x : OddLineAlgebra) : (c • x).soul = c * x.soul := rfl

/-- Natural number scalar multiplication -/
def nsmul' (n : ℕ) (x : OddLineAlgebra) : OddLineAlgebra := ⟨n * x.body, n * x.soul⟩

/-- Integer scalar multiplication -/
def zsmul' (n : ℤ) (x : OddLineAlgebra) : OddLineAlgebra := ⟨n * x.body, n * x.soul⟩

instance : AddCommGroup OddLineAlgebra where
  add_assoc x y z := by ext <;> simp <;> ring
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  neg_add_cancel x := by ext <;> simp
  add_comm x y := by ext <;> simp <;> ring
  nsmul := nsmul'
  nsmul_zero x := by ext <;> simp [nsmul']
  nsmul_succ n x := by ext <;> simp [nsmul'] <;> ring
  zsmul := zsmul'
  zsmul_zero' x := by ext <;> simp [zsmul']
  zsmul_succ' n x := by ext <;> simp [zsmul'] <;> ring
  zsmul_neg' n x := by ext <;> simp [zsmul'] <;> ring

/-- Power function -/
def npow' : ℕ → OddLineAlgebra → OddLineAlgebra
  | 0, _ => 1
  | n + 1, x => npow' n x * x

instance : Ring OddLineAlgebra where
  mul_assoc x y z := by ext <;> simp <;> ring
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  left_distrib x y z := by ext <;> simp <;> ring
  right_distrib x y z := by ext <;> simp <;> ring
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  npow := npow'
  npow_zero _ := rfl
  npow_succ _ _ := rfl

/-- The algebra map from ℝ to OddLineAlgebra embeds ℝ as the "body" part. -/
def algebraMapRingHom : ℝ →+* OddLineAlgebra where
  toFun := fun c => ⟨c, 0⟩
  map_one' := rfl
  map_mul' := fun a b => by ext <;> simp
  map_zero' := rfl
  map_add' := fun a b => by ext <;> simp

@[simp] theorem algebraMap_body (c : ℝ) : (algebraMapRingHom c).body = c := rfl
@[simp] theorem algebraMap_soul (c : ℝ) : (algebraMapRingHom c).soul = 0 := rfl

instance : Algebra ℝ OddLineAlgebra where
  smul := (· • ·)
  algebraMap := algebraMapRingHom
  commutes' c x := by
    ext
    · simp only [mul_body, algebraMap_body]; ring
    · simp only [mul_soul, algebraMap_body, algebraMap_soul]; ring
  smul_def' c x := by
    ext
    · simp only [smul_body, mul_body, algebraMap_body]
    · simp only [smul_soul, mul_soul, algebraMap_body, algebraMap_soul]; ring

/-- The odd generator θ with θ² = 0. -/
def theta : OddLineAlgebra := ⟨0, 1⟩

@[simp] theorem theta_body : theta.body = 0 := rfl
@[simp] theorem theta_soul : theta.soul = 1 := rfl

/-- θ² = 0 (the defining relation of the odd line algebra). -/
theorem theta_sq : theta * theta = 0 := by
  ext <;> simp

/-- Every element has the form body + soul * θ. -/
theorem decomposition (x : OddLineAlgebra) : x = ⟨x.body, 0⟩ + x.soul • theta := by
  ext <;> simp

/-- The projection to the body is an algebra homomorphism to ℝ. -/
def bodyHom : OddLineAlgebra →ₐ[ℝ] ℝ where
  toFun := OddLineAlgebra.body
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The kernel of bodyHom is the ideal (θ), which is nilpotent (squares to 0). -/
theorem soul_in_nilpotent_ideal (x : OddLineAlgebra) (hx : x.body = 0) :
    x * x = 0 := by
  ext
  · simp [hx]
  · simp [hx]

/-!
### SuperAlgebra Structure on OddLineAlgebra

OddLineAlgebra = ℝ[θ]/(θ²) has a natural ℤ/2-grading:
- Even part: ℝ·1 (constants)
- Odd part: ℝ·θ (multiples of θ)
-/

/-- The even submodule: elements with zero soul (pure body). -/
def evenSubmodule : Submodule ℝ OddLineAlgebra where
  carrier := { x | x.soul = 0 }
  add_mem' {x y} hx hy := by simp only [Set.mem_setOf_eq] at *; simp [hx, hy]
  zero_mem' := rfl
  smul_mem' c x hx := by simp only [Set.mem_setOf_eq] at *; simp [hx]

/-- The odd submodule: elements with zero body (multiples of θ). -/
def oddSubmodule : Submodule ℝ OddLineAlgebra where
  carrier := { x | x.body = 0 }
  add_mem' {x y} hx hy := by simp only [Set.mem_setOf_eq] at *; simp [hx, hy]
  zero_mem' := rfl
  smul_mem' c x hx := by simp only [Set.mem_setOf_eq] at *; simp [hx]

/-- Every element decomposes into even and odd parts. -/
theorem direct_sum_decomp (x : OddLineAlgebra) :
    ∃ (x₀ : evenSubmodule) (x₁ : oddSubmodule), x = x₀.val + x₁.val := by
  use ⟨⟨x.body, 0⟩, rfl⟩, ⟨⟨0, x.soul⟩, rfl⟩
  ext <;> simp

/-- Even times even is even. -/
theorem even_mul_even (x y : OddLineAlgebra) (hx : x ∈ evenSubmodule) (hy : y ∈ evenSubmodule) :
    x * y ∈ evenSubmodule := by
  show (x * y).soul = 0
  have hx' : x.soul = 0 := hx
  have hy' : y.soul = 0 := hy
  simp only [mul_soul, hx', hy', mul_zero, zero_mul, add_zero]

/-- Odd times odd is even. -/
theorem odd_mul_odd (x y : OddLineAlgebra) (hx : x ∈ oddSubmodule) (hy : y ∈ oddSubmodule) :
    x * y ∈ evenSubmodule := by
  show (x * y).soul = 0
  have hx' : x.body = 0 := hx
  have hy' : y.body = 0 := hy
  simp only [mul_soul, hx', hy', mul_zero, zero_mul, add_zero]

/-- Even times odd is odd. -/
theorem even_mul_odd (x y : OddLineAlgebra) (hx : x ∈ evenSubmodule) (hy : y ∈ oddSubmodule) :
    x * y ∈ oddSubmodule := by
  show (x * y).body = 0
  have hx' : x.soul = 0 := hx
  have hy' : y.body = 0 := hy
  simp only [mul_body, hy', mul_zero]

/-- Odd times even is odd. -/
theorem odd_mul_even (x y : OddLineAlgebra) (hx : x ∈ oddSubmodule) (hy : y ∈ evenSubmodule) :
    x * y ∈ oddSubmodule := by
  show (x * y).body = 0
  have hx' : x.body = 0 := hx
  have hy' : y.soul = 0 := hy
  simp only [mul_body, hx', zero_mul]

/-- OddLineAlgebra as a SuperAlgebra over ℝ. -/
def toSuperAlgebra : SuperAlgebra ℝ where
  carrier := OddLineAlgebra
  even := evenSubmodule
  odd := oddSubmodule
  direct_sum := direct_sum_decomp
  even_mul_even := even_mul_even
  odd_mul_odd := odd_mul_odd
  even_mul_odd := even_mul_odd
  odd_mul_even := odd_mul_even

/-- OddLineAlgebra is supercommutative: ab = (-1)^{|a||b|} ba.
    Since the only nonzero odd elements are multiples of θ and θ² = 0,
    supercommutativity follows from the fact that even elements commute
    and odd * odd = 0 (so -0 = 0). -/
instance : SuperCommutative toSuperAlgebra where
  super_comm := fun a b pa pb ha hb => by
    cases pa <;> cases pb
    · -- even * even = even * even (commutative)
      -- Goal: a * b = koszulSign even even • (b * a) = 1 • (b * a) = b * a
      simp only [↓reduceIte] at ha hb
      have ha' : a.soul = 0 := ha
      have hb' : b.soul = 0 := hb
      simp only [Parity.koszulSign_even_left, one_zsmul]
      apply OddLineAlgebra.ext
      · exact mul_comm a.body b.body
      · rw [mul_soul, mul_soul, ha', hb']; ring
    · -- even * odd: need ab = ba (koszulSign even odd = 1)
      simp only [↓reduceIte] at ha hb
      have ha' : a.soul = 0 := ha
      have hb' : b.body = 0 := hb
      simp only [Parity.koszulSign_even_left, one_zsmul]
      apply OddLineAlgebra.ext
      · rw [mul_body, mul_body, hb']; ring
      · rw [mul_soul, mul_soul, ha', hb']; ring
    · -- odd * even: need ab = ba (koszulSign odd even = 1)
      simp only [↓reduceIte] at ha hb
      have ha' : a.body = 0 := ha
      have hb' : b.soul = 0 := hb
      simp only [Parity.koszulSign_even_right, one_zsmul]
      apply OddLineAlgebra.ext
      · rw [mul_body, mul_body, ha']; ring
      · rw [mul_soul, mul_soul, ha', hb']; ring
    · -- odd * odd: ab = -ba, but both are 0 so 0 = -0
      -- ha : a ∈ toSuperAlgebra.odd, hb : b ∈ toSuperAlgebra.odd
      have ha' : a.body = 0 := ha
      have hb' : b.body = 0 := hb
      -- Goal: a * b = koszulSign odd odd • (b * a) = (-1) • (b * a)
      -- Both sides are 0 since odd * odd has body = 0 and soul = 0
      have hab : a * b = 0 := by
        apply OddLineAlgebra.ext
        · rw [mul_body, ha', zero_mul, zero_body]
        · rw [mul_soul, ha', hb', mul_zero, zero_mul, add_zero, zero_soul]
      have hba : b * a = 0 := by
        apply OddLineAlgebra.ext
        · rw [mul_body, hb', zero_mul, zero_body]
        · rw [mul_soul, ha', hb', mul_zero, zero_mul, add_zero, zero_soul]
      rw [hab, hba, smul_zero]

/-- 1 is in the even part (body = 1, soul = 0). -/
theorem one_mem_even : (1 : OddLineAlgebra) ∈ evenSubmodule := rfl

instance : SuperAlgebraWithOne toSuperAlgebra where
  one_even := one_mem_even

end OddLineAlgebra

/-!
## Trivial SuperAlgebra (for sheaf over ∅)

In sheaf theory, sections over the empty set should be a terminal object.
We define a trivial SuperAlgebra with a single element.
-/

/-- The trivial superalgebra with a single element.
    This is used for sections over the empty set in proper sheaves. -/
def TrivialSuperAlgebra : SuperAlgebra ℝ where
  carrier := Unit
  ring := inferInstance
  algebra := inferInstance
  even := ⊤  -- All elements (just ()) are even
  odd := ⊥   -- No odd elements
  direct_sum := fun x => ⟨⟨x, trivial⟩, ⟨0, Submodule.zero_mem ⊥⟩, by simp⟩
  even_mul_even := fun _ _ _ _ => trivial
  odd_mul_odd := fun _ _ hx _ => by
    have : (0 : Unit) ∈ (⊤ : Submodule ℝ Unit) := trivial
    convert this
  even_mul_odd := fun _ _ _ hy => by
    rw [Submodule.mem_bot] at hy
    rw [hy, mul_zero]
    exact Submodule.zero_mem _
  odd_mul_even := fun _ _ hx _ => by
    rw [Submodule.mem_bot] at hx
    rw [hx, zero_mul]
    exact Submodule.zero_mem _

/-- TrivialSuperAlgebra.carrier = Unit is a subsingleton -/
instance TrivialSuperAlgebra.instSubsingleton : Subsingleton TrivialSuperAlgebra.carrier :=
  inferInstanceAs (Subsingleton Unit)

instance : SuperCommutative TrivialSuperAlgebra where
  super_comm := fun _ _ _ _ _ _ => Subsingleton.elim _ _

instance : SuperAlgebraWithOne TrivialSuperAlgebra where
  one_even := trivial

open Classical in
/-- The structure sheaf for OddLine (ℝ^{0|1}).
    Returns TrivialSuperAlgebra for ∅ and OddLineAlgebra for nonempty sets.
    This ensures proper sheaf behavior where sections over ∅ are unique. -/
noncomputable def OddLineStructureSheaf (U : Set Unit) (_ : IsOpen U) : SuperAlgebra ℝ :=
  if U = ∅ then TrivialSuperAlgebra else OddLineAlgebra.toSuperAlgebra

open Classical in
/-- SuperCommutative instance for OddLineStructureSheaf -/
noncomputable instance OddLineStructureSheaf.instSuperCommutative (U : Set Unit) (hU : IsOpen U) :
    SuperCommutative (OddLineStructureSheaf U hU) := by
  unfold OddLineStructureSheaf
  split_ifs
  · exact inferInstance
  · exact inferInstance

/-!
### Infrastructure for OddLineStructureSheaf

We develop proper lemmas for working with the dependent types.
-/

/-- When U = ∅, the structure sheaf is TrivialSuperAlgebra. -/
theorem OddLineStructureSheaf_empty (hU : IsOpen (∅ : Set Unit)) :
    OddLineStructureSheaf ∅ hU = TrivialSuperAlgebra := by
  unfold OddLineStructureSheaf
  simp only [↓reduceIte]

/-- When U ≠ ∅, the structure sheaf is OddLineAlgebra.toSuperAlgebra. -/
theorem OddLineStructureSheaf_nonempty {U : Set Unit} (hU : IsOpen U) (hne : U ≠ ∅) :
    OddLineStructureSheaf U hU = OddLineAlgebra.toSuperAlgebra := by
  unfold OddLineStructureSheaf
  simp only [hne, ↓reduceIte]

/-- When U = ∅, the structure sheaf carrier equals Unit. -/
theorem OddLineStructureSheaf_carrier_empty {U : Set Unit} (hU : IsOpen U) (he : U = ∅) :
    (OddLineStructureSheaf U hU).carrier = Unit := by
  simp only [OddLineStructureSheaf, he, ↓reduceIte, TrivialSuperAlgebra]

/-- Cast carrier when we know U = ∅. Uses Equiv.cast for proper reduction. -/
def OddLineCarrier_cast_empty {U : Set Unit} (hU : IsOpen U) (he : U = ∅) :
    (OddLineStructureSheaf U hU).carrier ≃ Unit :=
  Equiv.cast (OddLineStructureSheaf_carrier_empty hU he)

/-- Cast carrier when we know U ≠ ∅. Uses Equiv.cast for proper reduction. -/
def OddLineCarrier_cast_nonempty {U : Set Unit} (hU : IsOpen U) (hne : U ≠ ∅) :
    (OddLineStructureSheaf U hU).carrier ≃ OddLineAlgebra :=
  Equiv.cast (congr_arg SuperAlgebra.carrier (OddLineStructureSheaf_nonempty hU hne))

/-!
### Restriction maps for OddLineStructureSheaf

For Unit, open sets are ∅ and Set.univ. Restriction maps:
- Set.univ → Set.univ: identity on OddLineAlgebra
- Set.univ → ∅: projection OddLineAlgebra → Unit (returns ())
- ∅ → ∅: identity on Unit
-/

open Classical in
/-- Restriction map for OddLineStructureSheaf.
    Defined using explicit casts. -/
noncomputable def OddLineRestriction (U V : Set Unit) (hU : IsOpen U) (hV : IsOpen V)
    (_ : V ⊆ U) : (OddLineStructureSheaf U hU).carrier → (OddLineStructureSheaf V hV).carrier :=
  if hUe : U = ∅ then
    -- U = ∅: carrier is Unit
    fun _ => (OddLineCarrier_cast_empty hV (Set.subset_eq_empty ‹V ⊆ U› hUe)).symm ()
  else if hVe : V = ∅ then
    -- U ≠ ∅, V = ∅: map OddLineAlgebra → Unit
    fun _ => (OddLineCarrier_cast_empty hV hVe).symm ()
  else
    -- U ≠ ∅, V ≠ ∅: both carriers are OddLineAlgebra, identity
    fun s => (OddLineCarrier_cast_nonempty hV hVe).symm
               ((OddLineCarrier_cast_nonempty hU hUe) s)

open Classical in
/-- Restriction is identity on the same set. -/
theorem OddLineRestriction_id (U : Set Unit) (hU : IsOpen U)
    (s : (OddLineStructureSheaf U hU).carrier) :
    OddLineRestriction U U hU hU (Set.Subset.refl U) s = s := by
  unfold OddLineRestriction
  split_ifs with hUe
  · -- U = ∅: both sides are in carrier of TrivialSuperAlgebra = Unit
    have : Subsingleton (OddLineStructureSheaf U hU).carrier := by
      simp only [OddLineStructureSheaf, hUe, ↓reduceIte]
      exact TrivialSuperAlgebra.instSubsingleton
    exact Subsingleton.elim _ _
  · -- U ≠ ∅: use Equiv.symm_apply_apply
    exact (OddLineCarrier_cast_nonempty hU hUe).symm_apply_apply s

open Classical in
/-- Restriction composes correctly. -/
theorem OddLineRestriction_comp (U V W : Set Unit) (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hVU : V ⊆ U) (hWV : W ⊆ V) (s : (OddLineStructureSheaf U hU).carrier) :
    OddLineRestriction V W hV hW hWV (OddLineRestriction U V hU hV hVU s) =
    OddLineRestriction U W hU hW (hWV.trans hVU) s := by
  -- Result is in W's carrier. If W = ∅, it's Unit (singleton), otherwise it's OddLineAlgebra.
  by_cases hWe : W = ∅
  · -- W = ∅: result is in Unit (singleton)
    have hSubsing : Subsingleton (OddLineStructureSheaf W hW).carrier := by
      simp only [OddLineStructureSheaf, hWe, ↓reduceIte]
      exact TrivialSuperAlgebra.instSubsingleton
    exact Subsingleton.elim _ _
  · -- W ≠ ∅: All sets are nonempty (since W ⊆ V ⊆ U and W ≠ ∅)
    have hVe : V ≠ ∅ := fun h => hWe (Set.subset_eq_empty hWV h)
    have hUe : U ≠ ∅ := fun h => hVe (Set.subset_eq_empty hVU h)
    -- Unfold and simplify
    unfold OddLineRestriction
    simp only [hUe, hVe, hWe, dif_neg, not_false_eq_true]
    -- Goal: castW⁻¹ (castV (castV⁻¹ (castU s))) = castW⁻¹ (castU s)
    -- Use: castV (castV⁻¹ x) = x
    rw [(OddLineCarrier_cast_nonempty hV hVe).apply_symm_apply]

open Classical in
/-- Sheaf locality for OddLineStructureSheaf. -/
theorem OddLine_sheaf_locality (U : Set Unit) (hU : IsOpen U)
    (ι : Type*) (V : ι → Set Unit) (hV : ∀ i, IsOpen (V i)) (hVU : ∀ i, V i ⊆ U)
    (hcover : U = ⋃ i, V i) (s t : (OddLineStructureSheaf U hU).carrier)
    (h : ∀ i, OddLineRestriction U (V i) hU (hV i) (hVU i) s =
              OddLineRestriction U (V i) hU (hV i) (hVU i) t) : s = t := by
  by_cases hUe : U = ∅
  · -- U = ∅: carrier is Unit (singleton)
    have hSubsing : Subsingleton (OddLineStructureSheaf U hU).carrier := by
      simp only [OddLineStructureSheaf, hUe, ↓reduceIte]
      exact TrivialSuperAlgebra.instSubsingleton
    exact Subsingleton.elim s t
  · -- U ≠ ∅: find an index with nonempty V i, use h at that index
    have hne : U.Nonempty := Set.nonempty_iff_ne_empty.mpr hUe
    rw [hcover] at hne
    obtain ⟨i, x, hxi⟩ := Set.nonempty_iUnion.mp hne
    have hVi : V i ≠ ∅ := Set.nonempty_iff_ne_empty.mp ⟨x, hxi⟩
    -- The restriction map for nonempty sets is an equiv, so h i implies s = t
    have hi := h i
    unfold OddLineRestriction at hi
    simp only [hUe, hVi, dif_neg, not_false_eq_true] at hi
    -- hi : castV⁻¹ (castU s) = castV⁻¹ (castU t)
    -- Apply castV to both sides, then castU⁻¹
    have hi' := congr_arg (OddLineCarrier_cast_nonempty (hV i) hVi) hi
    simp only [Equiv.apply_symm_apply] at hi'
    -- hi' : castU s = castU t
    exact (OddLineCarrier_cast_nonempty hU hUe).injective hi'

open Classical in
/-- Sheaf gluing for OddLineStructureSheaf. -/
theorem OddLine_sheaf_gluing (U : Set Unit) (hU : IsOpen U)
    (ι : Type*) (V : ι → Set Unit) (hV : ∀ i, IsOpen (V i)) (hVU : ∀ i, V i ⊆ U)
    (hcover : U = ⋃ i, V i) (s : ∀ i, (OddLineStructureSheaf (V i) (hV i)).carrier)
    (hcompat : ∀ i j,
      OddLineRestriction (V i) (V i ∩ V j) (hV i) (IsOpen.inter (hV i) (hV j)) Set.inter_subset_left (s i) =
      OddLineRestriction (V j) (V i ∩ V j) (hV j) (IsOpen.inter (hV i) (hV j)) Set.inter_subset_right (s j)) :
    ∃ t : (OddLineStructureSheaf U hU).carrier,
      ∀ i, OddLineRestriction U (V i) hU (hV i) (hVU i) t = s i := by
  by_cases hUe : U = ∅
  · -- U = ∅: all V i = ∅, any element works (carrier is Unit)
    have hSubsingU : Subsingleton (OddLineStructureSheaf U hU).carrier := by
      simp only [OddLineStructureSheaf, hUe, ↓reduceIte]
      exact TrivialSuperAlgebra.instSubsingleton
    -- Pick any element
    refine ⟨(OddLineCarrier_cast_empty hU hUe).symm (), fun i => ?_⟩
    have hVi : V i = ∅ := Set.subset_eq_empty (hVU i) hUe
    have hSubsingVi : Subsingleton (OddLineStructureSheaf (V i) (hV i)).carrier := by
      simp only [OddLineStructureSheaf, hVi, ↓reduceIte]
      exact TrivialSuperAlgebra.instSubsingleton
    exact Subsingleton.elim _ _
  · -- U ≠ ∅: find a representative index i₀ with V i₀ nonempty
    have hne : U.Nonempty := Set.nonempty_iff_ne_empty.mpr hUe
    rw [hcover] at hne
    obtain ⟨i₀, x₀, hx₀⟩ := Set.nonempty_iUnion.mp hne
    have hVi₀ : V i₀ ≠ ∅ := Set.nonempty_iff_ne_empty.mp ⟨x₀, hx₀⟩
    -- Construct the global section from s i₀
    -- s i₀ : (OddLineStructureSheaf (V i₀) (hV i₀)).carrier, which is OddLineAlgebra since V i₀ ≠ ∅
    let si₀_alg : OddLineAlgebra := (OddLineCarrier_cast_nonempty (hV i₀) hVi₀) (s i₀)
    -- Lift to global section
    let t : (OddLineStructureSheaf U hU).carrier := (OddLineCarrier_cast_nonempty hU hUe).symm si₀_alg
    refine ⟨t, fun i => ?_⟩
    by_cases hVi : V i = ∅
    · -- V i = ∅: carrier is Unit, any two elements are equal
      have hSubsingVi : Subsingleton (OddLineStructureSheaf (V i) (hV i)).carrier := by
        simp only [OddLineStructureSheaf, hVi, ↓reduceIte]
        exact TrivialSuperAlgebra.instSubsingleton
      exact Subsingleton.elim _ _
    · -- V i ≠ ∅: Use compatibility to show restriction of t equals s i
      -- The restriction of t to V i is: castVi⁻¹ (castU t) = castVi⁻¹ (si₀_alg)
      unfold OddLineRestriction
      simp only [hUe, hVi, dif_neg, not_false_eq_true]
      -- Goal: castVi⁻¹ (castU t) = s i
      -- Since t = castU⁻¹ si₀_alg, we have castU t = si₀_alg
      show (OddLineCarrier_cast_nonempty (hV i) hVi).symm
             ((OddLineCarrier_cast_nonempty hU hUe) t) = s i
      rw [show (OddLineCarrier_cast_nonempty hU hUe) t = si₀_alg from
          (OddLineCarrier_cast_nonempty hU hUe).apply_symm_apply si₀_alg]
      -- Goal: castVi⁻¹ si₀_alg = s i
      -- Use compatibility: restrictions of s i₀ and s i to intersection agree
      have hc := hcompat i₀ i
      unfold OddLineRestriction at hc
      -- V i₀ ∩ V i is nonempty since Unit has only one element and both V i₀, V i are nonempty
      have hInt : V i₀ ∩ V i ≠ ∅ := by
        have ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hVi
        have hx₀Vi : x₀ ∈ V i := by convert hy
        exact Set.nonempty_iff_ne_empty.mp ⟨x₀, hx₀, hx₀Vi⟩
      simp only [hVi₀, hVi, hInt, dif_neg, not_false_eq_true] at hc
      -- hc : castInt⁻¹ (castVi₀ (s i₀)) = castInt⁻¹ (castVi (s i))
      -- Apply castInt to both sides
      have hc' := congr_arg (OddLineCarrier_cast_nonempty (IsOpen.inter (hV i₀) (hV i)) hInt) hc
      simp only [Equiv.apply_symm_apply] at hc'
      -- hc' : castVi₀ (s i₀) = castVi (s i)
      -- By definition si₀_alg = castVi₀ (s i₀)
      -- Goal: castVi⁻¹ si₀_alg = s i, i.e., castVi⁻¹ (castVi₀ (s i₀)) = s i
      -- Substitute using hc': castVi⁻¹ (castVi (s i)) = s i
      show (OddLineCarrier_cast_nonempty (hV i) hVi).symm si₀_alg = s i
      rw [show si₀_alg = (OddLineCarrier_cast_nonempty (hV i) hVi) (s i) from hc']
      exact (OddLineCarrier_cast_nonempty (hV i) hVi).symm_apply_apply (s i)

end Supermanifolds
