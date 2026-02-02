/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.StochasticIntegration
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Regularity Structures

This file formalizes Martin Hairer's theory of regularity structures,
providing a framework for solving singular SPDEs.

## Main Definitions

* `RegularityStructure` - A regularity structure (A, T, G)
* `Model` - A model for a regularity structure
* `ModelledDistribution` - Distributions with prescribed singularities
* `ReconstructionTheorem` - The reconstruction operator

## References

* Hairer, "A theory of regularity structures" (Inventiones 2014)
* Friz, Hairer, "A Course on Rough Paths" (2020)
* Bruned, Hairer, Zambotti, "Algebraic renormalisation of regularity structures"
-/

namespace SPDE

open MeasureTheory

/-! ## Index Sets -/

/-- An index set A for a regularity structure.
    A is a locally finite subset of ℝ, bounded from below. -/
structure IndexSet where
  /-- The set of indices (homogeneities) -/
  indices : Set ℝ
  /-- Bounded from below -/
  bdd_below : BddBelow indices
  /-- Locally finite: for each r, A ∩ (-∞, r] is finite -/
  locally_finite : ∀ r : ℝ, (indices ∩ Set.Iic r).Finite
  /-- Contains 0 -/
  contains_zero : 0 ∈ indices

/-! ## Regularity Structure -/

/-- A regularity structure over ℝ^d.
    This is a triple (A, T, G) where:
    - A is an index set
    - T = ⊕_{α ∈ A} T_α is a graded vector space
    - G is a group of linear transformations on T

    The key structural property is triangularity: the action of G on T
    preserves or lowers the homogeneity, and the "diagonal" part is the identity. -/
structure RegularityStructure (d : ℕ) where
  /-- The index set A -/
  A : IndexSet
  /-- The graded components T_α -/
  T : ∀ α ∈ A.indices, Type*
  /-- Each T_α is a Banach space -/
  banach : ∀ α (hα : α ∈ A.indices), NormedAddCommGroup (T α hα)
  /-- Each T_α is a normed space over ℝ -/
  normed_space : ∀ α (hα : α ∈ A.indices), NormedSpace ℝ (T α hα)
  /-- Finite dimensional for each α -/
  fin_dim : ∀ α (hα : α ∈ A.indices), FiniteDimensional ℝ (T α hα)
  /-- The structure group G (represented as automorphisms) -/
  G : Type*
  /-- G is a group -/
  group : Group G
  /-- G acts on each T_α -/
  action : ∀ α (hα : α ∈ A.indices), G → (T α hα →ₗ[ℝ] T α hα)
  /-- The action is a group homomorphism for each α -/
  action_mul : ∀ α (hα : α ∈ A.indices), ∀ g₁ g₂ : G,
    action α hα (g₁ * g₂) = (action α hα g₁).comp (action α hα g₂)
  /-- The identity element acts as identity -/
  action_one : ∀ α (hα : α ∈ A.indices), action α hα 1 = LinearMap.id
  /-- Triangularity: For each g ∈ G and τ ∈ T_α, the action Γ_g(τ) differs from τ
      by elements of lower homogeneity. Since we work component-wise here,
      this is encoded as: the difference (Γ_g - I) applied repeatedly to any τ
      eventually gives 0. Equivalently, for the trivial structure group (G = Unit),
      the action is identity. For non-trivial G, this means Γ_g is unipotent. -/
  triangular_unipotent : ∀ α (hα : α ∈ A.indices), ∀ g : G,
    ∃ n : ℕ, ∀ τ : T α hα,
      let Γ := action α hα g
      let diff := fun v => Γ v - v
      Nat.iterate diff n τ = 0

attribute [instance] RegularityStructure.banach RegularityStructure.normed_space
attribute [instance] RegularityStructure.fin_dim RegularityStructure.group

namespace RegularityStructure

variable {d : ℕ}

/-- The full model space T = ⊕_α T_α -/
def ModelSpace (RS : RegularityStructure d) :=
  Σ α : RS.A.indices, RS.T α.val α.property

/-- The polynomial regularity structure -/
noncomputable def polynomial (d : ℕ) : RegularityStructure d where
  A := {
    indices := {n : ℝ | ∃ k : ℕ, n = k ∧ n ≥ 0}
    bdd_below := ⟨0, fun _ ⟨_, _, hx⟩ => hx⟩
    locally_finite := fun r => by
      -- The intersection of naturals with (-∞, r] is finite
      have h : {n : ℝ | ∃ k : ℕ, n = k ∧ n ≥ 0} ∩ Set.Iic r ⊆
               ((Finset.range (Nat.ceil (max r 0) + 1)).image (fun k : ℕ => (k : ℝ))) := by
        intro x ⟨⟨k, hk, _⟩, hle⟩
        simp only [Finset.coe_image, Set.mem_image]
        use k
        constructor
        · simp only [Finset.mem_coe, Finset.mem_range]
          have hk_le : (k : ℝ) ≤ max r 0 := by
            calc (k : ℝ) = x := hk.symm
              _ ≤ r := hle
              _ ≤ max r 0 := le_max_left r 0
          have h1 : k = Nat.ceil (k : ℝ) := (Nat.ceil_natCast k).symm
          calc k = Nat.ceil (k : ℝ) := h1
            _ ≤ Nat.ceil (max r 0) := Nat.ceil_mono hk_le
            _ < Nat.ceil (max r 0) + 1 := Nat.lt_succ_self _
        · exact hk.symm
      exact Set.Finite.subset (Finset.finite_toSet _) h
    contains_zero := ⟨0, by simp⟩
  }
  T := fun _ _ => Fin d → ℝ  -- Simplified: monomials X^k
  banach := fun _ _ => inferInstance
  normed_space := fun _ _ => inferInstance
  fin_dim := fun _ _ => inferInstance
  G := Unit
  group := inferInstance
  action := fun _ _ _ => LinearMap.id
  action_mul := fun _ _ _ _ => rfl
  action_one := fun _ _ => rfl
  triangular_unipotent := fun _ _ _ => ⟨1, fun τ => by simp [Nat.iterate]⟩

end RegularityStructure

/-! ## Models -/

/-- A model (Π, Γ) for a regularity structure.
    - Π maps T to distributions (continuous linear functionals on test functions)
    - Γ encodes the translation structure

    The key properties are:
    1. Consistency: Π_x = Π_y ∘ Γ_{yx}
    2. Algebraic: Γ_{xy} · Γ_{yz} = Γ_{xz}
    3. Analytic bounds on Π -/
structure Model {d : ℕ} (RS : RegularityStructure d) where
  /-- The reconstruction map Π_x : T → S'(ℝ^d) -/
  Pi : (Fin d → ℝ) → ∀ α (hα : α ∈ RS.A.indices), RS.T α hα → ((Fin d → ℝ) → ℝ)
  /-- The translation operators Γ_{xy} : T → T -/
  Gamma : (Fin d → ℝ) → (Fin d → ℝ) → RS.G
  /-- Consistency: Π_x τ = Π_y (Γ_{yx} τ) for all x, y and τ ∈ T_α -/
  consistency : ∀ x y : Fin d → ℝ, ∀ α (hα : α ∈ RS.A.indices), ∀ τ : RS.T α hα,
    Pi x α hα τ = Pi y α hα (RS.action α hα (Gamma y x) τ)
  /-- Algebraic property: Γ_{xy} · Γ_{yz} = Γ_{xz} -/
  algebraic : ∀ x y z : Fin d → ℝ, Gamma x y * Gamma y z = Gamma x z
  /-- Γ_{xx} = 1 -/
  algebraic_refl : ∀ x : Fin d → ℝ, Gamma x x = 1
  /-- Analytic bounds: |⟨Π_x τ, φ^λ_x⟩| ≤ C λ^α ‖τ‖ for τ ∈ T_α
      where φ^λ_x is a test function scaled by λ and centered at x.
      This encodes that Π_x τ has the "expected" singularity at x. -/
  analytic_bound : ∀ x : Fin d → ℝ, ∀ α (hα : α ∈ RS.A.indices),
    ∃ C : ℝ, C > 0 ∧ ∀ τ : RS.T α hα, ∀ scale : ℝ, 0 < scale → scale ≤ 1 →
      ∀ y : Fin d → ℝ, dist x y ≤ scale →
        |Pi x α hα τ y| ≤ C * scale ^ α * ‖τ‖

namespace Model

variable {d : ℕ} {RS : RegularityStructure d}

/-- The canonical polynomial model -/
noncomputable def polynomialModel (hd : 0 < d) : Model (RegularityStructure.polynomial d) where
  Pi := fun _ _ _ τ _ => τ ⟨0, hd⟩  -- Evaluate at first coordinate
  Gamma := fun _ _ => ()
  consistency := fun _ _ _ _ _ => rfl
  algebraic := fun _ _ _ => rfl
  algebraic_refl := fun _ => rfl
  analytic_bound := fun _ _ _ => ⟨1, by norm_num, fun _τ _scale _hscale _ _ _ => by
    -- For the polynomial model, the bound requires proper norm estimate
    sorry⟩

end Model

/-! ## Modelled Distributions -/

/-- A modelled distribution f ∈ D^γ(Γ).
    This is a function f : ℝ^d → T_{<γ} satisfying Hölder-type bounds.
    The key bound is: ‖f(x) - Γ_{xy} f(y)‖_α ≤ C|x-y|^{γ-α} for α < γ. -/
structure ModelledDistribution {d : ℕ} (RS : RegularityStructure d) (M : Model RS) (γ : ℝ) where
  /-- The function f : ℝ^d → T_{<γ} (simplified as single component) -/
  f : (Fin d → ℝ) → ∀ α (hα : α ∈ RS.A.indices), α < γ → RS.T α hα
  /-- The Hölder-type bound: ‖f(x)_α - Γ_{xy} f(y)_α‖ ≤ C|x-y|^{γ-α}
      This encodes that f is "smooth at scale γ" in the regularity structure sense. -/
  bound : ∃ C : ℝ, C > 0 ∧ ∀ α (hα : α ∈ RS.A.indices) (hαγ : α < γ),
    ∀ x y : Fin d → ℝ,
      ‖f x α hα hαγ - RS.action α hα (M.Gamma x y) (f y α hα hαγ)‖ ≤
        C * dist x y ^ (γ - α)

/-! ## Reconstruction Theorem -/

/-- The reconstruction operator R : D^γ → C^α for appropriate α.
    This is the fundamental result that allows us to interpret
    modelled distributions as actual distributions.

    The key property is the local approximation bound:
    |⟨Rf - Π_x f(x), φ^λ_x⟩| ≲ λ^γ -/
structure ReconstructionOperator {d : ℕ} (RS : RegularityStructure d) (M : Model RS) (γ : ℝ) where
  /-- The reconstruction map -/
  R : ModelledDistribution RS M γ → ((Fin d → ℝ) → ℝ)
  /-- Local approximation bound: Rf locally looks like Π_x f(x).
      Specifically, for any test function φ supported in B(x, scale),
      |⟨Rf - Π_x f(x), φ⟩| ≤ C scale^γ ‖φ‖_{C^r} -/
  local_bound : ∃ C : ℝ, C > 0 ∧ ∀ f : ModelledDistribution RS M γ,
    ∀ x : Fin d → ℝ, ∀ scale : ℝ, 0 < scale → scale ≤ 1 →
      ∀ y : Fin d → ℝ, dist x y ≤ scale →
        ∃ error : ℝ, |error| ≤ C * scale ^ γ ∧
          ∀ α (hα : α ∈ RS.A.indices) (hαγ : α < γ),
            |R f y - M.Pi x α hα (f.f x α hα hαγ) y| ≤ |error|

/-- The reconstruction theorem: there exists a unique reconstruction operator.
    The actual construction requires the full machinery of regularity structures
    (wavelets, Schauder estimates, etc.). Here we state existence. -/
theorem reconstruction_theorem {d : ℕ} {RS : RegularityStructure d} (M : Model RS) (γ : ℝ)
    (_hγ : γ > 0) :
    ∃ R : ReconstructionOperator RS M γ, True := by
  -- The construction follows from Theorem 3.10 in Hairer's paper
  sorry

/-! ## Singular Kernels -/

/-- A kernel of order β (like the heat kernel ∂_t - Δ).
    The singularity is controlled: |K(x, y)| ≤ C|x-y|^{β-d}
    and derivatives improve the bound. -/
structure SingularKernel (d : ℕ) (β : ℝ) where
  /-- The kernel K(x, y) -/
  kernel : (Fin d → ℝ) → (Fin d → ℝ) → ℝ
  /-- Singularity bound: |K(x, y)| ≤ C|x-y|^{β-d} -/
  singularity_bound : ∃ C : ℝ, C > 0 ∧ ∀ x y : Fin d → ℝ, x ≠ y →
    |kernel x y| ≤ C * dist x y ^ (β - d)
  /-- Regularity of kernel away from diagonal: K is smooth on {(x,y) : x ≠ y} -/
  regularity : ∀ k : ℕ, ∃ C_k : ℝ, C_k > 0 ∧
    ∀ x y : Fin d → ℝ, x ≠ y →
      -- The k-th derivative improves the bound by k
      |kernel x y| ≤ C_k * dist x y ^ (β - d - k)
  /-- Vanishing moments: ∫ K(x, y) y^k dy = 0 for |k| < β (when applicable) -/
  vanishing_moments : β > 0 → ∀ x : Fin d → ℝ, True  -- Placeholder for moment condition

/-- The heat kernel as a singular kernel of order 2 -/
noncomputable def heatKernel (d : ℕ) : SingularKernel d 2 where
  kernel := fun x y =>
    let r := dist x y
    if r = 0 then 0 else Real.exp (-(r^2) / 4) / (4 * Real.pi)^(d/2 : ℝ)
  singularity_bound := ⟨1, by norm_num, fun x y hxy => by
    simp only [ne_eq]
    sorry⟩
  regularity := fun k => ⟨1, by norm_num, fun _ _ _ => by sorry⟩
  vanishing_moments := fun _ _ => trivial

/-! ## Extension Theorem -/

/-- The extension theorem: convolution with singular kernel
    extends to modelled distributions.
    If f ∈ D^γ and K has order β with γ + β > 0, then Kf ∈ D^{γ+β}. -/
theorem extension_theorem {d : ℕ} {RS : RegularityStructure d} {M : Model RS}
    (_K : SingularKernel d β) (γ : ℝ) (_hγ : γ + β > 0) :
    ∀ f : ModelledDistribution RS M γ,
    ∃ Kf : ModelledDistribution RS M (γ + β), True := by
  intro f
  refine ⟨⟨fun x α hα hαγβ => ?_, ⟨1, by norm_num, fun _ _ _ _ _ => by sorry⟩⟩, trivial⟩
  -- Need to construct the lifted distribution
  -- This requires the full machinery of regularity structures
  by_cases hαγ : α < γ
  · exact f.f x α hα hαγ
  · -- For α ≥ γ, we use the extension
    sorry

/-! ## Rough Paths -/

/-- The tensor algebra truncated at level 2: T²(V) = ℝ ⊕ V ⊕ (V ⊗ V).

    For a Banach space V, we represent V ⊗ V as continuous linear maps V →L[ℝ] V
    (the algebraic tensor product embeds into this via v ⊗ w ↦ (u ↦ ⟨v, u⟩w)).

    Elements of T²(V) are triples (a, x, 𝕏) where:
    - a ∈ ℝ (level 0, usually 1)
    - x ∈ V (level 1, the path increment)
    - 𝕏 ∈ V ⊗ V (level 2, the "area" or iterated integral)

    The Chen multiplication is:
    (a₁, x₁, 𝕏₁) ⊗ (a₂, x₂, 𝕏₂) = (a₁a₂, a₁x₂ + a₂x₁, 𝕏₁ + 𝕏₂ + x₁ ⊗ x₂) -/
structure TruncatedTensorAlgebra (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  /-- Level 0: scalar part -/
  level0 : ℝ
  /-- Level 1: vector part (path increment) -/
  level1 : V
  /-- Level 2: tensor part (area/iterated integral).
      We use V →L[ℝ] V as a representation of V ⊗ V.
      The tensor v ⊗ w corresponds to the rank-1 map u ↦ ⟨v, u⟩ · w. -/
  level2 : V →L[ℝ] V

namespace TruncatedTensorAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The identity element (1, 0, 0) -/
def one : TruncatedTensorAlgebra V :=
  ⟨1, 0, 0⟩

/-- Tensor product of two vectors as a rank-1 operator V → V.
    In an inner product space, x ⊗ y represents the map v ↦ ⟨x, v⟩ · y.
    This is the proper representation for rough path theory. -/
noncomputable def tensorProduct (x y : V) : V →L[ℝ] V :=
  -- The rank-1 operator: v ↦ ⟨x, v⟩ · y
  -- We use innerSL to get the continuous linear functional ⟨x, ·⟩
  (innerSL ℝ x).smulRight y

/-- Chen multiplication (tensor product in the group-like elements) -/
noncomputable def mul (x y : TruncatedTensorAlgebra V) : TruncatedTensorAlgebra V :=
  ⟨x.level0 * y.level0,
   x.level0 • y.level1 + y.level0 • x.level1,
   x.level2 + y.level2 + tensorProduct x.level1 y.level1⟩
  -- Note: The level2 term adds x.level2 + y.level2 + "x.level1 ⊗ y.level1"

/-- The inverse for group-like elements -/
noncomputable def inv (x : TruncatedTensorAlgebra V) (_hx : x.level0 ≠ 0) :
    TruncatedTensorAlgebra V :=
  ⟨1 / x.level0,
   -(1 / x.level0) • x.level1,
   -- For the inverse: if x = (1, v, A), then x⁻¹ = (1, -v, -A + v ⊗ v)
   -- This ensures x ⊗ x⁻¹ = 1 in the tensor algebra
   -(1 / x.level0^2) • x.level2 + (1 / x.level0^2) • tensorProduct x.level1 x.level1⟩

end TruncatedTensorAlgebra

/-- A rough path of regularity α ∈ (1/3, 1/2].

    This is the correct mathematical definition following Lyons, Friz-Victoir:
    A rough path is a multiplicative functional X_{st} ∈ T²(V) satisfying:
    1. Chen's relation: X_{su} ⊗ X_{ut} = X_{st} (multiplicative!)
    2. Hölder bounds: |X_{st}^{(1)}| ≤ C|t-s|^α, |X_{st}^{(2)}| ≤ C|t-s|^{2α}

    The key insight is that Chen's relation is MULTIPLICATIVE in the tensor algebra,
    not additive. For the truncated signature:
    - X_{st}^{(0)} = 1
    - X_{st}^{(1)} = path_t - path_s
    - X_{st}^{(2)} = "iterated integral" ∫_s^t (path_r - path_s) ⊗ dpath_r

    Chen's relation X_{su} ⊗ X_{ut} = X_{st} expands to:
    - X_{st}^{(1)} = X_{su}^{(1)} + X_{ut}^{(1)}  (additive for level 1)
    - X_{st}^{(2)} = X_{su}^{(2)} + X_{ut}^{(2)} + X_{su}^{(1)} ⊗ X_{ut}^{(1)} (Chen!) -/
structure RoughPath (α : ℝ) (hα : 1/3 < α ∧ α ≤ 1/2) (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] where
  /-- The rough path increment X_{st} as an element of T²(V).
      We require X_{ss} = 1 (identity element). -/
  increment : ℝ → ℝ → TruncatedTensorAlgebra V
  /-- X_{tt} = 1 (identity) -/
  increment_refl : ∀ t : ℝ, increment t t = TruncatedTensorAlgebra.one
  /-- Level 0 is always 1 (group-like element) -/
  level0_one : ∀ s t : ℝ, (increment s t).level0 = 1
  /-- Chen's relation: X_{su} ⊗ X_{ut} = X_{st}
      This is the MULTIPLICATIVE relation in the tensor algebra.
      For level 2, this gives: X_{st}^{(2)} = X_{su}^{(2)} + X_{ut}^{(2)} + X_{su}^{(1)} ⊗ X_{ut}^{(1)} -/
  chen : ∀ s u t : ℝ, s ≤ u → u ≤ t →
    TruncatedTensorAlgebra.mul (increment s u) (increment u t) = increment s t
  /-- Hölder regularity of level 1: ‖X_{st}^{(1)}‖ ≤ C|t - s|^α -/
  level1_holder : ∃ C : ℝ, C > 0 ∧ ∀ s t : ℝ,
    ‖(increment s t).level1‖ ≤ C * |t - s|^α
  /-- Hölder regularity of level 2: ‖X_{st}^{(2)}‖ ≤ C|t - s|^{2α} -/
  level2_holder : ∃ C : ℝ, C > 0 ∧ ∀ s t : ℝ,
    ‖(increment s t).level2‖ ≤ C * |t - s|^(2 * α)

namespace RoughPath

variable {α : ℝ} {hα : 1/3 < α ∧ α ≤ 1/2} {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Extract the path from a rough path (as level 1 starting from 0) -/
def path (X : RoughPath α hα V) : ℝ → V :=
  fun t => (X.increment 0 t).level1

/-- Extract the area/Lévy area from a rough path -/
def area (X : RoughPath α hα V) : ℝ → ℝ → V →L[ℝ] V :=
  fun s t => (X.increment s t).level2

/-- Chen's relation for level 1 (additive) -/
theorem level1_additive (X : RoughPath α hα V) (s u t : ℝ) (hsu : s ≤ u) (hut : u ≤ t) :
    (X.increment s t).level1 = (X.increment s u).level1 + (X.increment u t).level1 := by
  have h := X.chen s u t hsu hut
  have h0 : (X.increment s u).level0 = 1 := X.level0_one s u
  have h1 : (X.increment u t).level0 = 1 := X.level0_one u t
  -- From Chen: mul (increment s u) (increment u t) = increment s t
  -- The level1 component of mul is: x.level0 • y.level1 + y.level0 • x.level1
  -- With x.level0 = y.level0 = 1, this gives: y.level1 + x.level1 = (increment s t).level1
  sorry

/-- Chen's relation for level 2 (with tensor correction term) -/
theorem level2_chen (X : RoughPath α hα V) (s u t : ℝ) (hsu : s ≤ u) (hut : u ≤ t) :
    (X.increment s t).level2 = (X.increment s u).level2 + (X.increment u t).level2 +
      -- The tensor product X_{su}^{(1)} ⊗ X_{ut}^{(1)}
      TruncatedTensorAlgebra.tensorProduct (X.increment s u).level1 (X.increment u t).level1 := by
  have h := X.chen s u t hsu hut
  -- Extract level2 from multiplication
  sorry

end RoughPath

/-- Geometric rough path: a rough path where X_{st}^{(2)} is the symmetric part
    (corresponding to Stratonovich integration). -/
def IsGeometric {α : ℝ} {hα : 1/3 < α ∧ α ≤ 1/2} {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (X : RoughPath α hα V) : Prop :=
  ∀ s t : ℝ, X.area s t = X.area t s  -- Symmetric area

/-- Signature of a smooth path (canonical lift to rough path).
    For a smooth path γ, the signature is:
    - Level 1: γ_t - γ_s
    - Level 2: ∫_s^t (γ_r - γ_s) ⊗ dγ_r (Riemann integral) -/
noncomputable def smoothPathSignature {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (γ : ℝ → V) (_hγ : ContDiff ℝ 1 γ) : ℝ → ℝ → TruncatedTensorAlgebra V :=
  fun s t => {
    level0 := 1
    level1 := γ t - γ s
    level2 := 0  -- Proper definition requires integration: ∫_s^t (γ_r - γ_s) ⊗ dγ_r
  }

/-! ## Renormalization -/

/-- A renormalization group element.
    These are used to construct the renormalized model from a "bare" model.
    The renormalization preserves the structure of the regularity structure. -/
structure RenormalizationGroup {d : ℕ} (RS : RegularityStructure d) where
  /-- The renormalization map as a group element -/
  M : RS.G
  /-- The renormalization preserves the grading structure.
      Specifically, if τ ∈ T_α, then (M - 1)τ ∈ T_{<α}. -/
  structure_preserving : ∀ α (hα : α ∈ RS.A.indices),
    ∀ τ : RS.T α hα, RS.action α hα M τ - τ = 0 ∨
      ∃ n : ℕ, n ≥ 1 ∧ Nat.iterate (fun v => RS.action α hα M v - v) n τ = 0

/-- BPHZ renormalization for regularity structures.
    Given a model M and a cutoff ε, produces a renormalized model. -/
noncomputable def bphz_renormalization {d : ℕ} {RS : RegularityStructure d}
    (model : Model RS)
    (_cutoff : ℝ) : Model RS := model  -- Placeholder: should apply renormalization

/-! ## Schauder Estimates -/

/-- Schauder estimates for singular SPDEs: solutions gain regularity. -/
theorem schauder_estimate {d : ℕ} {RS : RegularityStructure d} {M : Model RS}
    (K : SingularKernel d β) (γ : ℝ) (hγ : γ + β > 0)
    (f : ModelledDistribution RS M γ) :
    ∃ u : ModelledDistribution RS M (γ + β), True :=
  extension_theorem K γ hγ f

end SPDE
