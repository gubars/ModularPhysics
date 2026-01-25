/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import ModularPhysics.RigorousQFT.Wightman.Basic

/-!
# Operator-Valued Distributions

This file provides a rigorous mathematical foundation for operator-valued distributions
(OVDs), which are essential for the Wightman formulation of quantum field theory.

## Main Definitions

* `OperatorValuedDistribution` - A map from Schwartz test functions to (possibly unbounded)
  operators on a Hilbert space, satisfying appropriate continuity and linearity properties.
* `OperatorValuedDistribution.isHermitian` - Property that φ(f)* = φ(f̄) for real f
* `OperatorValuedDistribution.domain` - The common domain for all φ(f)

## Mathematical Background

In the Wightman framework, quantum fields are operator-valued distributions. A field φ
is not a pointwise operator φ(x), but rather assigns to each test function f ∈ 𝒮(ℝ^d)
an operator φ(f) on the Hilbert space of states.

The key requirements are:
1. **Linearity**: f ↦ φ(f) is linear
2. **Domain**: There exists a dense domain D ⊂ H such that φ(f)D ⊂ D for all f
3. **Continuity**: For each ψ, χ ∈ D, the map f ↦ ⟨χ, φ(f)ψ⟩ is a tempered distribution

## References

* Streater-Wightman, "PCT, Spin and Statistics, and All That", Chapter 3
* Reed-Simon, "Methods of Modern Mathematical Physics II", Chapter X
* Wightman-Gårding, "Fields as operator-valued distributions"
-/

noncomputable section

open scoped SchwartzMap InnerProductSpace
open Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (d : ℕ) [NeZero d]

/-! ### Basic definitions for operator-valued distributions -/

/-- The spacetime dimension type for Schwartz functions.
    For d spatial dimensions, spacetime is ℝ^{d+1}. -/
abbrev SpacetimeDim (d : ℕ) := Fin (d + 1) → ℝ

/-- Schwartz space on d+1 dimensional spacetime with complex values -/
abbrev SchwartzSpacetime (d : ℕ) := SchwartzMap (SpacetimeDim d) ℂ

/-- A dense subspace of a Hilbert space, used as the domain for field operators.
    We use a Submodule with an additional density hypothesis. -/
structure DenseSubspace (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The underlying submodule -/
  toSubmodule : Submodule ℂ H
  /-- Density: the closure equals the whole space -/
  dense : Dense (toSubmodule : Set H)

namespace DenseSubspace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Membership: x ∈ D means x is in the underlying submodule -/
instance instMembership : Membership H (DenseSubspace H) where
  mem := fun (D : DenseSubspace H) (x : H) => x ∈ D.toSubmodule

/-- The zero vector is in any dense subspace -/
theorem zero_mem (D : DenseSubspace H) : (0 : H) ∈ D :=
  Submodule.zero_mem D.toSubmodule

/-- Addition is closed -/
theorem add_mem (D : DenseSubspace H) {x y : H} (hx : x ∈ D) (hy : y ∈ D) : x + y ∈ D :=
  Submodule.add_mem D.toSubmodule hx hy

/-- Scalar multiplication is closed -/
theorem smul_mem (D : DenseSubspace H) {x : H} (hx : x ∈ D) (c : ℂ) : c • x ∈ D :=
  Submodule.smul_mem D.toSubmodule c hx

end DenseSubspace

/-- An operator-valued distribution is a map from Schwartz test functions to
    operators on a Hilbert space, with a common dense domain.

    The key property distinguishing this from arbitrary operator-valued maps is
    the continuity requirement: for any χ, ψ in the domain, the matrix element
    f ↦ ⟨χ, φ(f)ψ⟩ must be a tempered distribution (continuous linear functional
    on the Schwartz space). -/
structure OperatorValuedDistribution (d : ℕ) [NeZero d]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The common dense domain for all field operators -/
  domain : DenseSubspace H
  /-- The field operator applied to a test function f -/
  operator : SchwartzSpacetime d → (H → H)
  /-- Linearity of the field: φ(f + g) = φ(f) + φ(g) -/
  operator_add : ∀ f g : SchwartzSpacetime d, ∀ ψ ∈ domain,
    operator (f + g) ψ = operator f ψ + operator g ψ
  /-- Scalar linearity: φ(c·f) = c·φ(f) -/
  operator_smul : ∀ (c : ℂ) (f : SchwartzSpacetime d), ∀ ψ ∈ domain,
    operator (c • f) ψ = c • operator f ψ
  /-- Domain invariance: φ(f) maps D to D -/
  operator_domain : ∀ f : SchwartzSpacetime d, ∀ ψ ∈ domain, operator f ψ ∈ domain
  /-- Temperedness: for any χ, ψ ∈ D, the matrix element f ↦ ⟨χ, φ(f)ψ⟩ is continuous.
      This makes f ↦ ⟨χ, φ(f)ψ⟩ a tempered distribution on 𝒮(ℝ^{d+1}). -/
  matrix_element_continuous : ∀ χ ψ : H, χ ∈ domain → ψ ∈ domain →
    Continuous (fun f : SchwartzSpacetime d => ⟪χ, operator f ψ⟫_ℂ)

namespace OperatorValuedDistribution

variable {d : ℕ} [NeZero d]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The matrix element ⟨χ, φ(f)ψ⟩ as a function of f -/
def matrixElement (φ : OperatorValuedDistribution d H)
    (χ ψ : H) (hχ : χ ∈ φ.domain) (hψ : ψ ∈ φ.domain) :
    SchwartzSpacetime d → ℂ :=
  fun f => ⟪χ, φ.operator f ψ⟫_ℂ

/-- A field is hermitian (self-adjoint) if ⟨φ(f)χ, ψ⟩ = ⟨χ, φ(f̄)ψ⟩.
    Here f̄ denotes pointwise complex conjugation of the test function.
    For real-valued test functions, this implies φ(f) is symmetric. -/
def IsHermitian (φ : OperatorValuedDistribution d H)
    (conj : SchwartzSpacetime d → SchwartzSpacetime d) : Prop :=
  ∀ (f : SchwartzSpacetime d) (χ ψ : H),
    χ ∈ φ.domain → ψ ∈ φ.domain →
    ⟪φ.operator f χ, ψ⟫_ℂ = ⟪χ, φ.operator (conj f) ψ⟫_ℂ

/-- The n-fold application of field operators: φ(f₁)φ(f₂)···φ(fₙ)ψ
    Applied right-to-left: φ(fₙ) is applied first, then φ(fₙ₋₁), ..., then φ(f₁). -/
def operatorPow (φ : OperatorValuedDistribution d H) :
    (n : ℕ) → (Fin n → SchwartzSpacetime d) → H → H
  | 0, _, ψ => ψ
  | n + 1, fs, ψ =>
    let ψ' := operatorPow φ n (fun i => fs (Fin.succ i)) ψ
    φ.operator (fs 0) ψ'

/-- The n-fold application preserves the domain -/
theorem operatorPow_domain (φ : OperatorValuedDistribution d H)
    (n : ℕ) (fs : Fin n → SchwartzSpacetime d) (ψ : H) (hψ : ψ ∈ φ.domain) :
    φ.operatorPow n fs ψ ∈ φ.domain := by
  induction n with
  | zero => exact hψ
  | succ n ih =>
    simp only [operatorPow]
    exact φ.operator_domain _ _ (ih _)

/-- The algebraic span of vectors φ(f₁)···φ(fₙ)Ω -/
def algebraicSpan (φ : OperatorValuedDistribution d H) (Ω : H) : Submodule ℂ H :=
  Submodule.span ℂ { ψ | ∃ (n : ℕ) (fs : Fin n → SchwartzSpacetime d), ψ = φ.operatorPow n fs Ω }

end OperatorValuedDistribution

/-! ### Wightman n-point functions -/

/-- The Wightman n-point function W_n(f₁, ..., fₙ) = ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩.
    This is the vacuum expectation value of the product of smeared fields. -/
def WightmanNPoint (φ : OperatorValuedDistribution d H)
    (Ω : H) (n : ℕ) : (Fin n → SchwartzSpacetime d) → ℂ :=
  fun fs => ⟪Ω, φ.operatorPow n fs Ω⟫_ℂ

/-- The 2-point Wightman function (propagator) -/
def Wightman2Point (φ : OperatorValuedDistribution d H)
    (Ω : H) : SchwartzSpacetime d → SchwartzSpacetime d → ℂ :=
  fun f g => WightmanNPoint d φ Ω 2 ![f, g]

namespace WightmanNPoint

variable {d : ℕ} [NeZero d]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The 0-point function is 1 (assuming Ω is normalized).
    W_0 = ⟨Ω, Ω⟩ = ‖Ω‖² = 1 -/
theorem zero_point (d : ℕ) [NeZero d] (φ : OperatorValuedDistribution d H)
    (Ω : H) (hΩ_norm : ‖Ω‖ = 1) :
    _root_.WightmanNPoint d φ Ω 0 (fun _ => 0) = 1 := by
  simp only [WightmanNPoint]
  -- operatorPow 0 fs Ω = Ω by definition
  -- so ⟨Ω, Ω⟩ = ‖Ω‖² = 1
  sorry

/-- Linearity in an argument: W_n is linear in each test function slot.
    The full proof requires careful handling of Fin indices. -/
theorem linear_arg (d : ℕ) [NeZero d] (φ : OperatorValuedDistribution d H)
    (Ω : H) (n : ℕ) (k : Fin n)
    (f g : SchwartzSpacetime d) (fs : Fin n → SchwartzSpacetime d) :
    _root_.WightmanNPoint d φ Ω n (Function.update fs k (f + g)) =
    _root_.WightmanNPoint d φ Ω n (Function.update fs k f) +
    _root_.WightmanNPoint d φ Ω n (Function.update fs k g) := by
  sorry

end WightmanNPoint

/-! ### Covariance under Poincaré transformations -/

/-- A unitary representation of the Poincaré group on the Hilbert space -/
structure PoincareRepresentation (d : ℕ) [NeZero d]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The representation map -/
  U : PoincareGroup d → (H →L[ℂ] H)
  /-- Unitarity: U(g)* U(g) = 1 -/
  unitary : ∀ g, (U g).adjoint.comp (U g) = ContinuousLinearMap.id ℂ H
  /-- Group homomorphism property -/
  mul_map : ∀ g₁ g₂, U (g₁ * g₂) = (U g₁).comp (U g₂)
  /-- Identity maps to identity -/
  one_map : U 1 = ContinuousLinearMap.id ℂ H

namespace PoincareRepresentation

variable {d : ℕ} [NeZero d]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The energy-momentum operators (generators of translations) -/
def momentum (π : PoincareRepresentation d H) : Fin (d + 1) → (H → H) :=
  fun μ => fun ψ => sorry  -- Defined via Stone's theorem from the translation part

/-- The Hamiltonian (time component of momentum) -/
def hamiltonian (π : PoincareRepresentation d H) : H → H :=
  π.momentum 0

/-- The spatial momentum operators -/
def spatialMomentum (π : PoincareRepresentation d H) : Fin d → (H → H) :=
  fun i => π.momentum (Fin.succ i)

end PoincareRepresentation

/-- The action of a Poincaré transformation on a test function as a plain function.
    (g · f)(x) = f(g⁻¹ · x) where g · x = Λx + a.

    The Schwartz class is preserved under Poincaré transformations (linear transformations
    preserve rapid decrease), but proving this requires substantial analysis machinery. -/
def poincareActionOnTestFun (g : PoincareGroup d) (f : SpacetimeDim d → ℂ) :
    SpacetimeDim d → ℂ :=
  fun x => f (PoincareGroup.act g⁻¹ x)

/-- Covariance of a field under Poincaré transformations (weak form).

    For scalar fields, the covariance condition is:
      U(g) φ(f) U(g)⁻¹ = φ(g · f)
    where (g · f)(x) = f(g⁻¹ · x).

    This weak formulation expresses covariance at the level of the underlying
    functions, avoiding the need to prove that Poincaré action preserves
    the Schwartz class (which it does, but requires more analysis infrastructure). -/
def IsCovariantWeak (φ : OperatorValuedDistribution d H)
    (π : PoincareRepresentation d H)
    (poincareActionOnSchwartz : PoincareGroup d → SchwartzSpacetime d → SchwartzSpacetime d)
    : Prop :=
  ∀ (g : PoincareGroup d) (f : SchwartzSpacetime d) (χ ψ : H)
    (hχ : χ ∈ φ.domain) (hψ : ψ ∈ φ.domain),
    ⟪π.U g χ, φ.operator f (π.U g ψ)⟫_ℂ =
    ⟪χ, φ.operator (poincareActionOnSchwartz g f) ψ⟫_ℂ

end

