/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import ModularPhysics.RigorousQFT.Wightman.Basic
import ModularPhysics.RigorousQFT.Wightman.OperatorDistribution

/-!
# Wightman Axioms

This file provides a rigorous mathematical formulation of the Wightman axioms for
quantum field theory. The axioms are formalized as a structure `WightmanQFT` that
contains all the required data and properties.

## Main Definitions

* `WightmanQFT` - The complete structure satisfying all Wightman axioms
* `WightmanQFT.spectrumCondition` - Energy-momentum spectrum lies in forward light cone
* `WightmanQFT.locality` - Spacelike-separated fields commute

## The Wightman Axioms

The Wightman axioms (W1-W4) as formalized here:

**W1 (Covariance)**:
- There is a continuous unitary representation U of the Poincaré group on H
- The generators P_μ (energy-momentum) have spectrum in the forward light cone V₊
- There exists a unique vacuum vector Ω invariant under U(g)

**W2 (Field Operators)**:
- There exist field operators φ(f) for each test function f ∈ 𝒮(ℝ^{d+1})
- The domain D is dense and invariant under all φ(f)
- The subspace spanned by φ(f₁)···φ(fₙ)Ω is dense in H
- The field is covariant: U(g) φ(f) U(g)⁻¹ = φ(f ∘ g⁻¹)

**W3 (Locality)**:
- If supp(f) and supp(g) are spacelike separated, then [φ(f), φ(g)] = 0 on D

**W4 (Vacuum Uniqueness)**:
- The vacuum Ω is the unique vector (up to phase) invariant under time translations

## References

* Streater-Wightman, "PCT, Spin and Statistics, and All That"
* Glimm-Jaffe, "Quantum Physics: A Functional Integral Point of View"
* Haag, "Local Quantum Physics"
-/

noncomputable section

open scoped SchwartzMap InnerProductSpace
open Topology

variable (d : ℕ) [NeZero d]

/-! ### Spectrum Condition -/

/-- The forward light cone in momentum space: p₀ ≥ 0, p² ≤ 0.
    In the mostly positive signature, p² = -p₀² + |p⃗|², so p² ≤ 0 means p₀ ≥ |p⃗|.
    This is the region where timelike and lightlike momenta with positive energy lie. -/
def ForwardMomentumCone : Set (MinkowskiSpace d) :=
  MinkowskiSpace.ClosedForwardLightCone d

/-- The spectrum condition: the joint spectrum of the energy-momentum operators
    lies in the closed forward light cone.

    Mathematically: For any state ψ in the domain of the momentum operators,
    the spectral support of ψ (the support of its spectral measure) lies in V̄₊.

    Equivalently, for any translation-covariant state:
      ⟨ψ, U(a) ψ⟩ = ∫_{V̄₊} e^{ip·a} dμ_ψ(p)

    where V̄₊ = {p : p₀ ≥ 0 and p² ≤ 0} is the closed forward light cone
    (in mostly positive signature, p² = -p₀² + |p⃗|² ≤ 0 means p₀ ≥ |p⃗|).

    We express this via the Fourier transform of the 2-point function having
    support in the forward cone. -/
structure SpectralCondition (d : ℕ) [NeZero d]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : PoincareRepresentation d H) : Prop where
  /-- The energy is non-negative: for all states ψ, ⟨ψ, Hψ⟩ ≥ 0 where H = P₀ -/
  energy_nonneg : ∀ ψ : H, (⟪ψ, π.hamiltonian ψ⟫_ℂ).re ≥ 0
  /-- The mass-shell condition: p² ≤ 0 (in mostly positive signature).
      For any state ψ, the expectation value of P² = -P₀² + Σᵢ Pᵢ² is ≤ 0.
      This encodes that the spectral support lies in the forward cone. -/
  mass_shell : ∀ ψ : H, (⟪ψ, π.hamiltonian (π.hamiltonian ψ)⟫_ℂ).re ≥
    ∑ i : Fin d, (⟪ψ, π.spatialMomentum i (π.spatialMomentum i ψ)⟫_ℂ).re

/-! ### Locality -/

/-- Two Schwartz functions have spacelike-separated supports -/
def AreSpacelikeSeparatedSupports (f g : SchwartzSpacetime d) : Prop :=
  ∀ x ∈ Function.support f, ∀ y ∈ Function.support g,
    MinkowskiSpace.AreSpacelikeSeparated d x y

/-- The commutator of two operators on a domain -/
def Commutator {H : Type*} [AddCommGroup H] [Module ℂ H]
    (A B : H → H) (D : Set H) : Prop :=
  ∀ ψ ∈ D, A (B ψ) = B (A ψ)

/-- Locality: spacelike-separated fields commute -/
def IsLocal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : OperatorValuedDistribution d H) : Prop :=
  ∀ f g : SchwartzSpacetime d,
    AreSpacelikeSeparatedSupports d f g →
    Commutator (φ.operator f) (φ.operator g) φ.domain.toSubmodule

/-! ### Vacuum Properties -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A vector is invariant under the Poincaré representation -/
def IsPoincareInvariant (π : PoincareRepresentation d H) (Ω : H) : Prop :=
  ∀ g : PoincareGroup d, π.U g Ω = Ω

/-- A vector is invariant under time translations only -/
def IsTimeTranslationInvariant (π : PoincareRepresentation d H) (Ω : H) : Prop :=
  ∀ t : ℝ, π.U (PoincareGroup.translation' (fun i => if i = 0 then t else 0)) Ω = Ω

/-- Uniqueness of the vacuum: Ω is the unique (up to phase) translation-invariant vector -/
def VacuumUnique (π : PoincareRepresentation d H) (Ω : H) : Prop :=
  IsTimeTranslationInvariant d π Ω ∧
  ∀ ψ : H, IsTimeTranslationInvariant d π ψ → ∃ c : ℂ, ψ = c • Ω

/-! ### The Complete Wightman QFT Structure -/

/-- A Wightman quantum field theory consists of:
    - A Hilbert space H (the state space)
    - A unitary representation of the Poincaré group
    - Field operators satisfying the Wightman axioms

    This structure encapsulates all the Wightman axioms (W1-W4). -/
structure WightmanQFT (d : ℕ) [NeZero d] where
  /-- The Hilbert space of states -/
  HilbertSpace : Type*
  /-- Hilbert space is a normed additive commutative group -/
  [instNormedAddCommGroup : NormedAddCommGroup HilbertSpace]
  /-- Hilbert space has inner product structure -/
  [instInnerProductSpace : InnerProductSpace ℂ HilbertSpace]
  /-- Hilbert space is complete -/
  [instCompleteSpace : CompleteSpace HilbertSpace]

  -- W1: Poincaré Covariance and Spectrum Condition
  /-- The unitary representation of the Poincaré group -/
  poincare_rep : @PoincareRepresentation d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace
  /-- Spectrum condition: energy-momentum spectrum in forward cone -/
  spectrum_condition : @SpectralCondition d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace poincare_rep
  /-- The vacuum vector -/
  vacuum : HilbertSpace
  /-- The vacuum is normalized -/
  vacuum_normalized : @norm HilbertSpace instNormedAddCommGroup.toNorm vacuum = 1
  /-- The vacuum is Poincaré invariant -/
  vacuum_invariant : @IsPoincareInvariant d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace poincare_rep vacuum

  -- W2: Field Operators
  /-- The field operator-valued distribution -/
  field : @OperatorValuedDistribution d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace
  /-- The vacuum is in the domain -/
  vacuum_in_domain : vacuum ∈ field.domain
  /-- Cyclicity: the algebraic span of field operators on vacuum is dense -/
  cyclicity : @Dense HilbertSpace (instNormedAddCommGroup.toUniformSpace.toTopologicalSpace)
              (field.algebraicSpan vacuum).carrier
  /-- The action of Poincaré transformations on test functions.
      (g · f)(x) = f(g⁻¹ · x) where g · x = Λx + a.

      Note: Proving that Poincaré transformations preserve the Schwartz class
      requires substantial analysis infrastructure. We include this as data
      with the understanding that the underlying function is poincareActionOnTestFun. -/
  poincareActionOnSchwartz : PoincareGroup d → SchwartzSpacetime d → SchwartzSpacetime d
  /-- Covariance: U(g) φ(f) U(g)⁻¹ = φ(g·f) where (g·f)(x) = f(g⁻¹·x).

      Expressed via matrix elements: for all g ∈ ISO(1,d), f ∈ 𝒮, and ψ, χ ∈ D,
        ⟨U(g)χ, φ(f) U(g)ψ⟩ = ⟨χ, φ(g·f) ψ⟩

      For scalar fields, the field transforms as:
        U(g) φ(f) U(g)⁻¹ = φ(g·f)

      This is equivalent to: ⟨U(g)χ, φ(f) U(g)ψ⟩ = ⟨χ, φ(g·f) ψ⟩ by unitarity. -/
  covariance : ∀ (g : PoincareGroup d) (f : SchwartzSpacetime d) (χ ψ : HilbertSpace),
    χ ∈ field.domain → ψ ∈ field.domain →
    ⟪poincare_rep.U g χ, field.operator f (poincare_rep.U g ψ)⟫_ℂ =
    ⟪χ, field.operator (poincareActionOnSchwartz g f) ψ⟫_ℂ

  -- W3: Locality
  /-- Locality: spacelike-separated fields commute -/
  locality : @IsLocal d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace field

  -- W4: Vacuum Uniqueness
  /-- Uniqueness of vacuum -/
  vacuum_unique : @VacuumUnique d _ HilbertSpace instNormedAddCommGroup instInnerProductSpace instCompleteSpace poincare_rep vacuum

namespace WightmanQFT

variable {d : ℕ} [NeZero d]

-- Expose instances from WightmanQFT for use in definitions
attribute [instance] WightmanQFT.instNormedAddCommGroup
attribute [instance] WightmanQFT.instInnerProductSpace
attribute [instance] WightmanQFT.instCompleteSpace

/-- The Wightman n-point functions of a Wightman QFT.
    W_n(f₁,...,fₙ) = ⟨Ω, φ(f₁)···φ(fₙ)Ω⟩ -/
def wightmanFunction (qft : WightmanQFT d) (n : ℕ) :
    (Fin n → SchwartzSpacetime d) → ℂ :=
  fun fs => ⟪qft.vacuum, qft.field.operatorPow n fs qft.vacuum⟫_ℂ

/-- The 2-point function (propagator) W₂(f,g) = ⟨Ω, φ(f)φ(g)Ω⟩ -/
def twoPointFunction (qft : WightmanQFT d) :
    SchwartzSpacetime d → SchwartzSpacetime d → ℂ :=
  fun f g => qft.wightmanFunction 2 ![f, g]

/-- Symmetry property for bosonic fields: [φ(f), φ(g)] = 0 for any f, g -/
def IsBosonic (qft : WightmanQFT d) : Prop :=
  ∀ f g : SchwartzSpacetime d,
    Commutator (qft.field.operator f) (qft.field.operator g) qft.field.domain.toSubmodule

/-- The Reeh-Schlieder property: the vacuum is cyclic for local algebras.
    For any open region O, the vectors φ(f₁)···φ(fₙ)Ω with supp(fᵢ) ⊆ O are dense. -/
def ReehSchlieder (qft : WightmanQFT d) (O : Set (SpacetimeDim d)) : Prop :=
  let localSpan := Submodule.span ℂ
    { ψ | ∃ (n : ℕ) (fs : Fin n → SchwartzSpacetime d),
      (∀ i, Function.support (fs i) ⊆ O) ∧
      ψ = qft.field.operatorPow n fs qft.vacuum }
  Dense localSpan.carrier

/-- The Wightman functions are positive (reflection positivity).
    ‖φ(f₁)···φ(fₙ)Ω‖² ≥ 0, equivalently Re⟨ψ, ψ⟩ ≥ 0.
    For inner products in Hilbert space, ⟨ψ, ψ⟩ is real and equals ‖ψ‖². -/
def WightmanPositivity (qft : WightmanQFT d) : Prop :=
  ∀ n : ℕ, ∀ fs : Fin n → SchwartzSpacetime d,
    (⟪qft.field.operatorPow n fs qft.vacuum, qft.field.operatorPow n fs qft.vacuum⟫_ℂ).re ≥ 0

/-- Hermiticity of the 2-point function: W₂(f, g)* = W₂(ḡ, f̄).
    This follows from the hermiticity of the field. -/
def TwoPointHermitian (qft : WightmanQFT d) : Prop :=
  ∀ f g : SchwartzSpacetime d,
    starRingEnd ℂ (qft.twoPointFunction f g) = qft.twoPointFunction g f

end WightmanQFT

/-! ### Wightman Functions as Distributions -/

/-- The n-point domain: n copies of (d+1)-dimensional spacetime.
    Points are functions Fin n → Fin (d+1) → ℝ, i.e., n spacetime points. -/
abbrev NPointSpacetime (d n : ℕ) := Fin n → Fin (d + 1) → ℝ

/-- Schwartz space on n copies of spacetime -/
abbrev SchwartzNPointSpace (d n : ℕ) := SchwartzMap (NPointSpacetime d n) ℂ

/-- The Wightman n-point function as a distribution on n-point test functions.

    The smeared Wightman function W_n(F) for F ∈ 𝒮(ℝ^{n(d+1)}) is defined by:
      W_n(F) = ∫ dx₁...dxₙ W_n(x₁,...,xₙ) F(x₁,...,xₙ)

    For product test functions F = f₁ ⊗ ... ⊗ fₙ, this equals ⟨Ω, φ(f₁)...φ(fₙ)Ω⟩.
    The nuclear theorem guarantees extension to general test functions. -/
def WightmanDistribution (qft : WightmanQFT d) (n : ℕ) :
    SchwartzNPointSpace d n → ℂ :=
  fun F => sorry  -- Would require tensor product infrastructure to properly define

/-- Temperedness of Wightman functions: W_n extends to a continuous linear
    functional on the Schwartz space 𝒮(ℝ^{n(d+1)}).

    Mathematically, this means f ↦ W_n(f) is a tempered distribution, i.e.,
    there exist C > 0 and seminorm indices such that |W_n(f)| ≤ C · ‖f‖_{α,β}
    for all test functions f.

    This is expressed as continuity with respect to the Schwartz topology. -/
def WightmanTempered (qft : WightmanQFT d) (n : ℕ) : Prop :=
  Continuous (WightmanDistribution d qft n)

/-! ### Analytic Continuation -/

/-- A vector η ∈ ℝ^{d+1} lies in the open forward light cone V₊ if η₀ > 0 and η² < 0. -/
def InOpenForwardCone (d : ℕ) [NeZero d] (η : Fin (d + 1) → ℝ) : Prop :=
  η 0 > 0 ∧ MinkowskiSpace.minkowskiNormSq d η < 0

/-- The forward tube T_n in n copies of complexified spacetime.

    T_n = {(z₁,...,zₙ) ∈ ℂ^{n(d+1)} : Im(z₁) ∈ V₊, Im(z₂-z₁) ∈ V₊, ..., Im(zₙ-zₙ₋₁) ∈ V₊}

    where V₊ is the open forward light cone {η : η₀ > 0, η² < 0}.

    This is the domain to which Wightman functions analytically continue.

    We define the successive difference of imaginary parts η_k and require each
    to lie in V₊. -/
def ForwardTube (d n : ℕ) [NeZero d] : Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | ∀ k : Fin n,
    let prev : Fin (d + 1) → ℂ := if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩
    let η : Fin (d + 1) → ℝ := fun μ => (z k μ - prev μ).im
    InOpenForwardCone d η }

/-- The extended forward tube T_n^{ext} obtained by Lorentz covariance.

    T_n^{ext} = ⋃_{Λ ∈ L₊↑} Λ T_n

    where L₊↑ is the proper orthochronous Lorentz group.
    The edge-of-the-wedge theorem shows W_n extends to T_n^{ext}. -/
def ExtendedForwardTube (d n : ℕ) [NeZero d] : Set (Fin n → Fin (d + 1) → ℂ) :=
  ⋃ Λ : LorentzGroup.Restricted (d := d),
    { z | ∃ w ∈ ForwardTube d n, z = fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * w k ν }

/-- The Wightman functions have analytic continuation to the forward tube.

    The n-point Wightman function W_n(x₁,...,xₙ), initially defined as a
    distribution on real spacetime points, extends to a holomorphic function
    on the forward tube T_n.

    By Lorentz covariance, it further extends to the extended forward tube T_n^{ext}.
    The edge-of-the-wedge theorem (Bargmann-Hall-Wightman) shows this extension
    is single-valued. -/
structure WightmanAnalyticity (qft : WightmanQFT d) where
  /-- The analytic continuation of the n-point function to the forward tube -/
  analyticContinuation : (n : ℕ) → (ForwardTube d n) → ℂ
  /-- The continuation is holomorphic (analytic in each complex variable) -/
  isHolomorphic : ∀ n : ℕ, ∀ z : ForwardTube d n,
    DifferentiableAt ℂ (fun w => analyticContinuation n ⟨w, sorry⟩) z.val
  /-- Boundary values recover the Wightman distribution -/
  boundary_values : ∀ n : ℕ, ∀ f : SchwartzNPointSpace d n,
    WightmanDistribution d qft n f = sorry  -- ∫ W_n^{analytic}(x - iε) f(x) dx as ε → 0

end

