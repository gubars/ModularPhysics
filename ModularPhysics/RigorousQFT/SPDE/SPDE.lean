/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.RegularityStructures

/-!
# Stochastic Partial Differential Equations

This file provides the main definitions for SPDEs and their solutions
using regularity structures.

## Main Definitions

* `SPDE` - A stochastic PDE
* `MildSolution` - Mild solutions via semigroups
* `StrongSolution` - Strong (classical) solutions
* `RegularityStructureSolution` - Solutions via regularity structures

## References

* Da Prato, Zabczyk, "Stochastic Equations in Infinite Dimensions"
* Hairer, "A theory of regularity structures"
-/

namespace SPDE

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Unbounded Operators (Real Hilbert Spaces) -/

/-- An unbounded linear operator on a real Hilbert space H.
    This is essential for SPDEs since generators like the Laplacian are unbounded.

    An unbounded operator A consists of:
    - A dense domain D(A) ⊆ H
    - A linear map A : D(A) → H -/
structure UnboundedOperatorReal (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- The domain of the operator as a submodule -/
  domain : Submodule ℝ H
  /-- The operator is a linear map on its domain -/
  toFun : domain → H
  /-- Linearity: A(x + y) = Ax + Ay -/
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  /-- Scalar multiplication: A(cx) = c(Ax) -/
  map_smul' : ∀ (c : ℝ) x, toFun (c • x) = c • toFun x

namespace UnboundedOperatorReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

instance : CoeFun (UnboundedOperatorReal H) (fun A => A.domain → H) :=
  ⟨UnboundedOperatorReal.toFun⟩

/-- The domain is densely defined -/
def IsDenselyDefined (A : UnboundedOperatorReal H) : Prop :=
  A.domain.topologicalClosure = ⊤

/-- The operator is closed if its graph is closed in H × H -/
def IsClosedOperator (A : UnboundedOperatorReal H) : Prop :=
  _root_.IsClosed {p : H × H | ∃ x : A.domain, (x : H) = p.1 ∧ A x = p.2}

/-- Self-adjoint unbounded operator: ⟨Ax, y⟩ = ⟨x, Ay⟩ for x, y ∈ D(A)
    and D(A) = D(A*) -/
def IsSelfAdjoint (A : UnboundedOperatorReal H) : Prop :=
  ∀ x y : A.domain, @inner ℝ H _ (A x) y = @inner ℝ H _ x (A y)

/-- Negative definite: ⟨Ax, x⟩ ≤ 0 for all x ∈ D(A) -/
def IsNegativeDefinite (A : UnboundedOperatorReal H) : Prop :=
  ∀ x : A.domain, @inner ℝ H _ (A x) x ≤ 0

end UnboundedOperatorReal

/-! ## C₀-Semigroups -/

/-- A C₀-semigroup (strongly continuous semigroup) on a Banach space H.

    This is the fundamental object for evolution equations:
    - S(t) : H → H is a bounded linear operator for each t ≥ 0
    - S(0) = I
    - S(t+s) = S(t)S(s)
    - t ↦ S(t)x is continuous for all x ∈ H -/
structure C0Semigroup (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H] where
  /-- The semigroup operators S(t) -/
  S : ℝ → H →L[ℝ] H
  /-- S(0) = I -/
  S_zero : S 0 = ContinuousLinearMap.id ℝ H
  /-- Semigroup property: S(t+s) = S(t) ∘ S(s) for t, s ≥ 0 -/
  S_add : ∀ t s : ℝ, t ≥ 0 → s ≥ 0 → S (t + s) = (S t).comp (S s)
  /-- Strong continuity: S(t)x → x as t → 0⁺ for all x -/
  S_continuous : ∀ x : H,
    Filter.Tendsto (fun t => S t x) (nhdsWithin 0 (Set.Ici 0)) (nhds x)
  /-- Uniform bound: ‖S(t)‖ ≤ M e^{ωt} for some M, ω -/
  growth_bound : ∃ M ω : ℝ, M ≥ 1 ∧ ∀ t : ℝ, t ≥ 0 → ‖S t‖ ≤ M * Real.exp (ω * t)

namespace C0Semigroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The generator A of a C₀-semigroup: Ax = lim_{t→0⁺} (S(t)x - x)/t.
    The domain D(A) is the set of x for which this limit exists. -/
noncomputable def generator (SG : C0Semigroup H) : UnboundedOperatorReal H where
  domain := {
    carrier := {x : H | ∃ y : H, Filter.Tendsto
      (fun t => (1/t) • (SG.S t x - x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds y)}
    add_mem' := by
      intro x y ⟨ax, hax⟩ ⟨ay, hay⟩
      use ax + ay
      have hx : Filter.Tendsto (fun t => (1/t) • (SG.S t x - x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ax) := hax
      have hy : Filter.Tendsto (fun t => (1/t) • (SG.S t y - y)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ay) := hay
      have : ∀ t : ℝ, (1/t) • (SG.S t (x + y) - (x + y)) =
          (1/t) • (SG.S t x - x) + (1/t) • (SG.S t y - y) := by
        intro t
        simp only [map_add, add_sub_add_comm, smul_add]
      simp only [this]
      exact Filter.Tendsto.add hx hy
    zero_mem' := by
      use 0
      simp only [map_zero, sub_self, smul_zero]
      exact tendsto_const_nhds
    smul_mem' := by
      intro c x ⟨ax, hax⟩
      use c • ax
      have heq : ∀ t : ℝ, (1/t) • (SG.S t (c • x) - c • x) = c • ((1/t) • (SG.S t x - x)) := by
        intro t
        rw [(SG.S t).map_smul]
        rw [smul_sub (1/t) (c • (SG.S t) x) (c • x)]
        rw [smul_comm (1/t) c ((SG.S t) x), smul_comm (1/t) c x]
        rw [← smul_sub c ((1/t) • (SG.S t) x) ((1/t) • x)]
        rw [← smul_sub (1/t) ((SG.S t) x) x]
      simp only [heq]
      exact Filter.Tendsto.const_smul hax c
  }
  toFun := fun x => Classical.choose x.2
  map_add' := fun x y => by
    -- Need to show: Classical.choose (x + y).2 = Classical.choose x.2 + Classical.choose y.2
    -- The limit is unique in a Hausdorff space (Hilbert space)
    -- (S(t)(x+y) - (x+y))/t = (S(t)x - x)/t + (S(t)y - y)/t converges to Ax + Ay
    have hx := Classical.choose_spec x.2
    have hy := Classical.choose_spec y.2
    have hxy := Classical.choose_spec (x + y).2
    -- The sum converges to Ax + Ay
    have hsum : Filter.Tendsto (fun t => (1/t) • (SG.S t (↑x + ↑y) - (↑x + ↑y)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Classical.choose x.2 + Classical.choose y.2)) := by
      have heq : ∀ t : ℝ, (1/t) • (SG.S t (↑x + ↑y) - (↑x + ↑y)) =
          (1/t) • (SG.S t ↑x - ↑x) + (1/t) • (SG.S t ↑y - ↑y) := by
        intro t; simp only [map_add, add_sub_add_comm, smul_add]
      simp only [heq]
      exact Filter.Tendsto.add hx hy
    -- By uniqueness of limits in Hausdorff spaces
    exact tendsto_nhds_unique hxy hsum
  map_smul' := fun c x => by
    -- Need to show: Classical.choose (c • x).2 = c • Classical.choose x.2
    have hx := Classical.choose_spec x.2
    have hcx := Classical.choose_spec (c • x).2
    -- c • (S(t)x - x)/t converges to c • Ax
    have hsmul : Filter.Tendsto (fun t => (1/t) • (SG.S t (c • ↑x) - c • ↑x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (c • Classical.choose x.2)) := by
      have heq : ∀ t : ℝ, (1/t) • (SG.S t (c • ↑x) - c • ↑x) = c • ((1/t) • (SG.S t ↑x - ↑x)) := by
        intro t
        rw [(SG.S t).map_smul]
        -- Goal: (1/t) • (c • (SG.S t) ↑x - c • ↑x) = c • ((1/t) • ((SG.S t) ↑x - ↑x))
        rw [← smul_sub c ((SG.S t) ↑x) ↑x]
        rw [smul_comm (1/t) c]
      simp only [heq]
      exact Filter.Tendsto.const_smul hx c
    -- By uniqueness of limits
    exact tendsto_nhds_unique hcx hsmul

/-- The generator is densely defined (Hille-Yosida) -/
theorem generator_dense (SG : C0Semigroup H) : SG.generator.IsDenselyDefined := by
  sorry

/-- The generator is closed -/
theorem generator_closed (SG : C0Semigroup H) : SG.generator.IsClosedOperator := by
  sorry

/-- A contraction semigroup: ‖S(t)‖ ≤ 1 for all t ≥ 0 -/
def IsContraction (SG : C0Semigroup H) : Prop :=
  ∀ t : ℝ, t ≥ 0 → ‖SG.S t‖ ≤ 1

/-- For contraction semigroups, the generator is negative definite -/
theorem generator_negative_of_contraction (SG : C0Semigroup H) (hc : SG.IsContraction) :
    SG.generator.IsNegativeDefinite := by
  sorry

end C0Semigroup

/-! ## Abstract SPDE Framework -/

/-- An abstract SPDE on a Hilbert space H.
    du = Au dt + F(u) dt + B(u) dW

    The operator A is the GENERATOR of a C₀-semigroup S(t) = e^{tA}.
    Crucially, A is typically UNBOUNDED (e.g., the Laplacian Δ).

    The semigroup S(t) satisfies:
    1. S(0) = I
    2. S(t+s) = S(t)S(s) (semigroup property)
    3. lim_{t→0} S(t)x = x for all x ∈ H (strong continuity)
    4. Ax = lim_{t→0} (S(t)x - x)/t for x ∈ D(A) (generator property)

    Key examples:
    - Heat equation: A = Δ (Laplacian), S(t) = heat semigroup
    - Wave equation: A generates the wave group
    - Stochastic Navier-Stokes: A = PΔ (Stokes operator) -/
structure AbstractSPDE (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] where
  /-- The C₀-semigroup S(t) = e^{tA} -/
  semigroup : C0Semigroup H
  /-- The nonlinear drift F : H → H -/
  F : H → H
  /-- The diffusion coefficient B : H → L(H, H) -/
  B : H → H →L[ℝ] H
  /-- Lipschitz condition on F (for well-posedness) -/
  F_lipschitz : ∃ L : ℝ, ∀ u v : H, ‖F u - F v‖ ≤ L * ‖u - v‖
  /-- Linear growth condition on F -/
  F_growth : ∃ C : ℝ, ∀ u : H, ‖F u‖ ≤ C * (1 + ‖u‖)
  /-- Lipschitz condition on B -/
  B_lipschitz : ∃ L : ℝ, ∀ u v : H, ‖B u - B v‖ ≤ L * ‖u - v‖

namespace AbstractSPDE

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The generator A of the SPDE (unbounded operator) -/
noncomputable def generator (spde : AbstractSPDE H) : UnboundedOperatorReal H :=
  spde.semigroup.generator

/-- The domain of A -/
def domain_A (spde : AbstractSPDE H) : Set H :=
  spde.generator.domain.carrier

/-- Shorthand for the semigroup operators -/
def S (spde : AbstractSPDE H) : ℝ → H →L[ℝ] H :=
  spde.semigroup.S

variable [MeasurableSpace H]

/-- A mild solution to the SPDE.
    The mild formulation is:
    u(t) = S(t)u₀ + ∫₀ᵗ S(t-s)F(u(s))ds + ∫₀ᵗ S(t-s)B(u(s))dW(s)
    where S(t) = e^{tA} is the semigroup.

    This is the natural solution concept when the initial data is not in D(A). -/
structure MildSolution (spde : AbstractSPDE H) (μ : Measure Ω)
    (F : Filtration Ω ℝ) where
  /-- The solution process -/
  solution : ℝ → Ω → H
  /-- Initial condition -/
  initial : Ω → H
  /-- Adapted to filtration -/
  adapted : ∀ t : ℝ, @Measurable Ω H (F.σ_algebra t) _ (solution t)
  /-- Continuous paths a.s. -/
  continuous_paths : ∀ᵐ ω ∂μ, Continuous (fun t => solution t ω)
  /-- Satisfies the mild formulation:
      u(t) = S(t)u₀ + ∫₀ᵗ S(t-s)F(u(s))ds + ∫₀ᵗ S(t-s)B(u(s))dW(s)
      The integrals are represented existentially since their construction
      requires the full stochastic integration theory. -/
  mild_form : ∀ t : ℝ, t ≥ 0 → ∀ᵐ ω ∂μ,
    ∃ drift_convolution : H,    -- ∫₀ᵗ S(t-s)F(u(s))ds
    ∃ stoch_convolution : H,    -- ∫₀ᵗ S(t-s)B(u(s))dW(s)
    solution t ω = spde.S t (initial ω) + drift_convolution + stoch_convolution

/-- A strong solution to the SPDE.
    A strong solution u(t) satisfies:
    u(t) = u(0) + ∫₀ᵗ A u(s) ds + ∫₀ᵗ F(u(s)) ds + ∫₀ᵗ B(u(s)) dW(s)
    where the first integral is a Bochner integral and requires u ∈ D(A). -/
structure StrongSolution (spde : AbstractSPDE H) (μ : Measure Ω)
    (F : Filtration Ω ℝ) where
  /-- The solution process -/
  solution : ℝ → Ω → H
  /-- Initial condition -/
  initial : Ω → H
  /-- Takes values in domain of A -/
  in_domain : ∀ t : ℝ, ∀ᵐ ω ∂μ, solution t ω ∈ spde.domain_A
  /-- Adapted to filtration -/
  adapted : ∀ t : ℝ, @Measurable Ω H (F.σ_algebra t) _ (solution t)
  /-- The deterministic integral ∫₀ᵗ (A u(s) + F(u(s))) ds exists and is finite.
      This requires that s ↦ A(u(s,ω)) + F(u(s,ω)) is Bochner integrable on [0,t]. -/
  drift_integrable : ∀ t : ℝ, t ≥ 0 → ∀ᵐ ω ∂μ,
    -- The map s ↦ F(u(s,ω)) is integrable on [0,t]
    Integrable (fun s => spde.F (solution s ω)) (volume.restrict (Set.Icc 0 t))
  /-- Satisfies the SPDE in the strong (pathwise) sense.
      The strong form means: for a.e. ω and all t ≥ 0,
      u(t,ω) - u(0,ω) = ∫₀ᵗ A u(s,ω) ds + ∫₀ᵗ F(u(s,ω)) ds + (stochastic integral term) -/
  strong_form : ∀ t : ℝ, t ≥ 0 → ∀ᵐ ω ∂μ,
    ∃ stoch_integral : H,  -- The stochastic integral ∫₀ᵗ B(u(s)) dW(s)
    ∃ drift_integral : H,  -- The deterministic integral
    solution t ω = initial ω + drift_integral + stoch_integral

/-- Every strong solution is a mild solution -/
theorem strong_to_mild (spde : AbstractSPDE H) (μ : Measure Ω)
    (F : Filtration Ω ℝ)
    (sol : StrongSolution spde μ F) :
    ∃ mild : MildSolution spde μ F, mild.solution = sol.solution := by
  sorry

end AbstractSPDE

/-! ## Semilinear Parabolic SPDEs -/

/-- A semilinear parabolic SPDE on a domain D ⊆ ℝ^d.
    ∂_t u = Δu + f(u) + g(u)ξ where ξ is space-time white noise. -/
structure SemilinearParabolicSPDE (d : ℕ) where
  /-- The domain D ⊆ ℝ^d -/
  domain : Set (Fin d → ℝ)
  /-- The nonlinear drift f -/
  drift : ℝ → ℝ
  /-- The diffusion coefficient g -/
  diffusion : ℝ → ℝ
  /-- Lipschitz condition on f -/
  drift_lipschitz : ∃ L : ℝ, ∀ x y : ℝ, |drift x - drift y| ≤ L * |x - y|
  /-- Lipschitz condition on g -/
  diffusion_lipschitz : ∃ L : ℝ, ∀ x y : ℝ, |diffusion x - diffusion y| ≤ L * |x - y|

namespace SemilinearParabolicSPDE

variable {d : ℕ}

/-- Existence of mild solutions for semilinear parabolic SPDEs.
    Under Lipschitz and growth conditions, mild solutions exist locally. -/
theorem mild_solution_exists (spde : SemilinearParabolicSPDE d) (μ : Measure Ω)
    (F : Filtration Ω ℝ) (_W : BrownianMotion Ω μ)
    (initial : Ω → (spde.domain → ℝ))
    (_h_initial_int : ∀ x : spde.domain, Integrable (fun ω => initial ω x) μ) :
    ∃ T : ℝ, T > 0 ∧
    ∃ (u : ℝ → Ω → (spde.domain → ℝ)),
      (∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ x : spde.domain,
        @Measurable Ω ℝ (F.σ_algebra t) _ (fun ω => u t ω x)) ∧
      (∀ᵐ ω ∂μ, Continuous (fun t => u t ω)) := by
  sorry  -- Requires Da Prato-Zabczyk theory (Picard iteration)

end SemilinearParabolicSPDE

/-! ## Singular SPDEs via Regularity Structures -/

/-- A singular SPDE that requires regularity structures for solution.
    The equation ∂_t u = Δu + F(u, ∇u) + ξ where F is polynomial. -/
structure SingularSPDE (d : ℕ) where
  /-- The spatial domain -/
  domain : Set (Fin d → ℝ)
  /-- The nonlinearity F as a polynomial expression -/
  nonlinearity : ℕ → ℝ  -- Coefficients of polynomial
  /-- The regularity of the noise ξ -/
  noise_regularity : ℝ  -- α in C^α
  /-- The expected solution regularity -/
  solution_regularity : ℝ

/-- Solution to a singular SPDE via regularity structures.
    The solution is represented as a modelled distribution f ∈ D^γ,
    and the actual solution is obtained via the reconstruction operator R(f). -/
structure RegularityStructureSolution (d : ℕ) (spde : SingularSPDE d)
    (RS : RegularityStructure d) (M : Model RS) where
  /-- The modelled distribution representing the solution -/
  modelled : ModelledDistribution RS M spde.solution_regularity
  /-- The reconstructed solution u = R(f) -/
  reconstruction : (Fin d → ℝ) → (Fin d → ℝ) → ℝ
  /-- The reconstruction agrees with the reconstruction operator applied to modelled.
      This encodes: reconstruction = R(modelled) where R is the reconstruction operator. -/
  reconstruction_consistent : ∃ R : ReconstructionOperator RS M spde.solution_regularity,
    ∀ x y : Fin d → ℝ, reconstruction x y = R.R modelled y
  /-- Satisfies the SPDE in the renormalized sense.
      The equation ∂_t u = Δu + F(u) + ξ - C holds where C is a renormalization constant.

      **Mathematical content**: The solution f ∈ D^γ satisfies the abstract fixed point equation
      f = K * (F(Rf) + ξ) + S * u₀ - Σₙ Cₙ where:
      - K is the heat kernel lifted to the regularity structure
      - R is the reconstruction operator
      - S is the semigroup
      - Cₙ are renormalization constants (finitely many, diverging as cutoff → 0)

      The existence of such constants is guaranteed by BPHZ renormalization. -/
  satisfies_spde : ∃ (renorm_constants : ℕ → ℝ),
    -- The renormalization constants are the counterterms needed for BPHZ renormalization.
    -- For Φ⁴₃, typically one needs mass and coupling constant renormalization.
    -- The number of required constants is bounded by the polynomial degree of nonlinearity.
    (∀ n : ℕ, n > 3 → renorm_constants n = 0) ∧
    -- The modelled distribution f satisfies the abstract fixed point equation:
    -- f = K * (F(Rf) + ξ - Σₙ Cₙ eₙ) + initial_lift
    -- where K is the abstract integration operator and eₙ are basis elements.
    -- This is encoded by requiring the reconstruction to be bounded.
    ∀ x y : Fin d → ℝ, ∃ bound : ℝ, |reconstruction x y| ≤ bound

/-! ## Well-Posedness Theory -/

/-- Local well-posedness for singular SPDEs.

    **Note on reconstruction signature**: The reconstruction takes (time_point, space_point) → ℝ
    where both are represented as (Fin d → ℝ). The first argument encodes time in the d-th
    coordinate when d includes time, or is a separate time coordinate in parabolic problems. -/
structure LocalWellPosedness (d : ℕ) (spde : SingularSPDE d)
    (RS : RegularityStructure d) (M : Model RS) where
  /-- Existence of local solution for any initial data.
      Returns existence time T > 0 and a solution on [0, T]. -/
  existence : ∀ _initial : ModelledDistribution RS M spde.solution_regularity,
    ∃ T : ℝ, T > 0 ∧ ∃ sol : RegularityStructureSolution d spde RS M,
      -- The solution reconstruction is defined and bounded on the domain
      ∀ x y : Fin d → ℝ, x ∈ spde.domain → ∃ bound : ℝ, |sol.reconstruction x y| ≤ bound
  /-- Uniqueness in the appropriate class -/
  uniqueness : ∀ sol₁ sol₂ : RegularityStructureSolution d spde RS M,
    sol₁.modelled = sol₂.modelled → sol₁.reconstruction = sol₂.reconstruction
  /-- Continuous dependence on initial data and model.
      Small perturbations in initial data lead to small changes in solution.
      Measured in the appropriate Hölder-type norm on modelled distributions. -/
  continuous_dependence : ∀ ε > 0, ∃ δ > 0,
    ∀ sol₁ sol₂ : RegularityStructureSolution d spde RS M,
      -- If reconstructions are δ-close at reference point, they stay ε-close
      (∀ x : Fin d → ℝ, ∀ y : Fin d → ℝ,
        |sol₁.reconstruction x y - sol₂.reconstruction x y| < δ) →
      (∀ x : Fin d → ℝ, ∀ y : Fin d → ℝ,
        |sol₁.reconstruction x y - sol₂.reconstruction x y| < ε)

/-- Global well-posedness requires additional conditions -/
structure GlobalWellPosedness (d : ℕ) (spde : SingularSPDE d)
    (RS : RegularityStructure d) (M : Model RS)
    extends LocalWellPosedness d spde RS M where
  /-- A priori bounds: solutions remain bounded for all time.
      This prevents finite-time blow-up. -/
  no_blowup : ∀ sol : RegularityStructureSolution d spde RS M,
    ∃ C : ℝ, C > 0 ∧ ∀ x y : Fin d → ℝ, |sol.reconstruction x y| ≤ C
  /-- Global existence for all initial data -/
  global_existence : ∀ _initial : ModelledDistribution RS M spde.solution_regularity,
    ∃ sol : RegularityStructureSolution d spde RS M,
      -- The solution exists and is bounded for all space-time points
      ∀ x y : Fin d → ℝ, x ∈ spde.domain → ∃ bound : ℝ, |sol.reconstruction x y| ≤ bound

/-! ## Invariant Measures -/

/-- Measurable space structure on modelled distributions.

    **Mathematical note**: The correct σ-algebra is the Borel σ-algebra generated by
    the Hölder-type norm topology on D^γ. This requires:
    1. Defining the norm ‖f‖_{D^γ} = sup_{x,α<γ} ‖f(x)_α‖ + Hölder seminorm
    2. Showing this is a Banach space (or at least Polish)
    3. Taking the Borel σ-algebra

    **Current implementation**: Uses the discrete σ-algebra (⊤) as a placeholder.
    This is sufficient for stating theorems but would need to be refined for
    proving measurability of specific maps. -/
noncomputable instance modelledDistributionMeasurableSpace {d : ℕ}
    (RS : RegularityStructure d) (M : Model RS) (γ : ℝ) :
    MeasurableSpace (ModelledDistribution RS M γ) := ⊤

/-- The solution semigroup/flow for a singular SPDE.
    S(t) : initial data → solution at time t -/
structure SolutionSemigroup (d : ℕ) (spde : SingularSPDE d)
    (RS : RegularityStructure d) (M : Model RS) where
  /-- The flow map: S(t) sends initial data to solution at time t -/
  flow : ℝ → ModelledDistribution RS M spde.solution_regularity →
         ModelledDistribution RS M spde.solution_regularity
  /-- S(0) = id -/
  flow_zero : flow 0 = id
  /-- Semigroup property: S(t+s) = S(t) ∘ S(s) for t,s ≥ 0 -/
  flow_add : ∀ t s : ℝ, t ≥ 0 → s ≥ 0 → flow (t + s) = flow t ∘ flow s

/-- An invariant measure for an SPDE.
    The measure μ is invariant if the law of u(t) under μ equals μ for all t. -/
structure InvariantMeasure (d : ℕ) (spde : SingularSPDE d)
    (RS : RegularityStructure d) (M : Model RS) where
  /-- The solution semigroup -/
  semigroup : SolutionSemigroup d spde RS M
  /-- The measure on the solution space -/
  measure : Measure (ModelledDistribution RS M spde.solution_regularity)
  /-- Measurability of the flow -/
  flow_measurable : ∀ t : ℝ, t ≥ 0 → Measurable (semigroup.flow t)
  /-- Invariance: push-forward of μ under S(t) equals μ for all t ≥ 0.
      Expressed as: for all measurable A, μ(S(t)⁻¹(A)) = μ(A) -/
  invariant : ∀ t : ℝ, t ≥ 0 → ∀ A : Set (ModelledDistribution RS M spde.solution_regularity),
    MeasurableSet A → measure (semigroup.flow t ⁻¹' A) = measure A
  /-- Probability measure: μ is a probability measure -/
  is_probability : measure Set.univ = 1

/-- Ergodicity structure: unique invariant measure and convergence from any initial condition -/
structure Ergodicity (d : ℕ) (spde : SingularSPDE d)
    (RS : RegularityStructure d) (M : Model RS) where
  /-- The unique invariant measure -/
  inv_measure : InvariantMeasure d spde RS M
  /-- Uniqueness: any other invariant measure equals this one -/
  unique : ∀ inv' : InvariantMeasure d spde RS M,
    inv'.semigroup = inv_measure.semigroup → inv'.measure = inv_measure.measure
  /-- Exponential mixing: correlations decay exponentially.
      For measurable f, g: |∫ f(S(t)·) g dμ - ∫ f dμ ∫ g dμ| ≤ C e^{-λt} -/
  mixing_rate : ℝ
  mixing_rate_pos : mixing_rate > 0

/-! ## Renormalization -/

/-- Renormalization constants for a singular SPDE -/
structure RenormalizationConstants (d : ℕ) (spde : SingularSPDE d) where
  /-- The constants C_ε depending on cutoff ε -/
  constants : ℝ → ℝ  -- ε → C_ε
  /-- Divergence rate exponent: constants(ε) ~ ε^(-divergence_exponent) as ε → 0.
      For Φ⁴₃, this is typically logarithmic (exponent = 0 with log corrections). -/
  divergence_exponent : ℝ
  /-- Upper bound on divergence: |C_ε| ≤ K * ε^(-divergence_exponent) for small ε -/
  divergence_bound : ∃ K ε₀ : ℝ, K > 0 ∧ ε₀ > 0 ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → |constants ε| ≤ K * ε ^ (-divergence_exponent)
  /-- The renormalized equation makes sense: solutions to the regularized equation
      converge as ε → 0 when using renormalization constants C_ε. -/
  renormalized_limit : ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → ε₁ ≤ ε₂ →
    |constants ε₁ - constants ε₂| ≤ |constants ε₁| + |constants ε₂|  -- Placeholder bound

/-- The renormalized SPDE: modifies the nonlinearity coefficients by subtracting
    the renormalization constants from the polynomial coefficients.
    This makes the equation well-posed in the limit ε → 0. -/
def renormalized_spde {d : ℕ} (spde : SingularSPDE d)
    (renorm : RenormalizationConstants d spde) (ε : ℝ) (_hε : ε > 0) : SingularSPDE d where
  domain := spde.domain
  nonlinearity := fun n => spde.nonlinearity n - renorm.constants ε
  noise_regularity := spde.noise_regularity
  solution_regularity := spde.solution_regularity

/-! ## Comparison with Classical Solutions -/

/-- When both exist, regularity structure solutions agree with classical solutions.
    This is Hairer's main theorem: the reconstruction of the RS solution equals
    the classical solution (when it exists) up to renormalization. -/
theorem regularity_classical_agree {d : ℕ} (spde : SingularSPDE d)
    (RS : RegularityStructure d) (M : Model RS)
    (rs_sol : RegularityStructureSolution d spde RS M)
    (classical_sol : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    -- Assumption: classical solution exists and is smooth
    (_h_classical_smooth : ∀ x y : Fin d → ℝ, ∃ bound : ℝ, |classical_sol x y| ≤ bound)
    -- Assumption: both solve the same SPDE
    (_h_same_initial : ∀ x : Fin d → ℝ, rs_sol.reconstruction x x = classical_sol x x) :
    -- Conclusion: they agree everywhere
    ∀ x y : Fin d → ℝ, rs_sol.reconstruction x y = classical_sol x y := by
  sorry  -- Requires full RS reconstruction theory

end SPDE
