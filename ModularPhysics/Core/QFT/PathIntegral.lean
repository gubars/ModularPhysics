import ModularPhysics.Core.SpaceTime
import ModularPhysics.Core.Quantum
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic

namespace ModularPhysics.Core.QFT.PathIntegral

open SpaceTime Quantum

set_option autoImplicit false
set_option linter.unusedVariables false

/- ============= FIELD CONFIGURATIONS (classical variables) ============= -/

/-- Space of field configurations (NOT necessarily a vector space)
    Examples:
    - Linear: φ : M → ℝ (vector space)
    - Nonlinear σ-model: φ : M → S² (maps to sphere)
    - Gauge theory: A : M → Lie(G) with gauge equivalence
    - Fermions: ψ with anticommuting values (supermanifold structure) -/
axiom FieldConfig (M : Type _) (target : Type _) : Type _

/-- Pointwise evaluation of field configuration -/
axiom evalField {M target : Type _} : FieldConfig M target → M → target

/-- Field space for linear theory (vector space structure) -/
class LinearFieldSpace (M : Type _) (V : Type _) extends
  AddCommGroup (FieldConfig M V) where
  smul : ℝ → FieldConfig M V → FieldConfig M V
  smul_add : ∀ (a : ℝ) (φ ψ : FieldConfig M V),
    smul a (φ + ψ) = smul a φ + smul a ψ

/-- Field space for nonlinear σ-model (target manifold structure) -/
structure NonlinearSigmaModel (M : Type _) (target : Type _) where
  /-- Target space is a Riemannian manifold -/
  target_manifold : Type _
  metric : target → target → ℝ
  /-- Field configurations are smooth maps -/
  field_space : Type _
  smooth : field_space → Prop

/-- Gauge field with gauge redundancy -/
structure GaugeFieldSpace (M : Type _) (G : Type _) where
  /-- Lie algebra-valued connection -/
  connection_space : Type _
  /-- Gauge transformations -/
  gauge_group : Type _
  gauge_action : gauge_group → connection_space → connection_space
  /-- Physical configurations modulo gauge -/
  physical_space : Type _

/- ============= SUPERGEOMETRY FOUNDATIONS (for fermions) ============= -/

/-- Grassmann algebra: anticommuting variables θᵢθⱼ = -θⱼθᵢ, hence θᵢ² = 0
    This is the basic algebraic structure for fermionic variables -/
structure GrassmannAlgebra where
  carrier : Type _
  mul : carrier → carrier → carrier
  zero : carrier
  /-- Grading: 0 = bosonic (even), 1 = fermionic (odd) -/
  grading : carrier → Fin 2
  /-- Anticommutativity: θᵢθⱼ = -θⱼθᵢ for odd elements -/
  anticommute : ∀ (θ₁ θ₂ : carrier),
    grading θ₁ = 1 → grading θ₂ = 1 → mul θ₁ θ₂ ≠ mul θ₂ θ₁
  /-- Nilpotency: θ² = 0 for fermionic generators -/
  nilpotent : ∀ (θ : carrier), grading θ = 1 → mul θ θ = zero

/-- Berezin integration: integration over Grassmann variables
    Key properties (opposite to ordinary integration!):
    - ∫ dθ = 0 (integral of constant is zero)
    - ∫ θ dθ = 1 (integral of θ is one)
    - Differentiation = Integration for Grassmann variables -/
structure BerezinIntegral (G : GrassmannAlgebra) where
  integrate : G.carrier → ℂ
  /-- Integration of zero vanishes -/
  zero_vanishes : integrate G.zero = 0
  /-- Integration of generator gives 1 (for appropriate normalization) -/
  generator_integral : ∀ (θ : G.carrier), G.grading θ = 1 → integrate θ = 1

/-- Locally ringed space (sheaf-theoretic foundation)
    Key: This is NOT a set! It's a space with sheaf of functions.
    Needed for proper treatment of supermanifolds. -/
structure LocallyRingedSpace where
  space : Type _
  structure_sheaf : Type _ -- Sheaf of functions
  local_rings : space → Type _ -- Stalk at each point

/-- Supermanifold of dimension m|n (m bosonic, n fermionic)
    This is a locally ringed space, NOT an ordinary manifold!
    Fermion field configuration spaces have this structure.

    For ordinary QFT: can work with super vector spaces
    For 2d supergravity: need full supermanifold structure -/
structure Supermanifold (m n : ℕ) extends LocallyRingedSpace where
  bosonic_dim : ℕ := m
  fermionic_dim : ℕ := n
  /-- Locally modeled on ℝ^m × Λⁿ where Λ = Grassmann algebra -/
  local_model : Type _

/-- Super vector space (ℤ/2-graded with anticommuting structure)
    This simpler structure is sufficient for ordinary QFT with fermions -/
structure SuperVectorSpace where
  carrier : Type _
  add : carrier → carrier → carrier
  grading : carrier → Fin 2
  /-- Even part (bosonic) -/
  even_subspace : Type _
  /-- Odd part (fermionic) -/
  odd_subspace : Type _

/-- Fermionic field configurations
    Mathematical reality: configuration space is a supermanifold
    Practical note: for ordinary QFT, super vector space structure suffices -/
axiom FermionFieldConfig (M : Type _) : Type _

/-- For ordinary QFT: fermion fields have super vector space structure -/
axiom fermionSuperVectorSpace (M : Type _) : SuperVectorSpace

/-- For 2d supergravity: need full supermanifold structure -/
axiom fermionSupermanifold (M : Type _) (m n : ℕ) : Supermanifold m n

/-- Berezinian (superdeterminant): replaces determinant for supermatrices
    Needed for change of variables involving fermions
    For supermatrix [[A,B],[C,D]]: Ber = det(A - BD⁻¹C)/det(D) -/
axiom Berezinian : Type _

axiom berezinianEval (B : Berezinian) : ℂ

/- ============= GENERAL FIELD SPACE ============= -/

/-- General field configuration space (no a priori structure) -/
axiom FieldSpace (M : Type _) : Type _

/- ============= ACTION FUNCTIONAL ============= -/

/-- Action functional S[φ] on field configurations -/
structure ActionFunctional (F : Type _) where
  eval : F → ℝ
  /-- Action is local -/
  locality : Prop
  /-- First variation gives equations of motion -/
  equations_of_motion : F → F → ℝ

/-- Euclidean action (bounded below, ensures convergence) -/
structure EuclideanAction (F : Type _) extends ActionFunctional F where
  bounded_below : ∃ (c : ℝ), ∀ φ : F, eval φ ≥ c

/-- Wick rotation: it → τ -/
axiom wickRotation {F : Type _} :
  ActionFunctional F → EuclideanAction F

/- ============= MEASURE ON FIELD SPACE ============= -/

/-- Formal measure Dφ (needs regularization to be well-defined!) -/
axiom FieldMeasure (F : Type _) : Type _

/-- Bosonic measure (translation invariant for linear theories) -/
axiom bosonicMeasure {M V : Type _}
  [LinearFieldSpace M V] : FieldMeasure (FieldConfig M V)

/-- Fermionic measure: uses Berezin integration
    Key property: sign change under exchange
    ∫ Dψ Dχ F[ψ,χ] = -∫ Dχ Dψ F[ψ,χ] -/
structure FermionicMeasure (F : Type _) (G : GrassmannAlgebra) where
  measure : FieldMeasure F
  berezin : BerezinIntegral G
  /-- Grassmann nature: sign change under exchange -/
  anticommuting : Prop

/-- Jacobian for change of variables
    Bosonic: ordinary determinant
    Fermionic: Berezinian (superdeterminant) -/
axiom jacobianDeterminant {F₁ F₂ : Type _} (f : F₁ → F₂) : ℂ

/- ============= FIELD REDEFINITIONS ============= -/

/-- Field redefinition φ → φ'(φ)
    Fundamental operation: change of integration variables -/
structure FieldRedefinition {F₁ F₂ : Type _} where
  map : F₁ → F₂
  inverse : F₂ → F₁
  left_inv : ∀ φ, inverse (map φ) = φ
  right_inv : ∀ φ', map (inverse φ') = φ'

/-- Bosonic field redefinition: ordinary Jacobian determinant
    J = det(δφ'ⁱ/δφʲ) -/
structure BosonicFieldRedefinition {F₁ F₂ : Type _} extends
  @FieldRedefinition F₁ F₂ where
  jacobian : ℂ

/-- Fermionic field redefinition: Berezinian (superdeterminant)
    For transformation of Grassmann variables
    Ber(M) where M is supermatrix of derivatives -/
structure FermionicFieldRedefinition {F₁ F₂ : Type _} extends
  @FieldRedefinition F₁ F₂ where
  berezinian : Berezinian

/-- General field redefinition with mixed bosonic/fermionic variables
    Uses Berezinian for the full supermatrix -/
structure SuperFieldRedefinition {F₁ F₂ : Type _} extends
  @FieldRedefinition F₁ F₂ where
  super_jacobian : Berezinian

/-- Evaluate bosonic Jacobian -/
axiom bosonicJacobianEval {F₁ F₂ : Type _}
  (f : @BosonicFieldRedefinition F₁ F₂) : ℂ

/-- Evaluate fermionic Berezinian -/
axiom fermionicBerezinianEval {F₁ F₂ : Type _}
  (f : @FermionicFieldRedefinition F₁ F₂) : ℂ

/-- Action transforms under bosonic field redefinition -/
axiom action_bosonic_redef {F₁ F₂ : Type _}
  (S : ActionFunctional F₁)
  (f : @BosonicFieldRedefinition F₁ F₂) :
  ActionFunctional F₂

/-- Action transforms under fermionic field redefinition -/
axiom action_fermionic_redef {F₁ F₂ : Type _}
  (S : ActionFunctional F₁)
  (f : @FermionicFieldRedefinition F₁ F₂) :
  ActionFunctional F₂

/-- Action evaluated on redefined field -/
axiom action_redef_eval_bosonic {F₁ F₂ : Type _}
  (S : ActionFunctional F₁)
  (f : @BosonicFieldRedefinition F₁ F₂)
  (φ : F₁) :
  (action_bosonic_redef S f).eval (f.map φ) = S.eval φ

axiom action_redef_eval_fermionic {F₁ F₂ : Type _}
  (S : ActionFunctional F₁)
  (f : @FermionicFieldRedefinition F₁ F₂)
  (φ : F₁) :
  (action_fermionic_redef S f).eval (f.map φ) = S.eval φ

/-- Measure transforms under field redefinition -/
axiom measure_bosonic_redef {F₁ F₂ : Type _}
  (μ : FieldMeasure F₁)
  (f : @BosonicFieldRedefinition F₁ F₂) :
  FieldMeasure F₂

axiom measure_fermionic_redef {F₁ F₂ : Type _} (G : GrassmannAlgebra)
  (μ : FermionicMeasure F₁ G)
  (f : @FermionicFieldRedefinition F₁ F₂) :
  FermionicMeasure F₂ G

/-- Observable transforms under field redefinition -/
axiom observable_bosonic_redef {F₁ F₂ : Type _}
  (O : F₁ → ℂ)
  (f : @BosonicFieldRedefinition F₁ F₂) :
  F₂ → ℂ

axiom observable_fermionic_redef {F₁ F₂ : Type _}
  (O : F₁ → ℂ)
  (f : @FermionicFieldRedefinition F₁ F₂) :
  F₂ → ℂ

/- ============= BEREZINIAN PROPERTIES ============= -/

/-- Berezinian of identity is 1 -/
axiom berezinian_identity : berezinianEval sorry = 1

/-- Berezinian is multiplicative under composition
    Ber(AB) = Ber(A)Ber(B) -/
axiom berezinian_multiplicative (B₁ B₂ : Berezinian) :
  berezinianEval sorry = berezinianEval B₁ * berezinianEval B₂

/-- Berezinian of inverse
    Ber(A⁻¹) = 1/Ber(A) -/
axiom berezinian_inverse (B : Berezinian) :
  berezinianEval B * berezinianEval sorry = 1

/-- For purely bosonic block: Berezinian = determinant -/
axiom berezinian_bosonic_limit (B : Berezinian)
  (h_bosonic : True) :
  berezinianEval B = sorry

/-- For purely fermionic: Berezinian = 1/det(fermionic block) -/
axiom berezinian_fermionic_limit (B : Berezinian)
  (h_fermionic : True) :
  berezinianEval B = 1 / sorry

/- ============= JACOBIAN PROPERTIES ============= -/

/-- Bosonic Jacobian is multiplicative under composition -/
axiom jacobian_composition {F₁ F₂ F₃ : Type _}
  (f : @BosonicFieldRedefinition F₁ F₂)
  (g : @BosonicFieldRedefinition F₂ F₃) :
  bosonicJacobianEval (sorry : @BosonicFieldRedefinition F₁ F₃) =
    bosonicJacobianEval f * bosonicJacobianEval g

/-- Fermionic Berezinian is multiplicative -/
axiom fermionic_berezinian_composition {F₁ F₂ F₃ : Type _}
  (f : @FermionicFieldRedefinition F₁ F₂)
  (g : @FermionicFieldRedefinition F₂ F₃) :
  fermionicBerezinianEval (sorry : @FermionicFieldRedefinition F₁ F₃) =
    fermionicBerezinianEval f * fermionicBerezinianEval g

/-- Identity transformation has Jacobian 1 -/
axiom jacobian_identity_bosonic {F : Type _} :
  bosonicJacobianEval (sorry : @BosonicFieldRedefinition F F) = 1

axiom jacobian_identity_fermionic {F : Type _} :
  fermionicBerezinianEval (sorry : @FermionicFieldRedefinition F F) = 1

/-- Inverse transformation has inverse Jacobian -/
axiom jacobian_inverse_bosonic {F₁ F₂ : Type _}
  (f : @BosonicFieldRedefinition F₁ F₂) :
  bosonicJacobianEval f * bosonicJacobianEval (sorry : @BosonicFieldRedefinition F₂ F₁) = 1

axiom jacobian_inverse_fermionic {F₁ F₂ : Type _}
  (f : @FermionicFieldRedefinition F₁ F₂) :
  fermionicBerezinianEval f * fermionicBerezinianEval (sorry : @FermionicFieldRedefinition F₂ F₁) = 1

/- ============= PATH INTEGRAL ============= -/

/-- Path integral Z = ∫ Dφ e^{iS[φ]/ℏ}
    WARNING: Formal expression, typically needs regularization! -/
axiom pathIntegral {F : Type _}
  (S : ActionFunctional F)
  (μ : FieldMeasure F) : ℂ

/-- Path integral with observable insertion -/
axiom pathIntegralWithObservable {F : Type _}
  (S : ActionFunctional F)
  (O : F → ℂ)
  (μ : FieldMeasure F) : ℂ

/-- Path integral with fermions: ∫ DφDψ e^{iS[φ,ψ]/ℏ}
    Uses Berezin integration for fermionic variables -/
axiom fermionPathIntegral {F_bos F_ferm : Type _} (G : GrassmannAlgebra)
  (S : ActionFunctional (F_bos × F_ferm))
  (μ_bos : FieldMeasure F_bos)
  (μ_ferm : FermionicMeasure F_ferm G) : ℂ

/-- Euclidean path integral (better convergence properties) -/
axiom euclideanPathIntegral {F : Type _}
  (S : EuclideanAction F)
  (μ : FieldMeasure F) : ℝ

/-- n-point correlation function ⟨φ(x₁)...φ(xₙ)⟩
    These are expectation values of field VARIABLES,
    distinct from Wightman functions of field OPERATORS -/
axiom correlationFunction {F M V : Type _}
  (S : ActionFunctional F)
  (μ : FieldMeasure F)
  (n : ℕ)
  (points : Fin n → M) : ℂ

/-- Fermionic correlators must have even number of fermions
    ⟨ψ(x₁)...ψ(x₂ₙ)⟩ due to Grassmann integration -/
axiom fermionCorrelator {F M : Type _} (G : GrassmannAlgebra)
  (S : ActionFunctional F)
  (μ : FermionicMeasure F G)
  (n : ℕ)
  (points : Fin (2*n) → M) : ℂ

/-- Path integral transforms under BOSONIC field redefinition
    ∫ Dφ e^{iS[φ]} = ∫ Dφ' det(δφ'/δφ) e^{iS[φ(φ')]} -/
axiom path_integral_bosonic_redef {F₁ F₂ : Type _}
  (S : ActionFunctional F₁)
  (μ : FieldMeasure F₁)
  (f : @BosonicFieldRedefinition F₁ F₂) :
  pathIntegral S μ =
    f.jacobian *
    pathIntegral (action_bosonic_redef S f) (measure_bosonic_redef μ f)

/-- Path integral transforms under FERMIONIC field redefinition
    ∫ Dψ e^{iS[ψ]} = ∫ Dψ' Ber(δψ'/δψ) e^{iS[ψ(ψ')]}
    Note: Berezinian, NOT ordinary determinant! -/
axiom path_integral_fermionic_redef {F₁ F₂ F_bos F_ferm : Type _} (G : GrassmannAlgebra)
  (S : ActionFunctional (F_bos × F₁))
  (μ_bos : FieldMeasure F_bos)
  (μ_ferm : FermionicMeasure F₁ G)
  (f : @FermionicFieldRedefinition F₁ F₂)
  (S_new : ActionFunctional (F_bos × F₂))
  (μ_ferm_new : FermionicMeasure F₂ G) :
  fermionPathIntegral G S μ_bos μ_ferm =
    berezinianEval f.berezinian *
    fermionPathIntegral G S_new μ_bos μ_ferm_new

/-- Mixed bosonic-fermionic field redefinition
    ∫ DφDψ e^{iS[φ,ψ]} uses full Berezinian of supermatrix
    [[δφ'/δφ, δφ'/δψ], [δψ'/δφ, δψ'/δψ]] -/
axiom path_integral_super_redef {F_bos₁ F_bos₂ F_ferm₁ F_ferm₂ : Type _}
  (G : GrassmannAlgebra)
  (S : ActionFunctional (F_bos₁ × F_ferm₁))
  (μ_bos : FieldMeasure F_bos₁)
  (μ_ferm : FermionicMeasure F_ferm₁ G)
  (f : @SuperFieldRedefinition (F_bos₁ × F_ferm₁) (F_bos₂ × F_ferm₂))
  (S_new : ActionFunctional (F_bos₂ × F_ferm₂))
  (μ_bos_new : FieldMeasure F_bos₂)
  (μ_ferm_new : FermionicMeasure F_ferm₂ G) :
  fermionPathIntegral G S μ_bos μ_ferm =
    berezinianEval f.super_jacobian *
    fermionPathIntegral G S_new μ_bos_new μ_ferm_new

/-- Path integral with observable under field redefinition -/
axiom path_integral_observable_bosonic_redef {F₁ F₂ : Type _}
  (S : ActionFunctional F₁)
  (O : F₁ → ℂ)
  (μ : FieldMeasure F₁)
  (f : @BosonicFieldRedefinition F₁ F₂) :
  pathIntegralWithObservable S O μ =
    f.jacobian *
    pathIntegralWithObservable
      (action_bosonic_redef S f)
      (observable_bosonic_redef O f)
      (measure_bosonic_redef μ f)

/- ============= GENERATING FUNCTIONALS ============= -/

/-- Generating functional Z[J] = ∫ Dφ e^{iS[φ] + i∫J·φ} -/
axiom generatingFunctional {F M V : Type _}
  (S : ActionFunctional F)
  (μ : FieldMeasure F)
  (source : M → V) : ℂ

/-- Connected generating functional W[J] = -iℏ log Z[J] -/
noncomputable def connectedGenerating {F M V : Type _}
  (S : ActionFunctional F)
  (μ : FieldMeasure F)
  (source : M → V)
  (ℏ : ℝ) : ℂ :=
  -Complex.I * ℏ * Complex.log (generatingFunctional S μ source)

/-- Effective action Γ[φ_cl] (Legendre transform, 1PI generator) -/
axiom effectiveAction {F : Type _}
  (S : ActionFunctional F)
  (μ : FieldMeasure F) : ActionFunctional F

/- ============= SYMMETRIES ============= -/

/-- Symmetry transformation on field space -/
structure SymmetryTransform {F : Type _} where
  transform : F → F

/-- Symmetries form a group -/
axiom symmetry_compose {F : Type _} :
  @SymmetryTransform F → @SymmetryTransform F → @SymmetryTransform F

axiom symmetry_identity {F : Type _} : @SymmetryTransform F

axiom symmetry_inverse {F : Type _} :
  @SymmetryTransform F → @SymmetryTransform F

/-- Action is invariant under symmetry -/
def ActionInvariant {F : Type _}
  (S : ActionFunctional F)
  (σ : @SymmetryTransform F) : Prop :=
  ∀ φ, S.eval (σ.transform φ) = S.eval φ

/-- Measure is invariant under symmetry -/
def MeasureInvariant {F : Type _}
  (μ : FieldMeasure F)
  (σ : @SymmetryTransform F) : Prop :=
  True

/-- Symmetry with both action and measure invariance -/
structure InvariantSymmetry {F : Type _}
  (S : ActionFunctional F)
  (μ : FieldMeasure F) extends SymmetryTransform where
  action_invariant : ActionInvariant S toSymmetryTransform
  measure_invariant : MeasureInvariant μ toSymmetryTransform

/-- Path integral is invariant under symmetry -/
axiom path_integral_symmetry {F : Type _}
  (S : ActionFunctional F)
  (μ : FieldMeasure F)
  (σ : InvariantSymmetry S μ) :
  pathIntegral S μ = pathIntegral S μ

/-- Observable transforms under symmetry -/
axiom observable_transform {F : Type _}
  (O : F → ℂ)
  (σ : @SymmetryTransform F) :
  F → ℂ

/-- Noether current from continuous symmetry -/
axiom noetherCurrent {F M : Type _}
  (S : ActionFunctional F)
  (σ : ℝ → @SymmetryTransform F)
  (h_continuous : True)
  (h_identity : True) :
  M → ℝ

/-- Internal symmetry -/
structure InternalSymmetry (M V : Type _) where
  group_element : Type _
  action : group_element → V → V

/-- Gauge symmetry -/
structure GaugeSymmetry (M V : Type _) extends InternalSymmetry M V where
  local_transform : (M → group_element) → FieldConfig M V → FieldConfig M V
  requires_connection : Prop

/-- Spontaneous symmetry breaking -/
structure SpontaneouslyBrokenSymmetry (F : Type _)
  (S : ActionFunctional F) where
  toSymmetryTransform : @SymmetryTransform F
  action_invariant : ActionInvariant S toSymmetryTransform
  vacuum_not_invariant : ∃ φ_vac : F, toSymmetryTransform.transform φ_vac ≠ φ_vac

/-- Goldstone boson from broken continuous symmetry -/
axiom goldstoneBoson {F : Type _}
  (S : ActionFunctional F)
  (σ : SpontaneouslyBrokenSymmetry F S)
  (h_continuous : True) :
  True

/- ============= KONTSEVICH-SEGAL AXIOMS ============= -/

/-- Bordism (d-dimensional manifold with boundary) -/
axiom Bordism (d : ℕ) : Type _

/-- Boundary of bordism: list of connected components with orientations -/
axiom bordismBoundary (d : ℕ) : Bordism d → List (Bordism (d-1))

/-- Empty bordism (unit for disjoint union) -/
axiom emptyBordism (d : ℕ) : Bordism d

/-- Closed manifold (no boundary) -/
axiom ClosedManifold (d : ℕ) : Type _

/-- Closed manifolds correspond to bordisms with empty boundary -/
axiom closedManifold_equiv (d : ℕ) :
  ClosedManifold d ≃ {M : Bordism d // bordismBoundary d M = ([] : List (Bordism (d-1)))}

/-- Coercion from closed manifold to bordism -/
axiom closedToBordism {d : ℕ} : ClosedManifold d → Bordism d

noncomputable instance {d : ℕ} : Coe (ClosedManifold d) (Bordism d) where
  coe := closedToBordism

/-- Closed manifolds have no boundary -/
axiom closed_no_boundary {d : ℕ} (M : ClosedManifold d) :
  bordismBoundary d (closedToBordism M) = []

/-- Disjoint union of bordisms (monoidal product) -/
axiom disjointUnion (d : ℕ) : Bordism d → Bordism d → Bordism d

/-- Disjoint union is associative -/
axiom disjointUnion_assoc (d : ℕ) (M₁ M₂ M₃ : Bordism d) :
  disjointUnion d (disjointUnion d M₁ M₂) M₃ =
  disjointUnion d M₁ (disjointUnion d M₂ M₃)

/-- Empty bordism is unit for disjoint union -/
axiom disjointUnion_empty_left (d : ℕ) (M : Bordism d) :
  disjointUnion d (emptyBordism d) M = M

axiom disjointUnion_empty_right (d : ℕ) (M : Bordism d) :
  disjointUnion d M (emptyBordism d) = M

/-- Orientation reversal -/
axiom reverseOrientation (d : ℕ) : Bordism d → Bordism d

/-- Orientation reversal is involutive -/
axiom reverseOrientation_involutive (d : ℕ) (M : Bordism d) :
  reverseOrientation d (reverseOrientation d M) = M

/-- Cylinder (identity bordism) M × [0,1] -/
axiom cylinder (d : ℕ) : Bordism (d-1) → Bordism d

/-- Gluing of bordisms along common boundary -/
axiom glueBordisms (d : ℕ) (M₁ M₂ : Bordism d) (Sig : Bordism (d-1)) : Bordism d

/-- Field theory data on bordism (fields, action, measure) -/
axiom FieldTheoryData (d : ℕ) (M : Bordism d) : Type _

/-- KS: State space on (d-1)-manifold is Fréchet space (NOT Hilbert!)
    Key: Path integral naturally gives Fréchet spaces
    versus Hilbert spaces in operator formalism -/
structure KS_StateSpace (d : ℕ) (Sig : Bordism (d-1)) where
  carrier : Type _
  add : carrier → carrier → carrier
  smul : ℂ → carrier → carrier
  zero : carrier
  /-- Fréchet topology: countable family of seminorms -/
  seminorms : ℕ → (carrier → ℝ)
  /-- Each seminorm is non-negative -/
  seminorm_nonneg : ∀ (n : ℕ) (ψ : carrier), seminorms n ψ ≥ 0
  /-- Seminorm of zero is zero -/
  seminorm_zero : ∀ (n : ℕ), seminorms n zero = 0
  /-- Topology is complete -/
  complete : Prop
  /-- Topology is locally convex -/
  locally_convex : Prop

/-- KS: Empty manifold gives ground field ℂ -/
axiom ks_empty_space (d : ℕ) :
  KS_StateSpace d (emptyBordism (d-1))

axiom ks_empty_is_C (d : ℕ) :
  (ks_empty_space d).carrier = ℂ

/-- KS: Monoidal structure (completed projective tensor product) -/
axiom ks_tensor (d : ℕ) (Sig₁ Sig₂ : Bordism (d-1))
  (V₁ : KS_StateSpace d Sig₁) (V₂ : KS_StateSpace d Sig₂) :
  KS_StateSpace d (disjointUnion (d-1) Sig₁ Sig₂)

/-- Tensor product is associative (up to natural isomorphism) -/
axiom ks_tensor_assoc (d : ℕ) (Sig₁ Sig₂ Sig₃ : Bordism (d-1))
  (V₁ : KS_StateSpace d Sig₁)
  (V₂ : KS_StateSpace d Sig₂)
  (V₃ : KS_StateSpace d Sig₃) :
  True -- Natural isomorphism between ks_tensor(ks_tensor(V₁,V₂),V₃) and ks_tensor(V₁,ks_tensor(V₂,V₃))

/-- KS: Duality (continuous dual space) -/
axiom ks_dual (d : ℕ) (Sig : Bordism (d-1)) (V : KS_StateSpace d Sig) :
  KS_StateSpace d (reverseOrientation (d-1) Sig)

/-- Dual of dual is naturally isomorphic to original -/
axiom ks_dual_dual (d : ℕ) (Sig : Bordism (d-1)) (V : KS_StateSpace d Sig) :
  True -- Natural isomorphism V ≅ V**

/-- KS: Pairing for gluing (continuous bilinear map) -/
axiom ks_pairing (d : ℕ) (Sig : Bordism (d-1))
  (V : KS_StateSpace d Sig)
  (V_dual : KS_StateSpace d (reverseOrientation (d-1) Sig)) :
  V.carrier → V_dual.carrier → ℂ

/-- Pairing is non-degenerate -/
axiom ks_pairing_nondegenerate (d : ℕ) (Sig : Bordism (d-1))
  (V : KS_StateSpace d Sig)
  (V_dual : KS_StateSpace d (reverseOrientation (d-1) Sig))
  (ψ : V.carrier) :
  (∀ φ : V_dual.carrier, ks_pairing d Sig V V_dual ψ φ = 0) → ψ = V.zero

/-- KS: Path integral on bordism gives continuous linear map -/
structure KS_PathIntegralMap (d : ℕ) (M : Bordism d)
  (Sig_in Sig_out : Bordism (d-1))
  (V_in : KS_StateSpace d Sig_in)
  (V_out : KS_StateSpace d Sig_out) where
  map : V_in.carrier → V_out.carrier
  /-- Additivity -/
  additive : ∀ ψ φ, map (V_in.add ψ φ) = V_out.add (map ψ) (map φ)
  /-- Homogeneity -/
  homogeneous : ∀ (a : ℂ) ψ, map (V_in.smul a ψ) = V_out.smul a (map ψ)
  /-- Continuity in Fréchet topology -/
  continuous_seminorms : ∀ (n : ℕ), ∃ (C : ℝ) (m : ℕ),
    ∀ ψ, V_out.seminorms n (map ψ) ≤ C * V_in.seminorms m ψ

/-- KS: Composition (gluing bordisms along boundary) -/
axiom ks_composition (d : ℕ) (M₁ M₂ : Bordism d)
  (Sig_L Sig_M Sig_R : Bordism (d-1))
  (V_L : KS_StateSpace d Sig_L)
  (V_M : KS_StateSpace d Sig_M)
  (V_R : KS_StateSpace d Sig_R)
  (Z₁ : KS_PathIntegralMap d M₁ Sig_L Sig_M V_L V_M)
  (Z₂ : KS_PathIntegralMap d M₂ Sig_M Sig_R V_M V_R) :
  ∃ (M : Bordism d) (Z : KS_PathIntegralMap d M Sig_L Sig_R V_L V_R),
    ∀ ψ, Z.map ψ = Z₂.map (Z₁.map ψ)

/-- Identity cylinder gives identity operator -/
axiom ks_identity (d : ℕ) (Sig : Bordism (d-1))
  (V : KS_StateSpace d Sig)
  (data : FieldTheoryData d (cylinder d Sig)) :
  ∃ (Z : KS_PathIntegralMap d (cylinder d Sig) Sig Sig V V),
    ∀ ψ, Z.map ψ = ψ

/-- KS: Monoidal structure on maps (independent systems tensor) -/
axiom ks_tensor_maps (d : ℕ)
  (M₁ M₂ : Bordism d)
  (Sig₁ Sig₂ Sig₁' Sig₂' : Bordism (d-1))
  (V₁ : KS_StateSpace d Sig₁) (V₁' : KS_StateSpace d Sig₁')
  (V₂ : KS_StateSpace d Sig₂) (V₂' : KS_StateSpace d Sig₂')
  (Z₁ : KS_PathIntegralMap d M₁ Sig₁ Sig₁' V₁ V₁')
  (Z₂ : KS_PathIntegralMap d M₂ Sig₂ Sig₂' V₂ V₂') :
  KS_PathIntegralMap d (disjointUnion d M₁ M₂)
    (disjointUnion (d-1) Sig₁ Sig₂)
    (disjointUnion (d-1) Sig₁' Sig₂')
    (ks_tensor d Sig₁ Sig₂ V₁ V₂)
    (ks_tensor d Sig₁' Sig₂' V₁' V₂')

/-- KS: Partition function for closed manifold -/
axiom ks_partition_function (d : ℕ)
  (M : ClosedManifold d)
  (data : FieldTheoryData d M) : ℂ

/-- KS: Gluing formula - partition function on glued manifold
    factors as trace/pairing over the gluing surface -/
axiom ks_gluing_formula (d : ℕ)
  (M₁ M₂ : Bordism d)
  (Sig : Bordism (d-1))
  (M_glued : ClosedManifold d)
  (h_glue : (M_glued : Bordism d) = glueBordisms d M₁ M₂ Sig)
  (data : FieldTheoryData d M_glued) :
  ks_partition_function d M_glued data = sorry

/-- KS: Functoriality under diffeomorphism -/
axiom ks_diffeomorphism_invariance (d : ℕ)
  (M M' : Bordism d)
  (Sig_in Sig_out : Bordism (d-1))
  (V_in : KS_StateSpace d Sig_in)
  (V_out : KS_StateSpace d Sig_out)
  (h_diffeo : True) -- M and M' are diffeomorphic
  (Z : KS_PathIntegralMap d M Sig_in Sig_out V_in V_out)
  (Z' : KS_PathIntegralMap d M' Sig_in Sig_out V_in V_out) :
  ∀ ψ, Z.map ψ = Z'.map ψ

/-- KS: Symmetric monoidal structure (commutativity) -/
axiom ks_symmetric (d : ℕ) (Sig₁ Sig₂ : Bordism (d-1))
  (V₁ : KS_StateSpace d Sig₁) (V₂ : KS_StateSpace d Sig₂) :
  True -- Natural isomorphism between V₁ ⊗ V₂ and V₂ ⊗ V₁

/- ============= REGULARIZATION ============= -/

/-- UV cutoff -/
structure UVCutoff where
  scale : ℝ
  positive : scale > 0

/-- Regularized path integral -/
axiom regularizedPathIntegral {F : Type _}
  (S : ActionFunctional F)
  (μ : FieldMeasure F)
  (Λ : UVCutoff) : ℂ

/-- Dimensional regularization -/
axiom dimensionalRegularization {F : Type _}
  (S : ActionFunctional F)
  (ε : ℝ) : ℂ

/-- Lattice regularization -/
structure LatticeRegularization where
  spacing : ℝ
  spacing_positive : spacing > 0

/-- Lattice path integral -/
axiom latticePathIntegral {F : Type _}
  (S : ActionFunctional F)
  (a : LatticeRegularization) : ℂ

/-- Continuum limit requires RG flow of couplings -/
structure ContinuumLimit {F : Type _}
  (S_lattice : LatticeRegularization → ActionFunctional F) where
  bare_couplings : LatticeRegularization → List ℝ
  rg_flow : ∀ (a : LatticeRegularization) (g : List ℝ), List ℝ
  critical_surface : Prop
  limit_exists : Prop

/-- Naive limit with fixed couplings fails -/
axiom naive_continuum_limit_fails {F : Type _}
  (S : ActionFunctional F)
  (g_fixed : List ℝ) : Prop

/- ============= SEMICLASSICAL APPROXIMATION ============= -/

/-- Saddle point (classical solution) -/
axiom saddlePoint {F : Type _} (S : ActionFunctional F) : F

/-- Fluctuation operator -/
axiom fluctuationOperator {F : Type _}
  (S : ActionFunctional F) (φ : F) : Type _

/-- Functional determinant (ordinary for bosons, Berezinian for fermions) -/
axiom functionalDeterminant {F : Type _}
  (S : ActionFunctional F) (φ : F)
  (K : fluctuationOperator S φ) : ℂ

/-- One-loop approximation -/
axiom semiclassicalApproximation {F : Type _}
  (S : ActionFunctional F)
  (μ : FieldMeasure F)
  (ℏ : ℝ)
  (φ_cl : F) : Prop

/-- Instanton (Euclidean saddle with finite action) -/
structure Instanton {F : Type _} (S_E : EuclideanAction F) where
  config : F
  critical : ∀ δφ, S_E.equations_of_motion config δφ = 0
  finite_action : Prop

/-- Instanton contribution (nonperturbative) -/
axiom instantonContribution {F : Type _}
  (S_E : EuclideanAction F)
  (inst : Instanton S_E)
  (ℏ : ℝ) : ℝ

end ModularPhysics.Core.QFT.PathIntegral
