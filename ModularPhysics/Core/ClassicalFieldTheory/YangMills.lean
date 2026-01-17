import ModularPhysics.Core.ClassicalFieldTheory.Electromagnetic

namespace ModularPhysics.Core.ClassicalFieldTheory

/-- Lie algebra-valued gauge field A_μ = A_μ^a T^a -/
axiom YMField : Type*

/-- Lie algebra element -/
axiom LieAlgebraElement : Type*

/-- Yang-Mills field strength: F_μν = ∂_μ A_ν - ∂_ν A_μ + [A_μ, A_ν] -/
axiom ymFieldStrength (A : YMField) : TensorField 4 4

/-- Yang-Mills Lagrangian: L = -(1/2)Tr(F_μν F^μν) -/
axiom yangMillsLagrangian (A : YMField) : ScalarField

/-- Yang-Mills equations: D_μ F^μν = J^ν where D_μ is covariant derivative -/
axiom yangMillsEquations (A : YMField) (x : SpaceTimePoint) : Prop

/-- Gauge covariant derivative: D_μ = ∂_μ + ig A_μ -/
axiom gaugeCovariantDerivative (A : YMField) :
  SpaceTimePoint → Fin 4 → LieAlgebraElement

/-- Non-abelian gauge transformation: A_μ → U A_μ U⁻¹ - (i/g)(∂_μ U)U⁻¹ -/
axiom nonAbelianGaugeTransform (A : YMField) (U : SpaceTimePoint → YMField) : YMField

/-- Instanton solution (self-dual): F = *F -/
axiom instanton : YMField

/-- Topological charge (Pontryagin index): Q = ∫ Tr(F ∧ F) -/
axiom topologicalCharge (A : YMField) : ℤ

/-- θ-vacuum angle -/
axiom thetaVacuum (theta : ℝ) : Prop

end ModularPhysics.Core.ClassicalFieldTheory
