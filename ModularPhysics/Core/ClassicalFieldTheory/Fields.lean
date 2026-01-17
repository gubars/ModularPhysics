import ModularPhysics.Core.SpaceTime.Basic
import ModularPhysics.Core.SpaceTime.Metrics

namespace ModularPhysics.Core.ClassicalFieldTheory

open SpaceTime

/-- Classical field configuration: maps spacetime points to values -/
def ClassicalField (F : Type*) := SpaceTimePoint → F

/-- Scalar field -/
abbrev ScalarField := ClassicalField ℝ

/-- Complex scalar field -/
abbrev ComplexScalarField := ClassicalField ℂ

/-- Vector field (4-vector at each point) -/
abbrev VectorField := ClassicalField (Fin 4 → ℝ)

/-- Tensor field -/
def TensorField (m n : ℕ) := ClassicalField (Fin m → Fin n → ℝ)

/-- Spinor field (axiomatized) -/
axiom SpinorField : Type*

/-- Dirac spinor -/
axiom DiracSpinor : Type*

/-- Partial derivative ∂_μ φ -/
axiom partialDerivative {F : Type*} :
  ClassicalField F → Fin 4 → ClassicalField F

/-- Covariant derivative ∇_μ (uses metric connection) -/
axiom covariantDerivative {F : Type*} :
  SpacetimeMetric → ClassicalField F → Fin 4 → ClassicalField F

/-- d'Alembertian operator □ = ∂_μ ∂^μ (flat spacetime) -/
axiom dalembertian : ScalarField → ScalarField

/-- Laplacian in curved spacetime -/
axiom laplacian : SpacetimeMetric → ScalarField → ScalarField

/-- Lie derivative along vector field -/
axiom lieDerivative {F : Type*} :
  VectorField → ClassicalField F → ClassicalField F

/-- Exterior derivative -/
axiom exteriorDerivative : VectorField → TensorField 4 4

end ModularPhysics.Core.ClassicalFieldTheory
