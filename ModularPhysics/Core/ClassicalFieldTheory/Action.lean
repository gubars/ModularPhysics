import ModularPhysics.Core.ClassicalFieldTheory.Fields

namespace ModularPhysics.Core.ClassicalFieldTheory

/-- Action functional S[φ] = ∫ L d⁴x -/
axiom Action {F : Type*} : ClassicalField F → ℝ

/-- Lagrangian density L(φ, ∂φ) -/
axiom lagrangianDensity {F : Type*} :
  ClassicalField F → SpaceTimePoint → ℝ

/-- Hamiltonian density H(φ, π) -/
axiom hamiltonianDensity {F : Type*} :
  ClassicalField F → SpaceTimePoint → ℝ

/-- Canonical momentum π = ∂L/∂(∂_t φ) -/
axiom canonicalMomentum {F : Type*} : ClassicalField F → ClassicalField F

/-- Legendre transform: H = πφ̇ - L -/
axiom legendreTransform {F : Type*} : ClassicalField F → Prop

/-- Poisson bracket {F, G} -/
axiom poissonBracket {F G : Type*} :
  ClassicalField F → ClassicalField G → ℝ

end ModularPhysics.Core.ClassicalFieldTheory
