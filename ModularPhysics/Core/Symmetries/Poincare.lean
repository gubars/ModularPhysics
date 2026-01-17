import ModularPhysics.Core.Symmetries.Lorentz
import ModularPhysics.Core.SpaceTime.Basic

namespace ModularPhysics.Core.Symmetries

open SpaceTime

/-- Poincaré transformation: (Λ, a) with x ↦ Λx + a -/
structure PoincareTransform where
  lorentz : LorentzTransform
  translation : Fin 4 → ℝ

/-- Apply Poincaré transformation to spacetime point -/
noncomputable def PoincareTransform.apply (P : PoincareTransform) (x : SpaceTimePoint) : SpaceTimePoint :=
  fun μ => (P.lorentz.apply x) μ + P.translation μ

/-- Apply Poincaré transformation to a set -/
noncomputable def poincareImage (g : PoincareTransform) (O : Set SpaceTimePoint) : Set SpaceTimePoint :=
  {x | ∃ y ∈ O, x = g.apply y}

/-- Poincaré composition -/
noncomputable def poincareCompose (P₁ P₂ : PoincareTransform) : PoincareTransform where
  lorentz := lorentzCompose P₁.lorentz P₂.lorentz
  translation := fun μ => P₁.translation μ + (P₁.lorentz.apply (fun ν => P₂.translation ν)) μ

/-- Poincaré identity -/
noncomputable def poincareIdentity : PoincareTransform where
  lorentz := LorentzTransform.id
  translation := fun _ => 0

/-- Poincaré inverse -/
noncomputable def poincareInverse (P : PoincareTransform) : PoincareTransform where
  lorentz := lorentzInverse P.lorentz
  translation := fun μ => -((lorentzInverse P.lorentz).apply P.translation) μ

/-- Poincaré group structure -/
noncomputable instance : Group PoincareTransform where
  mul := poincareCompose
  one := poincareIdentity
  inv := poincareInverse
  mul_assoc := by sorry
  one_mul := by sorry
  mul_one := by sorry
  inv_mul_cancel := by sorry

end ModularPhysics.Core.Symmetries
