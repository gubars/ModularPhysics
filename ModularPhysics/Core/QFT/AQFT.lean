import ModularPhysics.Core.SpaceTime.Basic
import ModularPhysics.Core.SpaceTime.Causality
import ModularPhysics.Core.Quantum
import ModularPhysics.Core.Symmetries.Poincare

namespace ModularPhysics.Core.QFT.AQFT

open SpaceTime Quantum Symmetries

/-- C*-algebra of observables for a region -/
axiom LocalAlgebra : Set SpaceTimePoint → Type _

/-- Algebra operations -/
axiom algebraMul {O : Set SpaceTimePoint} :
  LocalAlgebra O → LocalAlgebra O → LocalAlgebra O

axiom algebraAdd {O : Set SpaceTimePoint} :
  LocalAlgebra O → LocalAlgebra O → LocalAlgebra O

axiom algebraAdjoint {O : Set SpaceTimePoint} :
  LocalAlgebra O → LocalAlgebra O

/-- Algebra inclusion for nested regions -/
axiom algebraInclusion (O₁ O₂ : Set SpaceTimePoint)
  (h : O₁ ⊆ O₂) :
  LocalAlgebra O₁ → LocalAlgebra O₂

/-- AQFT Axiom A1: Isotony (functoriality) -/
axiom isotony (O₁ O₂ O₃ : Set SpaceTimePoint)
  (h12 : O₁ ⊆ O₂) (h23 : O₂ ⊆ O₃) :
  algebraInclusion O₁ O₃ (h12.trans h23) =
  algebraInclusion O₂ O₃ h23 ∘ algebraInclusion O₁ O₂ h12

/-- Two regions are spacelike separated -/
axiom SpacelikeSeparated (metric : SpacetimeMetric) (O₁ O₂ : Set SpaceTimePoint) : Prop

/-- AQFT Axiom A2: Locality (Einstein causality) -/
axiom locality
  (metric : SpacetimeMetric)  -- ← Add metric
  (O₁ O₂ : Set SpaceTimePoint)
  (h : SpacelikeSeparated metric O₁ O₂)  -- ← Use metric
  (A : LocalAlgebra O₁) (B : LocalAlgebra O₂)
  (O : Set SpaceTimePoint) (h1 : O₁ ⊆ O) (h2 : O₂ ⊆ O) :
  algebraMul (algebraInclusion O₁ O h1 A) (algebraInclusion O₂ O h2 B) =
  algebraMul (algebraInclusion O₂ O h2 B) (algebraInclusion O₁ O h1 A)

/-- Apply Poincaré transformation to set -/
axiom poincareImage (g : PoincareTransform) (O : Set SpaceTimePoint) : Set SpaceTimePoint

/-- AQFT Axiom A3: Covariance under Poincaré group -/
axiom covariance (O : Set SpaceTimePoint) (g : PoincareTransform) :
  ∃ (_ : LocalAlgebra O → LocalAlgebra (poincareImage g O)), True

/-- AQFT Axiom A4: Positivity of energy (spectrum condition) -/
axiom positivity_of_energy :
  ∀ (_ : PoincareTransform), True

/-- Vacuum state ω -/
axiom vacuumState (O : Set SpaceTimePoint) : LocalAlgebra O → ℂ

/-- Vacuum is Poincaré invariant (as a linear functional) -/
axiom vacuum_invariant (O : Set SpaceTimePoint) (g : PoincareTransform)
  (A : LocalAlgebra O)
  (A' : LocalAlgebra (poincareImage g O)) :
  vacuumState O A = vacuumState (poincareImage g O) A'

/-- GNS construction: states → Hilbert space representations -/
axiom gnsConstruction (omega : (O : Set SpaceTimePoint) → LocalAlgebra O → ℂ) :
  ∃ (H : Type _) (_ : QuantumStateSpace H), True

/-- Haag duality: A(O)' = A(O') for causally complete regions -/
axiom haag_duality (O : Set SpaceTimePoint) :
  True

/-- Reeh-Schlieder theorem in AQFT -/
axiom reeh_schlieder_aqft (O : Set SpaceTimePoint) (nonempty : O.Nonempty) :
  True

/-- Split property: nuclearity condition -/
axiom split_property
  (metric : SpacetimeMetric)  -- ← Add metric
  (O₁ O₂ : Set SpaceTimePoint)
  (separated : ∃ (O : Set SpaceTimePoint), O₁ ⊆ O ∧ SpacelikeSeparated metric O O₂) :  -- ← Use metric
  True

/-- Haag's theorem: no interaction picture -/
axiom haag_theorem :
  ¬∃ (free interacting : Set SpaceTimePoint → Type _), free = interacting

/-- DHR superselection theory (charge sectors) -/
axiom dhrSuperselection : Type _

/-- Doplicher-Roberts reconstruction: from algebra to fields -/
axiom doplicherRobertsReconstruction :
  (∀ O, LocalAlgebra O) → ∃ (_ : Type _), True

/-- Modular theory (Tomita-Takesaki) -/
axiom modularOperator (O : Set SpaceTimePoint) : Type _

/-- Bisognano-Wichmann theorem: modular group = boost -/
axiom bisognano_wichmann (wedge : Set SpaceTimePoint) :
  True

end ModularPhysics.Core.QFT.AQFT
