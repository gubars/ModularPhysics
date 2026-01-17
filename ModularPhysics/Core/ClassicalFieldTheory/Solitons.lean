import ModularPhysics.Core.ClassicalFieldTheory.Scalar
import ModularPhysics.Core.ClassicalFieldTheory.YangMills

namespace ModularPhysics.Core.ClassicalFieldTheory

/-- Kink solution (φ⁴ in 1+1D) -/
axiom kinkSolution : ScalarField

/-- Domain wall -/
axiom domainWall : ScalarField

/-- Vortex solution (Abrikosov-Nielsen-Olesen) -/
axiom vortexSolution : ComplexScalarField × EMPotential

/-- Monopole solution ('t Hooft-Polyakov) -/
axiom magneticMonopole : YMField

/-- Skyrmion -/
axiom skyrmion : VectorField

/-- Cosmic string -/
axiom cosmicString : ScalarField

/-- Topological charge for solitons -/
axiom solitonCharge {F : Type*} (phi : ClassicalField F) : ℤ

/-- Soliton stability from topology -/
axiom soliton_stable {F : Type*} (phi : ClassicalField F)
    (h : solitonCharge phi ≠ 0) :
  ∃ (E_min : ℝ), ∀ (psi : ClassicalField F),
    solitonCharge psi = solitonCharge phi → totalEnergy psi ≥ E_min

end ModularPhysics.Core.ClassicalFieldTheory
