/-
  Basic Definitions for Glimm-Jaffe Construction of φ⁴₂ Theory

  This module provides foundational definitions used throughout the
  construction of 2D φ⁴ theory following Glimm-Jaffe "Quantum Physics:
  A Functional Integral Point of View" (1987).

  The construction proceeds in stages:
  1. Lattice approximation (Ch 9.5-9.6)
  2. Correlation inequalities (Ch 4, 10.2)
  3. Reflection positivity (Ch 10.4)
  4. Multiple reflections and upper bounds (Ch 10.5, 11.3)
  5. Infinite volume limit (Ch 11.2)
  6. Regularity and axioms (Ch 12)

  References:
  - Glimm-Jaffe (1987) "Quantum Physics: A Functional Integral Point of View"
  - Osterwalder-Schrader (1973, 1975) Axioms for Euclidean Green's functions
-/

import ModularPhysics.Core.QFT.Euclidean.SchwingerFunctions
import ModularPhysics.Core.QFT.Euclidean.OsterwalderSchrader

namespace ModularPhysics.Papers.GlimmJaffe

-- Re-export from Core/QFT/Euclidean for convenience
open ModularPhysics.Core.QFT.Euclidean

/-! ## Euclidean Space

We use the definitions from Core/QFT/Euclidean:
- `EuclideanPoint d` : points in d-dimensional Euclidean space
- `euclideanOrigin d` : the origin
- `euclideanDistance` : Euclidean distance
- `radialDistance` : distance from origin
- `timeReflection` : time reflection operator Θ
- `IsOrthogonal` : orthogonal matrix predicate
-/

/-- Alias for Core's euclideanOrigin for local use -/
abbrev origin (d : ℕ) : EuclideanPoint d := euclideanOrigin d

/-- Alias for Core's euclideanDistance -/
noncomputable abbrev euclideanDist {d : ℕ} (x y : EuclideanPoint d) : ℝ :=
  euclideanDistance x y

/-! ## Lattice Structure -/

/-- A lattice in Rᵈ with spacing δ -/
structure Lattice (d : ℕ) where
  spacing : ℝ
  spacing_pos : spacing > 0

/-- Number of lattice sites in a box of side L -/
noncomputable def Lattice.numSitesInBox {d : ℕ} (lat : Lattice d) (L : ℝ) : ℕ :=
  Nat.floor ((L / lat.spacing) ^ d)

/-- A configuration of field values on a finite lattice -/
def LatticeConfig (numSites : ℕ) := Fin numSites → ℝ

/-! ## Additional Reflection Operations

Core provides `timeReflection`. We add coordinate reflection and translation.
-/

/-- Spatial reflection in coordinate μ -/
def coordinateReflection {d : ℕ} (μ₀ : Fin d) (x : EuclideanPoint d) : EuclideanPoint d :=
  fun μ => if μ = μ₀ then -x μ else x μ

/-- Translation by vector a -/
def translate {d : ℕ} (a : EuclideanPoint d) (x : EuclideanPoint d) : EuclideanPoint d :=
  fun μ => x μ + a μ

/-! ## Orthogonal Transformations

Core provides `IsOrthogonal` (checking R·Rᵀ = I).
We provide a stronger version and application function.
-/

/-- An orthogonal matrix (rotation/reflection) - checks both R·Rᵀ = I and Rᵀ·R = I -/
def IsOrthogonalStrong {d : ℕ} (R : Fin d → Fin d → ℝ) : Prop :=
  (∀ i j, ∑ k, R i k * R j k = if i = j then 1 else 0) ∧
  (∀ i j, ∑ k, R k i * R k j = if i = j then 1 else 0)

/-- Strong orthogonality implies Core's orthogonality -/
theorem IsOrthogonalStrong.toIsOrthogonal {d : ℕ} {R : Fin d → Fin d → ℝ}
    (h : IsOrthogonalStrong R) : IsOrthogonal R := h.1

/-- Apply orthogonal transformation to a point -/
def applyOrthogonal {d : ℕ} (R : Fin d → Fin d → ℝ) (x : EuclideanPoint d) : EuclideanPoint d :=
  fun μ => ∑ ν, R μ ν * x ν

/-! ## Bare Parameters -/

/-- Bare parameters of φ⁴ theory before renormalization -/
structure BareParameters where
  /-- Bare mass squared (can be negative for spontaneous symmetry breaking) -/
  m₀_sq : ℝ
  /-- Bare coupling constant -/
  lambda : ℝ
  /-- Coupling must be positive for stability -/
  lambda_pos : lambda > 0
  /-- UV cutoff (inverse lattice spacing) -/
  cutoff : ℝ
  /-- Cutoff must be positive -/
  cutoff_pos : cutoff > 0

/-- Bare mass (when m₀² > 0) -/
noncomputable def BareParameters.m₀ (params : BareParameters) : ℝ :=
  if params.m₀_sq ≥ 0 then Real.sqrt params.m₀_sq else 0

/-- Lattice spacing from cutoff: δ = 1/Λ -/
noncomputable def BareParameters.latticeSpacing (params : BareParameters) : ℝ :=
  1 / params.cutoff

/-! ## Physical (Renormalized) Parameters -/

/-- Physical parameters after renormalization -/
structure PhysicalParameters where
  /-- Physical mass (pole of propagator) -/
  m_phys : ℝ
  /-- Physical mass is positive -/
  m_phys_pos : m_phys > 0
  /-- Physical coupling (from scattering amplitude) -/
  lambda_phys : ℝ
  /-- Physical coupling is non-negative -/
  lambda_phys_nonneg : lambda_phys ≥ 0

/-! ## Polynomial Interactions -/

/-- A polynomial P(φ) for P(φ)₂ theories -/
structure InteractionPolynomial where
  /-- Coefficients: P(φ) = Σᵢ aᵢ φⁱ -/
  coeffs : ℕ → ℝ
  /-- Degree of the polynomial -/
  degree : ℕ
  /-- Only finitely many nonzero coefficients -/
  finite_support : ∀ n > degree, coeffs n = 0
  /-- Leading coefficient is positive (for stability) -/
  leading_pos : coeffs degree > 0
  /-- Degree is even (for stability) -/
  degree_even : Even degree

/-- The φ⁴ interaction polynomial: P(φ) = λφ⁴/4! + m²φ²/2
    Requires λ > 0 for stability (leading coefficient positive). -/
noncomputable def phi4Polynomial (m_sq lambda : ℝ) (h_lambda : lambda > 0) : InteractionPolynomial where
  coeffs := fun n =>
    if n = 4 then lambda / 24
    else if n = 2 then m_sq / 2
    else 0
  degree := 4
  finite_support := by intro n hn; split_ifs with h1 h2 <;> [omega; omega; rfl]
  leading_pos := by
    simp only
    -- coeffs 4 = lambda / 24, and lambda > 0
    show lambda / 24 > 0
    positivity
  degree_even := ⟨2, rfl⟩

/-- Evaluate polynomial at a point (for small degree, explicit sum suffices) -/
noncomputable def InteractionPolynomial.eval (P : InteractionPolynomial) (φ : ℝ) : ℝ :=
  -- For P(φ)₂ theories, degree ≤ 4 is typical, so explicit evaluation is fine
  P.coeffs 0 + P.coeffs 1 * φ + P.coeffs 2 * φ^2 + P.coeffs 3 * φ^3 + P.coeffs 4 * φ^4

/-! ## Dimension Counting -/

/-- Mass dimension of a quantity in d dimensions -/
def massDimension (_d : ℕ) : Type := ℤ

/-- Coupling dimension [λ] = 4 - d for φ⁴ theory -/
def couplingDimension (d : ℕ) : ℤ := 4 - d

/-- A theory is super-renormalizable if [λ] > 0 -/
def isSuperRenormalizable (d : ℕ) : Prop := couplingDimension d > 0

/-- φ⁴₂ is super-renormalizable: [λ] = 4 - 2 = 2 > 0 -/
theorem phi4_2d_super_renormalizable : isSuperRenormalizable 2 := by
  unfold isSuperRenormalizable couplingDimension
  norm_num

end ModularPhysics.Papers.GlimmJaffe
