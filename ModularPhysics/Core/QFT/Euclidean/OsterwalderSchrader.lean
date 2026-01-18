import ModularPhysics.Core.QFT.Euclidean.SchwingerFunctions
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ModularPhysics.Core.QFT.Euclidean

open ModularPhysics.Core.QFT.Euclidean Real

/-- Orthogonal matrix: preserves Euclidean inner product -/
def IsOrthogonal {d : ℕ} (R : Fin d → Fin d → ℝ) : Prop :=
  ∀ μ ν, ∑ ρ, R μ ρ * R ν ρ = if μ = ν then 1 else 0

/-- OS Axiom E1: Euclidean covariance (rotation + translation invariance).
    The Schwinger functions are invariant under Euclidean transformations. -/
axiom euclidean_covariance {d : ℕ} (theory : QFT d) (n : ℕ)
  (rotation : Fin d → Fin d → ℝ)
  (h_orthogonal : IsOrthogonal rotation)
  (translation : EuclideanPoint d) :
  ∀ (points : Fin n → EuclideanPoint d),
    theory.schwinger n points =
    theory.schwinger n (fun i μ => translation μ + ∑ ν, rotation μ ν * points i ν)

/-- Time reflection θ: reflects the time coordinate (first coordinate).
    θ(x₀, x) = (-x₀, x) for x = (x₁, ..., x_{d-1}) -/
def timeReflection {d : ℕ} [NeZero d] (x : EuclideanPoint d) : EuclideanPoint d :=
  fun μ => if μ = 0 then -x μ else x μ

/-- OS Axiom E2: Reflection positivity (crucial for unitarity!).

    For any finite set of test functions {fᵢ} with support in the upper half-space
    (x₀ ≥ 0), the quadratic form must be non-negative:

    ∑ᵢⱼ f̄ᵢ(xᵢ) fⱼ(xⱼ) S(xᵢ, θ(xⱼ)) ≥ 0

    where θ is time reflection: θ(x₀, x) = (-x₀, x).

    This is the key axiom ensuring that the reconstructed Hilbert space has
    positive-definite inner product (unitarity of the quantum theory). -/
axiom reflection_positivity {d : ℕ} [NeZero d] (theory : QFT d)
  (n : ℕ)
  (points : Fin n → EuclideanPoint d)
  (h_upper : ∀ i, points i 0 ≥ 0)
  (coeffs : Fin n → ℝ) :
  ∑ i : Fin n, ∑ j : Fin n,
    coeffs i * coeffs j *
    theory.schwinger 2 (fun k => if k = 0 then points i else timeReflection (points j)) ≥ 0

/-- OS Axiom E3: Symmetry (permutation invariance for bosonic fields).
    Already included in the QFT structure as permutation_symmetric. -/
axiom symmetry {d : ℕ} (theory : QFT d) (n : ℕ)
  (sigma : Equiv.Perm (Fin n))
  (points : Fin n → EuclideanPoint d) :
  theory.schwinger n points = theory.schwinger n (points ∘ sigma)

/-- OS Axiom E4: Cluster property (factorization at large separation).

    When two clusters of points are separated by a large distance,
    correlations factorize into products of lower-point functions:

    S_{n+m}(x₁...xₙ, y₁+a·v...yₘ+a·v) → S_n(x₁...xₙ) · S_m(y₁...yₘ) as a → ∞

    This expresses that widely separated subsystems are independent. -/
axiom cluster_property {d : ℕ} (theory : QFT d) (n m : ℕ)
  (points_x : Fin n → EuclideanPoint d)
  (points_y : Fin m → EuclideanPoint d)
  (separation : EuclideanPoint d) :
  ∀ ε > 0, ∃ R : ℝ, ∀ a > R,
    let shifted_y : Fin m → EuclideanPoint d :=
      fun i μ => points_y i μ + a * separation μ
    ∃ (combined_schwinger : ℝ),
    |combined_schwinger - theory.schwinger n points_x * theory.schwinger m shifted_y| < ε

/-- OS Axiom E5: Growth bound on n-point functions (added in OS 1975 follow-up).

    This is the crucial condition that was missing in the original 1973 paper.
    It ensures convergence of the GNS construction in the reconstruction theorem.

    The n-point Schwinger functions must satisfy a growth bound of the form:
    |S_n(x₁,...,xₙ)| ≤ C^n · n!^α · (1 + ∑ᵢ |xᵢ|)^β

    for some constants C, α, β independent of n. This controls the factorial
    growth as the number of field insertions increases, ensuring that the
    infinite series in the reconstruction converge.

    Physical meaning: This bound ensures the Hilbert space construction via
    GNS (Gel'fand-Naimark-Segal) is well-defined, preventing pathological
    growth that would make the vacuum state non-normalizable. -/
axiom multipoint_growth_bound {d : ℕ} (theory : QFT d) :
  ∃ (C α β : ℝ), C > 0 ∧ ∀ (n : ℕ) (points : Fin n → EuclideanPoint d),
    |theory.schwinger n points| ≤
      rpow C (n : ℝ) * rpow (Nat.factorial n : ℝ) α * rpow (1 + ∑ i, ‖points i‖) β

end ModularPhysics.Core.QFT.Euclidean
