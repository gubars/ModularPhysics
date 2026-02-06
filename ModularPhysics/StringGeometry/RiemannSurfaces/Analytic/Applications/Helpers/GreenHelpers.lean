import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Green's Function Helpers

This file provides helper definitions and lemmas for Green's function theory.

## Main definitions

* Fundamental solution properties
* Poisson kernel properties
* Disk Green's function properties

## Implementation Notes

We prove basic properties using Mathlib's norm and logarithm theory.
-/

namespace RiemannSurfaces.Analytic.Helpers

open Complex Real

/-!
## Fundamental Solution

The fundamental solution G₀(z, w) = -(1/2π) log|z - w| satisfies Δ G₀ = δ.
-/

/-- The fundamental solution -/
noncomputable def fundamentalSol (w z : ℂ) : ℝ :=
  -(1 / (2 * Real.pi)) * Real.log ‖z - w‖

/-- Fundamental solution is symmetric -/
theorem fundamentalSol_symm (z w : ℂ) :
    fundamentalSol z w = fundamentalSol w z := by
  simp only [fundamentalSol, norm_sub_rev]

/-- Fundamental solution at z = w is undefined (would be -∞) -/
theorem fundamentalSol_at_pole (w : ℂ) :
    ‖w - w‖ = 0 := by
  simp

/-!
## Disk Green's Function

G_D(z, w) = -(1/2π) log|z - w| + (1/2π) log|1 - w̄z| for the unit disk.
-/

/-- Reflection of w across the unit circle -/
noncomputable def reflection (w : ℂ) (_ : w ≠ 0) : ℂ :=
  1 / (starRingEnd ℂ w)

/-- Reflection maps interior to exterior -/
theorem reflection_norm (w : ℂ) (hw : w ≠ 0) (hwlt : ‖w‖ < 1) :
    ‖reflection w hw‖ > 1 := by
  unfold reflection
  rw [norm_div, norm_one]
  simp only [RCLike.norm_conj]
  rw [one_div]
  -- ‖w‖⁻¹ > 1 iff ‖w‖ < 1 (for ‖w‖ > 0)
  rw [gt_iff_lt, one_lt_inv₀ (norm_pos_iff.mpr hw)]
  exact hwlt

/-- The correction term in disk Green's function -/
noncomputable def diskCorrection (w z : ℂ) : ℝ :=
  (1 / (2 * Real.pi)) * Real.log ‖1 - (starRingEnd ℂ) w * z‖

/-- Disk Green's function -/
noncomputable def diskGreenDef (w z : ℂ) : ℝ :=
  fundamentalSol w z + diskCorrection w z

/-- Key identity: |z - w|² = |1 - w̄z|² when |z| = 1.
    Proof: Both expand to 1 - zw̄ - wz̄ + |w|² using |z|² = 1. -/
theorem norm_sub_sq_eq_norm_one_sub_conj_mul_sq (w z : ℂ) (hz : ‖z‖ = 1) :
    ‖z - w‖^2 = ‖1 - (starRingEnd ℂ) w * z‖^2 := by
  -- Convert to normSq which is easier to compute with
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  -- Key fact: |z|² = 1
  have hz2 : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz, one_pow]
  -- Expand |z - w|² = |z|² + |w|² - 2*(z * conj w).re
  rw [Complex.normSq_sub, hz2]
  -- Expand |1 - w̄z|² = 1 + |w̄z|² - 2*((1 : ℂ) * conj(conj w * z)).re
  rw [Complex.normSq_sub, Complex.normSq_one]
  -- |w̄z|² = |w̄|² · |z|² = |w|² · 1 = |w|²
  rw [Complex.normSq_mul, Complex.normSq_conj, hz2, mul_one]
  -- Simplify: conj(conj w * z) = conj(conj w) * conj z = w * conj z
  -- And (z * conj w).re = (w * conj z).re
  simp only [map_mul, RingHomCompTriple.comp_apply, one_mul]
  -- Now the goal is about real parts being equal
  -- (z * conj w).re = (w * conj z).re
  have h : (z * (starRingEnd ℂ) w).re = (w * (starRingEnd ℂ) z).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  -- RingHom.id ℂ w = w
  simp only [RingHom.id_apply]
  linarith

/-- At boundary |z| = 1: |z - w| = |1 - w̄z|. -/
theorem boundary_identity (w z : ℂ) (hz : ‖z‖ = 1) :
    ‖z - w‖ = ‖1 - (starRingEnd ℂ) w * z‖ := by
  have h := norm_sub_sq_eq_norm_one_sub_conj_mul_sq w z hz
  have h1 : ‖z - w‖ ≥ 0 := norm_nonneg _
  have h2 : ‖1 - (starRingEnd ℂ) w * z‖ ≥ 0 := norm_nonneg _
  exact sq_eq_sq₀ h1 h2 |>.mp h

/-- Disk Green's function vanishes on boundary -/
theorem diskGreen_vanishes_boundary (w z : ℂ) (_ : ‖w‖ < 1) (hz : ‖z‖ = 1) :
    diskGreenDef w z = 0 := by
  unfold diskGreenDef fundamentalSol diskCorrection
  -- Use boundary_identity: |z - w| = |1 - w̄z| when |z| = 1
  rw [boundary_identity w z hz]
  ring

/-!
## Poisson Kernel

P(z, ζ) = (1 - |z|²) / |ζ - z|² for |z| < 1, |ζ| = 1.
-/

/-- Poisson kernel definition -/
noncomputable def poissonKernelDef (z ζ : ℂ) : ℝ :=
  (1 - ‖z‖^2) / ‖ζ - z‖^2

/-- Poisson kernel is positive inside the disk -/
theorem poissonKernel_pos (z ζ : ℂ) (hz : ‖z‖ < 1) (_ : ‖ζ‖ = 1) (hne : z ≠ ζ) :
    poissonKernelDef z ζ > 0 := by
  unfold poissonKernelDef
  apply div_pos
  · -- 1 - |z|² > 0 since |z| < 1
    have h1 : ‖z‖^2 < 1 := by
      calc ‖z‖^2 < 1^2 := sq_lt_sq' (by linarith [norm_nonneg z]) hz
        _ = 1 := one_pow 2
    linarith
  · -- |ζ - z|² > 0 since ζ ≠ z
    apply sq_pos_of_pos
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr (Ne.symm hne)

/-!
## Symmetry Properties

Green's functions are symmetric: G(z, w) = G(w, z).
-/

/-- Helper: |1 - z̄w| = |1 - w̄z| -/
theorem norm_one_sub_conj_mul_symm (z w : ℂ) :
    ‖1 - (starRingEnd ℂ) z * w‖ = ‖1 - (starRingEnd ℂ) w * z‖ := by
  -- Use that conj(1 - z̄w) = 1 - zw̄ and |conj(a)| = |a|
  have h : (starRingEnd ℂ) (1 - (starRingEnd ℂ) z * w) = 1 - z * (starRingEnd ℂ) w := by
    simp only [map_sub, map_one, map_mul, RingHomCompTriple.comp_apply]
    rfl
  rw [← RCLike.norm_conj (1 - (starRingEnd ℂ) z * w), h]
  -- Now 1 - z * w̄ = 1 - w̄ * z by commutativity of multiplication in ℂ
  congr 1
  ring

/-- Disk Green's function is symmetric -/
theorem diskGreen_symm (z w : ℂ) :
    diskGreenDef z w = diskGreenDef w z := by
  unfold diskGreenDef
  -- Uses fundamentalSol_symm and that |1 - z̄w| = |1 - w̄z|
  rw [fundamentalSol_symm]
  unfold diskCorrection
  rw [norm_one_sub_conj_mul_symm]

end RiemannSurfaces.Analytic.Helpers
