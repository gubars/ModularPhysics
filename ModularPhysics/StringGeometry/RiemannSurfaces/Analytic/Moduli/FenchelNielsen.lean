import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Fenchel-Nielsen Coordinates

This file defines Fenchel-Nielsen coordinates on Teichmüller space.

## Mathematical Background

For a pants decomposition of a surface Σ_g (3g - 3 simple closed curves), we get
global coordinates on Teichmüller space T_g:
- l_i ∈ ℝ_{>0}: hyperbolic length of i-th curve (3g - 3 parameters)
- θ_i ∈ ℝ: twist parameter (3g - 3 parameters)

These (l, θ) give a real-analytic diffeomorphism:
  T_g ≅ ℝ_{>0}^{3g-3} × ℝ^{3g-3}

showing T_g is diffeomorphic to ℝ^{6g-6}.

## Main Definitions

* `FenchelNielsenCoordinates` - Length and twist parameters for T_g

## References

* Wolpert "Fenchel-Nielsen deformation"
* Hubbard "Teichmüller Theory" Vol I
-/

namespace RiemannSurfaces.Analytic

/-- Fenchel-Nielsen coordinates on Teichmüller space T_g.

    For a pants decomposition of Σ_g (3g - 3 simple closed curves), we get
    global coordinates on T_g:
    - l_i ∈ ℝ_{>0}: hyperbolic length of i-th curve (3g - 3 parameters)
    - θ_i ∈ ℝ/2πℤ: twist parameter (3g - 3 parameters)

    These (l, θ) give a real-analytic diffeomorphism:
      T_g ≅ ℝ_{>0}^{3g-3} × ℝ^{3g-3}

    showing T_g is diffeomorphic to ℝ^{6g-6}.

    Note: We use 3 * g - 3 directly. For g ≥ 2, this equals the complex
    dimension of T_g. For g = 0, 1 this gives 0 which is correct. -/
structure FenchelNielsenCoordinates (g : ℕ) where
  /-- Length parameters l_i > 0 for each curve in pants decomposition -/
  lengths : Fin (3 * g - 3) → ℝ
  /-- All lengths are positive -/
  lengths_pos : ∀ i, lengths i > 0
  /-- Twist parameters θ_i ∈ ℝ (lift of angle in ℝ/2πℤ) -/
  twists : Fin (3 * g - 3) → ℝ

/-- Number of curves in a pants decomposition of a genus g surface -/
def pantsDecompositionSize (g : ℕ) : ℕ := 3 * g - 3

/-- Real dimension of Teichmüller space T_g (for g ≥ 2) -/
def teichmullerRealDimension (g : ℕ) : ℕ := 6 * g - 6

/-- Complex dimension equals 3g - 3 -/
theorem teichmuller_complex_dimension (g : ℕ) (hg : g ≥ 1) :
    teichmullerRealDimension g = 2 * pantsDecompositionSize g := by
  unfold teichmullerRealDimension pantsDecompositionSize
  omega

/-- The total twist parameter (sum of all twists) -/
noncomputable def FenchelNielsenCoordinates.totalTwist {g : ℕ}
    (fn : FenchelNielsenCoordinates g) : ℝ :=
  Finset.sum Finset.univ fn.twists

/-- The total length parameter (sum of all lengths) -/
noncomputable def FenchelNielsenCoordinates.totalLength {g : ℕ}
    (fn : FenchelNielsenCoordinates g) : ℝ :=
  Finset.sum Finset.univ fn.lengths

/-- Total length is positive (when g ≥ 2) -/
theorem FenchelNielsenCoordinates.totalLength_pos {g : ℕ} (hg : g ≥ 2)
    (fn : FenchelNielsenCoordinates g) : fn.totalLength > 0 := by
  unfold totalLength
  have hpos : 3 * g - 3 > 0 := by omega
  have hne : (Finset.univ : Finset (Fin (3 * g - 3))).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fin.pos_iff_nonempty.mp hpos
  exact Finset.sum_pos (fun i _ => fn.lengths_pos i) hne

/-- Scaling lengths by a positive factor -/
noncomputable def FenchelNielsenCoordinates.scaleLengths {g : ℕ}
    (fn : FenchelNielsenCoordinates g) (c : ℝ) (hc : c > 0) :
    FenchelNielsenCoordinates g where
  lengths := fun i => c * fn.lengths i
  lengths_pos := fun i => mul_pos hc (fn.lengths_pos i)
  twists := fn.twists

/-- Shifting all twists by a constant -/
def FenchelNielsenCoordinates.shiftTwists {g : ℕ}
    (fn : FenchelNielsenCoordinates g) (θ : ℝ) :
    FenchelNielsenCoordinates g where
  lengths := fn.lengths
  lengths_pos := fn.lengths_pos
  twists := fun i => fn.twists i + θ

end RiemannSurfaces.Analytic
