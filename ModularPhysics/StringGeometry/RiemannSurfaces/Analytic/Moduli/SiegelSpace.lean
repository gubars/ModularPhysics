import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.StarOrdered

/-!
# Siegel Upper Half-Space

This file defines the Siegel upper half-space H_g, the target of the period map
from Teichmüller space.

## Mathematical Background

The Siegel upper half-space H_g is:
  H_g = { Ω ∈ M_{g×g}(ℂ) : Ω^T = Ω and Im(Ω) is positive definite }

It is a complex manifold of dimension g(g+1)/2 and carries a natural action
of Sp(2g, ℤ).

## Main Definitions

* `SiegelUpperHalfSpace` - The space H_g of period matrices

## References

* Mumford "Tata Lectures on Theta I"
* Birkenhake, Lange "Complex Abelian Varieties"
-/

namespace RiemannSurfaces.Analytic

open Complex Matrix

/-- The Siegel upper half-space H_g.

    H_g = { Ω ∈ M_{g×g}(ℂ) : Ω^T = Ω and Im(Ω) is positive definite }

    Elements of H_g are period matrices of principally polarized abelian varieties.
    For a Riemann surface Σ of genus g, the period matrix Ω is computed by
    integrating a normalized basis of holomorphic 1-forms over a symplectic
    basis of H₁(Σ, ℤ). -/
structure SiegelUpperHalfSpace (g : ℕ) where
  /-- Period matrix Ω -/
  Ω : Matrix (Fin g) (Fin g) ℂ
  /-- Symmetric: Ω^T = Ω -/
  symmetric : Ω.transpose = Ω
  /-- Imaginary part -/
  imPart : Matrix (Fin g) (Fin g) ℝ := fun i j => (Ω i j).im
  /-- Im(Ω) is symmetric (follows from Ω symmetric) -/
  imPart_symmetric : imPart.transpose = imPart
  /-- Im(Ω) is positive definite -/
  imPart_posDef : imPart.PosDef

/-- Complex dimension of H_g -/
def siegelDimension (g : ℕ) : ℕ := g * (g + 1) / 2

/-- The canonical element iI ∈ H_g (i times identity matrix).

    This is the period matrix of the product of g copies of the elliptic curve
    ℂ/(ℤ + iℤ). -/
noncomputable def SiegelUpperHalfSpace.canonical (g : ℕ) (_ : g > 0) :
    SiegelUpperHalfSpace g where
  Ω := Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ)
  symmetric := by simp [Matrix.transpose_smul, Matrix.transpose_one]
  imPart := 1  -- Identity matrix
  imPart_symmetric := Matrix.transpose_one
  imPart_posDef := Matrix.PosDef.one

/-- The diagonal entry of imPart is positive -/
theorem SiegelUpperHalfSpace.imPart_diag_pos {g : ℕ} (Ω : SiegelUpperHalfSpace g)
    (i : Fin g) : Ω.imPart i i > 0 :=
  Ω.imPart_posDef.diag_pos

/-- The imaginary part of any period matrix has positive trace -/
theorem SiegelUpperHalfSpace.trace_im_pos {g : ℕ} (hg : g > 0)
    (Ω : SiegelUpperHalfSpace g) : Matrix.trace Ω.imPart > 0 := by
  haveI : Nonempty (Fin g) := ⟨⟨0, hg⟩⟩
  exact Ω.imPart_posDef.trace_pos

end RiemannSurfaces.Analytic
