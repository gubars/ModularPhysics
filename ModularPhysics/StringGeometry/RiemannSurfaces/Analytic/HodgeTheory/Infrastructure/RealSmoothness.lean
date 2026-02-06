import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import ModularPhysics.StringGeometry.RiemannSurfaces.Analytic.Basic

/-!
# ℝ-Smoothness on Complex Manifolds

This file develops the theory of ℝ-smooth functions on complex manifolds
(Riemann surfaces), providing the infrastructure needed for (p,q)-forms
and the ∂̄-operator.

## Mathematical Background

A complex manifold with model `𝓘(ℂ, ℂ)` can also be viewed as a real manifold
with model `𝓘(ℝ, ℂ)`. The key insight is that **the same ChartedSpace works
for both** - only the smoothness notion changes:

- `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) n f` requires ℂ-linear Fréchet derivatives
- `ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n f` requires only ℝ-linear Fréchet derivatives

Since every ℂ-linear map is ℝ-linear, ℂ-smooth implies ℝ-smooth.

This matters for:
- Complex conjugation (ℝ-smooth but not ℂ-smooth)
- The ∂̄-operator (involves conjugation)
- (0,1)-forms (transform via conjugate of transition functions)

## References

* Griffiths, Harris "Principles of Algebraic Geometry" §0.5
* Wells "Differential Analysis on Complex Manifolds" Ch II
-/

namespace RiemannSurfaces.Analytic

open scoped Manifold
open Complex Topology

/-!
## Core Infrastructure: ℂ-Smooth Implies ℝ-Smooth

The fundamental bridging lemma: every ℂ-smooth function is ℝ-smooth.
-/

/-- ℂ-differentiability implies ℝ-differentiability.
    This is the fundamental scalar restriction result at a point. -/
theorem differentiableAt_real_of_complex {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {x : E} (hf : DifferentiableAt ℂ f x) :
    DifferentiableAt ℝ f x := by
  -- Every ℂ-linear map is ℝ-linear via restrict scalars
  obtain ⟨L, hL⟩ := hf
  exact ⟨L.restrictScalars ℝ, hL.restrictScalars ℝ⟩

/-- ℂ-Differentiable implies ℝ-Differentiable (global version). -/
theorem differentiable_real_of_complex {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} (hf : Differentiable ℂ f) :
    Differentiable ℝ f :=
  hf.restrictScalars ℝ

/-- ℂ-ContDiff of order 0 implies ℝ-ContDiff of order 0.
    This is just continuity, which doesn't depend on the scalar field. -/
theorem contDiff_zero_real_of_complex {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} (hf : ContDiff ℂ 0 f) :
    ContDiff ℝ 0 f := by
  rw [contDiff_zero] at hf ⊢
  exact hf

/-- ℂ-ContDiff of order 1 implies ℝ-ContDiff of order 1.
    Uses that ℂ-differentiability implies ℝ-differentiability. -/
theorem contDiff_one_real_of_complex {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} (hf : ContDiff ℂ 1 f) :
    ContDiff ℝ 1 f := by
  rw [contDiff_one_iff_fderiv] at hf ⊢
  constructor
  · exact hf.1.restrictScalars ℝ
  · -- The ℝ-derivative is the restriction of the ℂ-derivative
    -- fderiv ℝ f = (fderiv ℂ f).restrictScalars ℝ
    have heq : fderiv ℝ f = fun x => (fderiv ℂ f x).restrictScalars ℝ := by
      funext x
      exact (hf.1 x).fderiv_restrictScalars ℝ
    rw [heq]
    -- Composition: fderiv ℂ f is continuous, restrictScalars is continuous
    exact (ContinuousLinearMap.continuous_restrictScalars (𝕜' := ℝ)).comp hf.2

/-- ℂ-ContDiff implies ℝ-ContDiff.
    The key is that ℂ-differentiability implies ℝ-differentiability,
    and this carries through to all orders of derivatives.

    **Mathematical content**: Every ℂ-linear map is ℝ-linear, so:
    - ℂ-differentiability implies ℝ-differentiability
    - The ℝ-Fréchet derivative is the scalar restriction of the ℂ-derivative
    - Continuity of derivatives transfers since it's the same underlying function -/
theorem contDiff_real_of_complex {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {n : ℕ∞} (hf : ContDiff ℂ n f) :
    ContDiff ℝ n f :=
  -- Mathlib provides this via HasFTaylorSeriesUpToOn.restrictScalars
  hf.restrict_scalars ℝ

/-- A ℂ-manifold is also an ℝ-manifold (transition maps are ℝ-smooth if ℂ-smooth). -/
theorem isManifold_real_of_complex {M : Type*}
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ⊤ M] :
    IsManifold 𝓘(ℝ, ℂ) ⊤ M := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  -- Get the ℂ-smooth condition on transition maps from HasGroupoid
  have hC := HasGroupoid.compatible (G := contDiffGroupoid ⊤ 𝓘(ℂ, ℂ)) he he'
  -- Unfold membership in contDiffGroupoid
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hC
  -- Extract the forward smoothness condition (property of (e.symm ≫ₕ e'))
  have hfwd := hC.1
  -- For 𝓘(ℂ, ℂ) and 𝓘(ℝ, ℂ), both I and I.symm are identity
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, Function.comp_id,
    modelWithCornersSelf_coe_symm, Set.preimage_id_eq, Set.range_id,
    OpenPartialHomeomorph.trans_source] at hfwd ⊢
  -- Apply scalar restriction: ℂ-smooth implies ℝ-smooth
  exact hfwd.restrict_scalars ℝ

/-- ℂ-smooth on manifolds implies ℝ-smooth.
    Key insight: The ChartedSpace structure is the same (charts map to ℂ).
    Only the smoothness notion changes in the ContDiffOn condition. -/
theorem contMDiff_real_of_complex {M N : Type*}
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ⊤ M]
    [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ, ℂ) ⊤ N]
    {f : M → N} (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⊤ f) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ f := by
  -- First establish that M, N are ℝ-manifolds
  haveI : IsManifold 𝓘(ℝ, ℂ) ⊤ M := isManifold_real_of_complex
  haveI : IsManifold 𝓘(ℝ, ℂ) ⊤ N := isManifold_real_of_complex
  -- Use the characterization: continuous + chart representations are smooth
  rw [contMDiff_iff] at hf ⊢
  refine ⟨hf.1, fun x y => ?_⟩
  -- The chart representation is the same function (since 𝓘(ℂ,ℂ) and 𝓘(ℝ,ℂ) are both identity on ℂ)
  -- We need to show ℝ-smoothness from ℂ-smoothness
  have hC : ContDiffOn ℂ ⊤ (extChartAt 𝓘(ℂ, ℂ) y ∘ f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
      ((extChartAt 𝓘(ℂ, ℂ) x).target ∩
        (extChartAt 𝓘(ℂ, ℂ) x).symm ⁻¹' (f ⁻¹' (extChartAt 𝓘(ℂ, ℂ) y).source)) := hf.2 x y
  -- The extended charts for 𝓘(ℂ, ℂ) and 𝓘(ℝ, ℂ) are the same (both use identity)
  have eq1 : extChartAt 𝓘(ℝ, ℂ) x = extChartAt 𝓘(ℂ, ℂ) x := rfl
  have eq2 : extChartAt 𝓘(ℝ, ℂ) y = extChartAt 𝓘(ℂ, ℂ) y := rfl
  rw [eq1, eq2]
  -- Apply scalar restriction
  exact hC.restrict_scalars ℝ

/-- Specialization for functions from a Riemann surface to ℂ. -/
theorem contMDiff_real_of_complex_rs {RS : RiemannSurface} {f : RS.carrier → ℂ}
    (hf : letI := RS.topology
          letI := RS.chartedSpace
          letI := RS.isManifold
          ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⊤ f) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ f := by
  letI := RS.topology
  letI := RS.chartedSpace
  letI := RS.isManifold
  -- ℂ is a manifold over itself with 𝓘(ℂ, ℂ), hence also with 𝓘(ℝ, ℂ)
  haveI : IsManifold 𝓘(ℝ, ℂ) ⊤ RS.carrier := isManifold_real_of_complex
  -- Use the general contMDiff_real_of_complex for functions to ℂ
  -- Note: ℂ as a manifold is IsManifold 𝓘(ℂ, ℂ) ⊤ ℂ by instIsManifoldModelSpace
  exact contMDiff_real_of_complex hf

/-!
## Conjugation is ℝ-Smooth

Complex conjugation is ℝ-smooth but not ℂ-smooth (it's antiholomorphic).
-/

/-- Complex conjugation is an ℝ-linear continuous map. -/
def conjCLM : ℂ →L[ℝ] ℂ where
  toFun := starRingEnd ℂ
  map_add' := map_add (starRingEnd ℂ)
  map_smul' := fun r z => by
    -- r • z for r : ℝ and z : ℂ is r * z (scalar multiplication)
    -- conj(r * z) = r * conj(z) since conj(r) = r for r ∈ ℝ
    simp only [RingHom.id_apply]
    rw [Complex.real_smul, Complex.real_smul]
    rw [map_mul, Complex.conj_ofReal]
  cont := Complex.continuous_conj

/-- Complex conjugation is ℝ-smooth as a map ℂ → ℂ. -/
theorem conj_contDiff_real : ContDiff ℝ ⊤ (starRingEnd ℂ : ℂ → ℂ) :=
  conjCLM.contDiff

/-- Conjugation is ℝ-smooth for any smoothness level. -/
theorem conj_contDiff_real_n {n : ℕ∞} : ContDiff ℝ n (starRingEnd ℂ : ℂ → ℂ) :=
  conj_contDiff_real.of_le le_top

/-- Composition with conjugation preserves ℝ-smoothness. -/
theorem contDiff_conj_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {n : ℕ∞} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => starRingEnd ℂ (f x)) :=
  conj_contDiff_real_n.comp hf

/-- Complex conjugation is ℝ-smooth on complex manifolds. -/
theorem conj_contMDiff_real {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {f : M → ℂ} (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ f) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ (fun x => starRingEnd ℂ (f x)) :=
  conj_contDiff_real.comp_contMDiff hf

/-!
## ℝ-Smooth Functions on Riemann Surfaces
-/

/-- An ℝ-smooth function on a Riemann surface.

    Uses `ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤` which requires ℝ-differentiability
    in charts, but still uses the same ChartedSpace as the RiemannSurface. -/
structure RealSmoothFunction (RS : RiemannSurface) where
  toFun : RS.carrier → ℂ
  smooth' : letI := RS.topology
            letI := RS.chartedSpace
            ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ toFun

namespace RealSmoothFunction

variable {RS : RiemannSurface}

instance : CoeFun (RealSmoothFunction RS) (fun _ => RS.carrier → ℂ) := ⟨toFun⟩

@[ext]
theorem ext {f g : RealSmoothFunction RS} (h : ∀ p, f.toFun p = g.toFun p) : f = g := by
  cases f; cases g; congr 1; funext p; exact h p

/-- Constant functions are ℝ-smooth. -/
noncomputable def const (c : ℂ) : RealSmoothFunction RS where
  toFun := fun _ => c
  smooth' := by letI := RS.topology; letI := RS.chartedSpace; exact contMDiff_const

noncomputable instance : Zero (RealSmoothFunction RS) := ⟨const 0⟩
noncomputable instance : One (RealSmoothFunction RS) := ⟨const 1⟩

/-- Addition of ℝ-smooth functions. -/
noncomputable def add (f g : RealSmoothFunction RS) : RealSmoothFunction RS where
  toFun := fun p => f.toFun p + g.toFun p
  smooth' := by letI := RS.topology; letI := RS.chartedSpace; exact f.smooth'.add g.smooth'

noncomputable instance : Add (RealSmoothFunction RS) := ⟨add⟩

/-- Negation of ℝ-smooth functions. -/
noncomputable def neg (f : RealSmoothFunction RS) : RealSmoothFunction RS where
  toFun := fun p => -f.toFun p
  smooth' := by letI := RS.topology; letI := RS.chartedSpace; exact f.smooth'.neg

noncomputable instance : Neg (RealSmoothFunction RS) := ⟨neg⟩

/-- Subtraction of ℝ-smooth functions. -/
noncomputable def sub (f g : RealSmoothFunction RS) : RealSmoothFunction RS where
  toFun := fun p => f.toFun p - g.toFun p
  smooth' := by letI := RS.topology; letI := RS.chartedSpace; exact f.smooth'.sub g.smooth'

noncomputable instance : Sub (RealSmoothFunction RS) := ⟨sub⟩

/-- Multiplication of ℝ-smooth functions.
    Note: Uses that ℂ has ContMDiffMul 𝓘(ℝ, ℂ) structure. -/
noncomputable def mul (f g : RealSmoothFunction RS) : RealSmoothFunction RS where
  toFun := fun p => f.toFun p * g.toFun p
  smooth' := by
    letI := RS.topology; letI := RS.chartedSpace
    -- Multiplication in ℂ is ℝ-smooth
    have hmul : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => p.1 * p.2) := contDiff_mul
    have hpair : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ × ℂ) ⊤ (fun p => (f.toFun p, g.toFun p)) :=
      f.smooth'.prodMk_space g.smooth'
    exact hmul.comp_contMDiff hpair

noncomputable instance : Mul (RealSmoothFunction RS) := ⟨mul⟩

@[simp] lemma add_toFun (f g : RealSmoothFunction RS) (p : RS.carrier) :
    (f + g).toFun p = f.toFun p + g.toFun p := rfl

@[simp] lemma neg_toFun (f : RealSmoothFunction RS) (p : RS.carrier) :
    (-f).toFun p = -f.toFun p := rfl

@[simp] lemma sub_toFun (f g : RealSmoothFunction RS) (p : RS.carrier) :
    (f - g).toFun p = f.toFun p - g.toFun p := rfl

@[simp] lemma mul_toFun (f g : RealSmoothFunction RS) (p : RS.carrier) :
    (f * g).toFun p = f.toFun p * g.toFun p := rfl

@[simp] lemma zero_toFun (p : RS.carrier) : (0 : RealSmoothFunction RS).toFun p = 0 := rfl
@[simp] lemma one_toFun (p : RS.carrier) : (1 : RealSmoothFunction RS).toFun p = 1 := rfl

/-- ℝ-smooth functions form a commutative ring. -/
noncomputable instance : CommRing (RealSmoothFunction RS) where
  add := add
  add_assoc a b c := by ext p; exact add_assoc _ _ _
  zero := 0
  zero_add a := by ext p; exact zero_add _
  add_zero a := by ext p; exact add_zero _
  neg := neg
  neg_add_cancel a := by ext p; exact neg_add_cancel _
  add_comm a b := by ext p; exact add_comm _ _
  mul := mul
  mul_assoc a b c := by ext p; exact mul_assoc _ _ _
  one := 1
  one_mul a := by ext p; exact one_mul _
  mul_one a := by ext p; exact mul_one _
  left_distrib a b c := by ext p; exact mul_add _ _ _
  right_distrib a b c := by ext p; exact add_mul _ _ _
  mul_comm a b := by ext p; exact mul_comm _ _
  zero_mul a := by ext p; exact zero_mul _
  mul_zero a := by ext p; exact mul_zero _
  sub_eq_add_neg a b := by ext p; exact sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Conjugation of an ℝ-smooth function is ℝ-smooth. -/
noncomputable def conj (f : RealSmoothFunction RS) : RealSmoothFunction RS where
  toFun := fun p => starRingEnd ℂ (f.toFun p)
  smooth' := by
    letI := RS.topology; letI := RS.chartedSpace
    exact conj_contMDiff_real f.smooth'

@[simp] lemma conj_toFun (f : RealSmoothFunction RS) (p : RS.carrier) :
    f.conj.toFun p = starRingEnd ℂ (f.toFun p) := rfl

/-- Conjugation is an involution. -/
theorem conj_conj (f : RealSmoothFunction RS) : f.conj.conj = f := by
  ext p
  simp only [conj_toFun, starRingEnd_self_apply]

/-- Conjugation is additive. -/
theorem conj_add (f g : RealSmoothFunction RS) : (f + g).conj = f.conj + g.conj := by
  ext p
  simp only [conj_toFun, add_toFun, map_add]

/-- Conjugation is multiplicative. -/
theorem conj_mul (f g : RealSmoothFunction RS) : (f * g).conj = f.conj * g.conj := by
  ext p
  simp only [conj_toFun, mul_toFun, map_mul]

/-- Conjugation of zero is zero. -/
@[simp] theorem conj_zero : (0 : RealSmoothFunction RS).conj = 0 := by
  ext p
  simp only [conj_toFun, zero_toFun, map_zero]

/-- Conjugation of one is one. -/
@[simp] theorem conj_one : (1 : RealSmoothFunction RS).conj = 1 := by
  ext p
  simp only [conj_toFun, one_toFun, map_one]

/-- Conjugation of negation. -/
theorem conj_neg (f : RealSmoothFunction RS) : (-f).conj = -f.conj := by
  ext p
  simp only [conj_toFun, neg_toFun, map_neg]

end RealSmoothFunction

/-!
## Real and Imaginary Parts

The real and imaginary parts of an ℝ-smooth function are also ℝ-smooth.
-/

/-- The real part as a continuous ℝ-linear map. -/
def Complex.reCLM : ℂ →L[ℝ] ℝ := Complex.reLm.toContinuousLinearMap

/-- The imaginary part as a continuous ℝ-linear map. -/
def Complex.imCLM : ℂ →L[ℝ] ℝ := Complex.imLm.toContinuousLinearMap

/-- Real part extraction is ℝ-smooth. -/
theorem Complex.re_contDiff_real : ContDiff ℝ ⊤ (Complex.re : ℂ → ℝ) :=
  Complex.reCLM.contDiff

/-- Imaginary part extraction is ℝ-smooth. -/
theorem Complex.im_contDiff_real : ContDiff ℝ ⊤ (Complex.im : ℂ → ℝ) :=
  Complex.imCLM.contDiff

/-- The real part of an ℝ-smooth function is ℝ-smooth (as a real-valued function). -/
theorem RealSmoothFunction.re_smooth {RS : RiemannSurface}
    (f : RealSmoothFunction RS) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ⊤ (fun p => (f.toFun p).re) := by
  letI := RS.topology; letI := RS.chartedSpace
  exact Complex.re_contDiff_real.comp_contMDiff f.smooth'

/-- The imaginary part of an ℝ-smooth function is ℝ-smooth (as a real-valued function). -/
theorem RealSmoothFunction.im_smooth {RS : RiemannSurface}
    (f : RealSmoothFunction RS) :
    letI := RS.topology
    letI := RS.chartedSpace
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ⊤ (fun p => (f.toFun p).im) := by
  letI := RS.topology; letI := RS.chartedSpace
  exact Complex.im_contDiff_real.comp_contMDiff f.smooth'

/-!
## Converting ℂ-Smooth to ℝ-Smooth

For use with forms - convert ℂ-smooth functions to ℝ-smooth.
-/

/-- Create an ℝ-smooth function from a proof of ℂ-smoothness.
    This is the main bridge for using the existing holomorphic infrastructure. -/
noncomputable def RealSmoothFunction.ofHolomorphic {RS : RiemannSurface}
    (f : RS.carrier → ℂ)
    (hf : letI := RS.topology
          letI := RS.chartedSpace
          letI := RS.isManifold
          ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⊤ f) : RealSmoothFunction RS where
  toFun := f
  smooth' := contMDiff_real_of_complex_rs hf

end RiemannSurfaces.Analytic
