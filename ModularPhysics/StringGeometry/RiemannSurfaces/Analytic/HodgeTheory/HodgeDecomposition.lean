import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import ModularPhysics.StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Dolbeault

/-!
# Hodge Decomposition on Riemann Surfaces

This file develops Hodge theory for compact Riemann surfaces, including the
Hodge star operator, the Laplacian, harmonic forms, and the Hodge decomposition theorem.

## Mathematical Background

### The Hodge Star Operator

On a Riemann surface with the standard metric induced by the complex structure,
the Hodge star operator ⋆ acts on forms as follows:

For a Riemann surface with local coordinate z = x + iy and area form ω = (i/2) dz ∧ dz̄:
- ⋆1 = ω = (i/2) dz ∧ dz̄
- ⋆ω = 1
- ⋆dz = -i dz̄ (up to normalization)
- ⋆dz̄ = i dz

### The Laplacian

The Laplacian on a Riemann surface can be expressed as:
  Δ = 2i ∂∂̄ = -2i ∂̄∂

On functions: Δf = 4 ∂²f/∂z∂z̄

The Laplacian is self-adjoint with respect to the L² inner product.

### Harmonic Forms

A form ω is harmonic if Δω = 0, which is equivalent to:
  dω = 0 and d⋆ω = 0 (closed and co-closed)

For a Riemann surface:
- Harmonic 0-forms = constant functions (on compact surfaces)
- Harmonic 1-forms = holomorphic 1-forms ⊕ antiholomorphic 1-forms
- Harmonic (1,1)-forms = constant multiples of the area form (on compact surfaces)

### Hodge Decomposition

For a compact Riemann surface X of genus g:

  Ω^1(X) = H^1(X) ⊕ im(d) ⊕ im(d⋆)

where H^1(X) is the space of harmonic 1-forms, dim H^1(X) = 2g.

More refined:
  Ω^{1,0}(X) = H^{1,0}(X) ⊕ ∂̄(Ω^0)
  Ω^{0,1}(X) = H^{0,1}(X) ⊕ ∂(Ω^0)

where H^{1,0} = holomorphic 1-forms and H^{0,1} = their conjugates.

## Main Definitions

* `HodgeStar` - The Hodge star operator
* `HodgeLaplacian` - The Hodge Laplacian Δ
* `IsHarmonic` - Predicate for harmonic forms
* `HarmonicForms` - The space of harmonic forms

## References

* Griffiths, Harris "Principles of Algebraic Geometry" Ch 0.7
* Wells "Differential Analysis on Complex Manifolds" Ch IV
* Forster "Lectures on Riemann Surfaces" §20-21
-/

namespace RiemannSurfaces.Analytic

open Complex Topology
open scoped Manifold

variable {RS : RiemannSurface}

/-!
## The Hodge Star Operator

On a Riemann surface with the standard Kähler metric, the Hodge star satisfies:
  ⋆: Ω^{p,q} → Ω^{1-p,1-q}
-/

/-- The Hodge star on (1,0)-forms: ⋆(f dz) = -i f dz̄ (with standard normalization).
    This reflects the conformal structure of the Riemann surface. -/
noncomputable def hodgeStar_10 (ω : Form_10 RS) : Form_01 RS :=
  (-Complex.I) • (ω.conj)

/-- The Hodge star on (0,1)-forms: ⋆(g dz̄) = i g dz -/
noncomputable def hodgeStar_01 (ω : Form_01 RS) : Form_10 RS :=
  Complex.I • (ω.conj)

/-- ⋆⋆ = (-1)^{p(n-p)} on p-forms. For 1-forms on a 2-real-dimensional surface: ⋆⋆ = -1 -/
theorem hodgeStar_10_hodgeStar_01 (ω : Form_10 RS) :
    hodgeStar_01 (hodgeStar_10 ω) = -ω := by
  simp only [hodgeStar_10, hodgeStar_01]
  -- ⋆⋆ω = i • ((-i • ω.conj).conj) = i • (-i.conj • ω.conj.conj) = i • (i • ω) = -ω
  rw [Form_01.conj_smul, Form_10.conj_conj]
  -- Now have: I • (starRingEnd ℂ (-I) • ω)
  -- starRingEnd ℂ (-I) = I (conjugate of -I is I)
  simp only [map_neg, Complex.conj_I]
  -- Now have: I • (-(-I) • ω) = I • (I • ω)
  rw [neg_neg]
  -- Combine nested smul: I • (I • ω) = (I * I) • ω
  rw [smul_smul]
  -- I * I = -1
  simp only [Complex.I_mul_I, neg_smul, one_smul]

theorem hodgeStar_01_hodgeStar_10 (ω : Form_01 RS) :
    hodgeStar_10 (hodgeStar_01 ω) = -ω := by
  simp only [hodgeStar_10, hodgeStar_01]
  -- ⋆⋆ω = (-i) • ((i • ω.conj).conj) = (-i) • (i.conj • ω.conj.conj) = (-i) • ((-i) • ω) = -ω
  rw [Form_10.conj_smul, Form_01.conj_conj]
  -- Now have: (-I) • (starRingEnd ℂ I • ω)
  -- starRingEnd ℂ I = -I (conjugate of I is -I)
  simp only [Complex.conj_I]
  -- Now have: (-I) • ((-I) • ω)
  -- Combine nested smul: (-I) • ((-I) • ω) = ((-I) * (-I)) • ω
  rw [smul_smul]
  -- (-I) * (-I) = I² = -1
  simp only [neg_mul_neg, Complex.I_mul_I, neg_smul, one_smul]

/-- For MDifferentiable functions on a Riemann surface with 𝓘(ℂ, ℂ) model,
    the chart expression is ℂ-differentiable at every point in the chart target.

    This is the key infrastructure lemma: MDifferentiable f means f ∘ (chartAt q)⁻¹ is
    ℂ-differentiable at chartAt q for every q. We want to show that for a fixed chart e,
    f ∘ e.symm is ℂ-differentiable at every point z ∈ e.target.

    The proof uses:
    1. For z ∈ e.target, let q = e.symm z, so q ∈ e.source
    2. f is MDifferentiableAt at q
    3. Let e' = chartAt ℂ q (could differ from e)
    4. Then f ∘ e'.symm is DifferentiableAt at e' q
    5. On the overlap, e' ∘ e.symm is holomorphic (chart compatibility)
    6. f ∘ e.symm = (f ∘ e'.symm) ∘ (e' ∘ e.symm) locally
    7. Composition of holomorphic functions is holomorphic -/
theorem mdifferentiable_chart_diffAt {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ, ℂ) ⊤ M] {f : M → ℂ} (hmDiff : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f)
    (e : OpenPartialHomeomorph M ℂ) (he : e ∈ atlas ℂ M) (z : ℂ) (hz : z ∈ e.target) :
    DifferentiableAt ℂ (f ∘ e.symm) z := by
  -- q = e.symm z is in e.source
  let q := e.symm z
  have hq_source : q ∈ e.source := e.map_target hz

  -- f is MDifferentiableAt at q
  have hmdiff_q : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f q := hmDiff q

  -- The canonical chart at q
  let e' := chartAt ℂ q
  have hq_e'_source : q ∈ e'.source := mem_chart_source ℂ q

  -- Target chart simplifies (target is ℂ)
  have htarget : extChartAt 𝓘(ℂ, ℂ) (f q) = PartialEquiv.refl ℂ := by simp only [mfld_simps]
  have hrange : Set.range (𝓘(ℂ, ℂ) : ℂ → ℂ) = Set.univ := by simp

  -- Use mdifferentiableAt_iff_of_mem_source
  have hfq_source : f q ∈ (chartAt ℂ (f q)).source := mem_chart_source ℂ (f q)
  rw [mdifferentiableAt_iff_of_mem_source hq_e'_source hfq_source] at hmdiff_q

  -- Extract: f ∘ e'.symm is DifferentiableWithinAt at e' q
  simp only [hrange, htarget, PartialEquiv.refl_coe] at hmdiff_q
  have hdiff_e' : DifferentiableAt ℂ (f ∘ e'.symm) (e' q) := by
    have hfun_eq : id ∘ f ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm = f ∘ e'.symm := by
      ext w
      simp only [Function.comp_apply, id_eq, extChartAt, OpenPartialHomeomorph.extend_coe_symm,
        modelWithCornersSelf_coe_symm, e']
    rw [hfun_eq] at hmdiff_q
    exact hmdiff_q.2.differentiableAt Filter.univ_mem

  -- Now we need to relate f ∘ e.symm to f ∘ e'.symm
  -- On the overlap: f ∘ e.symm = (f ∘ e'.symm) ∘ (e' ∘ e.symm)

  -- e' ∘ e.symm is the transition map, which is holomorphic on its domain
  -- Since both e and e' are in the atlas, e' ∘ e.symm is smooth (actually holomorphic for Riemann surfaces)

  -- The point z satisfies: e.symm z = q ∈ e'.source (since q ∈ e.source and e' = chartAt q)
  have hq_e'_source' : e.symm z ∈ e'.source := hq_e'_source

  -- On a neighborhood of z, e' ∘ e.symm is well-defined and holomorphic
  -- and f ∘ e.symm = (f ∘ e'.symm) ∘ (e' ∘ e.symm)

  -- Chart transition is differentiable (holomorphic for Riemann surfaces)
  have htrans_diff : DifferentiableAt ℂ (e' ∘ e.symm) z := by
    -- e.symm is continuous, e' is a chart, on the overlap the transition is smooth
    -- For 𝓘(ℂ, ℂ) (holomorphic atlas), transitions are holomorphic
    have he' : e' ∈ atlas ℂ M := chart_mem_atlas ℂ q
    -- The transition e' ∘ e.symm is smooth on e.target ∩ e'.symm.source (the overlap in ℂ)
    -- For a Riemann surface atlas, this is actually holomorphic
    -- Use StructureGroupoid.compatible to get membership in contDiffGroupoid
    have hmem : e.symm ≫ₕ e' ∈ contDiffGroupoid ⊤ 𝓘(ℂ, ℂ) :=
      StructureGroupoid.compatible (contDiffGroupoid ⊤ 𝓘(ℂ, ℂ)) he he'
    -- Extract ContDiffOn from membership in contDiffGroupoid
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hmem
    -- hmem.1 : contDiffPregroupoid property for e.symm ≫ₕ e'
    -- For 𝓘(ℂ, ℂ), this simplifies to ContDiffOn ℂ ⊤ (e.symm ≫ₕ e') (e.symm ≫ₕ e').source
    have hcd_source : ContDiffOn ℂ ⊤ (𝓘(ℂ, ℂ) ∘ (e.symm ≫ₕ e') ∘ 𝓘(ℂ, ℂ).symm)
        (𝓘(ℂ, ℂ).symm ⁻¹' (e.symm ≫ₕ e').source ∩ Set.range 𝓘(ℂ, ℂ)) := hmem.1
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
        Set.range_id, Set.inter_univ] at hcd_source
    -- hcd_source : ContDiffOn ℂ ⊤ (e.symm ≫ₕ e') (e.symm ≫ₕ e').source
    -- The source is e.symm.source ∩ e.symm ⁻¹' e'.source = e.target ∩ e.symm ⁻¹' e'.source
    have hsymm_source : e.symm.source = e.target := rfl
    have hdom : z ∈ e.target ∩ e.symm ⁻¹' e'.source := by
      constructor
      · exact hz
      · simp only [Set.mem_preimage]
        exact hq_e'_source'
    -- The domain of e.symm ≫ₕ e' is exactly e.target ∩ e.symm ⁻¹' e'.source
    have hsource_eq : (e.symm ≫ₕ e').source = e.target ∩ e.symm ⁻¹' e'.source := by
      simp only [OpenPartialHomeomorph.trans_source, hsymm_source]
    -- ContDiffOn ⊤ implies DifferentiableOn, which gives DifferentiableWithinAt
    have hcd : ContDiffWithinAt ℂ ⊤ (e.symm ≫ₕ e') (e.target ∩ e.symm ⁻¹' e'.source) z := by
      rw [← hsource_eq]
      exact hcd_source z (by rw [hsource_eq]; exact hdom)
    -- Convert to DifferentiableAt using that the domain is open
    have hopen : IsOpen (e.target ∩ e.symm ⁻¹' e'.source) := by
      rw [← hsource_eq]
      exact (e.symm ≫ₕ e').open_source
    have hdw : DifferentiableWithinAt ℂ (e.symm ≫ₕ e') (e.target ∩ e.symm ⁻¹' e'.source) z :=
      hcd.differentiableWithinAt (WithTop.top_ne_zero)
    -- Convert DifferentiableWithinAt to DifferentiableAt using that z is in the interior
    have hda := DifferentiableWithinAt.differentiableAt hdw (IsOpen.mem_nhds hopen hdom)
    -- Finally, (e.symm ≫ₕ e') = e' ∘ e.symm on the domain
    have hcomp : e' ∘ e.symm =ᶠ[nhds z] (e.symm ≫ₕ e') := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      use e.target ∩ e.symm ⁻¹' e'.source, IsOpen.mem_nhds hopen hdom
      intro w _
      rfl
    exact hda.congr_of_eventuallyEq hcomp.symm

  -- Now compose: f ∘ e.symm = (f ∘ e'.symm) ∘ (e' ∘ e.symm)
  have hcomp_eq : f ∘ e.symm =ᶠ[nhds z] (f ∘ e'.symm) ∘ (e' ∘ e.symm) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    -- On e.target ∩ e.symm⁻¹(e'.source), we have e'.symm (e' (e.symm w)) = e.symm w
    have hsymm_source' : e.symm.source = e.target := rfl
    have hsource_eq : (e.symm ≫ₕ e').source = e.target ∩ e.symm ⁻¹' e'.source := by
      simp only [OpenPartialHomeomorph.trans_source, hsymm_source']
    have hopen : IsOpen (e.target ∩ e.symm ⁻¹' e'.source) := by
      rw [← hsource_eq]
      exact (e.symm ≫ₕ e').open_source
    use e.target ∩ e.symm ⁻¹' e'.source
    constructor
    · apply IsOpen.mem_nhds hopen
      exact ⟨hz, hq_e'_source'⟩
    · intro w ⟨_, hw_preimage⟩
      simp only [Function.comp_apply]
      -- e'.symm (e' (e.symm w)) = e.symm w when e.symm w ∈ e'.source
      have hw_e'_source : e.symm w ∈ e'.source := hw_preimage
      rw [e'.left_inv hw_e'_source]

  -- Composition of differentiable functions is differentiable
  -- First show the composed function is differentiable
  have hcomp_diff : DifferentiableAt ℂ (fun w => f (e'.symm (e' (e.symm w)))) z := by
    have h1 : DifferentiableAt ℂ (e' ∘ e.symm) z := htrans_diff
    have h2 : DifferentiableAt ℂ (f ∘ e'.symm) ((e' ∘ e.symm) z) := by
      have heq : (e' ∘ e.symm) z = e' q := rfl
      rw [heq]
      exact hdiff_e'
    exact h2.comp z h1

  -- Now use that on the overlap, e'.symm (e' (e.symm w)) = e.symm w
  exact hcomp_diff.congr_of_eventuallyEq hcomp_eq

/-!
## The Laplacian

On a Riemann surface, the Laplacian decomposes as Δ = Δ_∂ + Δ_∂̄ where
  Δ_∂̄ = ∂̄⋆∂̄ + ∂̄∂̄⋆

For functions, this simplifies considerably because ∂̄² = 0.
-/

/-- The ∂̄-Laplacian on functions: Δ_∂̄ f = ⋆∂̄⋆∂̄f.
    On a Riemann surface, this equals 2∂∂̄. -/
noncomputable def laplacian_dbar_fun (f : SmoothFunction RS) : SmoothFunction RS := by
  letI := RS.topology
  letI := RS.chartedSpace
  -- Δ_∂̄ f = ⋆∂̄(⋆∂̄f) - but ∂̄f is a (0,1)-form, ⋆∂̄f is a (1,0)-form
  -- ∂̄(⋆∂̄f) would be a (1,1)-form, and ⋆ of that is a function
  -- For simplicity, we define via the coordinate expression
  refine ⟨fun p => ?_, ?_⟩
  · let e := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p
    -- Δf = 4 ∂²f/∂z∂z̄ in local coordinates
    exact 4 * wirtingerDeriv_z (wirtingerDeriv_zbar (f.toFun ∘ e.symm)) (e p)
  · -- SmoothFunction is ℂ-smooth (holomorphic), so wirtingerDerivBar vanishes on chart targets.
    -- wirtingerDeriv of a locally-zero function is zero. Hence the section ≡ 0.
    haveI : IsManifold 𝓘(ℂ, ℂ) ⊤ RS.carrier := RS.isManifold
    have hmDiff : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f.toFun :=
      f.smooth'.mdifferentiable (by decide : (⊤ : WithTop ℕ∞) ≠ 0)
    convert contMDiff_const (c := (0 : ℂ)) using 1
    funext p
    simp only [wirtingerDeriv_z]
    -- Show wirtingerDerivBar (f ∘ e.symm) is zero on the open chart target
    let e := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p
    have he_atlas : e ∈ atlas ℂ RS.carrier := chart_mem_atlas ℂ p
    have hp_source : p ∈ e.source := mem_chart_source ℂ p
    have hep_target : e p ∈ e.target := e.map_source hp_source
    -- wirtingerDerivBar (f ∘ e.symm) is zero on e.target (open set)
    have hbar_zero : ∀ z ∈ e.target,
        Infrastructure.wirtingerDerivBar (f.toFun ∘ e.symm) z = 0 := by
      intro z hz
      have hdiff := mdifferentiable_chart_diffAt hmDiff e he_atlas z hz
      exact (Infrastructure.holomorphic_iff_wirtingerDerivBar_zero.mp hdiff).2
    -- wirtingerDerivBar (f ∘ e.symm) =ᶠ[nhds (e p)] 0
    have hbar_eq : Infrastructure.wirtingerDerivBar (f.toFun ∘ e.symm) =ᶠ[nhds (e p)]
        fun _ => 0 := by
      apply Filter.eventuallyEq_iff_exists_mem.mpr
      exact ⟨e.target, e.open_target.mem_nhds hep_target, fun z hz => hbar_zero z hz⟩
    -- fderiv of a locally-zero function is zero
    have hfderiv_zero : fderiv ℝ (Infrastructure.wirtingerDerivBar (f.toFun ∘ e.symm)) (e p) =
        fderiv ℝ (fun _ => (0 : ℂ)) (e p) :=
      Filter.EventuallyEq.fderiv_eq hbar_eq
    -- wirtingerDeriv uses fderiv, so it's zero
    -- Bridge wirtingerDeriv_zbar = Infrastructure.wirtingerDerivBar, then unfold wirtingerDeriv
    have hwz_eq : wirtingerDeriv_zbar (f.toFun ∘ ↑e.symm) =
        Infrastructure.wirtingerDerivBar (f.toFun ∘ ↑e.symm) := rfl
    rw [hwz_eq]
    unfold Infrastructure.wirtingerDeriv
    rw [hfderiv_zero]
    simp

/-- A function is harmonic iff Δf = 0 -/
def SmoothFunction.IsHarmonic (f : SmoothFunction RS) : Prop :=
  laplacian_dbar_fun f = 0

/-- Holomorphic functions are harmonic -/
theorem holomorphic_implies_harmonic (f : SmoothFunction RS) (hf : f.IsHolomorphic) :
    f.IsHarmonic := by
  -- If ∂̄f = 0, then Δf = 4∂∂̄f = 4∂(0) = 0
  letI := RS.topology
  letI := RS.chartedSpace
  unfold SmoothFunction.IsHarmonic laplacian_dbar_fun
  congr 1
  funext p

  -- Get the chart at p
  let e := @chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p
  have he : e ∈ atlas ℂ RS.carrier := chart_mem_atlas ℂ p

  -- Extract MDifferentiability from IsHolomorphic
  have hmDiff : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f.toFun :=
    (isHolomorphic_iff_mDifferentiable f).mp hf

  haveI : IsManifold 𝓘(ℂ, ℂ) ⊤ RS.carrier := RS.isManifold
  have hp_source : p ∈ e.source := mem_chart_source ℂ p
  have heP_target : e p ∈ e.target := e.map_source hp_source

  -- Key: wirtingerDerivBar (f ∘ e.symm) = 0 on e.target
  have hwbar_all : ∀ z ∈ e.target, wirtingerDeriv_zbar (f.toFun ∘ e.symm) z = 0 := by
    intro z hz
    -- By mdifferentiable_chart_diffAt, f ∘ e.symm is ℂ-differentiable at z
    have hdiff_z : DifferentiableAt ℂ (f.toFun ∘ e.symm) z :=
      mdifferentiable_chart_diffAt hmDiff e he z hz
    -- ℂ-differentiable implies wirtingerDerivBar = 0
    simp only [wirtingerDeriv_zbar]
    exact (Infrastructure.holomorphic_iff_wirtingerDerivBar_zero.mp hdiff_z).2

  -- wirtingerDerivBar (f ∘ e.symm) equals the zero function on the open set e.target
  -- Hence fderiv of this function at any point in e.target is zero
  -- Hence wirtingerDeriv at e p is zero

  have htarget_open : IsOpen e.target := e.open_target

  -- The function wirtingerDerivBar (f ∘ e.symm) is locally constant (= 0)
  -- fderiv of a locally constant function is zero
  have hfderiv_zero : fderiv ℝ (fun z => wirtingerDeriv_zbar (f.toFun ∘ e.symm) z) (e p) = 0 := by
    -- Use that f is locally zero on e.target
    have hlocal_zero : (fun z => wirtingerDeriv_zbar (f.toFun ∘ e.symm) z) =ᶠ[nhds (e p)] 0 := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      use e.target, IsOpen.mem_nhds htarget_open heP_target
      intro z hz
      exact hwbar_all z hz
    -- fderiv of a function that is locally constant zero is zero
    have hfderiv_const : fderiv ℝ (fun _ : ℂ => (0 : ℂ)) (e p) = 0 := fderiv_const_apply 0
    rw [hlocal_zero.fderiv_eq]
    exact hfderiv_const

  -- Now compute wirtingerDeriv
  simp only [wirtingerDeriv_z]
  unfold Infrastructure.wirtingerDeriv
  rw [hfderiv_zero]
  simp

/-!
## Harmonic 1-Forms
-/

/-- A (1,0)-form is harmonic iff it's holomorphic (∂̄ω = 0) -/
def Form_10.IsHarmonic (ω : Form_10 RS) : Prop :=
  dbar_10 ω = 0

/-- A (0,1)-form is harmonic iff it's antiholomorphic (∂ω = 0) -/
def Form_01.IsHarmonic (ω : Form_01 RS) : Prop :=
  -- ∂ω would be a (1,1)-form
  -- In our framework, this is equivalent to ω being the conjugate of a holomorphic form
  ∃ η : Form_10 RS, η.IsHarmonic ∧ ω = η.conj

/-- Holomorphic 1-forms are harmonic -/
theorem holomorphic_form_is_harmonic (ω : Form_10 RS) (hω : ω.IsHolomorphic') :
    ω.IsHarmonic := hω

/-!
## Linearity of ∂̄ on (1,0)-forms

The operator ∂̄ : Ω^{1,0} → Ω^{1,1} is ℂ-linear. This follows from linearity
of the Wirtinger derivative wirtingerDerivBar.
-/

/-- Helper: Form_10 sections composed with chart inverse are ℝ-differentiable.
    This is needed for applying wirtingerDerivBar algebraic lemmas. -/
private theorem form10_chart_differentiableAt (ω : Form_10 RS) (p : RS.carrier) :
    letI := RS.topology; letI := RS.chartedSpace
    DifferentiableAt ℝ (ω.toSection ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) := by
  letI := RS.topology; letI := RS.chartedSpace
  haveI : IsManifold 𝓘(ℂ, ℂ) ⊤ RS.carrier := RS.isManifold
  haveI : IsManifold 𝓘(ℝ, ℂ) ⊤ RS.carrier := isManifold_real_of_complex
  exact Infrastructure.differentiableAt_chart_comp ω.smooth' p

/-- ∂̄ is additive: dbar_10 (ω₁ + ω₂) = dbar_10 ω₁ + dbar_10 ω₂ -/
theorem dbar_10_add (ω₁ ω₂ : Form_10 RS) :
    dbar_10 (ω₁ + ω₂) = dbar_10 ω₁ + dbar_10 ω₂ := by
  letI := RS.topology; letI := RS.chartedSpace
  apply Form_11.ext; funext p
  simp only [Form_11.add_toSection]
  -- At point p, the value of dbar_10 (ω₁ + ω₂) is
  -- -(wirtingerDerivBar ((ω₁ + ω₂).toSection ∘ e.symm) (e p))
  show -(Infrastructure.wirtingerDerivBar ((ω₁ + ω₂).toSection ∘
    (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
    ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p)) =
    -(Infrastructure.wirtingerDerivBar (ω₁.toSection ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
      ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p)) +
    -(Infrastructure.wirtingerDerivBar (ω₂.toSection ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
      ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p))
  -- (ω₁ + ω₂).toSection ∘ e.symm = (ω₁.toSection ∘ e.symm) + (ω₂.toSection ∘ e.symm)
  have hfun_eq : (ω₁ + ω₂).toSection ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm =
      (ω₁.toSection ∘ (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm) +
      (ω₂.toSection ∘ (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm) := by
    ext z; simp only [Function.comp_apply, Form_10.add_toSection, Pi.add_apply]
  rw [hfun_eq]
  have h1 := form10_chart_differentiableAt ω₁ p
  have h2 := form10_chart_differentiableAt ω₂ p
  rw [Infrastructure.wirtingerDerivBar_add h1 h2]
  ring

/-- ∂̄ is ℂ-linear in scalar multiplication: dbar_10 (c • ω) = c • dbar_10 ω -/
theorem dbar_10_smul (c : ℂ) (ω : Form_10 RS) :
    dbar_10 (c • ω) = c • dbar_10 ω := by
  letI := RS.topology; letI := RS.chartedSpace
  apply Form_11.ext; funext p
  simp only [Form_11.smul_toSection]
  show -(Infrastructure.wirtingerDerivBar ((c • ω).toSection ∘
    (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
    ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p)) =
    c * -(Infrastructure.wirtingerDerivBar (ω.toSection ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm)
      ((@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p) p))
  have hfun_eq : (c • ω).toSection ∘
      (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm =
      c • (ω.toSection ∘ (@chartAt ℂ _ RS.carrier RS.topology RS.chartedSpace p).symm) := by
    ext z; simp only [Function.comp_apply, Form_10.smul_toSection, Pi.smul_apply, smul_eq_mul]
  rw [hfun_eq]
  have h := form10_chart_differentiableAt ω p
  rw [Infrastructure.wirtingerDerivBar_const_smul c h]
  ring

/-- Harmonic (1,0)-forms are closed under addition. -/
theorem isHarmonic_add {ω₁ ω₂ : Form_10 RS} (h₁ : ω₁.IsHarmonic) (h₂ : ω₂.IsHarmonic) :
    (ω₁ + ω₂).IsHarmonic := by
  unfold Form_10.IsHarmonic at *
  rw [dbar_10_add, h₁, h₂, add_zero]

/-- Harmonic (1,0)-forms are closed under scalar multiplication. -/
theorem isHarmonic_smul {ω : Form_10 RS} (c : ℂ) (h : ω.IsHarmonic) :
    (c • ω).IsHarmonic := by
  unfold Form_10.IsHarmonic at *
  rw [dbar_10_smul, h, smul_zero]

/-- Zero form is harmonic. -/
theorem isHarmonic_zero : (0 : Form_10 RS).IsHarmonic := by
  unfold Form_10.IsHarmonic
  rw [show (0 : Form_10 RS) = (0 : ℂ) • (0 : Form_10 RS) by simp]
  rw [dbar_10_smul, zero_smul]

/-- Negation preserves harmonicity. -/
theorem isHarmonic_neg {ω : Form_10 RS} (h : ω.IsHarmonic) : (-ω).IsHarmonic := by
  rw [show (-ω : Form_10 RS) = (-1 : ℂ) • ω by ext p; simp]
  exact isHarmonic_smul (-1) h

/-- Subtraction preserves harmonicity. -/
theorem isHarmonic_sub {ω₁ ω₂ : Form_10 RS} (h₁ : ω₁.IsHarmonic) (h₂ : ω₂.IsHarmonic) :
    (ω₁ - ω₂).IsHarmonic := by
  rw [sub_eq_add_neg]
  exact isHarmonic_add h₁ (isHarmonic_neg h₂)

/-!
## The Space of Harmonic Forms

For a compact Riemann surface of genus g:
- dim H^{1,0}(X) = g (holomorphic 1-forms)
- dim H^{0,1}(X) = g (antiholomorphic 1-forms)
- dim H^1(X) = 2g (harmonic 1-forms)
-/

/-- Harmonic (1,0)-forms form a ℂ-submodule of all (1,0)-forms.
    This is the kernel of the ∂̄-operator, which is ℂ-linear. -/
def harmonicSubmodule10 (RS : RiemannSurface) : Submodule ℂ (Form_10 RS) where
  carrier := { ω | ω.IsHarmonic }
  add_mem' := fun ha hb => isHarmonic_add ha hb
  zero_mem' := isHarmonic_zero
  smul_mem' := fun c _ hω => isHarmonic_smul c hω

/-- The type of harmonic (1,0)-forms (holomorphic 1-forms) -/
def Harmonic10Forms (RS : RiemannSurface) := { ω : Form_10 RS // ω.IsHarmonic }

/-- The type of harmonic (0,1)-forms (antiholomorphic 1-forms) -/
def Harmonic01Forms (RS : RiemannSurface) := { ω : Form_01 RS // ω.IsHarmonic }

/-- Harmonic10Forms is equivalent to the harmonicSubmodule10 carrier. -/
def Harmonic10Forms.equivSubmodule (RS : RiemannSurface) :
    Harmonic10Forms RS ≃ harmonicSubmodule10 RS :=
  Equiv.subtypeEquivRight (fun _ => Iff.rfl)

/-- Conjugation gives an isomorphism H^{1,0} ≅ H^{0,1} -/
noncomputable def conjugate_harmonic_iso (RS : RiemannSurface) :
    Harmonic10Forms RS → Harmonic01Forms RS := fun ⟨ω, hω⟩ =>
  ⟨ω.conj, ⟨ω, hω, rfl⟩⟩

theorem conjugate_harmonic_iso_bijective (RS : RiemannSurface) :
    Function.Bijective (conjugate_harmonic_iso RS) := by
  constructor
  · -- Injective
    intro ⟨ω₁, h₁⟩ ⟨ω₂, h₂⟩ heq
    simp only [conjugate_harmonic_iso] at heq
    have heq' : ω₁.conj = ω₂.conj := Subtype.ext_iff.mp heq
    have := congr_arg Form_01.conj heq'
    simp only [Form_10.conj_conj] at this
    exact Subtype.ext this
  · -- Surjective
    intro ⟨ω, hω⟩
    obtain ⟨η, hη, rfl⟩ := hω
    exact ⟨⟨η, hη⟩, rfl⟩

/-!
## Hodge Decomposition Theorem

The main theorem: every (p,q)-form decomposes uniquely as
  ω = ω_harm + ∂̄α + ∂̄⋆β

where ω_harm is harmonic.
-/

/-- Hodge decomposition for (0,1)-forms on a compact Riemann surface:
    Every (0,1)-form decomposes as ω = ω_harm + ∂̄f
    where ω_harm ∈ H^{0,1} and f is a smooth function. -/
theorem hodge_decomposition_01 (CRS : CompactRiemannSurface) (ω : Form_01 CRS.toRiemannSurface) :
    ∃ (ω_harm : Form_01 CRS.toRiemannSurface) (f : SmoothFunction CRS.toRiemannSurface),
      ω_harm.IsHarmonic ∧ ω = ω_harm + dbar_fun f := by
  sorry

/-- Hodge decomposition for (1,0)-forms:
    Every (1,0)-form decomposes as ω = ω_harm + ∂g
    where ω_harm ∈ H^{1,0}. -/
theorem hodge_decomposition_10 (CRS : CompactRiemannSurface) (ω : Form_10 CRS.toRiemannSurface) :
    ∃ (ω_harm : Form_10 CRS.toRiemannSurface),
      ω_harm.IsHarmonic ∧ (dbar_10 ω = dbar_10 ω_harm) := by
  -- Every (1,0)-form that is ∂̄-closed is holomorphic
  sorry

/-- The dimension of H^{1,0} equals the genus -/
theorem dim_harmonic_10_eq_genus (CRS : CompactRiemannSurface) :
    ∃ (basis : Fin CRS.genus → Harmonic10Forms CRS.toRiemannSurface),
      Function.Injective basis := by
  sorry

/-- Hodge theorem: Harmonic forms represent de Rham cohomology.
    H^1_dR(X) ≅ H^1_harm(X) for compact X.

    More precisely, the inclusion of harmonic 1-forms into closed 1-forms
    induces an isomorphism H^1_harm → H^1_dR. Every de Rham cohomology class
    has a unique harmonic representative.

    For a Riemann surface of genus g, this gives dim H^1_dR = 2g since
    H^1_harm = H^{1,0} ⊕ H^{0,1} has dimension g + g = 2g. -/
theorem hodge_isomorphism (CRS : CompactRiemannSurface) :
    ∃ (harmonic_to_deRham :
        (Harmonic10Forms CRS.toRiemannSurface ⊕ Harmonic01Forms CRS.toRiemannSurface) →
        -- Target would be H^1_dR, represented as closed forms mod exact
        Unit),  -- Placeholder for de Rham cohomology type
      Function.Surjective harmonic_to_deRham := by
  -- Every closed form is cohomologous to a unique harmonic form
  -- This requires the Hodge decomposition and elliptic regularity
  sorry

/-!
## L² Inner Products and Orthogonality
-/

/-- The L² inner product structure on (1,0)-forms.

    ⟨ω, η⟩ = ∫_X ω ∧ ⋆η̄

    This is a sesquilinear, conjugate-symmetric, positive definite pairing.
    Its existence follows from the hermitian metric induced by the complex structure. -/
structure L2InnerProduct10 (CRS : CompactRiemannSurface) where
  /-- The inner product pairing -/
  pairing : Form_10 CRS.toRiemannSurface → Form_10 CRS.toRiemannSurface → ℂ
  /-- Sesquilinearity in second argument -/
  sesquilinear_right : ∀ ω η₁ η₂ c,
    pairing ω (η₁ + c • η₂) = pairing ω η₁ + (starRingEnd ℂ c) * pairing ω η₂
  /-- Conjugate symmetry -/
  conj_symm : ∀ ω η, pairing η ω = starRingEnd ℂ (pairing ω η)
  /-- Positive definiteness -/
  pos_def : ∀ ω, ω ≠ 0 → (pairing ω ω).re > 0

/-- Existence of L² inner product on (1,0)-forms.
    This follows from the existence of a hermitian metric on the surface. -/
theorem l2_inner_product_10_exists (CRS : CompactRiemannSurface) :
    Nonempty (L2InnerProduct10 CRS) := by
  sorry  -- Requires: integration theory and hermitian metric

/-- The L² inner product on (1,0)-forms, given an inner product structure.

    ⟨ω, η⟩ = ∫_X ω ∧ ⋆η̄

    For a Riemann surface with local coordinate z, the Hodge star gives
    ⋆dz = -i dz̄, so ω ∧ ⋆η̄ is a (1,1)-form that can be integrated. -/
noncomputable def innerProduct_10 (CRS : CompactRiemannSurface)
    (ip : L2InnerProduct10 CRS)
    (ω η : Form_10 CRS.toRiemannSurface) : ℂ :=
  ip.pairing ω η

/-- Harmonic forms are orthogonal to exact forms.

    If ω is harmonic (∂̄ω = 0) and η = ∂̄f for some function f, then ⟨ω, η⟩ = 0.
    This follows from integration by parts: ⟨ω, ∂̄f⟩ = ⟨∂̄*ω, f⟩ = 0
    since harmonic forms are coclosed (∂̄*ω = 0). -/
theorem harmonic_orthogonal_exact (CRS : CompactRiemannSurface)
    (ip : L2InnerProduct10 CRS)
    (ω_harm : Harmonic10Forms CRS.toRiemannSurface)
    (f : SmoothFunction CRS.toRiemannSurface) :
    innerProduct_10 CRS ip ω_harm.val
      (⟨(dbar_fun f).toSection, (dbar_fun f).smooth'⟩ : Form_10 _) = 0 := by
  sorry  -- Requires: integration by parts

/-!
## Dolbeault Isomorphism

The Dolbeault theorem identifies:
  H^{p,q}_∂̄(X) ≅ H^q(X, Ω^p)

where Ω^p is the sheaf of holomorphic p-forms.
-/

/-- Dolbeault isomorphism: H^{0,1}_∂̄ ≅ H¹(X, O) where O is the structure sheaf.

    The Dolbeault cohomology H^{0,1}_∂̄(X) = Ω^{0,1}(X) / im(∂̄)
    is isomorphic to the sheaf cohomology H¹(X, O).

    For a compact Riemann surface of genus g:
    - dim H^{0,1}_∂̄ = g (antiholomorphic 1-forms)
    - dim H¹(X, O) = g (first cohomology of structure sheaf)

    The isomorphism is given by the ∂̄-Poincaré lemma and the
    long exact sequence in sheaf cohomology. -/
theorem dolbeault_isomorphism_01 (CRS : CompactRiemannSurface) :
    ∃ (iso : Harmonic01Forms CRS.toRiemannSurface → Unit),  -- Target is H¹(X, O)
      Function.Bijective iso := by
  -- The Dolbeault isomorphism requires:
  -- 1. ∂̄-Poincaré lemma (local exactness)
  -- 2. Partition of unity (existence of cutoff functions)
  -- 3. Identification of harmonic forms with cohomology classes
  sorry

end RiemannSurfaces.Analytic
