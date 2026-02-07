import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Calculus.Conformal.NormedSpace
import Mathlib.Topology.Covering.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import ModularPhysics.StringGeometry.RiemannSurfaces.Topology.Basic

/-!
# Analytic Theory: Complex Manifold Structure

This file provides the analytic (complex-analytic) definition of Riemann surfaces
as connected 1-dimensional complex manifolds.

## Mathematical Background

A Riemann surface is a connected complex manifold of complex dimension 1.
This means:
1. A topological space with charts to open subsets of ℂ
2. Transition functions are holomorphic (complex differentiable)
3. Connected

## Relationship to Other Definitions

- **Analytic** (this file): Complex manifolds, holomorphic functions
- **Algebraic** (Algebraic/): Smooth projective curves over ℂ
- **GAGA**: For compact surfaces, these are equivalent

This file is imported by the main Basic.lean for backward compatibility.

## Main Definitions

* `RiemannSurface` - A connected 1-dimensional complex manifold
* `CompactRiemannSurface` - A compact Riemann surface with genus

## Complex Manifold Structure via Mathlib

We use Mathlib's `IsManifold (modelWithCornersSelf ℂ ℂ) ∞ M` for complex manifold structure.
The model `modelWithCornersSelf ℂ ℂ` uses ℂ as the scalar field, so `ContDiffOn ℂ n` checks
ℂ-differentiability (Fréchet derivative is ℂ-linear), which is equivalent
to holomorphicity via Cauchy-Riemann equations.

The key theorem bridging these notions is `DifferentiableOn.contDiffOn` from
`Mathlib.Analysis.Complex.CauchyIntegral`: on open sets, complex differentiability
implies `ContDiffOn ℂ n` for any n, since holomorphic functions are analytic.

## References

* Farkas, Kra "Riemann Surfaces"
* Griffiths, Harris "Principles of Algebraic Geometry", Chapter 2
* Donaldson "Riemann Surfaces"
-/

namespace RiemannSurfaces.Analytic

open scoped Manifold

/-!
## Complex Manifold Structure

Mathlib provides `IsManifold I n M` for n-times differentiable manifolds.
For complex manifolds of dimension 1, we use:
- Model: `modelWithCornersSelf ℂ ℂ` (the identity model with corners on ℂ)
- Smoothness: `∞` (smooth, which for ℂ means holomorphic/analytic)

The `IsManifold (modelWithCornersSelf ℂ ℂ) ∞ M` class requires transition functions to be
`ContDiffOn ℂ ∞`, i.e., infinitely ℂ-differentiable. Since ℂ-differentiability
requires the Fréchet derivative to be ℂ-linear (equivalent to Cauchy-Riemann),
this gives exactly the structure of a complex manifold with holomorphic transitions.
-/

/-!
## Riemann Surface Definition
-/

/-- A Riemann surface is a connected 1-dimensional complex manifold.

    A Riemann surface consists of:
    1. A topological space M that is Hausdorff and second countable
    2. A ChartedSpace structure over ℂ (atlas of charts to ℂ)
    3. Holomorphic transition functions (IsManifold (modelWithCornersSelf ℂ ℂ) ∞)
    4. Connectedness

    **1-dimensionality:** The complex dimension is 1 because the model space is ℂ
    (not ℂⁿ for n > 1). This is encoded in `ChartedSpace ℂ M` where the model
    space ℂ has dim_ℂ = 1. Equivalently, it has real dimension 2.

    **Complex manifold structure:** We use Mathlib's `IsManifold (modelWithCornersSelf ℂ ℂ) ∞ M`
    which requires transitions to be `ContDiffOn ℂ ∞`. Since ℂ-differentiability
    (Fréchet derivative being ℂ-linear) is equivalent to holomorphicity via
    Cauchy-Riemann, this gives a complex manifold with holomorphic transitions.

    **Key invariants:**
    - Riemann surfaces are orientable (ℂ ≅ ℝ² with standard orientation)
    - Connected Riemann surfaces are classified by their topology (genus for compact)
    - Every Riemann surface has a unique complex structure compatible with its atlas -/
structure RiemannSurface where
  /-- The underlying type -/
  carrier : Type*
  /-- Topological structure -/
  topology : TopologicalSpace carrier
  /-- Hausdorff separation -/
  t2 : @T2Space carrier topology
  /-- Second countable -/
  secondCountable : @SecondCountableTopology carrier topology
  /-- Charted space over ℂ -/
  chartedSpace : @ChartedSpace ℂ _ carrier topology
  /-- Complex manifold structure with holomorphic transitions -/
  isManifold : @IsManifold ℂ _ ℂ _ _ ℂ _ (modelWithCornersSelf ℂ ℂ) ⊤ carrier topology chartedSpace
  /-- Connected -/
  connected : @ConnectedSpace carrier topology

/-- The carrier of a Riemann surface is infinite.

    **Proof:** By contradiction. If the carrier were finite, then a chart
    would map a finite open subset to an open subset of ℂ. But open subsets
    of ℂ that are finite must be clopen (finite = closed in T1 space, open by
    hypothesis). Since ℂ is connected, the only nonempty clopen set is ℂ itself.
    But ℂ is infinite, contradicting finiteness. -/
instance RiemannSurface.carrier_infinite (RS : RiemannSurface) : Infinite RS.carrier := by
  letI := RS.topology
  letI := RS.chartedSpace
  haveI := RS.t2
  haveI := RS.connected
  constructor  -- Goal: ¬ Finite RS.carrier
  intro hfin
  -- Pick a point (connected → nonempty)
  obtain ⟨x⟩ : Nonempty RS.carrier := RS.connected.toNonempty
  -- Get the chart at x: an OpenPartialHomeomorph to ℂ
  let e := chartAt ℂ x
  -- e.target is the image of e.source, which is finite since carrier is finite
  have htgt_fin : Set.Finite e.target := by
    have hsrc_fin : Set.Finite e.source := Set.toFinite e.source
    have := hsrc_fin.image e
    rwa [e.image_source_eq_target] at this
  -- e.target is open in ℂ (from OpenPartialHomeomorph)
  have htgt_open : IsOpen e.target := e.open_target
  -- e.target is closed (finite subset of T1 space ℂ)
  have htgt_closed : IsClosed e.target := htgt_fin.isClosed
  -- e.target is nonempty (contains the image of x)
  have htgt_ne : e.target.Nonempty := ⟨e x, mem_chart_target ℂ x⟩
  -- ℂ is connected, so a nonempty clopen set must be all of ℂ
  have htgt_clopen : IsClopen e.target := ⟨htgt_closed, htgt_open⟩
  have htgt_univ : e.target = Set.univ := htgt_clopen.eq_univ htgt_ne
  -- But Set.univ in ℂ is infinite (ℂ has CharZero, hence Infinite ℂ)
  rw [htgt_univ] at htgt_fin
  exact Set.infinite_univ htgt_fin

/-!
## Standard Examples
-/

/-- ℂ is preconnected (proof via convexity: ℂ is convex hence preconnected) -/
private theorem complex_isPreconnected_univ : IsPreconnected (Set.univ : Set ℂ) :=
  convex_univ.isPreconnected

/-- ℂ is a connected space -/
private instance complex_connectedSpace : ConnectedSpace ℂ where
  isPreconnected_univ := complex_isPreconnected_univ
  toNonempty := ⟨0⟩

/-- The complex plane ℂ as a Riemann surface.

    ℂ is automatically a complex manifold via `instIsManifoldModelSpace`:
    the model space is always a manifold over itself. -/
noncomputable def ComplexPlane : RiemannSurface where
  carrier := ℂ
  topology := inferInstance
  t2 := inferInstance
  secondCountable := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance  -- instIsManifoldModelSpace
  connected := complex_connectedSpace

/-!
## Riemann Sphere

The Riemann sphere ℂP¹ = ℂ ∪ {∞} is the one-point compactification of ℂ.
It has a two-chart atlas:
- φ₀: ℂ → ℂ (identity on the finite part)
- φ₁: (OnePoint ℂ) \ {0} → ℂ, z ↦ 1/z with ∞ ↦ 0

The transition function φ₁ ∘ φ₀⁻¹(z) = 1/z is holomorphic on ℂ \ {0}.

**Note:** Full construction of the charted space structure requires significant
infrastructure. We provide the structure with placeholders that should be
filled in when Mathlib has better support for one-point compactification
as a manifold.
-/

/-- The finite chart on the Riemann sphere: embeds ℂ into OnePoint ℂ.

    This chart covers everything except the point at infinity.
    The source is `Set.range (↑)` (the image of the coercion ℂ → OnePoint ℂ).

    Construction uses the symm of the open embedding's partial homeomorphism:
    `coe : ℂ → OnePoint ℂ` is an open embedding, so its symm gives a partial
    homeomorphism from `OnePoint ℂ` to `ℂ` with source = range coe. -/
noncomputable def riemannSphereFiniteChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  ((OnePoint.isOpenEmbedding_coe (X := ℂ)).toOpenPartialHomeomorph (↑)).symm

/-- The chart at infinity on the Riemann sphere: z ↦ 1/z with ∞ ↦ 0.

    This chart covers everything except z = 0. -/
noncomputable def riemannSphereInftyChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ where
  toFun := fun x => match x with
    | OnePoint.some z => if z = 0 then 0 else z⁻¹  -- 0 is not in source
    | OnePoint.infty => 0
  invFun := fun w => if w = 0 then OnePoint.infty else OnePoint.some w⁻¹
  source := {OnePoint.infty} ∪ ((↑) '' {z : ℂ | z ≠ 0})
  target := Set.univ
  map_source' := fun _ _ => Set.mem_univ _
  map_target' := fun w _ => by
    by_cases hw : w = 0
    · simp [hw]
    · right; use w⁻¹; simp [inv_ne_zero hw, hw]
  left_inv' := fun x hx => by
    cases x with
    | infty =>
      -- toFun(∞) = 0, invFun(0) = ∞
      simp only [OnePoint.infty]
      rfl
    | coe z =>
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image, Set.mem_setOf_eq] at hx
      cases hx with
      | inl h => exact (OnePoint.coe_ne_infty z h).elim
      | inr h =>
        obtain ⟨w, hw, hwz⟩ := h
        -- hwz : ↑w = ↑z, so w = z and z ≠ 0
        have hz : z ≠ 0 := by
          have heq : w = z := OnePoint.coe_injective hwz
          rw [← heq]; exact hw
        -- toFun(↑z) = z⁻¹ (since z ≠ 0)
        -- invFun(z⁻¹) = ↑((z⁻¹)⁻¹) = ↑z (since z⁻¹ ≠ 0)
        have hz_inv_ne : z⁻¹ ≠ 0 := inv_ne_zero hz
        simp only [OnePoint.some]
        simp [hz, hz_inv_ne, inv_inv]
  right_inv' := fun w _ => by
    by_cases hw : w = 0 <;> simp [hw, inv_inv]
  open_source := by
    -- {∞} ∪ (coe '' {z | z ≠ 0}) is open
    -- In OnePoint topology, a set containing ∞ is open iff its preimage complement is compact
    rw [OnePoint.isOpen_iff_of_mem (by simp : OnePoint.infty ∈ _)]
    constructor
    · -- The complement of {z | z ≠ 0} in ℂ is {0}, which is closed
      convert isClosed_singleton (x := (0 : ℂ))
      ext z
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_union, Set.mem_singleton_iff,
        Set.mem_image, Set.mem_setOf_eq, not_or, not_exists, not_and]
      constructor
      · intro ⟨h1, h2⟩
        by_contra hz
        exact h2 z hz rfl
      · intro hz
        constructor
        · exact OnePoint.coe_ne_infty z
        · intro w hw hwz
          have : w = z := OnePoint.coe_injective hwz
          rw [this] at hw
          exact hw hz
    · -- {0} is compact
      convert isCompact_singleton (x := (0 : ℂ))
      ext z
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_union, Set.mem_singleton_iff,
        Set.mem_image, Set.mem_setOf_eq, not_or, not_exists, not_and]
      constructor
      · intro ⟨h1, h2⟩
        by_contra hz
        exact h2 z hz rfl
      · intro hz
        constructor
        · exact OnePoint.coe_ne_infty z
        · intro w hw hwz
          have : w = z := OnePoint.coe_injective hwz
          rw [this] at hw
          exact hw hz
  open_target := isOpen_univ
  continuousOn_toFun := by
    -- First prove the source is open (we'll need this)
    have source_open : IsOpen ({OnePoint.infty} ∪ (OnePoint.some '' {z : ℂ | z ≠ 0})) := by
      rw [OnePoint.isOpen_iff_of_mem (by simp : OnePoint.infty ∈ _)]
      constructor
      · convert isClosed_singleton (x := (0 : ℂ))
        ext z
        simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_union, Set.mem_singleton_iff,
          Set.mem_image, Set.mem_setOf_eq, not_or, not_exists, not_and]
        constructor
        · intro ⟨h1, h2⟩
          by_contra hz
          exact h2 z hz rfl
        · intro hz
          constructor
          · exact OnePoint.coe_ne_infty z
          · intro w hw hwz
            have : w = z := OnePoint.coe_injective hwz
            rw [this] at hw
            exact hw hz
      · convert isCompact_singleton (x := (0 : ℂ))
        ext z
        simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_union, Set.mem_singleton_iff,
          Set.mem_image, Set.mem_setOf_eq, not_or, not_exists, not_and]
        constructor
        · intro ⟨h1, h2⟩
          by_contra hz
          exact h2 z hz rfl
        · intro hz
          constructor
          · exact OnePoint.coe_ne_infty z
          · intro w hw hwz
            have : w = z := OnePoint.coe_injective hwz
            rw [this] at hw
            exact hw hz
    -- source is open, so ContinuousOn is equivalent to ContinuousAt at each point
    rw [source_open.continuousOn_iff]
    intro x hx
    cases x with
    | infty =>
      -- At ∞: need ContinuousAt f ∞ where f(∞) = 0
      rw [OnePoint.continuousAt_infty']
      -- Need: Tendsto (f ∘ coe) (coclosedCompact ℂ) (𝓝 0)
      -- f ∘ coe (z) = if z = 0 then 0 else z⁻¹
      -- The key is that z⁻¹ → 0 as |z| → ∞
      rw [Filter.hasBasis_coclosedCompact.tendsto_iff Metric.nhds_basis_ball]
      intro ε hε
      -- Need: ∃ closed compact K, ∀ z ∈ Kᶜ, f(coe z) ∈ ball 0 ε
      use Metric.closedBall 0 (1/ε)
      constructor
      · exact ⟨Metric.isClosed_closedBall, isCompact_closedBall 0 (1/ε)⟩
      · intro z hz
        simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
        simp only [Function.comp_apply]
        by_cases hz0 : z = 0
        · -- z = 0: but |0| = 0 < 1/ε since ε > 0, so 0 ∈ closedBall, contradiction
          simp only [hz0, norm_zero] at hz
          exact absurd (one_div_pos.mpr hε) (not_lt.mpr (le_of_lt hz))
        · -- z ≠ 0: f(coe z) = z⁻¹, and |z⁻¹| = 1/|z| < ε since |z| > 1/ε
          simp only [hz0, ↓reduceIte, Metric.mem_ball, dist_zero_right, norm_inv]
          have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
          -- From 1/ε < ‖z‖, we get ‖z‖⁻¹ < ε
          calc ‖z‖⁻¹ < (1/ε)⁻¹ := (inv_lt_inv₀ hz_pos (one_div_pos.mpr hε)).mpr hz
               _ = ε := by rw [one_div, inv_inv]
    | coe z =>
      -- At coe z with z in source, so z ≠ 0
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image, Set.mem_setOf_eq] at hx
      have hz_ne : z ≠ 0 := by
        cases hx with
        | inl h => exact (OnePoint.coe_ne_infty z h).elim
        | inr h =>
          obtain ⟨w, hw, hwz⟩ := h
          exact OnePoint.coe_injective hwz ▸ hw
      -- ContinuousAt f (coe z) ↔ ContinuousAt (f ∘ coe) z
      rw [OnePoint.continuousAt_coe]
      -- f ∘ coe (w) = if w = 0 then 0 else w⁻¹
      -- At z ≠ 0, in a neighborhood of z (not containing 0), this is just w⁻¹
      have h_inv_cont : ContinuousAt (fun w : ℂ => w⁻¹) z := continuousAt_inv₀ hz_ne
      apply h_inv_cont.congr
      -- The functions agree in a neighborhood of z
      filter_upwards [Metric.ball_mem_nhds z (norm_pos_iff.mpr hz_ne)]
      intro w hw
      simp only [Function.comp_apply]
      by_cases hw0 : w = 0
      · -- w = 0 would mean |0 - z| < |z|, i.e., |z| < |z|, contradiction
        simp only [hw0, Metric.mem_ball, dist_zero_left] at hw
        exact (lt_irrefl _ hw).elim
      · simp only [hw0, ↓reduceIte]
  continuousOn_invFun := by
    -- target = Set.univ, so this is ContinuousOn on all of ℂ
    rw [isOpen_univ.continuousOn_iff]
    intro w _
    by_cases hw : w = 0
    · -- At w = 0: invFun(0) = ∞
      subst hw
      -- Need ContinuousAt (fun w => if w = 0 then ∞ else coe(w⁻¹)) 0
      -- i.e., as w → 0, this function → ∞
      simp only [ContinuousAt, ↓reduceIte]
      -- Use the basis characterization of nhds ∞
      rw [OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
      intro K ⟨hK_closed, hK_compact⟩
      -- Need to show: ∀ᶠ w in 𝓝 0, f(w) ∈ (coe '' Kᶜ) ∪ {∞}
      -- For w = 0: f(0) = ∞ ∈ {∞} ✓
      -- For w ≠ 0: f(w) = coe(w⁻¹), need w⁻¹ ∈ Kᶜ, i.e., w⁻¹ ∉ K
      -- Since K is bounded, ∃ M, K ⊆ ball 0 M. For |w| < 1/M, |w⁻¹| > M, so w⁻¹ ∉ K
      obtain ⟨M, hM_pos, hM⟩ := hK_compact.isBounded.subset_ball_lt 0 0
      apply Filter.eventually_of_mem (Metric.ball_mem_nhds 0 (by positivity : 0 < 1/(M+1)))
      intro w' hw'
      simp only [Metric.mem_ball, dist_zero_right] at hw'
      by_cases hw'0 : w' = 0
      · -- f(0) = ∞
        simp only [hw'0, ↓reduceIte]
        right; rfl
      · -- f(w') = coe(w'⁻¹)
        simp only [hw'0, ↓reduceIte]
        left
        simp only [Set.mem_image, Set.mem_compl_iff]
        use w'⁻¹
        constructor
        · -- w'⁻¹ ∉ K because |w'⁻¹| > M
          intro hK
          have hM_bound := hM hK
          simp only [Metric.mem_ball, dist_zero_right] at hM_bound
          have hw'_pos : 0 < ‖w'‖ := norm_pos_iff.mpr hw'0
          rw [norm_inv] at hM_bound
          have h1 : ‖w'‖⁻¹ < M := hM_bound
          have h2 : M⁻¹ < ‖w'‖ := inv_lt_of_inv_lt₀ hw'_pos h1
          have h3 : (M + 1)⁻¹ ≤ M⁻¹ := inv_anti₀ hM_pos (by linarith : M ≤ M + 1)
          have h4 : (M + 1)⁻¹ < ‖w'‖ := lt_of_le_of_lt h3 h2
          rw [inv_eq_one_div] at h4
          linarith
        · rfl
    · -- At w ≠ 0: invFun(w) = coe(w⁻¹)
      -- invFun w' = if w' = 0 then OnePoint.infty else OnePoint.some w'⁻¹
      -- For w' near w ≠ 0, this equals OnePoint.some w'⁻¹
      have h_cont : ContinuousAt (fun w' => OnePoint.some (w'⁻¹ : ℂ)) w :=
        OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hw)
      apply h_cont.congr
      -- Show the functions agree in a neighborhood of w
      filter_upwards [Metric.ball_mem_nhds w (norm_pos_iff.mpr hw)]
      intro w' hw'
      by_cases hw'0 : w' = 0
      · -- w' = 0 would mean |w| < |w|, contradiction
        simp only [hw'0, Metric.mem_ball, dist_zero_left] at hw'
        exact (lt_irrefl _ hw').elim
      · simp only [hw'0, ↓reduceIte]

/-- ChartedSpace instance for the Riemann sphere.

    **Construction:** Uses two charts:
    - `riemannSphereFiniteChart`: identity on the finite part (covers ℂ)
    - `riemannSphereInftyChart`: z ↦ 1/z with ∞ ↦ 0 (covers (OnePoint ℂ) \ {0})

    **Transition function:** φ₁ ∘ φ₀⁻¹(z) = 1/z on ℂ \ {0}, which is holomorphic. -/
noncomputable instance chartedSpace_onePoint : ChartedSpace ℂ (OnePoint ℂ) where
  atlas := {riemannSphereFiniteChart, riemannSphereInftyChart}
  chartAt := fun x => match x with
    | .infty => riemannSphereInftyChart
    | .some z => if z = 0 then riemannSphereFiniteChart else riemannSphereInftyChart
  mem_chart_source := fun x => by
    cases x with
    | infty => simp [riemannSphereInftyChart]
    | coe z =>
      by_cases hz : z = 0
      · simp only [hz, ↓reduceIte]
        -- Need to show (0 : ℂ) ∈ source of finite chart = range coe
        simp only [riemannSphereFiniteChart, OpenPartialHomeomorph.symm_source,
          Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
        exact Set.mem_range_self (0 : ℂ)
      · simp only [hz, ↓reduceIte, riemannSphereInftyChart]
        right; exact ⟨z, hz, rfl⟩
  chart_mem_atlas := fun x => by
    cases x with
    | infty => right; rfl
    | coe z =>
      by_cases hz : z = 0
      · simp only [hz, ↓reduceIte]; left; rfl
      · simp only [hz, ↓reduceIte]; right; rfl

/-- Helper: The finite chart applies coe.symm -/
theorem riemannSphereFiniteChart_apply (z : ℂ) :
    riemannSphereFiniteChart (OnePoint.some z) = z := by
  have hmem : OnePoint.some z ∈ riemannSphereFiniteChart.source := by
    simp only [riemannSphereFiniteChart, OpenPartialHomeomorph.symm_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.mem_range]
    exact ⟨z, rfl⟩
  have hmap : riemannSphereFiniteChart.symm (riemannSphereFiniteChart (OnePoint.some z)) =
      OnePoint.some z := riemannSphereFiniteChart.left_inv hmem
  have hsymm : ∀ w, riemannSphereFiniteChart.symm w = OnePoint.some w := by
    intro w
    simp only [riemannSphereFiniteChart, OpenPartialHomeomorph.symm_symm,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply]
  rw [hsymm] at hmap
  exact OnePoint.coe_injective hmap

/-- Helper: The infty chart's toFun on finite points -/
theorem riemannSphereInftyChart_apply_coe (z : ℂ) (hz : z ≠ 0) :
    riemannSphereInftyChart (OnePoint.some z) = z⁻¹ := by
  -- Direct computation from the definition
  show (match OnePoint.some z with
    | OnePoint.some w => if w = 0 then 0 else w⁻¹
    | OnePoint.infty => 0) = z⁻¹
  simp only [hz, ↓reduceIte]

/-- Helper: The finite chart's symm applies coe -/
theorem riemannSphereFiniteChart_symm_apply (z : ℂ) :
    riemannSphereFiniteChart.symm z = OnePoint.some z := by
  simp only [riemannSphereFiniteChart, OpenPartialHomeomorph.symm_symm,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply]

/-- Helper: The infty chart's invFun on nonzero points -/
theorem riemannSphereInftyChart_symm_apply (z : ℂ) (hz : z ≠ 0) :
    riemannSphereInftyChart.symm z = OnePoint.some z⁻¹ := by
  -- invFun w = if w = 0 then ∞ else some w⁻¹
  -- For z ≠ 0, invFun z = some z⁻¹
  have h : riemannSphereInftyChart.invFun z = OnePoint.some z⁻¹ := by
    simp only [riemannSphereInftyChart, hz, ↓reduceIte]
  convert h using 1

/-- IsManifold instance for the Riemann sphere.

    **Holomorphicity:** The transition function z ↦ 1/z is holomorphic
    on ℂ \ {0}, with derivative -1/z². Since holomorphic implies ContDiff ℂ ∞,
    this makes the Riemann sphere a complex manifold. -/
noncomputable instance isManifold_onePoint : IsManifold (modelWithCornersSelf ℂ ℂ) ⊤ (OnePoint ℂ) where
  compatible := fun {e e'} he he' => by
    simp only [atlas] at he he'
    simp only [chartedSpace_onePoint] at he he'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he he'
    -- Need to check all four combinations of charts
    -- The key is that z ↦ 1/z is holomorphic on ℂ \ {0}, hence ContDiff ℂ ∞
    rcases he with rfl | rfl <;> rcases he' with rfl | rfl
    · -- finite ↔ finite: identity transition
      exact symm_trans_mem_contDiffGroupoid riemannSphereFiniteChart
    · -- finite → infty: transition map is z ↦ z⁻¹
      -- Show membership in contDiffGroupoid
      unfold contDiffGroupoid
      rw [mem_groupoid_of_pregroupoid]
      simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
        Function.comp_id, Function.id_comp, Set.preimage_id_eq, Set.range_id, Set.inter_univ, id_eq]
      constructor
      · -- ContDiffOn for the transition
        -- Source is {z : ℂ | z ≠ 0} since finiteChart.symm z = some z and
        -- inftyChart.source = {∞} ∪ coe '' {z | z ≠ 0}
        have hsub : (riemannSphereFiniteChart.symm ≫ₕ riemannSphereInftyChart).source ⊆ {(0 : ℂ)}ᶜ := by
          intro z hz
          simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
            Set.mem_inter_iff, Set.mem_preimage] at hz
          obtain ⟨hz1, hz2⟩ := hz
          -- hz2 : finiteChart.symm z ∈ inftyChart.source
          rw [riemannSphereFiniteChart_symm_apply] at hz2
          simp only [riemannSphereInftyChart, Set.mem_union, Set.mem_singleton_iff,
            Set.mem_image, Set.mem_setOf_eq] at hz2
          rcases hz2 with h | ⟨w, hw, heq⟩
          · exact (OnePoint.coe_ne_infty z h).elim
          · exact OnePoint.coe_injective heq ▸ hw
        have heq : ∀ z ∈ (riemannSphereFiniteChart.symm ≫ₕ riemannSphereInftyChart).source,
            (riemannSphereFiniteChart.symm ≫ₕ riemannSphereInftyChart) z = z⁻¹ := by
          intro z hz
          have hz0 : z ≠ 0 := Set.mem_compl_singleton_iff.mp (hsub hz)
          simp only [OpenPartialHomeomorph.trans_apply, riemannSphereFiniteChart_symm_apply]
          exact riemannSphereInftyChart_apply_coe z hz0
        exact ((contDiffOn_inv ℂ).mono hsub).congr heq
      · -- ContDiffOn for the inverse transition (symm)
        -- Use contrapositive: if z = 0 were in target, then symm z would be in source
        -- but symm 0 = finiteChart (inftyChart.symm 0) = finiteChart ∞, and ∞ ∉ finiteChart.source
        have hsub : (riemannSphereFiniteChart.symm ≫ₕ riemannSphereInftyChart).target ⊆ {(0 : ℂ)}ᶜ := by
          intro z hz
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro hz0
          have hz_preimg := (riemannSphereFiniteChart.symm ≫ₕ riemannSphereInftyChart).map_target hz
          have hsymm_eq : (riemannSphereFiniteChart.symm ≫ₕ riemannSphereInftyChart).symm z =
              riemannSphereFiniteChart (riemannSphereInftyChart.symm z) := rfl
          rw [hz0] at hsymm_eq
          have hinf : riemannSphereInftyChart.symm 0 = OnePoint.infty := by
            show riemannSphereInftyChart.invFun 0 = OnePoint.infty
            simp only [riemannSphereInftyChart, ↓reduceIte]
          rw [hinf] at hsymm_eq
          -- trans_target = inftyChart.target ∩ inftyChart.symm ⁻¹' finiteChart.symm.target
          -- For z = 0: inftyChart.symm 0 = ∞ ∉ finiteChart.symm.target = finiteChart.source = range some
          have h_infty_not_range : OnePoint.infty ∉ Set.range (OnePoint.some : ℂ → OnePoint ℂ) := by
            simp only [Set.mem_range, not_exists]
            intro x; exact OnePoint.coe_ne_infty x
          subst hz0
          rw [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at hz
          -- hz.2 : inftyChart.symm 0 ∈ finiteChart.symm.target = finiteChart.source = range some
          rw [hinf] at hz
          simp only [riemannSphereFiniteChart, OpenPartialHomeomorph.symm_symm,
            Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] at hz
          exact h_infty_not_range hz.2
        have heq : ∀ z ∈ (riemannSphereFiniteChart.symm ≫ₕ riemannSphereInftyChart).target,
            (riemannSphereFiniteChart.symm ≫ₕ riemannSphereInftyChart).symm z = z⁻¹ := by
          intro z hz
          have hz0 : z ≠ 0 := Set.mem_compl_singleton_iff.mp (hsub hz)
          have htrans : (riemannSphereFiniteChart.symm ≫ₕ riemannSphereInftyChart).symm z =
              riemannSphereFiniteChart (riemannSphereInftyChart.symm z) := rfl
          rw [htrans, riemannSphereInftyChart_symm_apply z hz0, riemannSphereFiniteChart_apply]
        exact ((contDiffOn_inv ℂ).mono hsub).congr heq
    · -- infty → finite: transition map is z ↦ z⁻¹ (symmetric case)
      -- This is riemannSphereInftyChart.symm ≫ₕ riemannSphereFiniteChart
      -- inftyChart.symm z = some z⁻¹ for z ≠ 0, and finiteChart (some w) = w
      -- So the transition is z ↦ z⁻¹ on {z | z ≠ 0}
      unfold contDiffGroupoid
      rw [mem_groupoid_of_pregroupoid]
      simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
        Function.comp_id, Function.id_comp, Set.preimage_id_eq, Set.range_id, Set.inter_univ, id_eq]
      constructor
      · -- ContDiffOn for the transition
        have hsub : (riemannSphereInftyChart.symm ≫ₕ riemannSphereFiniteChart).source ⊆ {(0 : ℂ)}ᶜ := by
          intro z hz
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro hz0
          simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
            Set.mem_inter_iff, Set.mem_preimage] at hz
          rw [hz0] at hz
          have hinf : riemannSphereInftyChart.symm 0 = OnePoint.infty := by
            show riemannSphereInftyChart.invFun 0 = OnePoint.infty
            simp only [riemannSphereInftyChart, ↓reduceIte]
          rw [hinf] at hz
          simp only [riemannSphereFiniteChart, OpenPartialHomeomorph.symm_source,
            Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.mem_range] at hz
          obtain ⟨w, hw⟩ := hz.2
          exact OnePoint.coe_ne_infty w hw
        have heq : ∀ z ∈ (riemannSphereInftyChart.symm ≫ₕ riemannSphereFiniteChart).source,
            (riemannSphereInftyChart.symm ≫ₕ riemannSphereFiniteChart) z = z⁻¹ := by
          intro z hz
          have hz0 : z ≠ 0 := Set.mem_compl_singleton_iff.mp (hsub hz)
          simp only [OpenPartialHomeomorph.trans_apply]
          rw [riemannSphereInftyChart_symm_apply z hz0, riemannSphereFiniteChart_apply]
        exact ((contDiffOn_inv ℂ).mono hsub).congr heq
      · -- ContDiffOn for the inverse transition
        have hsub : (riemannSphereInftyChart.symm ≫ₕ riemannSphereFiniteChart).target ⊆ {(0 : ℂ)}ᶜ := by
          intro z hz
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro hz0
          subst hz0
          -- (trans).symm 0 ∈ trans.source would mean inftyChart.symm 0 ∈ finiteChart.source
          -- But inftyChart.symm 0 = ∞ and ∞ ∉ finiteChart.source = range some
          have hz_preimg := (riemannSphereInftyChart.symm ≫ₕ riemannSphereFiniteChart).map_target hz
          simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
            Set.mem_inter_iff, Set.mem_preimage] at hz_preimg
          -- hz_preimg.2 : inftyChart.symm ((trans).symm 0) ∈ finiteChart.source
          -- (trans).symm 0 = inftyChart (finiteChart.symm 0) = inftyChart (some 0) = 0
          have hsymm_val : (riemannSphereInftyChart.symm ≫ₕ riemannSphereFiniteChart).symm (0 : ℂ) = (0 : ℂ) := by
            show riemannSphereInftyChart (riemannSphereFiniteChart.symm (0 : ℂ)) = (0 : ℂ)
            rw [riemannSphereFiniteChart_symm_apply]
            show (match OnePoint.some (0 : ℂ) with
              | OnePoint.some w => if w = 0 then (0 : ℂ) else w⁻¹
              | OnePoint.infty => (0 : ℂ)) = (0 : ℂ)
            simp only [↓reduceIte]
          rw [hsymm_val] at hz_preimg
          -- Now hz_preimg.2 : inftyChart.symm 0 ∈ finiteChart.source
          have hinfsymm0 : riemannSphereInftyChart.symm 0 = OnePoint.infty := by
            show riemannSphereInftyChart.invFun 0 = OnePoint.infty
            simp only [riemannSphereInftyChart, ↓reduceIte]
          rw [hinfsymm0] at hz_preimg
          simp only [riemannSphereFiniteChart, OpenPartialHomeomorph.symm_source,
            Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.mem_range] at hz_preimg
          obtain ⟨w, hw⟩ := hz_preimg.2
          exact OnePoint.coe_ne_infty w hw
        have heq : ∀ z ∈ (riemannSphereInftyChart.symm ≫ₕ riemannSphereFiniteChart).target,
            (riemannSphereInftyChart.symm ≫ₕ riemannSphereFiniteChart).symm z = z⁻¹ := by
          intro z hz
          have hz0 : z ≠ 0 := Set.mem_compl_singleton_iff.mp (hsub hz)
          have htrans : (riemannSphereInftyChart.symm ≫ₕ riemannSphereFiniteChart).symm z =
              riemannSphereInftyChart (riemannSphereFiniteChart.symm z) := rfl
          rw [htrans, riemannSphereFiniteChart_symm_apply, riemannSphereInftyChart_apply_coe z hz0]
        exact ((contDiffOn_inv ℂ).mono hsub).congr heq
    · -- infty ↔ infty: identity transition
      exact symm_trans_mem_contDiffGroupoid riemannSphereInftyChart

/-- The Riemann sphere ℂP¹ (one-point compactification of ℂ) -/
noncomputable def RiemannSphere : RiemannSurface where
  carrier := OnePoint ℂ
  topology := inferInstance
  t2 := inferInstance  -- OnePoint of locally compact T2 space is T4 hence T2
  secondCountable := RiemannSurfaces.Topology.OnePoint.Complex.secondCountableTopology
  chartedSpace := chartedSpace_onePoint
  isManifold := isManifold_onePoint
  connected := RiemannSurfaces.Topology.OnePoint.Complex.connectedSpace

/-!
## Compact Riemann Surfaces and Genus
-/

/-- A compact Riemann surface with specified genus.

    **Why genus is in the structure:**
    Mathematically, genus is determined by the topology: g = dim H₁(Σ, ℤ) / 2.
    Mathlib has singular homology (`AlgebraicTopology.singularHomologyFunctor`)
    but lacks computations for specific spaces like spheres or tori.

    Until such computations are available, we include genus as part of the
    structure, which is equivalent to working with "labeled" Riemann surfaces
    as is common in moduli theory.

    **Characterization:** For a compact Riemann surface of genus g:
    - χ = 2 - 2g (Euler characteristic)
    - dim H₁(Σ, ℤ) = 2g (first Betti number)
    - deg(K) = 2g - 2 (canonical bundle degree) -/
structure CompactRiemannSurface extends RiemannSurface where
  /-- Compactness -/
  compact : @CompactSpace carrier topology
  /-- The topological genus -/
  genus : ℕ

/-- A function f : RS → ℂ is holomorphic if it is complex-differentiable as a map of manifolds. -/
def RiemannSurface.IsHolomorphic (RS : RiemannSurface) (f : RS.carrier → ℂ) : Prop :=
  @MDifferentiable ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) RS.carrier RS.topology RS.chartedSpace
    ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ℂ _ _ f

/-- On a compact connected Riemann surface, every holomorphic function is constant.

    This is the analytic analogue of `regularIsConstant` in the algebraic approach.
    Uses Mathlib's maximum modulus principle: `MDifferentiable.exists_eq_const_of_compactSpace`

    **Proof**: A compact Riemann surface is a compact connected complex manifold.
    By the maximum modulus principle, any holomorphic function attains its maximum,
    and by connectedness, this forces the function to be constant. -/
theorem CompactRiemannSurface.holomorphicIsConstant (CRS : CompactRiemannSurface)
    (f : CRS.carrier → ℂ) (hf : CRS.toRiemannSurface.IsHolomorphic f) :
    ∃ c : ℂ, ∀ x, f x = c := by
  letI := CRS.topology
  letI := CRS.chartedSpace
  letI := CRS.isManifold
  haveI : CompactSpace CRS.carrier := CRS.compact
  haveI : PreconnectedSpace CRS.carrier := CRS.connected.toPreconnectedSpace
  -- Use Mathlib's theorem for compact connected complex manifolds
  have hconst := hf.exists_eq_const_of_compactSpace
  obtain ⟨v, hv⟩ := hconst
  exact ⟨v, fun x => congrFun hv x⟩

/-- Genus 0: the Riemann sphere -/
noncomputable def genus0Surface : CompactRiemannSurface where
  toRiemannSurface := RiemannSphere
  compact := @OnePoint.instCompactSpace ℂ _
  genus := 0

/-- The Riemann sphere has genus 0 (by definition in our structure) -/
theorem genus0Surface_genus : genus0Surface.genus = 0 := rfl

end RiemannSurfaces.Analytic

-- Re-export for backward compatibility
namespace RiemannSurfaces

export Analytic (RiemannSurface CompactRiemannSurface
  ComplexPlane RiemannSphere genus0Surface genus0Surface_genus
  chartedSpace_onePoint isManifold_onePoint)

end RiemannSurfaces
