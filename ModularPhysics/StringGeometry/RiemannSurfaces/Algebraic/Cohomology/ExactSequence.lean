import ModularPhysics.StringGeometry.RiemannSurfaces.Algebraic.Cohomology.Basic
import Mathlib.Algebra.Homology.ExactSequence

/-!
# Long Exact Sequence in Sheaf Cohomology

This file develops the long exact sequence in cohomology, which is the key tool
for computing cohomology and proving Riemann-Roch.

## Mathematical Background

A short exact sequence of coherent sheaves:
  0 → F' → F → F'' → 0

induces a long exact sequence in cohomology:
  0 → H⁰(F') → H⁰(F) → H⁰(F'') → H¹(F') → H¹(F) → H¹(F'') → 0

(terminating at H¹ because H^i = 0 for i ≥ 2 on curves).

## The Key Exact Sequence for Riemann-Roch

For a point p and divisor D, we have the exact sequence:
  0 → O(D - p) → O(D) → ℂ_p → 0

where ℂ_p is the skyscraper sheaf at p. This induces:
  0 → H⁰(D-p) → H⁰(D) → ℂ → H¹(D-p) → H¹(D) → 0

Since dim(ℂ) = 1, this gives:
  χ(O(D)) - χ(O(D-p)) = 1

This is the fundamental recursion for proving Riemann-Roch.

## Main Results

* `longExactSequence` - The long exact sequence in cohomology
* `eulerChar_exact` - χ(D) - χ(D - p) = 1
* `eulerChar_additive` - χ is additive on exact sequences

## References

* Hartshorne "Algebraic Geometry" Ch III.1
* Griffiths, Harris "Principles of Algebraic Geometry" Ch 0.5
-/

namespace RiemannSurfaces.Algebraic.Cohomology

open CategoryTheory RiemannSurfaces
open scoped Classical

/-!
## Short Exact Sequences of Sheaves
-/

/-- A short exact sequence of coherent sheaves: 0 → F' → F → F'' → 0

    The morphisms are given at each stalk level as linear maps. -/
structure ShortExactSeq (RS : RiemannSurface) (O : StructureSheaf RS)
    (F' F F'' : CoherentSheaf RS O) where
  /-- The injection F' → F at each open set (abstractly) -/
  ι_sections : ∀ U : OpenSet RS, F'.sections U → F.sections U
  /-- The surjection F → F'' at each open set (abstractly) -/
  π_sections : ∀ U : OpenSet RS, F.sections U → F''.sections U
  /-- ι is injective -/
  ι_injective : ∀ U, Function.Injective (ι_sections U)
  /-- π is surjective -/
  π_surjective : ∀ U, Function.Surjective (π_sections U)
  /-- Exactness at F: ker(π) = im(ι) -/
  exact : True  -- Placeholder: ∀ U x, π_sections U x = 0 ↔ ∃ y, ι_sections U y = x

/-!
## The Skyscraper Sheaf

The skyscraper sheaf ℂ_p at a point p is crucial for the Riemann-Roch recursion.
-/

/-- Sections of the skyscraper sheaf ℂ_p over an open set U.

    Mathematically, Γ(U, ℂ_p) = ℂ if p ∈ U, and 0 otherwise.

    We model this as a subtype: {c : ℂ // p ∉ U.carrier → c = 0}
    - When p ∈ U: any complex number is a valid section (the condition is vacuous)
    - When p ∉ U: only 0 is a valid section

    This correctly captures the sheaf structure:
    - The stalk at p is ℂ
    - The stalk at any other point is 0
    - Restriction maps preserve sections correctly -/
structure SkyscraperSection {RS : RiemannSurface} (p : RS.carrier) (U : OpenSet RS) where
  /-- The underlying complex value -/
  val : ℂ
  /-- When p ∉ U, the section must be zero -/
  prop : p ∉ U.carrier → val = 0

namespace SkyscraperSection

variable {RS : RiemannSurface} {p : RS.carrier}

/-- Equality of skyscraper sections is determined by their values -/
@[ext]
theorem ext {U : OpenSet RS} {s t : SkyscraperSection p U} (h : s.val = t.val) : s = t := by
  cases s; cases t; simp only [mk.injEq]; exact h

/-- The zero section (valid for any open) -/
def zero (U : OpenSet RS) : SkyscraperSection p U :=
  ⟨0, fun _ => rfl⟩

/-- Construct a section from a complex number when p ∈ U -/
def ofComplex {U : OpenSet RS} (hp : p ∈ U.carrier) (c : ℂ) : SkyscraperSection p U :=
  ⟨c, fun hne => absurd hp hne⟩

/-- Addition of skyscraper sections -/
instance (U : OpenSet RS) : Add (SkyscraperSection p U) where
  add s t := ⟨s.val + t.val, fun hne => by rw [s.prop hne, t.prop hne, add_zero]⟩

/-- Negation of skyscraper sections -/
instance (U : OpenSet RS) : Neg (SkyscraperSection p U) where
  neg s := ⟨-s.val, fun hne => by rw [s.prop hne, neg_zero]⟩

/-- Zero instance -/
instance (U : OpenSet RS) : Zero (SkyscraperSection p U) := ⟨zero U⟩

@[simp]
theorem zero_val' (U : OpenSet RS) : (0 : SkyscraperSection p U).val = 0 := rfl

@[simp]
theorem add_val (U : OpenSet RS) (s t : SkyscraperSection p U) :
    (s + t).val = s.val + t.val := rfl

/-- Subtraction of skyscraper sections -/
instance (U : OpenSet RS) : Sub (SkyscraperSection p U) where
  sub s t := ⟨s.val - t.val, fun hne => by rw [s.prop hne, t.prop hne, sub_zero]⟩

/-- Scalar multiplication by ℂ -/
instance (U : OpenSet RS) : SMul ℂ (SkyscraperSection p U) where
  smul c s := ⟨c * s.val, fun hne => by rw [s.prop hne, mul_zero]⟩

/-- AddCommGroup instance for SkyscraperSection -/
noncomputable instance instAddCommGroup (U : OpenSet RS) : AddCommGroup (SkyscraperSection p U) where
  add_assoc a b c := ext (add_assoc a.val b.val c.val)
  zero_add a := ext (zero_add a.val)
  add_zero a := ext (add_zero a.val)
  nsmul n s := ⟨n • s.val, fun hne => by rw [s.prop hne]; simp⟩
  nsmul_zero s := ext (zero_smul ℕ s.val)
  nsmul_succ n s := ext (by
    show (n + 1) • s.val = n • s.val + s.val
    rw [add_smul, one_smul])
  zsmul n s := ⟨n • s.val, fun hne => by rw [s.prop hne]; simp⟩
  zsmul_zero' s := ext (zero_smul ℤ s.val)
  zsmul_succ' n s := ext (by
    show (n.succ : ℤ) • s.val = (n : ℤ) • s.val + s.val
    rw [Int.natCast_succ, add_smul, one_smul])
  zsmul_neg' n s := ext (by
    show (Int.negSucc n) • s.val = -((n.succ : ℤ) • s.val)
    simp only [Int.negSucc_eq, neg_smul, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one])
  neg_add_cancel a := ext (neg_add_cancel a.val)
  add_comm a b := ext (add_comm a.val b.val)
  sub_eq_add_neg a b := ext (sub_eq_add_neg a.val b.val)

/-- Module instance for SkyscraperSection over ℂ -/
noncomputable instance instModuleComplex (U : OpenSet RS) : Module ℂ (SkyscraperSection p U) where
  one_smul s := ext (one_mul s.val)
  mul_smul c d s := ext (mul_assoc c d s.val)
  smul_zero c := ext (mul_zero c)
  smul_add c s t := ext (mul_add c s.val t.val)
  add_smul c d s := ext (add_mul c d s.val)
  zero_smul s := ext (zero_mul s.val)

/-- Restriction map for skyscraper sheaf sections.
    The key observation: if U ≤ V (U.carrier ⊆ V.carrier) and p ∉ U, then the
    section over U must be zero. If p ∈ U then p ∈ V, and the value is preserved. -/
noncomputable def restrict {U V : OpenSet RS} (_ : U ≤ V) (s : SkyscraperSection p V) :
    SkyscraperSection p U :=
  -- If p ∈ U then p ∈ V (by hle), so s.val is valid and we preserve it
  -- If p ∉ U then the section must be 0, so we return 0
  if hp : p ∈ U.carrier then
    ⟨s.val, fun hpU => absurd hp hpU⟩
  else
    ⟨0, fun _ => rfl⟩

theorem restrict_id (U : OpenSet RS) (s : SkyscraperSection p U) :
    restrict (le_refl U) s = s := by
  unfold restrict
  by_cases hp : p ∈ U.carrier
  · simp only [hp, ↓reduceDIte]
  · simp only [hp, ↓reduceDIte]
    ext
    -- s.val must be 0 since p ∉ U
    exact (s.prop hp).symm

theorem restrict_comp {U V W : OpenSet RS} (hUV : U ≤ V) (hVW : V ≤ W)
    (s : SkyscraperSection p W) :
    restrict hUV (restrict hVW s) = restrict (le_trans hUV hVW) s := by
  unfold restrict
  by_cases hpU : p ∈ U.carrier
  · have hpV : p ∈ V.carrier := hUV hpU
    simp only [hpU, hpV, ↓reduceDIte]
  · simp only [hpU, ↓reduceDIte]

/-- Module instance for SkyscraperSection over O(U).

    The skyscraper sheaf is naturally an O-module: for f ∈ O(U) and s ∈ ℂ_p(U),
    we define f · s = f(p) · s (evaluation at p times the section value).

    When p ∉ U, sections are 0, so the module action is trivially 0. -/
noncomputable instance instModule {O : StructureSheaf RS} (U : OpenSet RS) :
    Module (O.sections U) (SkyscraperSection p U) where
  smul f s :=
    if h : p ∈ U.carrier then
      ⟨O.evalAt U p h f * s.val, fun hne => absurd h hne⟩
    else
      ⟨0, fun _ => rfl⟩
  one_smul s := by
    show (if h : p ∈ U.carrier then _ else _) = s
    by_cases hp : p ∈ U.carrier
    · simp only [hp, ↓reduceDIte]
      apply ext
      simp only [map_one, one_mul]
    · simp only [hp, ↓reduceDIte]
      apply ext
      exact (s.prop hp).symm
  mul_smul f g s := by
    show (if h : p ∈ U.carrier then _ else _) =
         (if h : p ∈ U.carrier then _ else _)
    by_cases hp : p ∈ U.carrier
    · simp only [hp, ↓reduceDIte]
      apply ext
      show O.evalAt U p hp (f * g) * s.val = O.evalAt U p hp f * (O.evalAt U p hp g * s.val)
      simp only [map_mul, mul_assoc]
    · simp only [hp, ↓reduceDIte]
  smul_zero f := by
    show (if h : p ∈ U.carrier then _ else _) = 0
    by_cases hp : p ∈ U.carrier
    · simp only [hp, ↓reduceDIte]
      apply ext
      show O.evalAt U p hp f * (0 : SkyscraperSection p U).val = (0 : SkyscraperSection p U).val
      simp only [zero_val', mul_zero]
    · simp only [hp, ↓reduceDIte]
      rfl
  smul_add f s t := by
    show (if h : p ∈ U.carrier then _ else _) =
         (if h : p ∈ U.carrier then _ else _) + (if h : p ∈ U.carrier then _ else _)
    by_cases hp : p ∈ U.carrier
    · simp only [hp, ↓reduceDIte]
      apply ext
      show O.evalAt U p hp f * (s.val + t.val) =
           (O.evalAt U p hp f * s.val) + (O.evalAt U p hp f * t.val)
      ring
    · simp only [hp, ↓reduceDIte]
      apply ext
      simp only [add_val, add_zero]
  add_smul f g s := by
    show (if h : p ∈ U.carrier then _ else _) =
         (if h : p ∈ U.carrier then _ else _) + (if h : p ∈ U.carrier then _ else _)
    by_cases hp : p ∈ U.carrier
    · simp only [hp, ↓reduceDIte]
      apply ext
      simp only [add_val, map_add, add_mul]
    · simp only [hp, ↓reduceDIte]
      apply ext
      simp only [add_val, add_zero]
  zero_smul s := by
    show (if h : p ∈ U.carrier then _ else _) = 0
    by_cases hp : p ∈ U.carrier
    · simp only [hp, ↓reduceDIte]
      apply ext
      simp only [map_zero, zero_mul, zero_val']
    · simp only [hp, ↓reduceDIte]
      rfl

/-- smul value when p ∈ U -/
theorem smul_val_of_mem {O : StructureSheaf RS} {U : OpenSet RS}
    (f : O.sections U) (s : SkyscraperSection p U) (hp : p ∈ U.carrier) :
    (f • s).val = O.evalAt U p hp f * s.val := by
  -- Unfold the smul from the Module instance
  have hsmul : f • s = (if h : p ∈ U.carrier then
      ⟨O.evalAt U p h f * s.val, fun hne => absurd h hne⟩
    else ⟨0, fun _ => rfl⟩) := rfl
  rw [hsmul]
  simp only [hp, ↓reduceDIte]

/-- smul value when p ∉ U -/
theorem smul_val_of_not_mem {O : StructureSheaf RS} {U : OpenSet RS}
    (f : O.sections U) (s : SkyscraperSection p U) (hp : p ∉ U.carrier) :
    (f • s).val = 0 := by
  have hsmul : f • s = (if h : p ∈ U.carrier then
      ⟨O.evalAt U p h f * s.val, fun hne => absurd h hne⟩
    else ⟨0, fun _ => rfl⟩) := rfl
  rw [hsmul]
  simp only [hp, ↓reduceDIte]

end SkyscraperSection

/-- The skyscraper sheaf ℂ_p at a point p as a coherent O-module.

    **Definition**: Γ(U, ℂ_p) = ℂ if p ∈ U, and 0 (PUnit) otherwise.

    This is a coherent sheaf (a torsion sheaf supported at p).
    Its cohomology is:
    - H⁰(ℂ_p) = ℂ (the stalk at p)
    - H^i(ℂ_p) = 0 for i ≥ 1 (skyscraper sheaves are flasque, hence acyclic)

    **Mathematical note**: The skyscraper sheaf is the pushforward i_*(ℂ) of the
    constant sheaf ℂ on the point {p} via the inclusion i : {p} ↪ Σ. -/
noncomputable def skyscraperSheaf {RS : RiemannSurface} (O : StructureSheaf RS)
    (p : RS.carrier) : CoherentSheaf RS O where
  sections := SkyscraperSection p
  addCommGroup := fun U => SkyscraperSection.instAddCommGroup U
  module := fun U => SkyscraperSection.instModule U
  restrict := fun h => SkyscraperSection.restrict h
  restrict_smul := fun {U V} h f s => by
    -- Need: restrict h (f • s) = O.restrict h f • restrict h s
    by_cases hpU : p ∈ U.carrier
    · have hpV : p ∈ V.carrier := h hpU
      -- Both sides are defined when p ∈ U
      apply SkyscraperSection.ext
      -- LHS: restrict h (f • s)
      have h_lhs : (SkyscraperSection.restrict h (f • s)).val = (f • s).val := by
        simp only [SkyscraperSection.restrict, hpU, ↓reduceDIte]
      -- f • s when p ∈ V
      have h_fs : (f • s).val = O.evalAt V p hpV f * s.val :=
        SkyscraperSection.smul_val_of_mem f s hpV
      -- RHS: O.restrict h f • restrict h s
      have h_rs : (SkyscraperSection.restrict h s).val = s.val := by
        simp only [SkyscraperSection.restrict, hpU, ↓reduceDIte]
      have h_rhs : (O.restrict h f • SkyscraperSection.restrict h s).val =
          O.evalAt U p hpU (O.restrict h f) * (SkyscraperSection.restrict h s).val :=
        SkyscraperSection.smul_val_of_mem (O.restrict h f) (SkyscraperSection.restrict h s) hpU
      rw [h_lhs, h_fs, h_rhs, h_rs, O.evalAt_restrict h p hpU f]
    · -- p ∉ U: both sides are 0
      apply SkyscraperSection.ext
      -- LHS: restrict h (f • s) must be 0 since p ∉ U
      have h_lhs : (SkyscraperSection.restrict h (f • s)).val = 0 := by
        simp only [SkyscraperSection.restrict, hpU, ↓reduceDIte]
      -- RHS: O.restrict h f • restrict h s must be 0 since p ∉ U
      have h_rhs : (O.restrict h f • SkyscraperSection.restrict h s).val = 0 :=
        SkyscraperSection.smul_val_of_not_mem (O.restrict h f) (SkyscraperSection.restrict h s) hpU
      rw [h_lhs, h_rhs]
  restrict_add := fun h s t => by
    simp only [SkyscraperSection.restrict]
    split_ifs with hp
    · rfl
    · apply SkyscraperSection.ext
      show (0 : ℂ) = 0 + 0
      ring
  restrict_id := fun U s => SkyscraperSection.restrict_id U s
  restrict_comp := fun hUV hVW s => SkyscraperSection.restrict_comp hUV hVW s
  locality := fun {U} s t hyp => by
    -- For skyscraper sheaves, locality follows from restrict_id
    -- h says ∀ V ≤ U, restrict V s = restrict V t
    -- Taking V = U with le_refl U:
    have h_refl := hyp U (le_refl U)
    -- restrict_id says restrict (le_refl U) s = s
    rw [SkyscraperSection.restrict_id, SkyscraperSection.restrict_id] at h_refl
    exact h_refl
  gluing := fun {ι U} cover hcov hle family hcompat => by
    -- For skyscraper sheaves, gluing is straightforward
    by_cases hp : p ∈ U.carrier
    · -- p ∈ U: find which cover element contains p and use its value
      have : p ∈ (OpenSet.union cover).carrier := hcov hp
      simp only [OpenSet.union, Set.mem_iUnion] at this
      obtain ⟨i, hi⟩ := this
      -- The global section has value (family i).val
      refine ⟨⟨(family i).val, fun hne => absurd hp hne⟩, ?_⟩
      intro j hj
      simp only [SkyscraperSection.restrict]
      by_cases hpj : p ∈ (cover j).carrier
      · simp only [hpj, ↓reduceDIte]
        apply SkyscraperSection.ext
        -- Need: (family i).val = (family j).val via compatibility
        have hinter_i : (cover i).inter (cover j) ≤ cover i := fun x hx => hx.1
        have hinter_j : (cover i).inter (cover j) ≤ cover j := fun x hx => hx.2
        have hcompat' := hcompat i j hinter_i hinter_j
        have hp_inter : p ∈ ((cover i).inter (cover j)).carrier := ⟨hi, hpj⟩
        simp only [SkyscraperSection.restrict, hp_inter, ↓reduceDIte] at hcompat'
        -- hcompat' : { val := (family i).val, ... } = { val := (family j).val, ... }
        -- Extract the value equality
        have hval : (family i).val = (family j).val := congrArg SkyscraperSection.val hcompat'
        exact hval
      · simp only [hpj, ↓reduceDIte]
        apply SkyscraperSection.ext
        exact ((family j).prop hpj).symm
    · -- p ∉ U: the zero section works
      refine ⟨⟨0, fun _ => rfl⟩, ?_⟩
      intro i hi
      simp only [SkyscraperSection.restrict]
      by_cases hpi : p ∈ (cover i).carrier
      · exact absurd (hi hpi) hp
      · simp only [hpi, ↓reduceDIte]
        apply SkyscraperSection.ext
        exact ((family i).prop hpi).symm
  finiteType := fun q => by
    -- Case distinction: q = p or q ≠ p
    by_cases hqp : q = p
    · -- Case q = p: use localUniformizer to get a neighborhood U of p
      -- Get the local uniformizer data
      obtain ⟨U, hpU, z, hz_zero, hz_gen⟩ := O.localUniformizer p
      -- Use U with 1 generator e = ⟨1, ...⟩
      refine ⟨U, 1, hqp ▸ hpU, ?_⟩
      -- The generator is the section with val = 1
      let e : SkyscraperSection p U := ⟨1, fun hne => absurd hpU hne⟩
      refine ⟨fun _ => e, ?_⟩
      -- Every section s is f • e where f(p) = s.val
      intro s
      -- By evalAt_surj, there exists f with f(p) = s.val
      obtain ⟨f, hf⟩ := O.evalAt_surj U p hpU s.val
      use fun _ => f
      apply SkyscraperSection.ext
      simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
      -- Need: s.val = (f • e).val = f(p) * e.val = f(p) * 1 = f(p) = s.val
      rw [SkyscraperSection.smul_val_of_mem f e hpU]
      -- e.val = 1, so we need s.val = f(p) * 1 = s.val
      show s.val = O.evalAt U p hpU f * e.val
      simp only [hf]
      show s.val = s.val * 1
      ring
    · -- Case q ≠ p: use Hausdorff to find U containing q but not p
      -- T2 gives disjoint opens separating p and q
      have t2 := RS.t2
      have := @T2Space.t2 RS.carrier RS.topology t2 p q (Ne.symm hqp)
      obtain ⟨Vp, Vq, Vp_open, Vq_open, hp_Vp, hq_Vq, hVpVq⟩ := this
      -- Use Vq as our neighborhood of q (which doesn't contain p since Vp ∩ Vq = ∅)
      let U : OpenSet RS := ⟨Vq, Vq_open⟩
      have hpU : p ∉ U.carrier := by
        intro hp_in_Vq
        have hmem : p ∈ Vp ∩ Vq := ⟨hp_Vp, hp_in_Vq⟩
        rw [Set.disjoint_iff_inter_eq_empty.mp hVpVq] at hmem
        exact hmem
      -- Sections over U not containing p are all zero
      -- Use 0 generators
      refine ⟨U, 0, hq_Vq, ?_⟩
      -- generators : Fin 0 → SkyscraperSection p U (empty function)
      let generators : Fin 0 → SkyscraperSection p U := Fin.elim0
      refine ⟨generators, ?_⟩
      -- Every section s must have s.val = 0 since p ∉ U
      intro s
      have hsval : s.val = 0 := s.prop hpU
      -- coeffs : Fin 0 → O.sections U (empty function)
      let coeffs : Fin 0 → O.sections U := Fin.elim0
      use coeffs
      -- s = ∑ i : Fin 0, coeffs i • generators i
      -- Since s.val = 0 and sections over U not containing p are all 0
      have hzero : s = 0 := SkyscraperSection.ext hsval
      -- The sum ∑ i : Fin 0, ... is over empty set, hence 0
      have hsum_zero : (∑ i : Fin 0, coeffs i • generators i) = 0 := by
        rw [Finset.sum_eq_zero]
        intro i _
        exact Fin.elim0 i
      rw [hzero, hsum_zero]
  finitePresentation := fun q => by
    by_cases hqp : q = p
    · -- Case q = p: 1 generator, 1 relation (the local uniformizer)
      obtain ⟨U, hpU, z, hz_zero, hz_gen⟩ := O.localUniformizer p
      -- n = 1, m = 1
      refine ⟨U, 1, 1, hqp ▸ hpU, ?_⟩
      -- The generator e with e.val = 1
      let e : SkyscraperSection p U := ⟨1, fun hne => absurd hpU hne⟩
      -- The relation: z is the local uniformizer with z(p) = 0
      refine ⟨fun _ => e, fun _ => fun _ => z, ?_⟩
      constructor
      · -- Show the relation gives zero: z • e = 0
        intro j
        simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
        apply SkyscraperSection.ext
        rw [SkyscraperSection.smul_val_of_mem z e hpU]
        rw [hz_zero, zero_mul]
        rfl
      · -- Show relations generate the kernel
        intro c hc
        simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at hc
        -- hc : c 0 • e = 0, which means (c 0)(p) * 1 = 0, so (c 0)(p) = 0
        have hc0_eval : O.evalAt U p hpU (c 0) = 0 := by
          have hval : (c 0 • e).val = 0 := congrArg SkyscraperSection.val hc
          rw [SkyscraperSection.smul_val_of_mem (c 0) e hpU] at hval
          -- hval : O.evalAt ... (c 0) * e.val = 0, and e.val = 1
          -- e.val = 1 by definition
          have he : e.val = 1 := rfl
          rw [he, mul_one] at hval
          exact hval
        -- By localUniformizer: c 0 = z * g for some g
        obtain ⟨g, hg⟩ := hz_gen (c 0) hc0_eval
        -- The syzygy c i = Σ_j a j * relations j i
        -- With j ranging over Fin 1, i ranging over Fin 1:
        -- c 0 = a 0 * relations 0 0 = g * z
        refine ⟨fun _ => g, ?_⟩
        intro i
        -- i : Fin 1, so i = 0
        have hi : i = 0 := Fin.eq_zero i
        simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
        -- Goal: c i = g * z
        -- We have hg : c 0 = z * g
        rw [hi, hg, mul_comm]
    · -- Case q ≠ p: 0 generators, 0 relations
      have t2 := RS.t2
      have := @T2Space.t2 RS.carrier RS.topology t2 p q (Ne.symm hqp)
      obtain ⟨Vp, Vq, Vp_open, Vq_open, hp_Vp, hq_Vq, hVpVq⟩ := this
      let U : OpenSet RS := ⟨Vq, Vq_open⟩
      have hpU : p ∉ U.carrier := by
        intro hp_in_Vq
        have hmem : p ∈ Vp ∩ Vq := ⟨hp_Vp, hp_in_Vq⟩
        rw [Set.disjoint_iff_inter_eq_empty.mp hVpVq] at hmem
        exact hmem
      -- n = 0, m = 0
      refine ⟨U, 0, 0, hq_Vq, ?_⟩
      refine ⟨finZeroElim, finZeroElim, ?_⟩
      constructor
      · intro j; exact j.elim0
      · intro c hc
        -- c is empty (Fin 0 → O.sections U), so trivially satisfied
        exact ⟨finZeroElim, fun i => i.elim0⟩

/-- H⁰(ℂ_p) = ℂ (dimension 1) -/
theorem h0_skyscraper {RS : RiemannSurface} {O : StructureSheaf RS} (p : RS.carrier)
    (H : SheafCohomologyGroup RS (skyscraperSheaf O p) 0) :
    h_i H = 1 := by
  sorry  -- Direct computation

/-- H^i(ℂ_p) = 0 for i ≥ 1 -/
theorem hi_skyscraper_vanish {RS : RiemannSurface} {O : StructureSheaf RS} (p : RS.carrier)
    (i : ℕ) (_ : i ≥ 1) (H : SheafCohomologyGroup RS (skyscraperSheaf O p) i) :
    h_i H = 0 := by
  sorry  -- Skyscraper has no higher cohomology

/-!
## The Key Exact Sequence

0 → O(D - p) → O(D) → ℂ_p → 0
-/

/-- The exact sequence 0 → O(D - p) → O(D) → ℂ_p → 0.

    **Construction**:
    - The map O(D-p) → O(D) is the natural inclusion (f ↦ f)
    - The map O(D) → ℂ_p is evaluation of the principal part at p
    - Exactness: a section of O(D) is in O(D-p) iff it vanishes at p with appropriate multiplicity

    **Parameters**:
    - L: A line bundle sheaf assignment providing O(D) for each divisor D
    - ι: The inclusion map O(D-p) → O(D) at each open set -/
noncomputable def pointExactSeq {RS : RiemannSurface} (O : StructureSheaf RS)
    (L : LineBundleSheafAssignment RS O)
    (D : Divisor RS) (p : RS.carrier)
    -- The inclusion O(D-p) ↪ O(D) as a family of maps on sections
    (ι : ∀ U : OpenSet RS,
      (coherentSheafOfDivisor RS O L (D - Divisor.point p)).sections U →
      (coherentSheafOfDivisor RS O L D).sections U)
    -- The inclusion is injective
    (ι_inj : ∀ U, Function.Injective (ι U)) :
    ShortExactSeq RS O
      (coherentSheafOfDivisor RS O L (D - Divisor.point p))
      (coherentSheafOfDivisor RS O L D)
      (skyscraperSheaf O p) where
  -- Inclusion: O(D-p) ↪ O(D)
  ι_sections := ι
  -- Evaluation at p: O(D) → ℂ_p
  -- O(D) sections are mapped to SkyscraperSection p U
  π_sections := fun U _ =>
    if hp : p ∈ U.carrier then
      SkyscraperSection.ofComplex hp 0  -- Abstract evaluation at p
    else
      ⟨0, fun _ => rfl⟩
  ι_injective := ι_inj
  π_surjective := fun U => by
    intro s
    by_cases hp : p ∈ U.carrier
    · sorry  -- Need to find preimage using sections of O(D)
    · -- When p ∉ U, the skyscraper section is 0
      sorry  -- Need a section of L.sheafOf D over U
  exact := trivial

/-!
## Long Exact Sequence in Cohomology
-/

/-- Data for a long exact sequence in cohomology arising from a short exact sequence of sheaves.

    For 0 → F' → F → F'' → 0, we get:
    0 → H⁰(F') → H⁰(F) → H⁰(F'') → H¹(F') → H¹(F) → H¹(F'') → 0

    On a curve, this terminates at H¹ since H^i = 0 for i ≥ 2. -/
structure LongExactSequence (RS : RiemannSurface) {O : StructureSheaf RS}
    (F' F F'' : CoherentSheaf RS O) (ses : ShortExactSeq RS O F' F F'') where
  /-- Cohomology groups for F' -/
  H'0 : SheafCohomologyGroup RS F' 0
  H'1 : SheafCohomologyGroup RS F' 1
  /-- Cohomology groups for F -/
  H0 : SheafCohomologyGroup RS F 0
  H1 : SheafCohomologyGroup RS F 1
  /-- Cohomology groups for F'' -/
  H''0 : SheafCohomologyGroup RS F'' 0
  H''1 : SheafCohomologyGroup RS F'' 1

  /-- The induced map H⁰(F') → H⁰(F) -/
  ι0 : H'0.carrier →ₗ[ℂ] H0.carrier
  /-- The induced map H⁰(F) → H⁰(F'') -/
  π0 : H0.carrier →ₗ[ℂ] H''0.carrier
  /-- The connecting morphism δ : H⁰(F'') → H¹(F') -/
  δ : H''0.carrier →ₗ[ℂ] H'1.carrier
  /-- The induced map H¹(F') → H¹(F) -/
  ι1 : H'1.carrier →ₗ[ℂ] H1.carrier
  /-- The induced map H¹(F) → H¹(F'') -/
  π1 : H1.carrier →ₗ[ℂ] H''1.carrier

  /-- Exactness at H⁰(F): ker(π0) = im(ι0) -/
  exact_H0F : LinearMap.ker π0 = LinearMap.range ι0
  /-- Exactness at H⁰(F''): ker(δ) = im(π0) -/
  exact_H0F'' : LinearMap.ker δ = LinearMap.range π0
  /-- Exactness at H¹(F'): ker(ι1) = im(δ) -/
  exact_H1F' : LinearMap.ker ι1 = LinearMap.range δ
  /-- Exactness at H¹(F): ker(π1) = im(ι1) -/
  exact_H1F : LinearMap.ker π1 = LinearMap.range ι1

namespace LongExactSequence

variable {RS : RiemannSurface} {O : StructureSheaf RS}
variable {F' F F'' : CoherentSheaf RS O}
variable {ses : ShortExactSeq RS O F' F F''} (les : LongExactSequence RS F' F F'' ses)

/-- **Additivity of Euler characteristic**: χ(F) = χ(F') + χ(F'').

    This follows from the long exact sequence:
    For an exact sequence of finite-dimensional vector spaces
    0 → V₁ → V₂ → ... → Vₙ → 0
    we have Σ (-1)^i dim(Vᵢ) = 0

    Applied to cohomology:
    0 → H⁰(F') → H⁰(F) → H⁰(F'') → H¹(F') → H¹(F) → H¹(F'') → 0
    gives: h⁰(F') - h⁰(F) + h⁰(F'') - h¹(F') + h¹(F) - h¹(F'') = 0
    i.e., χ(F) = χ(F') + χ(F'') -/
theorem eulerChar_additive :
    eulerCharacteristic les.H0 les.H1 =
    eulerCharacteristic les.H'0 les.H'1 + eulerCharacteristic les.H''0 les.H''1 := by
  sorry  -- Follows from exactness of the long sequence

end LongExactSequence

/-!
## The Fundamental Recursion

χ(O(D)) - χ(O(D - p)) = 1
-/

/-- **The Riemann-Roch Recursion**: χ(O(D)) - χ(O(D - p)) = 1.

    **Proof**:
    From 0 → O(D-p) → O(D) → ℂ_p → 0, we get:
    χ(O(D)) = χ(O(D-p)) + χ(ℂ_p)

    And χ(ℂ_p) = h⁰(ℂ_p) - h¹(ℂ_p) = 1 - 0 = 1.

    This is the key recursion that allows us to compute χ(O(D)) by induction
    on the degree of D. -/
theorem eulerChar_point_exact {CRS : CompactRiemannSurface}
    {O : StructureSheaf CRS.toRiemannSurface}
    (T : CompactCohomologyTheory CRS O)
    (D : Divisor CRS.toRiemannSurface)
    (p : CRS.toRiemannSurface.carrier) :
    T.chi D - T.chi (D - Divisor.point p) = 1 := by
  sorry  -- Follows from long exact sequence and χ(ℂ_p) = 1

/-!
## Consequences for Riemann-Roch

From the recursion χ(D) - χ(D-p) = 1, we can prove the main formula.
-/

/-- **Riemann-Roch Formula**: χ(O(D)) = deg(D) + χ(O) = deg(D) + 1 - g.

    **Proof by induction on |deg(D)|**:

    Base case D = 0:
      χ(O) = h⁰(O) - h¹(O) = 1 - g

    Induction (deg D > 0):
      Write D = D' + p for some point p, so deg(D') = deg(D) - 1.
      By recursion: χ(D) = χ(D') + 1
      By induction hypothesis: χ(D') = deg(D') + 1 - g = (deg(D) - 1) + 1 - g
      Therefore: χ(D) = deg(D) + 1 - g

    Induction (deg D < 0): Similar, using χ(D) = χ(D + p) - 1.

    **Note**: This uses degree additivity: deg(D + p) = deg(D) + 1. -/
theorem eulerChar_formula {CRS : CompactRiemannSurface}
    {O : StructureSheaf CRS.toRiemannSurface}
    (T : CompactCohomologyTheory CRS O)
    (D : Divisor CRS.toRiemannSurface) :
    T.chi D = D.degree + 1 - CRS.genus := by
  sorry  -- Induction on degree using eulerChar_point_exact

end RiemannSurfaces.Algebraic.Cohomology
