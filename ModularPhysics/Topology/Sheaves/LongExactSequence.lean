import ModularPhysics.Topology.Sheaves.CechCohomology

/-!
# Long Exact Sequence in Čech Cohomology

This file develops the long exact sequence in Čech cohomology arising from
a short exact sequence of presheaves.

## Main Definitions

* `PresheafMorphism`: A morphism between presheaves of abelian groups
* `ShortExactSequence`: A short exact sequence 0 → F' → F → F'' → 0
* `connectingHomomorphism`: The connecting map δⁿ : Hⁿ(F'') → Hⁿ⁺¹(F')

## Main Results

* `longExactSequence`: The long exact sequence in cohomology
* `exactness_at_*`: Exactness at each term

## Mathematical Background

Given a short exact sequence of presheaves:
  0 → F' → F → F'' → 0

We get a long exact sequence in Čech cohomology:
  0 → H⁰(F') → H⁰(F) → H⁰(F'') →^δ H¹(F') → H¹(F) → H¹(F'') →^δ ...

The key construction is the connecting homomorphism δ, defined as follows:
Given a class [σ''] ∈ Hⁿ(F''), choose a lift σ of σ'' to Cⁿ(F).
Then dσ ∈ Cⁿ⁺¹(F) maps to 0 in Cⁿ⁺¹(F''), so dσ ∈ im(Cⁿ⁺¹(F') → Cⁿ⁺¹(F)).
Let τ' ∈ Cⁿ⁺¹(F') be a preimage. Then dτ' = 0 (since dσ = 0 in F and the map is injective).
So τ' is a cocycle, and δ([σ'']) := [τ'].

## References

* Wells, R.O. "Differential Analysis on Complex Manifolds" Chapter II.3
* Godement, R. "Topologie algébrique et théorie des faisceaux"
* Hartshorne, R. "Algebraic Geometry" Chapter III
-/

universe u v w

open CategoryTheory TopologicalSpace CechCohomology

namespace CechCohomology

variable {X : Type u} [TopologicalSpace X]

/-!
## Presheaf Morphisms

A morphism of presheaves is a family of group homomorphisms that commute with restriction.
-/

/-- A morphism between presheaves of abelian groups.

    This is a natural transformation: for each open U, we have φ_U : F(U) → G(U),
    and these commute with restriction maps. -/
structure PresheafMorphism (F G : AbPresheaf X) where
  /-- The map on sections over each open -/
  map : ∀ U : Opens X, F.sections U → G.sections U
  /-- The map is a group homomorphism -/
  map_add : ∀ U (s t : F.sections U), map U (s + t) = map U s + map U t
  /-- The map commutes with restriction -/
  naturality : ∀ {U V : Opens X} (h : U ≤ V) (s : F.sections V),
    map U (F.restrict h s) = G.restrict h (map V s)

namespace PresheafMorphism

variable {F G H : AbPresheaf X}

/-- A presheaf morphism preserves zero -/
theorem map_zero (φ : PresheafMorphism F G) (U : Opens X) : φ.map U 0 = 0 := by
  have h := φ.map_add U 0 0
  simp only [add_zero] at h
  have h2 : 0 + φ.map U 0 = φ.map U 0 + φ.map U 0 := by rw [zero_add]; exact h
  exact (add_right_cancel h2).symm

/-- A presheaf morphism preserves negation -/
theorem map_neg (φ : PresheafMorphism F G) (U : Opens X) (s : F.sections U) :
    φ.map U (-s) = -(φ.map U s) := by
  have h := φ.map_add U (-s) s
  rw [neg_add_cancel, map_zero] at h
  exact (neg_eq_of_add_eq_zero_left h.symm).symm

/-- A presheaf morphism preserves subtraction -/
theorem map_sub (φ : PresheafMorphism F G) (U : Opens X) (s t : F.sections U) :
    φ.map U (s - t) = φ.map U s - φ.map U t := by
  rw [sub_eq_add_neg, φ.map_add, φ.map_neg, sub_eq_add_neg]

/-- A presheaf morphism preserves finite sums -/
theorem map_sum {ι : Type*} (φ : PresheafMorphism F G) (U : Opens X) (s : Finset ι)
    (f : ι → F.sections U) :
    φ.map U (s.sum f) = s.sum (fun i => φ.map U (f i)) := by
  classical
  induction s using Finset.induction with
  | empty => simp [φ.map_zero]
  | insert x s hx ih => rw [Finset.sum_insert hx, φ.map_add, ih, Finset.sum_insert hx]

/-- A presheaf morphism preserves natural number scalar multiplication -/
theorem map_nsmul (φ : PresheafMorphism F G) (U : Opens X) (n : ℕ) (s : F.sections U) :
    φ.map U (n • s) = n • φ.map U s := by
  induction n with
  | zero => simp only [zero_smul, φ.map_zero]
  | succ k ih => simp only [succ_nsmul]; rw [φ.map_add, ih]

/-- A presheaf morphism preserves integer scalar multiplication -/
theorem map_zsmul (φ : PresheafMorphism F G) (U : Opens X) (n : ℤ) (s : F.sections U) :
    φ.map U (n • s) = n • φ.map U s := by
  cases n with
  | ofNat k => simp only [Int.ofNat_eq_natCast, natCast_zsmul, map_nsmul]
  | negSucc k =>
    -- Int.negSucc k • s = -((k + 1) • s) by negSucc_zsmul
    simp only [negSucc_zsmul, φ.map_neg, map_nsmul]

/-- The identity morphism -/
def id (F : AbPresheaf X) : PresheafMorphism F F where
  map := fun _ s => s
  map_add := fun _ _ _ => rfl
  naturality := fun _ _ => rfl

/-- Composition of presheaf morphisms -/
def comp (ψ : PresheafMorphism G H) (φ : PresheafMorphism F G) : PresheafMorphism F H where
  map := fun U s => ψ.map U (φ.map U s)
  map_add := fun U s t => by rw [φ.map_add, ψ.map_add]
  naturality := fun h s => by rw [φ.naturality, ψ.naturality]

/-- The kernel of a presheaf morphism at each open -/
def kernelAt (φ : PresheafMorphism F G) (U : Opens X) : Set (F.sections U) :=
  { s | φ.map U s = 0 }

/-- The image of a presheaf morphism at each open -/
def imageAt (φ : PresheafMorphism F G) (U : Opens X) : Set (G.sections U) :=
  { t | ∃ s : F.sections U, φ.map U s = t }

/-- A morphism is injective if it's injective at each open -/
def IsInjective (φ : PresheafMorphism F G) : Prop :=
  ∀ U : Opens X, Function.Injective (φ.map U)

/-- A morphism is surjective if it's surjective at each open -/
def IsSurjective (φ : PresheafMorphism F G) : Prop :=
  ∀ U : Opens X, Function.Surjective (φ.map U)

/-- Injective iff kernel is trivial -/
theorem isInjective_iff_kernel_trivial (φ : PresheafMorphism F G) :
    IsInjective φ ↔ ∀ U s, φ.map U s = 0 → s = 0 := by
  constructor
  · intro hinj U s hs
    -- hinj U : Function.Injective (φ.map U)
    -- hs : φ.map U s = 0
    -- We have φ.map U s = 0 = φ.map U 0 (by map_zero)
    have h : φ.map U s = φ.map U 0 := by rw [hs, map_zero]
    exact hinj U h
  · intro htriv U s t hst
    have : φ.map U (s - t) = 0 := by rw [map_sub, hst, sub_self]
    have hsub := htriv U (s - t) this
    exact sub_eq_zero.mp hsub

end PresheafMorphism

/-!
## Short Exact Sequences

A short exact sequence of presheaves: 0 → F' →^ι F →^π F'' → 0
-/

/-- A short exact sequence of presheaves of abelian groups.

    0 → F' →^ι F →^π F'' → 0

    At each open U:
    - ι_U is injective
    - π_U is surjective
    - ker(π_U) = im(ι_U)
-/
structure ShortExactSequence (F' F F'' : AbPresheaf X) where
  /-- The injection F' → F -/
  ι : PresheafMorphism F' F
  /-- The surjection F → F'' -/
  π : PresheafMorphism F F''
  /-- ι is injective -/
  ι_injective : ι.IsInjective
  /-- π is surjective -/
  π_surjective : π.IsSurjective
  /-- Exactness: ker(π) = im(ι) -/
  exact : ∀ U : Opens X, ι.imageAt U = π.kernelAt U

namespace ShortExactSequence

variable {F' F F'' : AbPresheaf X} (ses : ShortExactSequence F' F F'')

/-- π ∘ ι = 0 (follows from exactness) -/
theorem comp_zero (U : Opens X) (s : F'.sections U) : ses.π.map U (ses.ι.map U s) = 0 := by
  have h : ses.ι.map U s ∈ ses.ι.imageAt U := ⟨s, rfl⟩
  rw [ses.exact U] at h
  exact h

/-- If π(t) = 0, then t is in the image of ι -/
theorem ker_eq_im (U : Opens X) (t : F.sections U) (ht : ses.π.map U t = 0) :
    ∃ s : F'.sections U, ses.ι.map U s = t := by
  have h : t ∈ ses.π.kernelAt U := ht
  rw [← ses.exact U] at h
  exact h

end ShortExactSequence

/-!
## Induced Maps on Čech Cochains

A presheaf morphism induces maps on Čech cochains.
-/

/-- A presheaf morphism induces a map on Čech n-cochains -/
def inducedCochainMap (φ : PresheafMorphism F G) (U : OpenCover X) (n : ℕ) :
    CechCochain F U n → CechCochain G U n :=
  fun σ f => φ.map (U.inter f) (σ f)

/-- The induced map is a group homomorphism -/
theorem inducedCochainMap_add (φ : PresheafMorphism F G) (U : OpenCover X) (n : ℕ)
    (σ τ : CechCochain F U n) :
    inducedCochainMap φ U n (σ + τ) = inducedCochainMap φ U n σ + inducedCochainMap φ U n τ := by
  funext f
  simp only [inducedCochainMap]
  exact φ.map_add (U.inter f) (σ f) (τ f)

/-- The induced map preserves zero -/
theorem inducedCochainMap_zero (φ : PresheafMorphism F G) (U : OpenCover X) (n : ℕ) :
    inducedCochainMap φ U n 0 = 0 := by
  funext f
  simp only [inducedCochainMap]
  exact φ.map_zero (U.inter f)

/-- The induced map commutes with the Čech differential -/
theorem inducedCochainMap_comm_cechDiff (φ : PresheafMorphism F G) (U : OpenCover X) (n : ℕ)
    (σ : CechCochain F U n) :
    inducedCochainMap φ U (n + 1) (cechDiff F U n σ) =
    cechDiff G U n (inducedCochainMap φ U n σ) := by
  funext f
  simp only [inducedCochainMap, cechDiff]
  -- LHS: φ.map _ (∑ j, (-1)^j • F.restrict _ (σ (deleteFace j f)))
  -- RHS: ∑ j, (-1)^j • G.restrict _ (φ.map _ (σ (deleteFace j f)))
  -- By naturality: φ.map ∘ F.restrict = G.restrict ∘ φ.map
  -- By linearity: φ.map (∑ ...) = ∑ φ.map (...)
  -- By φ.map (n • x) = n • φ.map x

  -- Use map_sum for φ distributing over finite sums
  rw [φ.map_sum]
  congr 1
  funext j

  -- φ.map (n • x) = n • φ.map x (for integer scalars)
  rw [φ.map_zsmul]
  congr 1
  -- Now use naturality: φ.map (F.restrict h x) = G.restrict h (φ.map x)
  exact φ.naturality (inter_mono_deleteFace U j f) (σ (deleteFace j f))

/-!
## Induced Maps on Čech Cocycles

The induced cochain map restricts to cocycles and descends to cohomology.
-/

/-- A presheaf morphism induces a map on Čech cocycles -/
def inducedCocycleMap (φ : PresheafMorphism F G) (U : OpenCover X) (n : ℕ) :
    CechCocycles F U n → CechCocycles G U n :=
  fun ⟨σ, hσ⟩ => ⟨inducedCochainMap φ U n σ, by
    rw [← inducedCochainMap_comm_cechDiff, hσ, inducedCochainMap_zero]⟩

/-- The induced cocycle map is compatible with the cohomology equivalence relation -/
theorem inducedCocycleMap_respects_equiv (φ : PresheafMorphism F G) (U : OpenCover X) (n : ℕ)
    (σ σ' : CechCocycles F U (n + 1))
    (h : CechCohomologyRelSucc F U n σ σ') :
    CechCohomologyRelSucc G U n (inducedCocycleMap φ U (n + 1) σ)
                                  (inducedCocycleMap φ U (n + 1) σ') := by
  obtain ⟨τ, hτ⟩ := h
  use inducedCochainMap φ U n τ
  simp only [inducedCocycleMap]
  rw [← inducedCochainMap_comm_cechDiff, hτ]
  -- Need: φ(σ - σ') = φ(σ) - φ(σ')
  funext f
  simp only [inducedCochainMap]
  exact φ.map_sub (U.inter f) (σ.val f) (σ'.val f)

/-- A presheaf morphism induces a map on H^{n+1} -/
def inducedH (φ : PresheafMorphism F G) (U : OpenCover X) (n : ℕ) :
    CechHSucc F U n → CechHSucc G U n :=
  Quotient.lift
    (fun σ => Quotient.mk (CechCohomologySetoidSucc G U n) (inducedCocycleMap φ U (n + 1) σ))
    (fun σ σ' h => Quotient.sound (inducedCocycleMap_respects_equiv φ U n σ σ' h))

/-- A presheaf morphism induces a map on H^0 -/
def inducedH0 (φ : PresheafMorphism F G) (U : OpenCover X) :
    CechH0 F U → CechH0 G U :=
  inducedCocycleMap φ U 0

/-!
## The Connecting Homomorphism

The connecting homomorphism δⁿ : Hⁿ(F'') → Hⁿ⁺¹(F') is the key construction.
-/

/-- Given a short exact sequence and an F''-cocycle σ'', we can lift it to F
    (since π is surjective on cochains). -/
noncomputable def liftCochain (ses : ShortExactSequence F' F F'') (U : OpenCover X) (n : ℕ)
    (σ'' : CechCochain F'' U n) : CechCochain F U n :=
  fun f => (ses.π_surjective (U.inter f) (σ'' f)).choose

/-- The lift property: π(lift(σ'')) = σ'' -/
theorem liftCochain_spec (ses : ShortExactSequence F' F F'') (U : OpenCover X) (n : ℕ)
    (σ'' : CechCochain F'' U n) (f : Fin (n + 1) → U.ι) :
    ses.π.map (U.inter f) (liftCochain ses U n σ'' f) = σ'' f :=
  (ses.π_surjective (U.inter f) (σ'' f)).choose_spec

/-- For a cocycle σ'', the differential of its lift lies in the image of ι
    (since π(d(lift σ'')) = d(π(lift σ'')) = d(σ'') = 0) -/
theorem diff_lift_in_image (ses : ShortExactSequence F' F F'') (U : OpenCover X) (n : ℕ)
    (σ'' : CechCocycles F'' U n) (f : Fin (n + 2) → U.ι) :
    ∃ τ' : F'.sections (U.inter f),
      ses.ι.map (U.inter f) τ' = cechDiff F U n (liftCochain ses U n σ''.val) f := by
  apply ses.ker_eq_im
  -- Need: π(d(lift σ'')) = 0
  -- We have: π ∘ lift = id, so π(d(lift σ'')) = d(π(lift σ'')) = d(σ'') = 0
  have hcomm : ses.π.map (U.inter f) (cechDiff F U n (liftCochain ses U n σ''.val) f) =
      cechDiff F'' U n σ''.val f := by
    -- Use that inducedCochainMap commutes with cechDiff
    have := inducedCochainMap_comm_cechDiff ses.π U n (liftCochain ses U n σ''.val)
    have hf := congrFun this f
    simp only [inducedCochainMap] at hf
    rw [hf]
    congr 1
    funext g
    exact liftCochain_spec ses U n σ''.val g
  rw [hcomm, σ''.prop]
  rfl

/-- The preimage of d(lift σ'') under ι, chosen componentwise -/
noncomputable def connectingCochainAux (ses : ShortExactSequence F' F F'') (U : OpenCover X) (n : ℕ)
    (σ'' : CechCocycles F'' U n) : CechCochain F' U (n + 1) :=
  fun f => (diff_lift_in_image ses U n σ'' f).choose

/-- The connecting cochain maps to d(lift σ'') under ι -/
theorem connectingCochainAux_spec (ses : ShortExactSequence F' F F'') (U : OpenCover X) (n : ℕ)
    (σ'' : CechCocycles F'' U n) (f : Fin (n + 2) → U.ι) :
    ses.ι.map (U.inter f) (connectingCochainAux ses U n σ'' f) =
    cechDiff F U n (liftCochain ses U n σ''.val) f :=
  (diff_lift_in_image ses U n σ'' f).choose_spec

/-- The connecting cochain is a cocycle (since ι is injective and d² = 0) -/
theorem connectingCochainAux_cocycle (ses : ShortExactSequence F' F F'') (U : OpenCover X) (n : ℕ)
    (σ'' : CechCocycles F'' U n) :
    cechDiff F' U (n + 1) (connectingCochainAux ses U n σ'') = 0 := by
  -- We need to show d(τ') = 0
  -- We know ι(τ') = d(lift σ'')
  -- So ι(d(τ')) = d(ι(τ')) = d(d(lift σ'')) = 0 (by d² = 0)
  -- Since ι is injective, d(τ') = 0
  -- Work pointwise: two cochains are equal iff they agree at each index
  funext f
  -- Use injectivity of ι at the open U.inter f
  apply (PresheafMorphism.isInjective_iff_kernel_trivial ses.ι).mp ses.ι_injective (U.inter f)
  -- Goal: ses.ι.map (U.inter f) (cechDiff F' U (n + 1) (connectingCochainAux ...) f) = 0
  -- Use commutativity of ι with d
  have hcomm := inducedCochainMap_comm_cechDiff ses.ι U (n + 1) (connectingCochainAux ses U n σ'')
  have hf := congrFun hcomm f
  simp only [inducedCochainMap] at hf
  rw [hf]
  -- Now goal: cechDiff F U (n + 1) (inducedCochainMap ses.ι U (n + 1) (connectingCochainAux ...)) f = 0
  -- The ι-image of τ' is d(lift σ'')
  have htau : inducedCochainMap ses.ι U (n + 1) (connectingCochainAux ses U n σ'') =
      cechDiff F U n (liftCochain ses U n σ''.val) := by
    funext g
    simp only [inducedCochainMap]
    exact connectingCochainAux_spec ses U n σ'' g
  rw [htau]
  -- Now goal: cechDiff F U (n + 1) (cechDiff F U n (liftCochain ...)) f = 0
  -- This is d² = 0
  have := cechDiff_comp_zero F U n (liftCochain ses U n σ''.val)
  exact congrFun this f

/-- The connecting cocycle -/
noncomputable def connectingCocycle (ses : ShortExactSequence F' F F'') (U : OpenCover X) (n : ℕ)
    (σ'' : CechCocycles F'' U n) : CechCocycles F' U (n + 1) :=
  ⟨connectingCochainAux ses U n σ'', connectingCochainAux_cocycle ses U n σ''⟩

/-- The connecting homomorphism on H^0: δ⁰ : H⁰(F'') → H¹(F') -/
noncomputable def connectingH0 (ses : ShortExactSequence F' F F'') (U : OpenCover X) :
    CechH0 F'' U → CechHSucc F' U 0 :=
  fun σ'' => Quotient.mk (CechCohomologySetoidSucc F' U 0) (connectingCocycle ses U 0 σ'')

/-- Helper: For elements in ker(π), get preimage under ι -/
noncomputable def preimageUnderι (ses : ShortExactSequence F' F F'')
    (V : Opens X) (t : F.sections V) (ht : ses.π.map V t = 0) : F'.sections V :=
  (ses.ker_eq_im V t ht).choose

theorem preimageUnderι_spec (ses : ShortExactSequence F' F F'')
    (V : Opens X) (t : F.sections V) (ht : ses.π.map V t = 0) :
    ses.ι.map V (preimageUnderι ses V t ht) = t :=
  (ses.ker_eq_im V t ht).choose_spec

/-- For a cochain in ker(π), get preimage cochain under ι -/
noncomputable def preimageCochain (ses : ShortExactSequence F' F F'') (U : OpenCover X)
    (n : ℕ) (σ : CechCochain F U n) (hσ : ∀ f, ses.π.map (U.inter f) (σ f) = 0) :
    CechCochain F' U n :=
  fun f => preimageUnderι ses (U.inter f) (σ f) (hσ f)

theorem preimageCochain_spec (ses : ShortExactSequence F' F F'') (U : OpenCover X)
    (n : ℕ) (σ : CechCochain F U n) (hσ : ∀ f, ses.π.map (U.inter f) (σ f) = 0) (f : Fin (n + 1) → U.ι) :
    ses.ι.map (U.inter f) (preimageCochain ses U n σ hσ f) = σ f :=
  preimageUnderι_spec ses (U.inter f) (σ f) (hσ f)

/-- The connecting homomorphism on H^{n+1}: δⁿ⁺¹ : Hⁿ⁺¹(F'') → Hⁿ⁺²(F')

    The proof shows that if σ'' ~ τ'' (cohomologous), then δ(σ'') ~ δ(τ'').
    Key steps:
    1. σ'' - τ'' = d(η'') for some η''
    2. Lift η'' to η in F
    3. lift_σ - lift_τ - d(η) ∈ ker(π) = im(ι), so = ι(ξ) for some ξ
    4. d(lift_σ - lift_τ) = d(ι(ξ)) + d²(η) = ι(d(ξ))
    5. So connectingCochainAux(σ'') - connectingCochainAux(τ'') = d(ξ) -/
noncomputable def connectingH (ses : ShortExactSequence F' F F'') (U : OpenCover X) (n : ℕ) :
    CechHSucc F'' U n → CechHSucc F' U (n + 1) := by
  apply Quotient.lift (fun σ'' => Quotient.mk (CechCohomologySetoidSucc F' U (n + 1))
    (connectingCocycle ses U (n + 1) σ''))
  -- Need to show: if σ'' ~ τ'' then δ(σ'') ~ δ(τ'')
  intro σ'' τ'' hrel
  apply Quotient.sound
  -- σ'' - τ'' = d(η'') for some η''
  obtain ⟨η'', hη⟩ := hrel
  -- hη : σ''.val - τ''.val = cechDiff F'' U n η''

  -- Step 1: Lift η'' to η in F
  let η := liftCochain ses U n η''

  -- Step 2: Compute σ' - τ' - d(η) and show it's in ker(π)
  let diff_lifts := liftCochain ses U (n + 1) σ''.val - liftCochain ses U (n + 1) τ''.val -
                     cechDiff F U n η

  -- Show diff_lifts ∈ ker(π): π(diff_lifts) = σ'' - τ'' - d(η'') = 0
  have hdiff_ker : ∀ f, ses.π.map (U.inter f) (diff_lifts f) = 0 := fun f => by
    -- Unfold diff_lifts f = (lift_σ - lift_τ - d(η)) f
    show ses.π.map (U.inter f) ((liftCochain ses U (n + 1) σ''.val - liftCochain ses U (n + 1) τ''.val -
                     cechDiff F U n η) f) = 0
    -- (a - b - c) f = a f - b f - c f by Pi.sub_apply
    show ses.π.map (U.inter f) (liftCochain ses U (n + 1) σ''.val f -
         liftCochain ses U (n + 1) τ''.val f - cechDiff F U n η f) = 0
    rw [ses.π.map_sub, ses.π.map_sub]
    rw [liftCochain_spec ses U (n + 1) σ''.val f]
    rw [liftCochain_spec ses U (n + 1) τ''.val f]
    -- Need: π(d(η)) = d(π(η)) = d(η'')
    have hcomm := inducedCochainMap_comm_cechDiff ses.π U n η
    have hf := congrFun hcomm f
    simp only [inducedCochainMap] at hf
    rw [hf]
    have hπη : inducedCochainMap ses.π U n η = η'' := by
      funext g
      simp only [inducedCochainMap, η]
      exact liftCochain_spec ses U n η'' g
    rw [hπη]
    -- Now goal: σ''.val f - τ''.val f - cechDiff F'' U n η'' f = 0
    -- hη : cechDiff F'' U n η'' = σ''.val - τ''.val
    have hη_f := congrFun hη f
    -- hη_f : cechDiff F'' U n η'' f = (σ''.val - τ''.val) f = σ''.val f - τ''.val f
    rw [hη_f]
    -- Goal: σ''.val f - τ''.val f - (σ''.val - τ''.val) f = 0
    -- (σ''.val - τ''.val) f = σ''.val f - τ''.val f by definition (Pi.sub_apply)
    -- So goal becomes: (a - b) - (a - b) = 0
    exact sub_self _

  -- Step 3: Get ξ such that ι(ξ) = diff_lifts
  let ξ := preimageCochain ses U (n + 1) diff_lifts hdiff_ker

  -- Step 4: Show that d(ξ) = connectingCochainAux(σ'') - connectingCochainAux(τ'')
  use ξ
  -- Need to prove cochain equality: d(ξ) = connectingCocycle(σ'').val - connectingCocycle(τ'').val
  funext f
  simp only [connectingCocycle]
  -- Use injectivity of ι to prove equality: a = b iff ι(a) = ι(b)
  apply ses.ι_injective (U.inter f)
  -- Goal: ι(d(ξ) f) = ι((connectingCochainAux σ'' - connectingCochainAux τ'') f)
  -- Unfold Pi.sub_apply on RHS: (a - b) f = a f - b f
  show ses.ι.map (U.inter f) (cechDiff F' U (n + 1) ξ f) =
       ses.ι.map (U.inter f) (connectingCochainAux ses U (n + 1) σ'' f -
                               connectingCochainAux ses U (n + 1) τ'' f)
  rw [ses.ι.map_sub]
  rw [connectingCochainAux_spec ses U (n + 1) σ'' f]
  rw [connectingCochainAux_spec ses U (n + 1) τ'' f]
  -- RHS: d(lift_σ) f - d(lift_τ) f
  -- LHS: ι(d(ξ) f) = d(ι(ξ)) f (by naturality of ι and d)
  have hcomm := inducedCochainMap_comm_cechDiff ses.ι U (n + 1) ξ
  have hf := congrFun hcomm f
  simp only [inducedCochainMap] at hf
  rw [hf]
  -- Now LHS is: cechDiff F U (n + 1) (inducedCochainMap ses.ι U (n + 1) ξ) f
  -- Since ι(ξ) = diff_lifts = lift_σ - lift_τ - d(η)
  have hξ : inducedCochainMap ses.ι U (n + 1) ξ = diff_lifts := by
    funext g
    simp only [inducedCochainMap, ξ]
    exact preimageCochain_spec ses U (n + 1) diff_lifts hdiff_ker g
  rw [hξ]
  -- LHS: d(diff_lifts) f = d(lift_σ - lift_τ - d(η)) f
  simp only [diff_lifts]
  rw [cechDiff_sub, cechDiff_sub]
  -- Goal: (cechDiff ... - cechDiff ... - cechDiff (cechDiff η)) f = ... f - ... f
  -- First unfold (a - b - c) f = a f - b f - c f
  show cechDiff F U (n + 1) (liftCochain ses U (n + 1) σ''.val) f -
       cechDiff F U (n + 1) (liftCochain ses U (n + 1) τ''.val) f -
       cechDiff F U (n + 1) (cechDiff F U n η) f =
       cechDiff F U (n + 1) (liftCochain ses U (n + 1) σ''.val) f -
       cechDiff F U (n + 1) (liftCochain ses U (n + 1) τ''.val) f
  -- d(d(η)) = 0 by d² = 0
  have hdd := cechDiff_comp_zero F U n η
  have hdd_f := congrFun hdd f
  -- hdd_f : cechDiff F U (n + 1) (cechDiff F U n η) f = 0 f
  rw [hdd_f]
  -- Goal: a - b - 0 f = a - b
  -- For cochains (Pi types), (0 : α → β) x = 0 by Pi.zero_apply
  have h0 : (0 : CechCochain F U (n + 2)) f = 0 := rfl
  rw [h0, sub_zero]

end CechCohomology
