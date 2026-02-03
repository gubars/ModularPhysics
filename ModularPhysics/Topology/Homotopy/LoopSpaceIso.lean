/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.Topology.Homotopy.Suspension
import ModularPhysics.Topology.Homotopy.WeakEquivalence
import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Loop Space-Homotopy Group Isomorphism

This file establishes the fundamental isomorphism π_n(ΩX) ≅ π_{n+1}(X) between homotopy
groups of the loop space and the space itself.

## Main Results

* `loopSpaceHomotopyGroupEquiv` - The bijection π_n(ΩX) ≃ π_{n+1}(X)

## Mathematical Background

The key insight is that:
- An n-dimensional loop in ΩX (the loop space) can be "uncurried" to an (n+1)-dimensional loop in X
- This uncurrying is a homeomorphism at the level of GenLoop
- It descends to a bijection on homotopy groups

The construction uses Mathlib's `GenLoop.loopHomeo` which establishes:
  GenLoop (Fin (n+1)) X x ≃ₜ LoopSpace (GenLoop {j // j ≠ i} X x) GenLoop.const

## References

* May, "A Concise Course in Algebraic Topology", Chapter 8
* Hatcher, "Algebraic Topology", Chapter 4
-/

universe u

open CategoryTheory TopologicalSpace unitInterval Topology.Homotopy

namespace PointedTopSpace

variable (X : PointedTopSpace.{0})

/-! ## Connecting PointedTopSpace.loopSpace to Mathlib's LoopSpace -/

section LoopSpaceConnection

/-- Our `loopSpace X` has the same underlying type as Mathlib's `LoopSpace`. -/
theorem loopSpace_carrier_eq : (loopSpace X).carrier = LoopSpace X.carrier X.basepoint := rfl

/-- The basepoint of our loop space is the constant loop. -/
theorem loopSpace_basepoint_eq : (loopSpace X).basepoint = Path.refl X.basepoint := rfl

end LoopSpaceConnection

/-! ## The Curry Bijection at GenLoop Level

Mathlib provides the homeomorphism:
  GenLoop.loopHomeo i : GenLoop N X x ≃ₜ LoopSpace (GenLoop {j // j ≠ i} X x) GenLoop.const

For N = Fin (n+1) and i = ⟨n, ...⟩ (the last element), we get:
  GenLoop (Fin (n+1)) X x ≃ₜ LoopSpace (GenLoop {j : Fin (n+1) // j ≠ ⟨n, ...⟩} X x) GenLoop.const

The subtype {j : Fin (n+1) // j ≠ Fin.last n} is equivalent to Fin n via Fin.castSucc.
-/

section CurryBijection

variable (n : ℕ)

/-- The currying homeomorphism using the last index.
    This maps (n+1)-dimensional loops in X to loops in the space of n-dimensional loops. -/
def genLoopCurry : GenLoop (Fin (n + 1)) X.carrier X.basepoint ≃ₜ
    LoopSpace (GenLoop {j : Fin (n + 1) // j ≠ Fin.last n} X.carrier X.basepoint) GenLoop.const :=
  GenLoop.loopHomeo (Fin.last n)

/-- The inverse (uncurrying) map. -/
def genLoopUncurry : LoopSpace (GenLoop {j : Fin (n + 1) // j ≠ Fin.last n} X.carrier X.basepoint)
    GenLoop.const → GenLoop (Fin (n + 1)) X.carrier X.basepoint :=
  (genLoopCurry X n).symm

end CurryBijection

/-! ## Homotopy in the Target Space

The target of genLoopCurry is LoopSpace Y y = Path y y for some Y and y.
We need to connect Path homotopy to GenLoop homotopy.
-/

section PathHomotopy

variable (n : ℕ)

/-- Two paths that are path-homotopic give homotopic elements when viewed through uncurrying. -/
theorem uncurry_homotopic_of_path_homotopic
    {p₁ p₂ : LoopSpace (GenLoop {j : Fin (n + 1) // j ≠ Fin.last n} X.carrier X.basepoint)
      GenLoop.const}
    (h : p₁.Homotopic p₂) :
    GenLoop.Homotopic (genLoopUncurry X n p₁) (genLoopUncurry X n p₂) := by
  -- The uncurrying map is genLoopCurry.symm = loopHomeo.symm = fromLoop
  -- Use Mathlib's homotopicFrom which says: if (toLoop i p).Homotopic (toLoop i q)
  -- then Homotopic p q
  unfold genLoopUncurry genLoopCurry
  -- We need to show: GenLoop.Homotopic (fromLoop (Fin.last n) p₁) (fromLoop (Fin.last n) p₂)
  -- By homotopicFrom, it suffices to show:
  -- (toLoop (Fin.last n) (fromLoop (Fin.last n) p₁)).Homotopic
  -- (toLoop (Fin.last n) (fromLoop (Fin.last n) p₂))
  apply GenLoop.homotopicFrom (Fin.last n)
  -- Convert loopHomeo.symm to fromLoop, then use to_from
  simp only [GenLoop.loopHomeo_symm_apply, GenLoop.to_from]
  exact h

end PathHomotopy

/-! ## Infrastructure: Curry/Uncurry for GenLoop

The key isomorphism π_n(ΩX) ≅ π_{n+1}(X) requires converting between:
- GenLoop (Fin n) (Path x x) (Path.refl x): n-dimensional loops in the path space
- GenLoop (Fin (n+1)) X x: (n+1)-dimensional loops in X

The construction uses Mathlib's `homotopyGroupEquivFundamentalGroup` combined with
the fact that `Path x x ≃ GenLoop (Fin 1) X x` via `genLoopEquivOfUnique`.

The mathematical content is that an n-dimensional loop in the loop space ΩX
can be "uncurried" to an (n+1)-dimensional loop in X by viewing the path parameter
as an additional cube dimension.
-/

section CurryUncurryInfra

variable (n : ℕ)

/-- The uncurry map: GenLoop (Fin n) (Path x x) → GenLoop (Fin (n+1)) X.
    Given γ : I^n → Path x x, produce γ' : I^{n+1} → X by γ'(t) = γ(init t)(t(last n)). -/
def uncurryGenLoopMap (γ : GenLoop (Fin n) (Path X.basepoint X.basepoint) (Path.refl X.basepoint)) :
    GenLoop (Fin (n + 1)) X.carrier X.basepoint where
  val := ⟨fun t => (γ (Fin.init t)) (t (Fin.last n)), by
    -- Continuity: compose path evaluation with continuous maps
    have hpair : Continuous (fun t : Fin (n + 1) → I => (γ (Fin.init t), t (Fin.last n))) :=
      Continuous.prodMk (γ.val.continuous.comp (continuous_pi fun _ => continuous_apply _))
        (continuous_apply _)
    exact Continuous.comp continuous_eval hpair⟩
  property := by
    -- Boundary condition: if t is on boundary of I^{n+1}, then γ'(t) = x
    intro t ⟨i, hi⟩
    by_cases h : i = Fin.last n
    · -- i is the last index: t(last n) = 0 or 1, so path endpoint is x
      subst h
      show (γ (Fin.init t)) (t (Fin.last n)) = X.basepoint
      cases hi with
      | inl h0 => simp only [h0]; exact (γ (Fin.init t)).source
      | inr h1 => simp only [h1]; exact (γ (Fin.init t)).target
    · -- i is not the last index: (init t) is on boundary of I^n
      have hi' : Fin.init t ∈ Cube.boundary (Fin n) := by
        use ⟨i.val, Fin.val_lt_last h⟩
        simp only [Fin.init]
        convert hi using 1
      have hγ : γ (Fin.init t) = Path.refl X.basepoint := γ.property (Fin.init t) hi'
      show (γ (Fin.init t)) (t (Fin.last n)) = X.basepoint
      simp only [hγ, Path.refl_apply]

@[simp]
theorem uncurryGenLoopMap_apply
    (γ : GenLoop (Fin n) (Path X.basepoint X.basepoint) (Path.refl X.basepoint))
    (t : Fin (n + 1) → I) :
    (uncurryGenLoopMap X n γ).val t = (γ.val (Fin.init t)) (t (Fin.last n)) := rfl

/-- Helper: construct a path from a continuous function with given endpoints. -/
def mkPath' (f : I → X.carrier) (hf : Continuous f) (hs : f 0 = X.basepoint) (ht : f 1 = X.basepoint) :
    Path X.basepoint X.basepoint where
  toFun := f
  continuous_toFun := hf
  source' := hs
  target' := ht

@[simp]
theorem mkPath'_apply (f : I → X.carrier) (hf : Continuous f) (hs : f 0 = X.basepoint)
    (ht : f 1 = X.basepoint) (s : I) : mkPath' X f hf hs ht s = f s := rfl

/-- The curry map: GenLoop (Fin (n+1)) X → GenLoop (Fin n) (Path x x).
    Given δ : I^{n+1} → X, produce δ' : I^n → Path x x by δ'(t)(s) = δ(snoc t s). -/
def curryGenLoopMap (δ : GenLoop (Fin (n + 1)) X.carrier X.basepoint) :
    GenLoop (Fin n) (Path X.basepoint X.basepoint) (Path.refl X.basepoint) where
  val := ⟨fun t => mkPath' X (fun s => δ (Fin.snoc t s))
      (by -- Path continuity: s ↦ δ(Fin.snoc t s) is continuous
        have h : Continuous (fun s : I => @Fin.snoc n (fun _ => I) t s) := by
          apply continuous_pi
          intro i
          by_cases hi : i.val < n
          · simp only [Fin.snoc, dif_pos hi]
            exact continuous_const
          · simp only [Fin.snoc, dif_neg hi]
            exact continuous_id
        exact δ.val.continuous.comp h)
      (by -- source: δ(snoc t 0) = x (0 is on boundary)
        apply δ.property
        exact ⟨Fin.last n, Or.inl (@Fin.snoc_last n (fun _ => I) 0 t)⟩)
      (by -- target: δ(snoc t 1) = x (1 is on boundary)
        apply δ.property
        exact ⟨Fin.last n, Or.inr (@Fin.snoc_last n (fun _ => I) 1 t)⟩),
    by -- Outer continuity: t ↦ (Path given by s ↦ δ(snoc t s)) is continuous
      apply Path.continuous_uncurry_iff.mp
      -- Now prove: Continuous (fun (t, s) => δ(snoc t s))
      apply Continuous.comp δ.val.continuous
      apply continuous_pi
      intro i
      by_cases hi : i.val < n
      · simp only [Fin.snoc, dif_pos hi]
        exact (continuous_apply (⟨i.val, hi⟩ : Fin n)).comp continuous_fst
      · simp only [Fin.snoc, dif_neg hi]
        exact continuous_snd⟩
  property := by
    -- Boundary condition: if t is on boundary of I^n, then δ'(t) = Path.refl x
    intro t ⟨⟨j, hj⟩, hval⟩
    ext s
    simp only [mkPath', Path.refl_apply]
    apply δ.property
    -- snoc t s is on boundary of I^{n+1} because t_j is 0 or 1
    use Fin.castSucc ⟨j, hj⟩
    simp only [Fin.snoc, Fin.val_castSucc]
    simp only [dif_pos hj]
    exact hval

@[simp]
theorem curryGenLoopMap_apply
    (δ : GenLoop (Fin (n + 1)) X.carrier X.basepoint)
    (t : Fin n → I) (s : I) :
    ((curryGenLoopMap X n δ).val t) s = δ.val (Fin.snoc t s) := rfl

/-- Uncurrying commutes with transAt: composing path-valued GenLoops along index i in the
    n-cube corresponds to composing the uncurried (n+1)-cube GenLoops along Fin.castSucc i.

    This is a key compatibility lemma for proving the group homomorphism property.
    The proof shows that both sides evaluate to the same value at every point. -/
theorem uncurryGenLoopMap_transAt (i : Fin n)
    (γ₁ γ₂ : GenLoop (Fin n) (Path X.basepoint X.basepoint) (Path.refl X.basepoint)) :
    uncurryGenLoopMap X n (GenLoop.transAt i γ₁ γ₂) =
    GenLoop.transAt (Fin.castSucc i) (uncurryGenLoopMap X n γ₁) (uncurryGenLoopMap X n γ₂) := by
  -- Both sides are GenLoops in I^{n+1} → X. We show they're equal pointwise.
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  -- Unfold LHS: (transAt i γ₁ γ₂)(init t)(t(last n))
  simp only [uncurryGenLoopMap_apply]
  -- The transAt is defined as copy, and copy f g h applied to t equals g t
  rw [GenLoop.transAt, GenLoop.transAt]
  simp only [GenLoop.copy, ContinuousMap.coe_mk]
  -- Key: (Fin.init t) i = t (Fin.castSucc i)
  have hkey : (Fin.init t) i = t (Fin.castSucc i) := rfl
  simp only [hkey]
  -- Now both conditions match. Check the branches.
  split_ifs with h
  · -- First branch: both use γ₁ with scaled i-coordinate
    -- LHS: (γ₁ (update (init t) i scaled))(t (last n))
    -- RHS: (uncurry γ₁) (update t (castSucc i) scaled)
    --    = (γ₁ (init (update t (castSucc i) scaled))) ((update t (castSucc i) scaled) (last n))
    have hlast : Fin.last n ≠ Fin.castSucc i := by
      intro heq
      have : (Fin.last n).val = (Fin.castSucc i).val := congrArg Fin.val heq
      simp only [Fin.val_last, Fin.val_castSucc] at this
      omega
    have hinit : Fin.init (Function.update t (Fin.castSucc i)
        (Set.projIcc 0 1 zero_le_one (2 * t (Fin.castSucc i)))) =
        Function.update (Fin.init t) i (Set.projIcc 0 1 zero_le_one (2 * t (Fin.castSucc i))) := by
      ext j
      simp only [Fin.init, Function.update_apply]
      by_cases hj : j = i
      · subst hj; simp only [↓reduceIte]
      · simp only [hj, ↓reduceIte]
        have hne : Fin.castSucc j ≠ Fin.castSucc i := fun heq => hj (Fin.castSucc_injective _ heq)
        simp only [hne, ↓reduceIte]
    have hupdate_last : (Function.update t (Fin.castSucc i)
        (Set.projIcc 0 1 zero_le_one (2 * t (Fin.castSucc i)))) (Fin.last n) = t (Fin.last n) := by
      simp only [Function.update_apply, hlast, ↓reduceIte]
    -- The RHS is (uncurryGenLoopMap X n γ₁) applied to the updated t
    -- It unfolds to (γ₁ (init (updated t))) ((updated t) (last n))
    -- By hinit: init (updated t) = update (init t) i (...)
    -- By hupdate_last: (updated t) (last n) = t (last n)
    -- So RHS = (γ₁ (update (init t) i ...)) (t (last n)) = LHS
    let t' := Function.update t (Fin.castSucc i) (Set.projIcc 0 1 zero_le_one (2 * t (Fin.castSucc i)))
    -- Show that RHS = (γ₁ (Fin.init t')) (t' (Fin.last n))
    change (γ₁ (Function.update (Fin.init t) i _)) (t (Fin.last n)) =
           (γ₁ (Fin.init t')) (t' (Fin.last n))
    -- Both sides are equal: Fin.init t' = update (init t) i ... by hinit
    -- and t' (last n) = t (last n) by hupdate_last
    -- The Set.projIcc proofs are equal by proof irrelevance
    exact congrArg₂ (fun x y => (γ₁ x) y) hinit.symm hupdate_last.symm
  · -- Second branch: both use γ₂ with scaled i-coordinate
    have hlast : Fin.last n ≠ Fin.castSucc i := by
      intro heq
      have : (Fin.last n).val = (Fin.castSucc i).val := congrArg Fin.val heq
      simp only [Fin.val_last, Fin.val_castSucc] at this
      omega
    have hinit : Fin.init (Function.update t (Fin.castSucc i)
        (Set.projIcc 0 1 zero_le_one (2 * t (Fin.castSucc i) - 1))) =
        Function.update (Fin.init t) i (Set.projIcc 0 1 zero_le_one (2 * t (Fin.castSucc i) - 1)) := by
      ext j
      simp only [Fin.init, Function.update_apply]
      by_cases hj : j = i
      · subst hj; simp only [↓reduceIte]
      · simp only [hj, ↓reduceIte]
        have hne : Fin.castSucc j ≠ Fin.castSucc i := fun heq => hj (Fin.castSucc_injective _ heq)
        simp only [hne, ↓reduceIte]
    have hupdate_last : (Function.update t (Fin.castSucc i)
        (Set.projIcc 0 1 zero_le_one (2 * t (Fin.castSucc i) - 1))) (Fin.last n) = t (Fin.last n) := by
      simp only [Function.update_apply, hlast, ↓reduceIte]
    let t' := Function.update t (Fin.castSucc i) (Set.projIcc 0 1 zero_le_one (2 * t (Fin.castSucc i) - 1))
    change (γ₂ (Function.update (Fin.init t) i _)) (t (Fin.last n)) =
           (γ₂ (Fin.init t')) (t' (Fin.last n))
    exact congrArg₂ (fun x y => (γ₂ x) y) hinit.symm hupdate_last.symm

/-- The curry/uncurry equivalence at the GenLoop level.

    Mathematical content:
    - An element of GenLoop (Fin n) (Path x x) (Path.refl x) is a continuous map
      f : I^n → Path x x sending boundary to Path.refl x
    - This corresponds to a continuous map f̃ : I^n × I → X where f̃(t,s) = f(t)(s)
    - The boundary conditions match: f(∂I^n) = Path.refl x implies f̃(∂I^n × I) = x,
      and f̃(_, 0) = f̃(_, 1) = x (path endpoints)
    - Together, these mean f̃ sends the boundary of I^{n+1} to x

    This is a fundamental theorem relating loop spaces to higher cubes.
    The proof constructs the explicit curry/uncurry maps using Fin.init and Fin.snoc. -/
noncomputable def genLoopCurryEquiv :
    GenLoop (Fin n) (Path X.basepoint X.basepoint) (Path.refl X.basepoint) ≃
    GenLoop (Fin (n + 1)) X.carrier X.basepoint where
  toFun := uncurryGenLoopMap X n
  invFun := curryGenLoopMap X n
  left_inv := by
    -- curry ∘ uncurry = id
    intro γ
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    ext s
    -- Goal: (curryGenLoopMap (uncurryGenLoopMap γ) t) s = (γ t) s
    -- LHS = (uncurryGenLoopMap γ).val (Fin.snoc t s)
    --     = (γ.val (Fin.init (Fin.snoc t s))) ((Fin.snoc t s) (Fin.last n))
    --     = (γ.val t) s by Fin.init_snoc and Fin.snoc_last
    simp only [curryGenLoopMap_apply, uncurryGenLoopMap_apply, Fin.init_snoc, Fin.snoc_last]
  right_inv := by
    -- uncurry ∘ curry = id
    intro δ
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    simp only [uncurryGenLoopMap, curryGenLoopMap, ContinuousMap.coe_mk, mkPath']
    show δ (Fin.snoc (Fin.init t) (t (Fin.last n))) = δ t
    rw [Fin.snoc_init_self]

/-- The equivalence preserves homotopy (forward direction). -/
theorem genLoopCurryEquiv_homotopic
    {γ₁ γ₂ : GenLoop (Fin n) (Path X.basepoint X.basepoint) (Path.refl X.basepoint)}
    (h : GenLoop.Homotopic γ₁ γ₂) :
    GenLoop.Homotopic (genLoopCurryEquiv X n γ₁) (genLoopCurryEquiv X n γ₂) := by
  -- h gives us a homotopy H : I × (Fin n → I) → Path x x rel boundary
  -- We construct H' : I × (Fin (n+1) → I) → X by H'(t, s) = H(t, init s)(s(last n))
  unfold GenLoop.Homotopic at h ⊢
  unfold genLoopCurryEquiv
  simp only [Equiv.coe_fn_mk]
  obtain ⟨H⟩ := h
  -- Define the homotopy map
  let homotopyMap : I × (Fin (n + 1) → I) → X.carrier :=
    fun p => (H.1 (p.1, Fin.init p.2)) (p.2 (Fin.last n))
  have hcont : Continuous homotopyMap := by
    unfold homotopyMap
    have h1 : Continuous (fun p : I × (Fin (n + 1) → I) => (p.1, Fin.init p.2)) :=
      Continuous.prodMk continuous_fst
        (continuous_pi fun i => (continuous_apply i.castSucc).comp continuous_snd)
    have h2 : Continuous (fun p : I × (Fin (n + 1) → I) => H.1 (p.1, Fin.init p.2)) :=
      H.1.continuous.comp h1
    have h3 : Continuous (fun p : I × (Fin (n + 1) → I) => p.2 (Fin.last n)) :=
      (continuous_apply (Fin.last n)).comp continuous_snd
    -- Now combine: (path, t) ↦ path(t) is continuous
    exact h2.eval h3
  -- Show it's a HomotopyRel
  refine ⟨⟨⟨⟨homotopyMap, hcont⟩, ?_, ?_⟩, ?_⟩⟩
  · -- At time 0
    intro s
    show (H.1 (0, Fin.init s)) (s (Fin.last n)) = (uncurryGenLoopMap X n γ₁).val s
    simp only [H.1.apply_zero, uncurryGenLoopMap_apply]
  · -- At time 1
    intro s
    show (H.1 (1, Fin.init s)) (s (Fin.last n)) = (uncurryGenLoopMap X n γ₂).val s
    simp only [H.1.apply_one, uncurryGenLoopMap_apply]
  · -- Rel boundary: on boundary of I^{n+1}, value = uncurryGenLoopMap γ₁ s
    intro t s ⟨i, hi⟩
    show homotopyMap (t, s) = (uncurryGenLoopMap X n γ₁).val s
    simp only [homotopyMap, uncurryGenLoopMap_apply]
    by_cases hil : i = Fin.last n
    · -- i is the last index, so s(last n) = 0 or 1
      subst hil
      cases hi with
      | inl h0 =>
        simp only [h0]
        -- Both sides give (something) 0 = x because paths have source x
        trans X.basepoint
        · exact (H.1 (t, Fin.init s)).source
        · exact (γ₁.val (Fin.init s)).source.symm
      | inr h1 =>
        simp only [h1]
        trans X.basepoint
        · exact (H.1 (t, Fin.init s)).target
        · exact (γ₁.val (Fin.init s)).target.symm
    · -- i is not the last index, so init(s) is on boundary of I^n
      have hs' : Fin.init s ∈ Cube.boundary (Fin n) := by
        use ⟨i.val, Fin.val_lt_last hil⟩
        simp only [Fin.init]
        convert hi using 1
      -- H(t, init s) = γ₁(init s) by the rel property
      have hH := H.2 t (Fin.init s) hs'
      -- The hH says H.1(t, init s) = γ₁(init s) as Paths
      -- Apply both to s(last n)
      show (H.1 (t, Fin.init s)) (s (Fin.last n)) = (γ₁.val (Fin.init s)) (s (Fin.last n))
      exact congrFun (congrArg (↑·) hH) (s (Fin.last n))

/-- The equivalence preserves homotopy (backward direction). -/
theorem genLoopCurryEquiv_homotopic_inv
    {δ₁ δ₂ : GenLoop (Fin (n + 1)) X.carrier X.basepoint}
    (h : GenLoop.Homotopic δ₁ δ₂) :
    GenLoop.Homotopic ((genLoopCurryEquiv X n).symm δ₁) ((genLoopCurryEquiv X n).symm δ₂) := by
  -- Given homotopy H between δ₁ and δ₂, construct homotopy between their curried versions
  unfold GenLoop.Homotopic at h ⊢
  simp only [genLoopCurryEquiv, Equiv.coe_fn_symm_mk]
  obtain ⟨H⟩ := h
  -- H : (↑δ₁).HomotopyRel (↑δ₂) (Cube.boundary (Fin (n+1)))
  -- Define H'(t, s) = mkPath'(u ↦ H(t, snoc s u))
  refine ⟨⟨⟨⟨fun p => mkPath' X (fun u => H (p.1, @Fin.snoc n (fun _ => I) p.2 u))
    (by -- Path continuity
      have hsnoc : Continuous (fun u : I => @Fin.snoc n (fun _ => I) p.2 u) := by
        apply continuous_pi; intro i
        by_cases hi : i.val < n
        · simp only [Fin.snoc, dif_pos hi]; exact continuous_const
        · simp only [Fin.snoc, dif_neg hi]; exact continuous_id
      exact H.continuous.comp (Continuous.prodMk continuous_const hsnoc))
    (by -- source = x
      have hbdy : @Fin.snoc n (fun _ => I) p.2 0 ∈ Cube.boundary (Fin (n + 1)) :=
        ⟨Fin.last n, Or.inl (@Fin.snoc_last n (fun _ => I) 0 p.2)⟩
      show H (p.1, Fin.snoc p.2 0) = X.basepoint
      rw [H.eq_fst p.1 hbdy]
      exact δ₁.property _ hbdy)
    (by -- target = x
      have hbdy : @Fin.snoc n (fun _ => I) p.2 1 ∈ Cube.boundary (Fin (n + 1)) :=
        ⟨Fin.last n, Or.inr (@Fin.snoc_last n (fun _ => I) 1 p.2)⟩
      show H (p.1, Fin.snoc p.2 1) = X.basepoint
      rw [H.eq_fst p.1 hbdy]
      exact δ₁.property _ hbdy), ?_⟩, ?_, ?_⟩, ?_⟩⟩
  · -- Outer continuity
    apply Path.continuous_uncurry_iff.mp
    apply H.continuous.comp
    apply Continuous.prodMk (continuous_fst.comp continuous_fst)
    apply continuous_pi; intro i
    by_cases hi : i.val < n
    · simp only [Fin.snoc, dif_pos hi]
      exact (continuous_apply (⟨i.val, hi⟩ : Fin n)).comp (continuous_snd.comp continuous_fst)
    · simp only [Fin.snoc, dif_neg hi]
      exact continuous_snd
  · -- At time 0
    intro s; ext u
    simp only [mkPath'_apply, curryGenLoopMap_apply]
    exact H.apply_zero _
  · -- At time 1
    intro s; ext u
    simp only [mkPath'_apply, curryGenLoopMap_apply]
    exact H.apply_one _
  · -- Rel boundary
    intro t s ⟨⟨j, hj⟩, hjval⟩
    ext u
    simp only [curryGenLoopMap_apply]
    have hbdy : Fin.snoc s u ∈ Cube.boundary (Fin (n + 1)) := by
      use Fin.castSucc ⟨j, hj⟩
      simp only [Fin.snoc, Fin.val_castSucc, dif_pos hj]
      exact hjval
    exact H.eq_fst t hbdy

/-! ### Naturality of genLoopCurryEquiv

The curry equivalence is natural with respect to pointed maps. -/

/-- Naturality of genLoopCurryEquiv with respect to pointed maps.

    For f : X → Y, the curry equivalence commutes with the induced maps:
    currying a loop in ΩX and then applying f yields a homotopic result to
    applying Ωf and then currying.

    Mathematically: If γ : I^n → ΩX and f : X → Y, then
    curry(Ωf(γ)) ≈ f(curry(γ)) as maps I^{n+1} → Y.

    This follows because both operations just compose with f:
    - LHS: (Ωf(γ))(t)(s) = f(γ(t)(s)), then curry gives f(γ(init t)(t_last))
    - RHS: curry(γ) = γ(init t)(t_last), then f gives f(γ(init t)(t_last))
    So both are definitionally equal. -/
theorem genLoopCurryEquiv_natural {X Y : PointedTopSpace} (f : X ⟶ Y) (n : ℕ)
    (γ : GenLoop (Fin n) (loopSpace X).carrier (loopSpace X).basepoint) :
    (genLoopCurryEquiv Y n (inducedGenLoop (Fin n) (loopSpaceMap f) γ)) =
    (inducedGenLoop (Fin (n + 1)) f (genLoopCurryEquiv X n γ)) := by
  -- Both sides are definitionally equal - they both compute to f(γ(init t)(t_last))
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  -- LHS: (genLoopCurryEquiv Y n (inducedGenLoop (loopSpaceMap f) γ)).val t
  --    = uncurryGenLoopMap Y n (inducedGenLoop (loopSpaceMap f) γ) t
  --    = (inducedGenLoop (loopSpaceMap f) γ (Fin.init t)) (t (Fin.last n))
  --    = (loopSpaceMap f (γ (Fin.init t))) (t (Fin.last n))
  --    = f ((γ (Fin.init t)) (t (Fin.last n)))
  -- RHS: (inducedGenLoop f (genLoopCurryEquiv X n γ)).val t
  --    = f ((genLoopCurryEquiv X n γ).val t)
  --    = f (uncurryGenLoopMap X n γ t)
  --    = f ((γ (Fin.init t)) (t (Fin.last n)))
  simp only [genLoopCurryEquiv, Equiv.coe_fn_mk, uncurryGenLoopMap_apply,
             inducedGenLoop, toContinuousMap, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
             loopSpaceMap]
  rfl

/-- Corollary: genLoopCurryEquiv yields homotopic results with induced maps. -/
theorem genLoopCurryEquiv_natural_homotopic {X Y : PointedTopSpace} (f : X ⟶ Y) (n : ℕ)
    (γ : GenLoop (Fin n) (loopSpace X).carrier (loopSpace X).basepoint) :
    GenLoop.Homotopic
      (genLoopCurryEquiv Y n (inducedGenLoop (Fin n) (loopSpaceMap f) γ))
      (inducedGenLoop (Fin (n + 1)) f (genLoopCurryEquiv X n γ)) := by
  rw [genLoopCurryEquiv_natural]

end CurryUncurryInfra

/-! ## The Main Equivalence

The full equivalence π_n(ΩX) ≅ π_{n+1}(X) requires connecting our PointedTopSpace loop space
definition to Mathlib's GenLoop structure.

The key insight is that Mathlib provides:
- `GenLoop.loopHomeo i : GenLoop N X x ≃ₜ LoopSpace (GenLoop {j // j ≠ i} X x) GenLoop.const`
- `Fin.finSuccAboveEquiv p : Fin n ≃o {j : Fin (n+1) // j ≠ p}`
- `GenLoop.homotopicTo` and `homotopicFrom` for descending to quotients

The proof structure is:
1. Use `finSuccAboveEquiv` to relate `{j : Fin (n+1) // j ≠ Fin.last n}` to `Fin n`
2. Use `GenLoop.loopHomeo` to get the homeomorphism at the loop level
3. Use `Quotient.congr` with `homotopicTo/homotopicFrom` to descend to homotopy groups
-/

section MainEquivalence

/-- The bijection π_n(ΩX) ≅ π_{n+1}(X).

    Mathematical content:
    - LHS: π_n(ΩX) = GenLoop (Fin n) (Path x₀ x₀) constLoop / homotopy
    - RHS: π_{n+1}(X) = GenLoop (Fin (n+1)) X x₀ / homotopy

    The bijection comes from the curry/uncurry correspondence:
    - A map I^n → Path x₀ x₀ corresponds to a map I^{n+1} → X via currying
    - The boundary conditions match up correctly
    - The homeomorphism GenLoop.loopHomeo descends to quotients

    The construction uses:
    1. `Fin.finSuccAboveEquiv (Fin.last n)` to identify indices
    2. `GenLoop.loopHomeo (Fin.last n)` for the space-level homeomorphism
    3. `Quotient.congr` with `GenLoop.homotopicTo/homotopicFrom` for the quotient -/
noncomputable def loopSpaceHomotopyGroupEquiv (n : ℕ) :
    HomotopyGroup.Pi n (loopSpace X).carrier (loopSpace X).basepoint ≃
    HomotopyGroup.Pi (n + 1) X.carrier X.basepoint := by
  -- Use Quotient.congr with genLoopCurryEquiv
  -- LHS = HomotopyGroup (Fin n) (Path x x) (Path.refl x) = Quotient (GenLoop.Homotopic.setoid ...)
  -- RHS = HomotopyGroup (Fin (n+1)) X x = Quotient (GenLoop.Homotopic.setoid ...)
  -- The equivalence genLoopCurryEquiv : GenLoop (Fin n) (Path x x) ≃ GenLoop (Fin (n+1)) X x
  -- descends to quotients since it preserves homotopy.
  exact Quotient.congr (genLoopCurryEquiv X n) fun γ₁ γ₂ => ⟨
    genLoopCurryEquiv_homotopic X n,
    fun h => by
      have h' := genLoopCurryEquiv_homotopic_inv X n h
      have eq1 : (genLoopCurryEquiv X n).symm ((genLoopCurryEquiv X n) γ₁) = γ₁ :=
        (genLoopCurryEquiv X n).symm_apply_apply γ₁
      have eq2 : (genLoopCurryEquiv X n).symm ((genLoopCurryEquiv X n) γ₂) = γ₂ :=
        (genLoopCurryEquiv X n).symm_apply_apply γ₂
      convert h' using 2 <;> [exact eq1.symm; exact eq2.symm]⟩

/-- The equivalence respects the group structure for n ≥ 1. -/
theorem loopSpaceHomotopyGroupEquiv_mul (n : ℕ) (h1 h2 : HomotopyGroup.Pi (n + 1)
    (loopSpace X).carrier (loopSpace X).basepoint) :
    loopSpaceHomotopyGroupEquiv X (n + 1) (h1 * h2) =
    loopSpaceHomotopyGroupEquiv X (n + 1) h1 * loopSpaceHomotopyGroupEquiv X (n + 1) h2 := by
  -- Use quotient induction to get representatives first
  induction h1 using Quotient.ind
  induction h2 using Quotient.ind
  rename_i γ₁ γ₂
  -- Now h1 = ⟦γ₁⟧ and h2 = ⟦γ₂⟧
  -- Change the goal to use explicit function application for multiplication
  change loopSpaceHomotopyGroupEquiv X (n + 1) (((· * ·) : _ → _ → HomotopyGroup.Pi (n + 1)
      (loopSpace X).carrier (loopSpace X).basepoint) ⟦γ₁⟧ ⟦γ₂⟧) =
    (loopSpaceHomotopyGroupEquiv X (n + 1) ⟦γ₁⟧) * (loopSpaceHomotopyGroupEquiv X (n + 1) ⟦γ₂⟧)
  -- Rewrite source multiplication using mul_spec: ⟦p⟧ * ⟦q⟧ = ⟦transAt i q p⟧
  rw [HomotopyGroup.mul_spec (i := ⟨0, Nat.zero_lt_succ n⟩)]
  -- Now the goal is:
  -- loopSpaceHomotopyGroupEquiv ⟦transAt 0 γ₂ γ₁⟧ = loopSpaceHomotopyGroupEquiv ⟦γ₁⟧ * loopSpaceHomotopyGroupEquiv ⟦γ₂⟧
  -- loopSpaceHomotopyGroupEquiv is Quotient.congr with genLoopCurryEquiv
  -- (Quotient.congr e h) ⟦x⟧ = ⟦e x⟧ by Quotient.congr_mk
  unfold loopSpaceHomotopyGroupEquiv
  erw [Quotient.congr_mk, Quotient.congr_mk, Quotient.congr_mk]
  simp only [genLoopCurryEquiv, Equiv.coe_fn_mk]
  -- Apply the key lemma: uncurry (transAt i γ₂ γ₁) = transAt (castSucc i) (uncurry γ₂) (uncurry γ₁)
  rw [uncurryGenLoopMap_transAt]
  -- The LHS is now ⟦transAt (castSucc 0) (uncurry γ₂) (uncurry γ₁)⟧
  -- The RHS is ⟦uncurry γ₁⟧ * ⟦uncurry γ₂⟧
  -- Change the RHS to explicit function application
  change ⟦GenLoop.transAt (Fin.castSucc ⟨0, Nat.zero_lt_succ n⟩)
      (uncurryGenLoopMap X (n + 1) γ₂) (uncurryGenLoopMap X (n + 1) γ₁)⟧ =
    ((· * ·) : _ → _ → HomotopyGroup.Pi (n + 2) X.carrier X.basepoint)
      ⟦uncurryGenLoopMap X (n + 1) γ₁⟧ ⟦uncurryGenLoopMap X (n + 1) γ₂⟧
  -- Rewrite RHS using mul_spec
  rw [HomotopyGroup.mul_spec (i := ⟨0, Nat.zero_lt_succ (n + 1)⟩)]
  -- Now both sides are ⟦transAt 0 (uncurry γ₂) (uncurry γ₁)⟧
  -- castSucc 0 = 0 in Fin (n + 2)
  rfl

end MainEquivalence

/-! ## Application to Spectrum Homotopy Groups -/

section SpectrumApplication

variable {X' Y : PointedTopSpace.{0}}

/-- The composed transition map for spectrum homotopy groups.

    For spectrum homotopy groups, we need the transition map
    π_m(E_n) → π_m(ΩE_{n+1}) → π_{m+1}(E_{n+1})

    This is the composition of:
    1. The induced map from the structure map ε_n : E_n → ΩE_{n+1}
    2. The loop space isomorphism π_m(ΩE_{n+1}) ≅ π_{m+1}(E_{n+1})

    The combined map is what appears in the colimit defining π_k(E) for spectra. -/
noncomputable def spectrumTransitionMap (f : X' ⟶ loopSpace Y) (m : ℕ) :
    HomotopyGroup.Pi m X'.carrier X'.basepoint → HomotopyGroup.Pi (m + 1) Y.carrier Y.basepoint :=
  (loopSpaceHomotopyGroupEquiv Y m) ∘ (inducedπ m f)

/-- The transition map factors as stated. -/
theorem spectrumTransitionMap_eq (f : X' ⟶ loopSpace Y) (m : ℕ)
    (α : HomotopyGroup.Pi m X'.carrier X'.basepoint) :
    spectrumTransitionMap f m α = (loopSpaceHomotopyGroupEquiv Y m) (inducedπ m f α) := rfl

end SpectrumApplication

end PointedTopSpace
