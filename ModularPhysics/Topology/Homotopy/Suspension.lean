/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions
import ModularPhysics.Topology.Homotopy.Pointed

/-!
# Loop Space and Reduced Suspension

This file defines the loop space and reduced suspension functors on pointed topological spaces,
which are fundamental for stable homotopy theory.

## Main Definitions

* `PointedTopSpace.LoopSpace` - The loop space Ω(X, x₀) as a pointed space
* `PointedTopSpace.ReducedSuspension` - The reduced suspension ΣX as a pointed space
* Structure maps for the Σ ⊣ Ω adjunction

## Mathematical Background

For a pointed space (X, x₀):
- The loop space Ω(X, x₀) consists of continuous paths γ : I → X with γ(0) = γ(1) = x₀
- The reduced suspension ΣX = (X × I) / (X × {0} ∪ X × {1} ∪ {x₀} × I)

The fundamental property is the adjunction: [ΣX, Y]₊ ≃ [X, ΩY]₊

## References

* May, "A Concise Course in Algebraic Topology", Chapter 8
* Hatcher, "Algebraic Topology", Chapter 0
-/

universe u v

open CategoryTheory TopologicalSpace unitInterval

namespace PointedTopSpace

variable (X Y : PointedTopSpace.{u})

/-! ## Loop Space -/

section LoopSpace

/-- The underlying type of the loop space: loops based at the basepoint.
    This is the set of paths from x₀ to x₀. -/
def LoopSpaceType (X : PointedTopSpace) : Type u := Path X.basepoint X.basepoint

/-- The loop space inherits topology from Path, which has the compact-open topology
    as a subspace of C(I, X). -/
instance : TopologicalSpace (LoopSpaceType X) := inferInstanceAs (TopologicalSpace (Path _ _))

/-- The constant loop at the basepoint. -/
def constLoop (X : PointedTopSpace) : LoopSpaceType X := Path.refl X.basepoint

/-- The loop space of a pointed space, as a pointed space with the constant loop as basepoint. -/
def loopSpace (X : PointedTopSpace) : PointedTopSpace where
  carrier := LoopSpaceType X
  topology := inferInstance
  basepoint := constLoop X

/-- Notation for loop space. -/
scoped notation "Ω" => loopSpace

/-- A pointed map f : X → Y induces a map Ωf : ΩX → ΩY on loop spaces.
    This sends a loop γ based at x₀ to the loop f ∘ γ based at f(x₀) = y₀. -/
def loopSpaceMap {X Y : PointedTopSpace} (f : X ⟶ Y) : (Ω X) ⟶ (Ω Y) where
  toFun := fun γ => {
    toFun := f.toFun ∘ γ.toFun
    continuous_toFun := f.continuous.comp γ.continuous
    source' := by
      simp only [Function.comp_apply]
      have h1 : γ.toFun 0 = X.basepoint := γ.source
      rw [h1, f.map_basepoint]
    target' := by
      simp only [Function.comp_apply]
      have h1 : γ.toFun 1 = X.basepoint := γ.target
      rw [h1, f.map_basepoint]
  }
  continuous_toFun := by
    -- The map is continuous by functoriality of the compact-open topology:
    -- postcomposition with a continuous map is continuous.
    -- Path inherits its topology as a subspace of C(I, X).
    -- We use that Path topology is induced from C(I, X).
    rw [continuous_induced_rng]
    -- Need to show: (Path.toContinuousMap) ∘ (γ ↦ f ∘ γ) : Path x₀ x₀ → C(I, Y) is continuous
    -- This factors as: Path x₀ x₀ → C(I, X) → C(I, Y)
    -- where the first map is continuous (induced topology) and second is continuous_postcomp
    have h1 : Continuous (fun (γ : Path X.basepoint X.basepoint) => γ.toContinuousMap) :=
      continuous_induced_dom
    have h2 : Continuous (ContinuousMap.comp ⟨f.toFun, f.continuous⟩ : C(I, X.carrier) → C(I, Y.carrier)) :=
      ContinuousMap.continuous_postcomp ⟨f.toFun, f.continuous⟩
    exact h2.comp h1
  map_basepoint := by
    apply Path.ext
    funext t
    show f.toFun ((constLoop X).toFun t) = (constLoop Y).toFun t
    simp only [constLoop]
    -- Path.refl is the constant path, so (Path.refl x₀) t = x₀
    show f.toFun ((Path.refl X.basepoint) t) = (Path.refl Y.basepoint) t
    simp only [Path.refl]
    exact f.map_basepoint

/-- The loop space construction is functorial: identity maps to identity. -/
theorem loopSpaceMap_id : loopSpaceMap (𝟙 X) = 𝟙 (Ω X) := by
  apply Hom.ext
  funext γ
  apply Path.ext
  funext t
  rfl

/-- The loop space construction is functorial: composition is preserved. -/
theorem loopSpaceMap_comp {X Y Z : PointedTopSpace} (f : X ⟶ Y) (g : Y ⟶ Z) :
    loopSpaceMap (f ≫ g) = loopSpaceMap f ≫ loopSpaceMap g := by
  apply Hom.ext
  funext γ
  apply Path.ext
  funext t
  rfl

end LoopSpace

/-! ## Reduced Suspension -/

section ReducedSuspension

/-- The "collapsed set" in the reduced suspension: the union of
    X × {0}, X × {1}, and {x₀} × I. Points in this set will all be identified. -/
def inCollapsedSet (X : PointedTopSpace) (p : X.carrier × I) : Prop :=
  p.2 = 0 ∨ p.2 = 1 ∨ p.1 = X.basepoint

/-- The equivalence relation on X × I that defines the reduced suspension.
    Two points are equivalent iff they are equal or both lie in the collapsed set. -/
def suspensionRel (X : PointedTopSpace) : (X.carrier × I) → (X.carrier × I) → Prop :=
  fun p q => p = q ∨ (inCollapsedSet X p ∧ inCollapsedSet X q)

/-- The suspension relation is reflexive. -/
theorem suspensionRel_refl (X : PointedTopSpace) : Reflexive (suspensionRel X) :=
  fun _ => Or.inl rfl

/-- The suspension relation is symmetric. -/
theorem suspensionRel_symm (X : PointedTopSpace) : Symmetric (suspensionRel X) := by
  intro p q h
  cases h with
  | inl h => exact Or.inl h.symm
  | inr h => exact Or.inr ⟨h.2, h.1⟩

/-- The suspension relation is transitive. -/
theorem suspensionRel_trans (X : PointedTopSpace) : Transitive (suspensionRel X) := by
  intro p q r hpq hqr
  cases hpq with
  | inl hpq => rw [hpq]; exact hqr
  | inr hpq =>
    cases hqr with
    | inl hqr => rw [← hqr]; exact Or.inr hpq
    | inr hqr => exact Or.inr ⟨hpq.1, hqr.2⟩

/-- The setoid for the reduced suspension. -/
def suspensionSetoid (X : PointedTopSpace) : Setoid (X.carrier × I) where
  r := suspensionRel X
  iseqv := {
    refl := suspensionRel_refl X
    symm := fun h => suspensionRel_symm X h
    trans := fun h1 h2 => suspensionRel_trans X h1 h2
  }

/-- The underlying type of the reduced suspension as a quotient. -/
def ReducedSuspensionType (X : PointedTopSpace) : Type u :=
  Quotient (suspensionSetoid X)

/-- The quotient topology on the reduced suspension. -/
instance : TopologicalSpace (ReducedSuspensionType X) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

/-- The basepoint of the reduced suspension is the equivalence class of (x₀, 0). -/
def suspensionBasepoint (X : PointedTopSpace) : ReducedSuspensionType X :=
  Quotient.mk (suspensionSetoid X) (X.basepoint, ⟨0, unitInterval.zero_mem⟩)

/-- The reduced suspension of a pointed space. -/
def reducedSuspension (X : PointedTopSpace) : PointedTopSpace where
  carrier := ReducedSuspensionType X
  topology := inferInstance
  basepoint := suspensionBasepoint X

/-- Notation for reduced suspension. -/
scoped notation "Σ₊" => reducedSuspension

end ReducedSuspension

/-! ## Iterated Loop Spaces and Suspensions -/

section Iterated

/-- The n-fold loop space Ω^n X. -/
def iteratedLoopSpace (n : ℕ) (X : PointedTopSpace) : PointedTopSpace :=
  match n with
  | 0 => X
  | n + 1 => Ω (iteratedLoopSpace n X)

/-- Notation for iterated loop space. -/
scoped notation "Ω^" n => iteratedLoopSpace n

/-- The n-fold reduced suspension Σ^n X. -/
def iteratedSuspension (n : ℕ) (X : PointedTopSpace) : PointedTopSpace :=
  match n with
  | 0 => X
  | n + 1 => Σ₊ (iteratedSuspension n X)

/-- Notation for iterated suspension. -/
scoped notation "Σ₊^" n => iteratedSuspension n

end Iterated

/-! ## Σ ⊣ Ω Adjunction Unit -/

section AdjunctionUnit

/-- The inclusion map X × I → ΣX (before quotient). This is the quotient map. -/
def suspensionQuotientMap (X : PointedTopSpace) : X.carrier × I → ReducedSuspensionType X :=
  Quotient.mk (suspensionSetoid X)

/-- The quotient map is continuous. -/
theorem continuous_suspensionQuotientMap (X : PointedTopSpace) :
    Continuous (suspensionQuotientMap X) := continuous_quotient_mk'

/-- For a point x ∈ X, the path t ↦ [x, t] in ΣX. This is a loop since
    [x, 0] and [x, 1] are both identified with the basepoint. -/
def suspensionLoop (X : PointedTopSpace) (x : X.carrier) : Path (Σ₊ X).basepoint (Σ₊ X).basepoint where
  toFun := fun t => suspensionQuotientMap X (x, t)
  continuous_toFun := (continuous_suspensionQuotientMap X).comp
    (continuous_const.prodMk continuous_id)
  source' := by
    -- [x, 0] = basepoint since (x, 0) ∈ collapsed set
    simp only [suspensionQuotientMap]
    apply Quotient.sound
    right
    constructor
    · -- (x, 0) is in collapsed set
      left
      rfl
    · -- (basepoint, 0) is in collapsed set
      left
      rfl
  target' := by
    -- [x, 1] = basepoint since (x, 1) ∈ collapsed set
    simp only [suspensionQuotientMap]
    apply Quotient.sound
    right
    constructor
    · -- (x, 1) is in collapsed set
      right; left
      rfl
    · -- (basepoint, 0) is in collapsed set
      left
      rfl

/-- The unit of the Σ ⊣ Ω adjunction: η : X → Ω(ΣX).
    This sends a point x to the loop t ↦ [x, t] in ΣX. -/
def suspensionUnit (X : PointedTopSpace) : X ⟶ Ω (Σ₊ X) where
  toFun := fun x => suspensionLoop X x
  continuous_toFun := by
    -- Need to show x ↦ suspensionLoop X x is continuous
    -- This is a map X → Path pt pt, which has induced topology from C(I, ΣX)
    rw [continuous_induced_rng]
    -- Need: x ↦ (suspensionLoop X x).toContinuousMap is continuous
    -- Use uncurrying: this holds iff (x, t) ↦ [x, t] is continuous
    apply ContinuousMap.continuous_of_continuous_uncurry
    -- Show the uncurried version is continuous
    show Continuous (fun p : X.carrier × I => suspensionQuotientMap X (p.1, p.2))
    exact (continuous_suspensionQuotientMap X).comp (continuous_fst.prodMk continuous_snd)
  map_basepoint := by
    -- η(x₀) should be the constant loop
    apply Path.ext
    funext t
    simp only [suspensionLoop]
    -- [x₀, t] = basepoint since (x₀, t) ∈ collapsed set (x₀ is basepoint)
    apply Quotient.sound
    right
    constructor
    · -- (basepoint, t) is in collapsed set
      right; right
      rfl
    · -- (basepoint, 0) is in collapsed set
      left
      rfl

end AdjunctionUnit

/-! ## Functoriality of Suspension -/

section SuspensionMap

/-- Suspension of a pointed map. Sends [x, t] to [f(x), t]. -/
def suspensionMap {X Y : PointedTopSpace} (f : X ⟶ Y) : Σ₊ X ⟶ Σ₊ Y where
  toFun := Quotient.lift (fun p => Quotient.mk (suspensionSetoid Y) (f.toFun p.1, p.2))
    (by
      intro p q h
      apply Quotient.sound
      cases h with
      | inl h => exact Or.inl (by rw [h])
      | inr h =>
        right
        constructor
        · obtain ⟨hp, _⟩ := h
          cases hp with
          | inl hp => left; exact hp
          | inr hp =>
            cases hp with
            | inl hp => right; left; exact hp
            | inr hp => right; right; rw [hp]; exact f.map_basepoint
        · obtain ⟨_, hq⟩ := h
          cases hq with
          | inl hq => left; exact hq
          | inr hq =>
            cases hq with
            | inl hq => right; left; exact hq
            | inr hq => right; right; rw [hq]; exact f.map_basepoint
    )
  continuous_toFun := by
    apply Continuous.quotient_lift
    refine Continuous.comp ?_ (f.continuous.prodMap continuous_id)
    exact continuous_quotient_mk'
  map_basepoint := by
    show Quotient.lift _ _ (suspensionBasepoint X) = suspensionBasepoint Y
    simp only [suspensionBasepoint]
    apply Quotient.sound
    right
    constructor
    · right; right; exact f.map_basepoint
    · left; rfl

/-- Helper: suspensionMap applied at the quotient level.
    For a map f : X → Y, suspensionMap f sends [x, t] to [f(x), t]. -/
theorem suspensionMap_mk {X Y : PointedTopSpace} (f : X ⟶ Y) (x : X.carrier) (t : I) :
    (suspensionMap f).toFun (Quotient.mk (suspensionSetoid X) (x, t)) =
    Quotient.mk (suspensionSetoid Y) (f.toFun x, t) := rfl

/-- Suspension is functorial: Σ(id) = id -/
theorem suspensionMap_id (X : PointedTopSpace) :
    suspensionMap (𝟙 X) = 𝟙 (Σ₊ X) := by
  apply Hom.ext
  funext p
  induction p using Quotient.ind with
  | _ p =>
    rfl

/-- Suspension is functorial: Σ(g ∘ f) = Σg ∘ Σf -/
theorem suspensionMap_comp {X Y Z : PointedTopSpace} (f : X ⟶ Y) (g : Y ⟶ Z) :
    suspensionMap (f ≫ g) = suspensionMap f ≫ suspensionMap g := by
  apply Hom.ext
  funext p
  induction p using Quotient.ind with
  | _ p =>
    rfl

/-- The suspension unit is natural: for f : X → Y,
    the following diagram commutes:
    ```
    X ---η_X--> Ω(ΣX)
    |            |
    f          Ω(Σf)
    ↓            ↓
    Y ---η_Y--> Ω(ΣY)
    ```
    i.e., f ≫ η_Y = η_X ≫ Ω(Σf) -/
theorem suspensionUnit_natural {X Y : PointedTopSpace} (f : X ⟶ Y) :
    f ≫ suspensionUnit Y = suspensionUnit X ≫ loopSpaceMap (suspensionMap f) := by
  apply Hom.ext
  funext x
  apply Path.ext
  funext t
  -- LHS: (f ≫ suspensionUnit Y).toFun x t = (suspensionUnit Y).toFun (f.toFun x) t
  --    = suspensionLoop Y (f.toFun x) t = [f(x), t] in ΣY
  -- RHS: (loopSpaceMap (suspensionMap f)).toFun ((suspensionUnit X).toFun x) t
  --    = (suspensionMap f).toFun (suspensionLoop X x t)
  --    = (suspensionMap f).toFun [x, t] = [f(x), t] in ΣY
  simp only [comp_toFun, Function.comp_apply, suspensionUnit, suspensionLoop,
             loopSpaceMap, suspensionQuotientMap]
  rfl

end SuspensionMap

end PointedTopSpace
