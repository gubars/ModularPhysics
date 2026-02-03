/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.Topology.Spectra.Basic
import ModularPhysics.Topology.Homotopy.WeakEquivalence
import ModularPhysics.Topology.Homotopy.LoopSpaceIso
import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Homotopy Groups of Spectra

This file defines the homotopy groups of spectra, building on Mathlib's existing
homotopy group infrastructure (`π_n X x`).

## What Mathlib Provides
- `HomotopyGroup.Pi n X x` (denoted `π_n X x`) - the n-th homotopy group of X at basepoint x
- `GenLoop` - generalized loops I^n → X sending boundary to basepoint
- The fundamental group as a special case

## What We Define Here
- Transition maps in the colimit system for spectrum homotopy groups
- The stable homotopy group π_k(E) for k ∈ ℤ (including negative k)

## Mathematical Background

For a spectrum E with spaces E_n and structure maps ε_n : E_n → ΩE_{n+1}, we define:

  π_k(E) = colim_{n→∞} π_{n+k}(E_n)

The transition maps come from ε_n : π_m(E_n) → π_m(ΩE_{n+1}) ≅ π_{m+1}(E_{n+1}).

## References

* Adams, "Stable Homotopy and Generalised Homology", Part III
* May, "A Concise Course in Algebraic Topology", Chapter 22
-/

universe u

open CategoryTheory PointedTopSpace

namespace Topology

namespace Spectrum

variable (E : Spectrum)

/-! ## Accessing Mathlib's Homotopy Groups

We use Mathlib's `π_n X x` for the n-th homotopy group of a space X at basepoint x.
For pointed spaces, the basepoint is fixed, so we define convenient accessors. -/

section MathlibHomotopyGroups

/-- The n-th homotopy group of the k-th space of a spectrum, using Mathlib's definition. -/
abbrev levelHomotopyGroup (n k : ℕ) : Type :=
  HomotopyGroup.Pi n (E.spaceAt k).carrier (E.spaceAt k).basepoint

/-- The n-th homotopy group of the loop space of the k-th space. -/
abbrev loopLevelHomotopyGroup (n k : ℕ) : Type :=
  HomotopyGroup.Pi n (loopSpace (E.spaceAt k)).carrier (loopSpace (E.spaceAt k)).basepoint

/-- The induced map on homotopy groups from the structure map ε_k : E_k → ΩE_{k+1}.
    This maps π_n(E_k) → π_n(ΩE_{k+1}). -/
def structureMapInduced (k n : ℕ) :
    E.levelHomotopyGroup n k → E.loopLevelHomotopyGroup n (k + 1) :=
  inducedπ n (E.ε k)

/-- The full transition map in the colimit system for π_k(E):
    π_n(E_k) → π_n(ΩE_{k+1}) → π_{n+1}(E_{k+1})

    This is the composition of:
    1. The induced map from the structure map ε_k : E_k → ΩE_{k+1}
    2. The loop-space isomorphism π_n(ΩE_{k+1}) ≅ π_{n+1}(E_{k+1})

    This is the key map that appears in the colimit defining stable homotopy groups. -/
noncomputable def transitionMap (k n : ℕ) :
    E.levelHomotopyGroup n k → E.levelHomotopyGroup (n + 1) (k + 1) :=
  spectrumTransitionMap (E.ε k) n

/-- The transition map factors through the structure map induced map. -/
theorem transitionMap_eq (k n : ℕ) (x : E.levelHomotopyGroup n k) :
    E.transitionMap k n x =
    (loopSpaceHomotopyGroupEquiv (E.spaceAt (k + 1)) n) (E.structureMapInduced k n x) := by
  rfl

/-! ### Group Homomorphism Properties of Transition Maps -/

/-- The structure map induced map preserves multiplication.
    This follows from the general fact that induced maps on homotopy groups
    preserve the group structure. -/
theorem structureMapInduced_mul (k n : ℕ)
    (a b : E.levelHomotopyGroup (n + 1) k) :
    E.structureMapInduced k (n + 1) (a * b) =
    E.structureMapInduced k (n + 1) a * E.structureMapInduced k (n + 1) b := by
  unfold structureMapInduced
  exact inducedπ_mul n (E.ε k) a b

/-- The full transition map preserves multiplication.
    This combines the structure map induced map (which preserves multiplication)
    with the loop space isomorphism (which also preserves multiplication). -/
theorem transitionMap_mul (k n : ℕ)
    (a b : E.levelHomotopyGroup (n + 1) k) :
    E.transitionMap k (n + 1) (a * b) =
    E.transitionMap k (n + 1) a * E.transitionMap k (n + 1) b := by
  unfold transitionMap spectrumTransitionMap
  simp only [Function.comp_apply]
  rw [inducedπ_mul]
  -- loopSpaceHomotopyGroupEquiv_mul n works with π_{n+1}(ΩX)
  exact loopSpaceHomotopyGroupEquiv_mul (E.spaceAt (k + 1)) n
    (inducedπ (n + 1) (E.ε k) a) (inducedπ (n + 1) (E.ε k) b)

end MathlibHomotopyGroups

/-! ## Stable Homotopy Groups

The k-th stable homotopy group π_k(E) for k ∈ ℤ is defined as:
  π_k(E) = colim_{n≥max(0,-k)} π_{n+k}(E_n)

For Ω-spectra, this colimit stabilizes. -/

section StableHomotopyGroups

/-- The starting index for the colimit: max(0, -k). -/
def startIndex (k : ℤ) : ℕ := Int.toNat (-k)

/-- For n ≥ startIndex k, we have n + k ≥ 0. -/
theorem startIndex_spec (k : ℤ) (n : ℕ) (h : startIndex k ≤ n) : 0 ≤ (n : ℤ) + k := by
  unfold startIndex at h
  omega

/-- Convert n + k to a natural number when n ≥ startIndex k. -/
def levelIndex (k : ℤ) (n : ℕ) (_h : startIndex k ≤ n) : ℕ :=
  Int.toNat ((n : ℤ) + k)

/-- The level index is exactly n + k when n + k ≥ 0. -/
theorem levelIndex_eq (k : ℤ) (n : ℕ) (h : startIndex k ≤ n) :
    (levelIndex k n h : ℤ) = n + k := by
  unfold levelIndex
  exact Int.toNat_of_nonneg (startIndex_spec k n h)

/-- The n-th term in the colimit system for π_k(E). -/
def colimitTerm (k : ℤ) (n : ℕ) (h : startIndex k ≤ n) : Type :=
  E.levelHomotopyGroup (levelIndex k n h) n

/-- A representation of an element in the stable homotopy group.
    An element is represented by a pair (n, x) where:
    - n ≥ startIndex k
    - x ∈ π_{n+k}(E_n)

    Two representations are equivalent if they become equal after
    applying sufficiently many transition maps. -/
structure StableHomotopyGroupRep (k : ℤ) where
  /-- The level at which this element lives -/
  level : ℕ
  /-- Proof that the level is valid -/
  level_valid : startIndex k ≤ level
  /-- The element in the homotopy group at this level -/
  element : E.colimitTerm k level level_valid

/-- The stable homotopy group π_k(E) as the type of representations.

    Note: The full definition would quotient by the equivalence relation
    that identifies elements that become equal in the colimit. For now,
    we use the representation type directly. -/
def stableπ (k : ℤ) : Type := StableHomotopyGroupRep E k

/-- An element of π_k(E) at a specific level. -/
def stableπ.ofLevel (k : ℤ) (n : ℕ) (h : startIndex k ≤ n)
    (x : E.colimitTerm k n h) : stableπ E k :=
  ⟨n, h, x⟩

/-! ### Transition in the Colimit System

For the colimit, we need to apply the transition map from level n to level n+1.
The transition map goes: π_{n+k}(E_n) → π_{n+k+1}(E_{n+1}).

Note: The levelIndex at level n is (n+k), and at level n+1 is (n+1+k) = (n+k)+1.
-/

/-- Proof that if n ≥ startIndex k, then n + 1 ≥ startIndex k. -/
theorem startIndex_succ (k : ℤ) (n : ℕ) (h : startIndex k ≤ n) : startIndex k ≤ n + 1 :=
  Nat.le_succ_of_le h

/-- The level index increases by 1 when going from level n to level n+1. -/
theorem levelIndex_succ (k : ℤ) (n : ℕ) (h : startIndex k ≤ n) :
    levelIndex k (n + 1) (startIndex_succ k n h) = levelIndex k n h + 1 := by
  unfold levelIndex
  have h1 : 0 ≤ (n : ℤ) + k := startIndex_spec k n h
  have eq1 : ((n + 1 : ℕ) : ℤ) + k = (n : ℤ) + k + (1 : ℕ) := by simp; ring
  rw [eq1, Int.toNat_add_nat h1]

/-- The transition map from level n to level n+1 in the colimit system for π_k(E).
    This goes: E.colimitTerm k n → E.colimitTerm k (n+1)

    Uses the transitionMap which combines the structure map induced map with
    the loop-space isomorphism.

    The cast from levelIndex_succ is made explicit for easier reasoning. -/
noncomputable def colimitTransition (k : ℤ) (n : ℕ) (h : startIndex k ≤ n) :
    E.colimitTerm k n h → E.colimitTerm k (n + 1) (startIndex_succ k n h) :=
  -- By levelIndex_succ: levelIndex k (n+1) h' = levelIndex k n h + 1
  -- transitionMap produces E.levelHomotopyGroup (levelIndex k n h + 1) (n+1)
  -- colimitTerm k (n+1) h' = E.levelHomotopyGroup (levelIndex k (n+1) h') (n+1)
  -- Eq.mpr converts from RHS to LHS of the equality
  -- congrArg gives: levelHomotopyGroup (levelIndex k (n+1) _) _ = levelHomotopyGroup (levelIndex k n h + 1) _
  fun x => Eq.mpr (congrArg (E.levelHomotopyGroup · (n + 1)) (levelIndex_succ k n h))
             (E.transitionMap n (levelIndex k n h) x)

/-! ### The Equivalence Relation

Two representations (n, x) and (m, y) are equivalent if there exists N ≥ max(n, m)
such that the images of x and y in π_{N+k}(E_N) are equal.

Note: The equivalence relation is stated in terms of an existential witness of a
common level. The type-theoretic technicality of different target types is handled
by casting through the equality of levels.
-/

/-- Apply the transition map to go from level n to level N.
    Defined by induction on (N - n). This version uses the target level directly
    to avoid type mismatches. -/
noncomputable def imageAtLevel (k : ℤ) (n : ℕ) (hn : startIndex k ≤ n)
    (N : ℕ) (hN : n ≤ N) (x : E.colimitTerm k n hn) : E.colimitTerm k N (Nat.le_trans hn hN) :=
  if h : n = N then
    -- Base case: already at level N
    h ▸ x
  else
    -- Recursive case: apply one transition, then continue
    have hn' : n + 1 ≤ N := Nat.lt_of_le_of_ne hN h
    have hstep : startIndex k ≤ n + 1 := Nat.le_trans hn (Nat.le_succ n)
    let y := E.colimitTransition k n hn x
    imageAtLevel k (n + 1) hstep N hn' y
termination_by N - n

/-- The colimitTerm type doesn't depend on the proof h.
    This is because levelIndex only uses the value of n and k, not the proof. -/
theorem colimitTerm_proof_irrel (k : ℤ) (n : ℕ) (h₁ h₂ : startIndex k ≤ n) :
    E.colimitTerm k n h₁ = E.colimitTerm k n h₂ := rfl

/-- The colimitTerm type only depends on the level, so equal levels give equal types. -/
theorem colimitTerm_level_eq (k : ℤ) (n₁ n₂ : ℕ) (h₁ : startIndex k ≤ n₁) (h₂ : startIndex k ≤ n₂)
    (heq : n₁ = n₂) : E.colimitTerm k n₁ h₁ = E.colimitTerm k n₂ h₂ := by
  subst heq
  rfl

/-- Applying additional transitions from level M to level N. -/
noncomputable def extendToLevel (k : ℤ) (M : ℕ) (hM : startIndex k ≤ M) (N : ℕ) (hN : M ≤ N)
    (y : E.colimitTerm k M hM) : E.colimitTerm k N (Nat.le_trans hM hN) :=
  E.imageAtLevel k M hM N hN y

/-- Key lemma: extendToLevel is a function, so it preserves equality. -/
theorem extendToLevel_congr (k : ℤ) (M : ℕ) (hM : startIndex k ≤ M) (N : ℕ) (hN : M ≤ N)
    (y₁ y₂ : E.colimitTerm k M hM) (heq : y₁ = y₂) :
    E.extendToLevel k M hM N hN y₁ = E.extendToLevel k M hM N hN y₂ :=
  congrArg _ heq

/-- imageAtLevel n n x = x (identity at same level). -/
theorem imageAtLevel_self (k : ℤ) (n : ℕ) (hn : startIndex k ≤ n) (hnn : n ≤ n)
    (x : E.colimitTerm k n hn) :
    E.imageAtLevel k n hn n hnn x = x := by
  unfold imageAtLevel
  simp only [↓reduceDIte]

/-- Key lemma for transitivity: imageAtLevel composes through intermediate levels.
    Going from n to N via M gives the same result as going directly.

    Proof: By strong induction on (M - n). The recursive definition of imageAtLevel
    directly gives us the composition property. -/
theorem imageAtLevel_compose (k : ℤ) (n : ℕ) (hn : startIndex k ≤ n)
    (M : ℕ) (hM : n ≤ M) (N : ℕ) (hN : M ≤ N)
    (x : E.colimitTerm k n hn) :
    E.imageAtLevel k n hn N (Nat.le_trans hM hN) x =
    E.extendToLevel k M (Nat.le_trans hn hM) N hN (E.imageAtLevel k n hn M hM x) := by
  unfold extendToLevel
  -- We prove by strong induction on (M - n), the number of steps to reach M.
  induction hd : M - n using Nat.strong_induction_on generalizing n M with
  | _ d ih =>
    -- Case split on whether n = M
    by_cases hnM : n = M
    · -- n = M case: imageAtLevel n n x = x, so both sides equal imageAtLevel n N x
      subst hnM
      simp only [Nat.sub_self] at hd
      rw [imageAtLevel_self]
    · -- n < M case: unfold one step on both sides and use IH
      have hn_lt_M : n < M := Nat.lt_of_le_of_ne hM hnM
      have hn1_le_M : n + 1 ≤ M := hn_lt_M
      have hstep : startIndex k ≤ n + 1 := Nat.le_trans hn (Nat.le_succ n)
      have hn_ne_N : n ≠ N := fun h => by omega
      -- Unfold LHS: imageAtLevel n N x = imageAtLevel (n+1) N (colimitTransition n x)
      have hL : E.imageAtLevel k n hn N (Nat.le_trans hM hN) x =
                E.imageAtLevel k (n + 1) hstep N (Nat.le_trans hn1_le_M hN) (E.colimitTransition k n hn x) := by
        rw [imageAtLevel]
        simp only [hn_ne_N, ↓reduceDIte]
      -- Unfold RHS inner: imageAtLevel n M x = imageAtLevel (n+1) M (colimitTransition n x)
      have hR : E.imageAtLevel k n hn M hM x =
                E.imageAtLevel k (n + 1) hstep M hn1_le_M (E.colimitTransition k n hn x) := by
        rw [imageAtLevel]
        simp only [hnM, ↓reduceDIte]
      rw [hL, hR]
      -- Goal: imageAtLevel (n+1) N (colimitTransition n x) = imageAtLevel M N (imageAtLevel (n+1) M (colimitTransition n x))
      -- This is exactly the IH with M - (n+1) < M - n = d
      have hd' : M - (n + 1) < d := by omega
      exact ih (M - (n + 1)) hd' (n + 1) hstep M hn1_le_M hN (E.colimitTransition k n hn x) rfl

/-- The equivalence relation on StableHomotopyGroupRep.
    Two representations are equivalent if their images agree at some common level. -/
def StableHomotopyGroupRep.Equiv (k : ℤ) (r₁ r₂ : StableHomotopyGroupRep E k) : Prop :=
  ∃ (N : ℕ) (hN₁ : r₁.level ≤ N) (hN₂ : r₂.level ≤ N),
    E.imageAtLevel k r₁.level r₁.level_valid N hN₁ r₁.element =
    E.imageAtLevel k r₂.level r₂.level_valid N hN₂ r₂.element

/-- The equivalence relation is reflexive. -/
theorem StableHomotopyGroupRep.Equiv.refl (k : ℤ) (r : StableHomotopyGroupRep E k) :
    StableHomotopyGroupRep.Equiv E k r r :=
  ⟨r.level, le_refl _, le_refl _, rfl⟩

/-- The equivalence relation is symmetric. -/
theorem StableHomotopyGroupRep.Equiv.symm (k : ℤ) {r₁ r₂ : StableHomotopyGroupRep E k}
    (h : StableHomotopyGroupRep.Equiv E k r₁ r₂) :
    StableHomotopyGroupRep.Equiv E k r₂ r₁ := by
  obtain ⟨N, hN₁, hN₂, heq⟩ := h
  exact ⟨N, hN₂, hN₁, heq.symm⟩

/-- The equivalence relation is transitive.

    Mathematical proof: If r₁ ≡ r₂ at level N₁₂ and r₂ ≡ r₃ at level N₂₃, then at
    level N = max(N₁₂, N₂₃), we have image_N(r₁) = image_N(r₂) = image_N(r₃).
    This follows because applying additional transition maps preserves equality. -/
theorem StableHomotopyGroupRep.Equiv.trans (k : ℤ) {r₁ r₂ r₃ : StableHomotopyGroupRep E k}
    (h₁₂ : StableHomotopyGroupRep.Equiv E k r₁ r₂)
    (h₂₃ : StableHomotopyGroupRep.Equiv E k r₂ r₃) :
    StableHomotopyGroupRep.Equiv E k r₁ r₃ := by
  obtain ⟨N₁₂, hN₁, hN₂, heq₁₂⟩ := h₁₂
  obtain ⟨N₂₃, hN₂', hN₃, heq₂₃⟩ := h₂₃
  let N := max N₁₂ N₂₃
  use N, Nat.le_trans hN₁ (Nat.le_max_left _ _), Nat.le_trans hN₃ (Nat.le_max_right _ _)
  -- Step 1: Extend equality from N₁₂ to N
  -- image_N(r₁) = extendToLevel N₁₂ N (image_{N₁₂}(r₁))  [by imageAtLevel_compose]
  --             = extendToLevel N₁₂ N (image_{N₁₂}(r₂))  [by heq₁₂]
  --             = image_N(r₂)                             [by imageAtLevel_compose]
  have hN₁₂_le_N : N₁₂ ≤ N := Nat.le_max_left _ _
  have hN₂₃_le_N : N₂₃ ≤ N := Nat.le_max_right _ _
  -- Extend r₁ and r₂ from N₁₂ to N
  have heq₁₂_at_N : E.imageAtLevel k r₁.level r₁.level_valid N (Nat.le_trans hN₁ hN₁₂_le_N) r₁.element =
                    E.imageAtLevel k r₂.level r₂.level_valid N (Nat.le_trans hN₂ hN₁₂_le_N) r₂.element := by
    rw [imageAtLevel_compose E k r₁.level r₁.level_valid N₁₂ hN₁ N hN₁₂_le_N r₁.element]
    rw [imageAtLevel_compose E k r₂.level r₂.level_valid N₁₂ hN₂ N hN₁₂_le_N r₂.element]
    exact extendToLevel_congr E k N₁₂ _ N hN₁₂_le_N _ _ heq₁₂
  -- Step 2: Extend equality from N₂₃ to N
  have heq₂₃_at_N : E.imageAtLevel k r₂.level r₂.level_valid N (Nat.le_trans hN₂' hN₂₃_le_N) r₂.element =
                    E.imageAtLevel k r₃.level r₃.level_valid N (Nat.le_trans hN₃ hN₂₃_le_N) r₃.element := by
    rw [imageAtLevel_compose E k r₂.level r₂.level_valid N₂₃ hN₂' N hN₂₃_le_N r₂.element]
    rw [imageAtLevel_compose E k r₃.level r₃.level_valid N₂₃ hN₃ N hN₂₃_le_N r₃.element]
    exact extendToLevel_congr E k N₂₃ _ N hN₂₃_le_N _ _ heq₂₃
  -- Step 3: Combine - need to show the two r₂ images are the same
  -- heq₁₂_at_N gives image_N(r₁) = image_N(r₂) via path through N₁₂
  -- heq₂₃_at_N gives image_N(r₂) = image_N(r₃) via path through N₂₃
  -- The two image_N(r₂) terms have the same type (colimitTerm k N _) but potentially different proofs
  -- By colimitTerm_proof_irrel, they are definitionally equal
  calc E.imageAtLevel k r₁.level r₁.level_valid N _ r₁.element
      = E.imageAtLevel k r₂.level r₂.level_valid N _ r₂.element := heq₁₂_at_N
    _ = E.imageAtLevel k r₃.level r₃.level_valid N _ r₃.element := heq₂₃_at_N

/-- The setoid for stable homotopy group equivalence. -/
def stableHomotopySetoid (k : ℤ) : Setoid (StableHomotopyGroupRep E k) where
  r := StableHomotopyGroupRep.Equiv E k
  iseqv := {
    refl := StableHomotopyGroupRep.Equiv.refl E k
    symm := fun h => StableHomotopyGroupRep.Equiv.symm E k h
    trans := fun h₁ h₂ => StableHomotopyGroupRep.Equiv.trans E k h₁ h₂
  }

/-- The proper stable homotopy group π_k(E) as a quotient.
    This is the colimit of the system π_{n+k}(E_n) with transition maps. -/
def StableHomotopyGroup (k : ℤ) : Type :=
  Quotient (E.stableHomotopySetoid k)

/-- Notation for stable homotopy groups of spectra. -/
scoped notation "π_" k "(" E ")" => StableHomotopyGroup E k

/-- Construct an element of the stable homotopy group from a level representative. -/
def StableHomotopyGroup.mk (k : ℤ) (n : ℕ) (h : startIndex k ≤ n)
    (x : E.colimitTerm k n h) : StableHomotopyGroup E k :=
  @Quotient.mk' _ (E.stableHomotopySetoid k) ⟨n, h, x⟩

end StableHomotopyGroups

/-! ## Properties -/

section Properties

/-- For an Ω-spectrum, the structure map induces bijections on homotopy groups.
    This is because ε_k is a weak homotopy equivalence. -/
theorem omegaSpectrum_bijective (hE : IsOmegaSpectrum E) (k n : ℕ) :
    Function.Bijective (E.structureMapInduced k n) := by
  unfold structureMapInduced
  -- ε_k is a weak homotopy equivalence by definition of Ω-spectrum
  -- So it induces bijections on all homotopy groups
  exact hE k n

end Properties

/-! ## Induced Maps on Stable Homotopy Groups

For a spectrum map f : E → F, we define the induced map f_* : π_k(E) → π_k(F).
This requires showing that the level-wise induced maps commute with the transition
maps in the colimit system. -/

section InducedMaps

variable {E F G : Spectrum}

/-- The induced map on level homotopy groups from a spectrum map.
    Given f : E → F, this is (f_n)_* : π_m(E_n) → π_m(F_n). -/
def levelInducedMap (f : E ⟶ F) (m n : ℕ) :
    E.levelHomotopyGroup m n → F.levelHomotopyGroup m n :=
  inducedπ m (f.levelMap n)

/-- The induced map on loop-level homotopy groups.
    Given f : E → F, this is Ω(f_{n+1})_* : π_m(ΩE_{n+1}) → π_m(ΩF_{n+1}). -/
def loopLevelInducedMap (f : E ⟶ F) (m n : ℕ) :
    E.loopLevelHomotopyGroup m (n + 1) → F.loopLevelHomotopyGroup m (n + 1) :=
  inducedπ m (loopSpaceMap (f.levelMap (n + 1)))

/-- Composition of inducedGenLoop with two maps equals inducedGenLoop of their composition
    (pointwise equality, not just homotopic). -/
theorem inducedGenLoop_comp {X Y Z : PointedTopSpace} (N : Type*) (f : X ⟶ Y) (g : Y ⟶ Z)
    (γ : GenLoop N X.carrier X.basepoint) :
    inducedGenLoop N g (inducedGenLoop N f γ) = inducedGenLoop N (f ≫ g) γ := by
  apply Subtype.ext
  ext t
  rfl

/-- Key lemma: composing with f_n ≫ F.ε n gives the same GenLoop as E.ε n ≫ Ω(f_{n+1}).
    This follows from the spectrum map compatibility condition. -/
theorem inducedGenLoop_spectrum_comm (f : E ⟶ F) (n m : ℕ)
    (γ : GenLoop (Fin m) (E.spaceAt n).carrier (E.spaceAt n).basepoint) :
    inducedGenLoop (Fin m) (E.ε n ≫ loopSpaceMap (f.levelMap (n + 1))) γ =
    inducedGenLoop (Fin m) (f.levelMap n ≫ F.ε n) γ := by
  have hcomm : E.ε n ≫ loopSpaceMap (f.levelMap (n + 1)) = f.levelMap n ≫ F.ε n := f.comm n
  rw [hcomm]

/-- The structure map induced map factors through the loop space map.
    This is the key compatibility lemma. -/
theorem structureMapInduced_natural (f : E ⟶ F) (n m : ℕ) (x : E.levelHomotopyGroup m n) :
    loopLevelInducedMap f m n (E.structureMapInduced n m x) =
    F.structureMapInduced n m (levelInducedMap f m n x) := by
  unfold structureMapInduced loopLevelInducedMap levelInducedMap inducedπ
  induction x using Quotient.ind with
  | _ γ =>
    simp only [Quotient.map'_mk'']
    apply Quotient.sound
    -- LHS: inducedGenLoop (Ω(f_{n+1})) (inducedGenLoop (E.ε n) γ)
    -- RHS: inducedGenLoop (F.ε n) (inducedGenLoop (f_n) γ)
    -- By inducedGenLoop_comp: LHS = inducedGenLoop (E.ε n ≫ Ω(f_{n+1})) γ
    --                          RHS = inducedGenLoop (f_n ≫ F.ε n) γ
    rw [inducedGenLoop_comp, inducedGenLoop_comp]
    rw [inducedGenLoop_spectrum_comm]

/-- Key lemma: the spectrum map induced maps commute with the full transition map.
    This shows: F.transitionMap ∘ (f_n)_* = (f_{n+1})_* ∘ E.transitionMap -/
theorem transitionMap_natural (f : E ⟶ F) (n m : ℕ) (x : E.levelHomotopyGroup m n) :
    levelInducedMap f (m + 1) (n + 1) (E.transitionMap n m x) =
    F.transitionMap n m (levelInducedMap f m n x) := by
  unfold transitionMap spectrumTransitionMap
  simp only [Function.comp_apply]
  unfold levelInducedMap inducedπ
  induction x using Quotient.ind with
  | _ γ =>
    simp only [Quotient.map'_mk'']
    unfold loopSpaceHomotopyGroupEquiv
    apply Quotient.sound
    -- LHS: inducedGenLoop (f_{n+1}) (genLoopCurryEquiv E (inducedGenLoop (E.ε n) γ))
    -- RHS: genLoopCurryEquiv F (inducedGenLoop (F.ε n) (inducedGenLoop (f_n) γ))
    -- Use genLoopCurryEquiv_natural backwards to transform LHS
    have heq_natural := genLoopCurryEquiv_natural (f.levelMap (n + 1)) m
        (inducedGenLoop (Fin m) (E.ε n) γ)
    -- heq_natural : genLoopCurryEquiv F (inducedGenLoop (loopSpaceMap f_{n+1}) (inducedGenLoop (E.ε n) γ))
    --             = inducedGenLoop f_{n+1} (genLoopCurryEquiv E (inducedGenLoop (E.ε n) γ))
    have hgoal : inducedGenLoop (Fin (m + 1)) (f.levelMap (n + 1))
           (genLoopCurryEquiv (E.spaceAt (n + 1)) m (inducedGenLoop (Fin m) (E.ε n) γ))
        = genLoopCurryEquiv (F.spaceAt (n + 1)) m
           (inducedGenLoop (Fin m) (F.ε n) (inducedGenLoop (Fin m) (f.levelMap n) γ)) := by
      calc _ = genLoopCurryEquiv (F.spaceAt (n + 1)) m
             (inducedGenLoop (Fin m) (loopSpaceMap (f.levelMap (n + 1))) (inducedGenLoop (Fin m) (E.ε n) γ))
             := heq_natural.symm
        _ = genLoopCurryEquiv (F.spaceAt (n + 1)) m
             (inducedGenLoop (Fin m) (E.ε n ≫ loopSpaceMap (f.levelMap (n + 1))) γ)
             := by rw [inducedGenLoop_comp]
        _ = genLoopCurryEquiv (F.spaceAt (n + 1)) m
             (inducedGenLoop (Fin m) (f.levelMap n ≫ F.ε n) γ)
             := by rw [f.comm n]
        _ = genLoopCurryEquiv (F.spaceAt (n + 1)) m
             (inducedGenLoop (Fin m) (F.ε n) (inducedGenLoop (Fin m) (f.levelMap n) γ))
             := by rw [← inducedGenLoop_comp]
    -- Convert equality to homotopy
    exact hgoal ▸ GenLoop.Homotopic.refl _

/-- The induced map on colimit terms.
    For each level n ≥ startIndex k, this maps E.colimitTerm k n → F.colimitTerm k n. -/
def colimitTermInduced (f : E ⟶ F) (k : ℤ) (n : ℕ) (h : startIndex k ≤ n) :
    E.colimitTerm k n h → F.colimitTerm k n h :=
  levelInducedMap f (levelIndex k n h) n

/-- Helper lemma: levelInducedMap commutes with Eq.mpr type casts on the level index.
    When m₁ = m₂, applying levelInducedMap at m₁ to a casted element equals
    casting the result of levelInducedMap at m₂. -/
theorem levelInducedMap_eqMpr (f : E ⟶ F) (m₁ m₂ : ℕ) (n : ℕ) (hm : m₁ = m₂)
    (x : E.levelHomotopyGroup m₂ n) :
    levelInducedMap f m₁ n (Eq.mpr (congrArg (E.levelHomotopyGroup · n) hm) x) =
    Eq.mpr (congrArg (F.levelHomotopyGroup · n) hm) (levelInducedMap f m₂ n x) := by
  subst hm
  rfl

/-- Key naturality lemma: colimitTermInduced commutes with colimitTransition.
    F.colimitTransition (f_* x) = f_* (E.colimitTransition x) as quotient elements.

    This is the single-step commutativity that implies full commutativity with imageAtLevel.
    The proof uses transitionMap_natural. -/
theorem colimitTermInduced_colimitTransition (f : E ⟶ F) (k : ℤ) (n : ℕ) (hn : startIndex k ≤ n)
    (x : E.colimitTerm k n hn) :
    F.colimitTransition k n hn (colimitTermInduced f k n hn x) =
    colimitTermInduced f k (n + 1) (startIndex_succ k n hn) (E.colimitTransition k n hn x) := by
  -- transitionMap_natural says: levelInducedMap f (m+1) (n+1) (E.transitionMap n m x)
  --                           = F.transitionMap n m (levelInducedMap f m n x)
  have hnat := transitionMap_natural f n (levelIndex k n hn) x
  -- hlev : levelIndex k (n + 1) _ = levelIndex k n hn + 1
  have hlev : levelIndex k (n + 1) (startIndex_succ k n hn) = levelIndex k n hn + 1 :=
    levelIndex_succ k n hn
  -- Unfold definitions to expose the Eq.mpr structure
  unfold colimitTermInduced colimitTransition colimitTerm
  -- Both sides involve Eq.mpr with proofs derived from hlev
  -- Use Eq.rec to handle the dependent cast
  -- The key insight: both sides, when "un-cast", equal the same thing by hnat
  -- Prove by showing LHS = RHS via intermediate form
  have hE_type : E.levelHomotopyGroup (levelIndex k (n + 1) (startIndex_succ k n hn)) (n + 1) =
                 E.levelHomotopyGroup (levelIndex k n hn + 1) (n + 1) :=
    congrArg (E.levelHomotopyGroup · (n + 1)) hlev
  have hF_type : F.levelHomotopyGroup (levelIndex k (n + 1) (startIndex_succ k n hn)) (n + 1) =
                 F.levelHomotopyGroup (levelIndex k n hn + 1) (n + 1) :=
    congrArg (F.levelHomotopyGroup · (n + 1)) hlev
  -- The Eq.mpr in colimitTransition uses congrArg (levelHomotopyGroup · (n+1)) hlev
  -- Show both sides equal the same thing
  -- Use Eq.rec with the levelIndex equality to unify the types
  calc F.colimitTransition k n hn (colimitTermInduced f k n hn x)
      = Eq.mpr (congrArg (F.levelHomotopyGroup · (n + 1)) hlev)
          (F.transitionMap n (levelIndex k n hn) (levelInducedMap f (levelIndex k n hn) n x)) := rfl
    _ = Eq.mpr (congrArg (F.levelHomotopyGroup · (n + 1)) hlev)
          (levelInducedMap f (levelIndex k n hn + 1) (n + 1) (E.transitionMap n (levelIndex k n hn) x)) := by
        rw [hnat]
    _ = levelInducedMap f (levelIndex k (n + 1) (startIndex_succ k n hn)) (n + 1)
          (Eq.mpr (congrArg (E.levelHomotopyGroup · (n + 1)) hlev) (E.transitionMap n (levelIndex k n hn) x)) := by
        rw [← levelInducedMap_eqMpr f (levelIndex k (n + 1) _) (levelIndex k n hn + 1) (n + 1) hlev
            (E.transitionMap n (levelIndex k n hn) x)]
    _ = colimitTermInduced f k (n + 1) (startIndex_succ k n hn) (E.colimitTransition k n hn x) := rfl

/-- Helper: colimitTermInduced commutes with imageAtLevel.
    F.imageAtLevel (f_* x) = f_* (E.imageAtLevel x) -/
theorem colimitTermInduced_imageAtLevel (f : E ⟶ F) (k : ℤ) (n : ℕ) (hn : startIndex k ≤ n)
    (M : ℕ) (hM : n ≤ M) (x : E.colimitTerm k n hn) :
    F.imageAtLevel k n hn M hM (colimitTermInduced f k n hn x) =
    colimitTermInduced f k M (Nat.le_trans hn hM) (E.imageAtLevel k n hn M hM x) := by
  -- By strong induction on (M - n)
  induction hd : M - n using Nat.strong_induction_on generalizing n M with
  | _ d ih =>
    by_cases hnM : n = M
    · -- Base case: n = M
      subst hnM
      simp only [imageAtLevel_self]
    · -- Recursive case: n < M
      have hn_lt_M : n < M := Nat.lt_of_le_of_ne hM hnM
      have hstep : startIndex k ≤ n + 1 := Nat.le_trans hn (Nat.le_succ n)
      have hd' : M - (n + 1) < d := by omega
      -- Unfold imageAtLevel on both sides
      have hL : F.imageAtLevel k n hn M hM (colimitTermInduced f k n hn x) =
                F.imageAtLevel k (n + 1) hstep M hn_lt_M
                  (F.colimitTransition k n hn (colimitTermInduced f k n hn x)) := by
        rw [imageAtLevel]; simp only [hnM, ↓reduceDIte]
      have hR : E.imageAtLevel k n hn M hM x =
                E.imageAtLevel k (n + 1) hstep M hn_lt_M (E.colimitTransition k n hn x) := by
        rw [imageAtLevel]; simp only [hnM, ↓reduceDIte]
      rw [hL, hR]
      -- Use colimitTermInduced_colimitTransition to swap the order
      rw [colimitTermInduced_colimitTransition]
      -- Now apply IH
      exact ih (M - (n + 1)) hd' (n + 1) hstep M hn_lt_M (E.colimitTransition k n hn x) rfl

/-- The induced map on colimit representations preserves the equivalence relation.
    If two representations are equivalent in E, their images are equivalent in F. -/
theorem colimitTermInduced_preserves_equiv (f : E ⟶ F) (k : ℤ)
    (r₁ r₂ : StableHomotopyGroupRep E k)
    (heq : StableHomotopyGroupRep.Equiv E k r₁ r₂) :
    StableHomotopyGroupRep.Equiv F k
      ⟨r₁.level, r₁.level_valid, colimitTermInduced f k r₁.level r₁.level_valid r₁.element⟩
      ⟨r₂.level, r₂.level_valid, colimitTermInduced f k r₂.level r₂.level_valid r₂.element⟩ := by
  obtain ⟨N, hN₁, hN₂, heqN⟩ := heq
  use N, hN₁, hN₂
  -- Apply colimitTermInduced_imageAtLevel to both sides
  rw [colimitTermInduced_imageAtLevel f k r₁.level r₁.level_valid N hN₁ r₁.element]
  rw [colimitTermInduced_imageAtLevel f k r₂.level r₂.level_valid N hN₂ r₂.element]
  -- Now apply heqN
  exact congrArg _ heqN

/-- The induced map on stable homotopy group representations. -/
def StableHomotopyGroupRep.map (f : E ⟶ F) (k : ℤ) (r : StableHomotopyGroupRep E k) :
    StableHomotopyGroupRep F k where
  level := r.level
  level_valid := r.level_valid
  element := colimitTermInduced f k r.level r.level_valid r.element

/-- The induced map on stable homotopy groups.
    For f : E → F, this is f_* : π_k(E) → π_k(F). -/
noncomputable def stableπInduced (f : E ⟶ F) (k : ℤ) :
    StableHomotopyGroup E k → StableHomotopyGroup F k :=
  Quotient.map' (StableHomotopyGroupRep.map f k)
    (fun r₁ r₂ heq => colimitTermInduced_preserves_equiv f k r₁ r₂ heq)

/-- Notation for the induced map on stable homotopy groups. -/
scoped notation f "₊" => stableπInduced f

/-- The induced map is functorial: identity induces identity. -/
theorem stableπInduced_id (E : Spectrum) (k : ℤ) :
    stableπInduced (𝟙 E) k = id := by
  funext x
  induction x using Quotient.ind with
  | _ r =>
    simp only [stableπInduced, Quotient.map'_mk'', id_eq]
    apply Quotient.sound
    -- Show the representations are equivalent
    use r.level, le_refl _, le_refl _
    unfold StableHomotopyGroupRep.map colimitTermInduced levelInducedMap inducedπ
    simp only [imageAtLevel_self]
    -- (𝟙 E).levelMap n = 𝟙 (E.spaceAt n)
    -- inducedGenLoop (𝟙 X) γ = γ
    induction r.element using Quotient.ind with
    | _ γ =>
      simp only [Quotient.map'_mk'']
      congr 1

/-- The induced map is functorial: composition. -/
theorem stableπInduced_comp (f : E ⟶ F) (g : F ⟶ G) (k : ℤ) :
    stableπInduced (f ≫ g) k = stableπInduced g k ∘ stableπInduced f k := by
  funext x
  induction x using Quotient.ind with
  | _ r =>
    simp only [stableπInduced, Quotient.map'_mk'', Function.comp_apply]
    apply Quotient.sound
    -- Show the representations are equivalent
    use r.level, le_refl _, le_refl _
    unfold StableHomotopyGroupRep.map colimitTermInduced levelInducedMap inducedπ
    simp only [imageAtLevel_self]
    -- (f ≫ g).levelMap n = f.levelMap n ≫ g.levelMap n
    -- inducedGenLoop (f ≫ g) γ ≃ inducedGenLoop g (inducedGenLoop f γ)
    induction r.element using Quotient.ind with
    | _ γ =>
      simp only [Quotient.map'_mk'']
      congr 1

end InducedMaps

/-! ## Group Structure on Stable Homotopy Groups

The stable homotopy groups π_k(E) are abelian groups. The group structure comes from
the group structure on the level homotopy groups π_{n+k}(E_n), which are abelian
groups for n+k ≥ 2. Since the transition maps are group homomorphisms, the colimit
inherits an abelian group structure.

**Note:** The full group structure requires careful handling of the fact that
early levels (where n+k < 1) don't have group structure. The standard approach is
to take the colimit starting from a level where n+k ≥ 2. This is left as future work.

Key lemmas already proved:
- `transitionMap_mul`: transition maps preserve multiplication
- `inducedπ_mul`: induced maps on homotopy groups preserve multiplication
- `loopSpaceHomotopyGroupEquiv_mul`: the loop space isomorphism preserves multiplication
-/

section GroupStructure

variable (E : Spectrum) (k : ℤ)

/-- The minimum level for group structure: we need levelIndex k n h ≥ 1 for group structure.
    This is n such that n + k ≥ 1, i.e., n ≥ max(startIndex k, 1 - k). -/
def groupStartIndex : ℕ := max (startIndex k) (Int.toNat (1 - k))

/-- At groupStartIndex, the level index is at least 1. -/
theorem levelIndex_ge_one_at_groupStart :
    1 ≤ levelIndex k (groupStartIndex k) (Nat.le_max_left _ _) := by
  unfold groupStartIndex levelIndex startIndex
  -- Goal: 1 ≤ Int.toNat (↑(max (Int.toNat (-k)) (Int.toNat (1 - k))) + k)
  -- We need to show max(toNat(-k), toNat(1-k)) + k ≥ 1
  -- Let m = max (Int.toNat (-k)) (Int.toNat (1 - k))
  set m := max (Int.toNat (-k)) (Int.toNat (1 - k)) with hm_def
  -- We need 1 ≤ Int.toNat (↑m + k)
  -- First show ↑m + k ≥ 1
  have hm_ge : (m : ℤ) + k ≥ 1 := by
    have h1 : m ≥ Int.toNat (1 - k) := Nat.le_max_right _ _
    by_cases hk : 1 - k ≤ 0
    · -- 1 - k ≤ 0, so k ≥ 1, so m + k ≥ 0 + 1 = 1
      have hk1 : k ≥ 1 := by omega
      omega
    · -- 1 - k > 0, so toNat(1-k) = 1 - k, so m ≥ 1 - k, so m + k ≥ 1
      push_neg at hk
      have h2 : Int.toNat (1 - k) = (1 - k).toNat := rfl
      have h3 : (Int.toNat (1 - k) : ℤ) = 1 - k := Int.toNat_of_nonneg (by omega : 0 ≤ 1 - k)
      have h4 : (m : ℤ) ≥ 1 - k := by
        calc (m : ℤ) ≥ Int.toNat (1 - k) := Int.ofNat_le.mpr h1
          _ = 1 - k := h3
      omega
  -- Use Int.toNat_le_toNat: 1 ≤ x → toNat 1 ≤ toNat x
  have h1_eq : (1 : ℕ) = Int.toNat 1 := rfl
  rw [h1_eq]
  exact Int.toNat_le_toNat hm_ge

/-- At groupStartIndex, Fin (levelIndex) is nonempty, enabling the group structure. -/
instance groupStartIndex_nonempty :
    Nonempty (Fin (levelIndex k (groupStartIndex k) (Nat.le_max_left _ _))) := by
  have h := levelIndex_ge_one_at_groupStart k
  exact ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one h⟩⟩

end GroupStructure

end Spectrum

end Topology
