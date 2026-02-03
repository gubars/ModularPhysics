/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.Topology.Spectra.Basic
import ModularPhysics.Topology.Spectra.HomotopyGroups
import ModularPhysics.Topology.Homotopy.Sequences

/-!
# Cofiber Spectra and Long Exact Sequences

This file defines the cofiber spectrum of a spectrum map and establishes
the long exact sequence for stable homotopy groups.

## Main Definitions

* `Spectrum.cofiberSpectrum` - The cofiber spectrum Cf for f : E → F
* `Spectrum.cofiberInclusion` - The inclusion F → Cf
* `Spectrum.connectingMapSpectrum` - The connecting map Cf → Σ(E)

## Mathematical Background

For a spectrum map f : E → F, the cofiber spectrum is defined levelwise:
  (Cf)_n = mappingCone(f_n)

The structure maps for Cf come from the compatibility of the mapping cone
construction with the suspension-loop adjunction.

This gives the cofiber sequence of spectra:
  E → F → Cf → E[1] → F[1] → ...

where E[1] denotes the shift (suspension) of E.

The key result is the long exact sequence of stable homotopy groups:
  ... → π_k(E) → π_k(F) → π_k(Cf) → π_{k-1}(E) → ...

## References

* Adams, "Stable Homotopy and Generalised Homology", Part III
* May, "A Concise Course in Algebraic Topology", Chapter 8
-/

universe u

open CategoryTheory PointedTopSpace Relation

namespace Topology

namespace Spectrum

variable {E F G : Spectrum}

/-! ## Cofiber Spectrum

The cofiber spectrum Cf of a spectrum map f : E → F is defined levelwise:
  (Cf)_n = mappingCone(f_n : E_n → F_n)

The structure maps are induced from the compatibility of the mapping cone
with the suspension-loop adjunction.
-/

section CofiberSpectrum

/-- The spaces of the cofiber spectrum: (Cf)_n = mappingCone(f_n). -/
def cofiberSpaceAt (f : E ⟶ F) (n : ℕ) : PointedTopSpace :=
  mappingCone (f.levelMap n)

/-- Auxiliary function for structure map on F part:
    x ∈ F_n ↦ Ω(cofiberInclusion)(ε_F(x)) ∈ Ω(Cf_{n+1}) -/
def cofiberStructureMapF (f : E ⟶ F) (n : ℕ) (x : (F.spaceAt n).carrier) :
    LoopSpaceType (cofiberSpaceAt f (n + 1)) :=
  (loopSpaceMap (cofiberInclusion (f.levelMap (n + 1)))).toFun ((F.ε n).toFun x)

/-- Helper: construct a loop in Cf_{n+1} from a point (a, t) in E_n × I.
    The loop is s ↦ (ε_E(a)(s), t), which traces how ε_E(a) moves at constant height t. -/
def mkConeLoop (f : E ⟶ F) (n : ℕ)
    (p : (E.spaceAt n).carrier × pointedUnitInterval.carrier) :
    LoopSpaceType (cofiberSpaceAt f (n + 1)) := by
  let a := p.1
  let t := p.2
  -- ε_E(a) is a loop in E_{n+1}, accessed as a Path
  let loopE : Path (E.spaceAt (n + 1)).basepoint (E.spaceAt (n + 1)).basepoint :=
    (E.ε n).toFun a
  -- The underlying function of the loop
  let loopEFun : unitInterval → (E.spaceAt (n + 1)).carrier := loopE
  -- Construct the function s ↦ (ε_E(a)(s), t) in Cf_{n+1}
  let pathFun : unitInterval → (cofiberSpaceAt f (n + 1)).carrier := fun s =>
    (coneToCofiber (f.levelMap (n + 1))).toFun
      (smashQuotientMap (E.spaceAt (n + 1)) pointedUnitInterval (loopEFun s, t))
  -- Continuity
  have hcont : Continuous pathFun := by
    apply (coneToCofiber (f.levelMap (n + 1))).continuous.comp
    apply (continuous_smashQuotientMap _ _).comp
    exact loopE.continuous.prodMk continuous_const
  -- Source: at s = 0, loopE(0) = basepoint, so (basepoint, t) ∈ wedge → basepoint
  have hSource : pathFun ⟨0, unitInterval.zero_mem⟩ = (cofiberSpaceAt f (n + 1)).basepoint := by
    simp only [pathFun]
    have hloop0 : loopEFun ⟨0, unitInterval.zero_mem⟩ = (E.spaceAt (n + 1)).basepoint := loopE.source
    rw [hloop0]
    -- (basepoint, t) is in the wedge
    have hwedge : smashQuotientMap (E.spaceAt (n + 1)) pointedUnitInterval
        ((E.spaceAt (n + 1)).basepoint, t) = (reducedCone (E.spaceAt (n + 1))).basepoint := by
      apply Quotient.sound
      right
      exact ⟨Or.inl rfl, Or.inl rfl⟩
    rw [hwedge]
    exact (coneToCofiber (f.levelMap (n + 1))).map_basepoint
  -- Target: at s = 1, loopE(1) = basepoint, so (basepoint, t) ∈ wedge → basepoint
  have hTarget : pathFun ⟨1, unitInterval.one_mem⟩ = (cofiberSpaceAt f (n + 1)).basepoint := by
    simp only [pathFun]
    have hloop1 : loopEFun ⟨1, unitInterval.one_mem⟩ = (E.spaceAt (n + 1)).basepoint := loopE.target
    rw [hloop1]
    have hwedge : smashQuotientMap (E.spaceAt (n + 1)) pointedUnitInterval
        ((E.spaceAt (n + 1)).basepoint, t) = (reducedCone (E.spaceAt (n + 1))).basepoint := by
      apply Quotient.sound
      right
      exact ⟨Or.inl rfl, Or.inl rfl⟩
    rw [hwedge]
    exact (coneToCofiber (f.levelMap (n + 1))).map_basepoint
  exact Path.mk ⟨pathFun, hcont⟩ hSource hTarget

/-- When a point is in the wedge, smashQuotientMap sends it to the basepoint. -/
theorem smashQuotientMap_wedge_left (X Y : PointedTopSpace) (y : Y.carrier) :
    smashQuotientMap X Y (X.basepoint, y) = (smashProduct X Y).basepoint := by
  apply Quotient.sound
  right
  exact ⟨Or.inl rfl, Or.inl rfl⟩

theorem smashQuotientMap_wedge_right (X Y : PointedTopSpace) (x : X.carrier) :
    smashQuotientMap X Y (x, Y.basepoint) = (smashProduct X Y).basepoint := by
  apply Quotient.sound
  right
  exact ⟨Or.inr rfl, Or.inr rfl⟩

/-- The cone loop construction respects the smash equivalence relation.
    Points in the wedge (a = basepoint or t = 0) all give the constant loop. -/
theorem mkConeLoop_respects (f : E ⟶ F) (n : ℕ) :
    ∀ p q : (E.spaceAt n).carrier × pointedUnitInterval.carrier,
      smashRel (E.spaceAt n) pointedUnitInterval p q →
      mkConeLoop f n p = mkConeLoop f n q := by
  intro p q hpq
  cases hpq with
  | inl heq => rw [heq]
  | inr hwedge =>
    obtain ⟨hp, hq⟩ := hwedge
    -- Both p and q are in the wedge, so both loops go through basepoint at each s
    apply Path.ext
    funext s
    simp only [mkConeLoop, Path.coe_mk_mk]
    -- Define the loop functions explicitly
    let loopP : Path _ _ := (E.ε n).toFun p.1
    let loopQ : Path _ _ := (E.ε n).toFun q.1
    -- When either coordinate is at basepoint, the smash product collapses
    -- Case analysis on hp and hq
    cases hp with
    | inl ha =>
      -- p.1 = basepoint, so ε_E(p.1) is the constant loop at basepoint
      have hp_wedge : smashQuotientMap (E.spaceAt (n + 1)) pointedUnitInterval
          (loopP s, p.2) = (reducedCone (E.spaceAt (n + 1))).basepoint := by
        have hconst : (E.ε n).toFun (E.spaceAt n).basepoint = constLoop (E.spaceAt (n + 1)) :=
          (E.ε n).map_basepoint
        -- loopP = (E.ε n).toFun p.1 = (E.ε n).toFun basepoint = constLoop
        have hloopP : loopP = constLoop (E.spaceAt (n + 1)) := by
          show (E.ε n).toFun p.1 = _
          rw [ha]
          exact hconst
        simp only [hloopP, constLoop, Path.refl_apply]
        exact smashQuotientMap_wedge_left _ _ _
      cases hq with
      | inl hb =>
        have hq_wedge : smashQuotientMap (E.spaceAt (n + 1)) pointedUnitInterval
            (loopQ s, q.2) = (reducedCone (E.spaceAt (n + 1))).basepoint := by
          have hconst : (E.ε n).toFun (E.spaceAt n).basepoint = constLoop (E.spaceAt (n + 1)) :=
            (E.ε n).map_basepoint
          have hloopQ : loopQ = constLoop (E.spaceAt (n + 1)) := by
            show (E.ε n).toFun q.1 = _
            rw [hb]
            exact hconst
          simp only [hloopQ, constLoop, Path.refl_apply]
          exact smashQuotientMap_wedge_left _ _ _
        rw [hp_wedge, hq_wedge]
      | inr ht =>
        have hq_wedge : smashQuotientMap (E.spaceAt (n + 1)) pointedUnitInterval
            (loopQ s, q.2) = (reducedCone (E.spaceAt (n + 1))).basepoint := by
          rw [ht]
          exact smashQuotientMap_wedge_right _ _ _
        rw [hp_wedge, hq_wedge]
    | inr ht =>
      -- p.2 = 0 (basepoint of I₊), so (_, 0) ∈ wedge → basepoint
      have hp_wedge : smashQuotientMap (E.spaceAt (n + 1)) pointedUnitInterval
          (loopP s, p.2) = (reducedCone (E.spaceAt (n + 1))).basepoint := by
        rw [ht]
        exact smashQuotientMap_wedge_right _ _ _
      cases hq with
      | inl hb =>
        have hq_wedge : smashQuotientMap (E.spaceAt (n + 1)) pointedUnitInterval
            (loopQ s, q.2) = (reducedCone (E.spaceAt (n + 1))).basepoint := by
          have hconst : (E.ε n).toFun (E.spaceAt n).basepoint = constLoop (E.spaceAt (n + 1)) :=
            (E.ε n).map_basepoint
          have hloopQ : loopQ = constLoop (E.spaceAt (n + 1)) := by
            show (E.ε n).toFun q.1 = _
            rw [hb]
            exact hconst
          simp only [hloopQ, constLoop, Path.refl_apply]
          exact smashQuotientMap_wedge_left _ _ _
        rw [hp_wedge, hq_wedge]
      | inr ht' =>
        have hq_wedge : smashQuotientMap (E.spaceAt (n + 1)) pointedUnitInterval
            (loopQ s, q.2) = (reducedCone (E.spaceAt (n + 1))).basepoint := by
          rw [ht']
          exact smashQuotientMap_wedge_right _ _ _
        rw [hp_wedge, hq_wedge]

/-- Auxiliary function for structure map on cone part:
    (a, t) ∈ C(E_n) ↦ (s ↦ (ε_E(a)(s), t)) ∈ Ω(Cf_{n+1}) -/
def cofiberStructureMapCone (f : E ⟶ F) (n : ℕ)
    (c : (reducedCone (E.spaceAt n)).carrier) :
    LoopSpaceType (cofiberSpaceAt f (n + 1)) :=
  Quotient.lift (mkConeLoop f n) (mkConeLoop_respects f n) c

/-- The auxiliary map for the cofiber structure map before quotienting. -/
def cofiberStructureMapAux (f : E ⟶ F) (n : ℕ) :
    MappingConePreType (E.spaceAt n) (F.spaceAt n) →
    LoopSpaceType (cofiberSpaceAt f (n + 1)) := fun p =>
  match p with
  | Sum.inl x => cofiberStructureMapF f n x
  | Sum.inr c => cofiberStructureMapCone f n c

/-- Helper: apply a loop (Path) to a parameter s.
    Paths coerce to functions via their underlying ContinuousMap. -/
def applyLoop {X : PointedTopSpace} (γ : LoopSpaceType X) (s : unitInterval) : X.carrier :=
  γ.toContinuousMap s

/-- The auxiliary map respects the mapping cone equivalence relation.
    This uses the spectrum map compatibility f.comm : E.ε n ≫ Ω(f_{n+1}) = f_n ≫ F.ε n.

    Key insight: For the f(a) ~ (a, 1) case:
    - LHS: cofiberStructureMapF sends f(a) to Ω(cofiberInclusion)(ε_F(f(a)))
    - RHS: cofiberStructureMapCone sends (a, 1) to loop s ↦ coneToCofiber(ε_E(a)(s), 1)
    By f.comm: ε_F(f(a))(s) = f_{n+1}(ε_E(a)(s))
    And in Cf_{n+1}: (e, 1) ~ f_{n+1}(e), so both loops are equivalent. -/
theorem cofiberStructureMapAux_respects (f : E ⟶ F) (n : ℕ) :
    ∀ p q : MappingConePreType (E.spaceAt n) (F.spaceAt n),
      (mappingConeSetoid (f.levelMap n)).r p q →
      cofiberStructureMapAux f n p = cofiberStructureMapAux f n q := by
  intro p q hpq
  induction hpq with
  | rel _ _ hr =>
    simp only [cofiberStructureMapAux]
    cases hr with
    | inl hfa =>
      -- f(a) ~ (a, 1) case: both loops are equal by f.comm
      obtain ⟨a, hor⟩ := hfa
      cases hor with
      | inl h =>
        simp only [h.1, h.2]
        apply Path.ext
        funext s
        -- Both sides trace equivalent paths in Cf_{n+1}
        simp only [cofiberStructureMapF, cofiberStructureMapCone, mkConeLoop,
                   Path.coe_mk_mk, coneBase, smashQuotientMap, Quotient.lift_mk]
        -- The element ε_E(a)(s) witnesses the identification (e, 1) ~ f_{n+1}(e)
        let loopE : LoopSpaceType (E.spaceAt (n + 1)) := (E.ε n).toFun a
        apply Quotient.sound
        apply EqvGen.rel
        left
        use loopE.toContinuousMap s
        left
        constructor
        · -- Need: (cofiberInclusion applied to ε_F(f(a))(s)) = Sum.inl (f_{n+1}(ε_E(a)(s)))
          -- First show ε_F(f(a))(s) = f_{n+1}(ε_E(a)(s)) using f.comm
          show Sum.inl (((F.ε n).toFun ((f.levelMap n).toFun a)).toContinuousMap s) =
               Sum.inl ((f.levelMap (n + 1)).toFun (loopE.toContinuousMap s))
          congr 1
          -- f.comm : E.ε n ≫ loopSpaceMap (f_{n+1}) = f_n ≫ F.ε n
          have hcomm := f.comm n
          -- This gives: (F.ε n).toFun ((f_n).toFun a) = (loopSpaceMap f_{n+1}).toFun ((E.ε n).toFun a)
          have heq : (f.levelMap n ≫ F.ε n).toFun a = (E.ε n ≫ loopSpaceMap (f.levelMap (n + 1))).toFun a := by
            rw [hcomm]
          simp only [comp_toFun, Function.comp_apply] at heq
          -- heq : (F.ε n).toFun (f_n a) = (loopSpaceMap f_{n+1}).toFun (ε_E(a))
          -- Pointwise: ((F.ε n).toFun (f_n a)).toFun s = f_{n+1} (ε_E(a) s)
          have hpt : ((loopSpaceMap (f.levelMap (n + 1))).toFun ((E.ε n).toFun a)).toContinuousMap s =
                     (f.levelMap (n + 1)).toFun (((E.ε n).toFun a).toContinuousMap s) := by
            simp only [loopSpaceMap]
            rfl
          calc ((F.ε n).toFun ((f.levelMap n).toFun a)).toContinuousMap s
              = ((loopSpaceMap (f.levelMap (n + 1))).toFun ((E.ε n).toFun a)).toContinuousMap s := by
                  rw [← heq]
            _ = (f.levelMap (n + 1)).toFun (((E.ε n).toFun a).toContinuousMap s) := hpt
        · rfl
      | inr h =>
        simp only [h.1, h.2]
        apply Path.ext
        funext s
        simp only [cofiberStructureMapF, cofiberStructureMapCone, mkConeLoop,
                   Path.coe_mk_mk, coneBase, smashQuotientMap, Quotient.lift_mk]
        let loopE : LoopSpaceType (E.spaceAt (n + 1)) := (E.ε n).toFun a
        apply Quotient.sound
        apply EqvGen.rel
        left
        use loopE.toContinuousMap s
        right
        constructor
        · show Sum.inl (((F.ε n).toFun ((f.levelMap n).toFun a)).toFun s) =
               Sum.inl ((f.levelMap (n + 1)).toFun (loopE.toContinuousMap s))
          congr 1
          have hcomm := f.comm n
          have heq : (f.levelMap n ≫ F.ε n).toFun a = (E.ε n ≫ loopSpaceMap (f.levelMap (n + 1))).toFun a := by
            rw [hcomm]
          simp only [comp_toFun, Function.comp_apply] at heq
          have hpt : ((loopSpaceMap (f.levelMap (n + 1))).toFun ((E.ε n).toFun a)).toContinuousMap s =
                     (f.levelMap (n + 1)).toFun (((E.ε n).toFun a).toContinuousMap s) := by
            simp only [loopSpaceMap]
            rfl
          calc ((F.ε n).toFun ((f.levelMap n).toFun a)).toContinuousMap s
              = ((loopSpaceMap (f.levelMap (n + 1))).toFun ((E.ε n).toFun a)).toContinuousMap s := by
                  rw [← heq]
            _ = (f.levelMap (n + 1)).toFun (((E.ε n).toFun a).toContinuousMap s) := hpt
        · rfl
    | inr hbase =>
      -- Basepoint case: both map to constLoop
      cases hbase with
      | inl h =>
        simp only [h.1, h.2]
        -- Both sides are loops (paths), and we need to show they're equal
        -- LHS: cofiberStructureMapF at F.basepoint = Ω(cofiberInclusion)(ε_F(basepoint))
        -- RHS: cofiberStructureMapCone at cone basepoint
        have hbase_F : (F.ε n).toFun (F.spaceAt n).basepoint = constLoop (F.spaceAt (n + 1)) :=
          (F.ε n).map_basepoint
        have hbase_E : (E.ε n).toFun (E.spaceAt n).basepoint = constLoop (E.spaceAt (n + 1)) :=
          (E.ε n).map_basepoint
        simp only [cofiberStructureMapF, cofiberStructureMapCone]
        rw [hbase_F]
        -- LHS is now Ω(cofiberInclusion)(constLoop) = constLoop (composed with identity)
        apply Path.ext
        funext s
        -- LHS: ((loopSpaceMap cofiberInclusion).toFun constLoop) s
        -- This is: cofiberInclusion (constLoop s) = cofiberInclusion (basepoint)
        show ((loopSpaceMap (cofiberInclusion (f.levelMap (n + 1)))).toFun
              (constLoop (F.spaceAt (n + 1)))).toContinuousMap s =
             (Quotient.lift (mkConeLoop f n) (mkConeLoop_respects f n)
               (reducedCone (E.spaceAt n)).basepoint).toContinuousMap s
        -- LHS: loopSpaceMap(cofiberInclusion)(constLoop) = cofiberInclusion ∘ constLoop
        -- At point s: (cofiberInclusion ∘ constLoop)(s) = cofiberInclusion(basepoint)
        have hLHS : ((loopSpaceMap (cofiberInclusion (f.levelMap (n + 1)))).toFun
              (constLoop (F.spaceAt (n + 1)))).toContinuousMap s =
             (cofiberInclusion (f.levelMap (n + 1))).toFun (F.spaceAt (n + 1)).basepoint := by
          simp only [loopSpaceMap, constLoop]
          rfl
        rw [hLHS, (cofiberInclusion (f.levelMap (n + 1))).map_basepoint]
        -- RHS: mkConeLoop at cone basepoint
        simp only [reducedCone, smashProduct, smashBasepoint, Quotient.lift_mk,
                   mkConeLoop, ContinuousMap.coe_mk]
        simp only [hbase_E, constLoop, Path.refl_apply]
        rw [smashQuotientMap_wedge_right]
        -- Goal: pt Cf = coneToCofiber(smashBasepoint)
        -- coneToCofiber.map_basepoint uses Quotient.sound, not rfl
        -- reducedCone X = X ∧₊ pointedUnitInterval, so their basepoints are defeq
        have h := (coneToCofiber (f.levelMap (n + 1))).map_basepoint
        -- h : coneToCofiber(pt C₊(E_{n+1})) = pt (Cf f_{n+1})
        -- Goal: pt (Cf f_{n+1}) = coneToCofiber(pt (E_{n+1} ∧₊ I₊))
        -- Since C₊ X = X ∧₊ I₊, their basepoints are the same
        exact h.symm
      | inr h =>
        simp only [h.1, h.2]
        have hbase_F : (F.ε n).toFun (F.spaceAt n).basepoint = constLoop (F.spaceAt (n + 1)) :=
          (F.ε n).map_basepoint
        have hbase_E : (E.ε n).toFun (E.spaceAt n).basepoint = constLoop (E.spaceAt (n + 1)) :=
          (E.ε n).map_basepoint
        simp only [cofiberStructureMapF, cofiberStructureMapCone]
        rw [hbase_F]
        apply Path.ext
        funext s
        -- RHS: mkConeLoop at cone basepoint
        show (Quotient.lift (mkConeLoop f n) (mkConeLoop_respects f n)
               (reducedCone (E.spaceAt n)).basepoint).toContinuousMap s =
             ((loopSpaceMap (cofiberInclusion (f.levelMap (n + 1)))).toFun
               (constLoop (F.spaceAt (n + 1)))).toContinuousMap s
        -- RHS: loopSpaceMap(cofiberInclusion)(constLoop)(s) = cofiberInclusion(basepoint)
        have hRHS : ((loopSpaceMap (cofiberInclusion (f.levelMap (n + 1)))).toFun
              (constLoop (F.spaceAt (n + 1)))).toContinuousMap s =
             (cofiberInclusion (f.levelMap (n + 1))).toFun (F.spaceAt (n + 1)).basepoint := by
          simp only [loopSpaceMap, constLoop]
          rfl
        rw [hRHS, (cofiberInclusion (f.levelMap (n + 1))).map_basepoint]
        -- LHS: mkConeLoop at cone basepoint
        simp only [reducedCone, smashProduct, smashBasepoint, Quotient.lift_mk,
                   mkConeLoop, ContinuousMap.coe_mk]
        simp only [hbase_E, constLoop, Path.refl_apply]
        rw [smashQuotientMap_wedge_right]
        -- Goal: coneToCofiber(smashBasepoint) = pt Cf
        -- coneToCofiber.map_basepoint: coneToCofiber(pt C₊X) = pt Cf
        -- smashProduct X I₊ = reducedCone X = C₊ X, so basepoints are defeq
        exact (coneToCofiber (f.levelMap (n + 1))).map_basepoint
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- The structure map for the cofiber spectrum at level n.
    Maps Cf_n → Ω(Cf_{n+1}). -/
noncomputable def cofiberStructureMap (f : E ⟶ F) (n : ℕ) :
    cofiberSpaceAt f n ⟶ Ω (cofiberSpaceAt f (n + 1)) where
  toFun := Quotient.lift (cofiberStructureMapAux f n) (cofiberStructureMapAux_respects f n)
  continuous_toFun := by
    apply Continuous.quotient_lift
    -- Need continuity of cofiberStructureMapAux
    apply continuous_sum_dom.mpr
    constructor
    · -- On F_n: cofiberStructureMapF is continuous
      show Continuous (fun x => cofiberStructureMapF f n x)
      unfold cofiberStructureMapF
      exact (loopSpaceMap (cofiberInclusion (f.levelMap (n + 1)))).continuous.comp (F.ε n).continuous
    · -- On C(E_n): cofiberStructureMapCone is continuous
      show Continuous (fun c => cofiberStructureMapCone f n c)
      unfold cofiberStructureMapCone
      apply Continuous.quotient_lift
      -- mkConeLoop is continuous
      show Continuous (mkConeLoop f n)
      -- mkConeLoop produces a Path from a pair (a, t)
      -- The topology on Path/LoopSpaceType is induced from C(I, X)
      -- We need to show the induced map to C(I, X) is continuous
      rw [continuous_induced_rng]
      -- Goal: Continuous (fun p => (mkConeLoop f n p).toContinuousMap)
      -- The underlying function is: (a, t) ↦ (s ↦ coneToCofiber(smashQuotientMap(ε_E(a)(s), t)))
      -- Use the fact that C(I, X) has the compact-open topology
      -- and we can use ContinuousMap.continuous_of_continuous_uncurry
      apply ContinuousMap.continuous_of_continuous_uncurry
      -- Goal: Continuous (fun (p, s) => coneToCofiber(smashQuotientMap(ε_E(p.1)(s), p.2)))
      show Continuous (fun ps : ((E.spaceAt n).carrier × pointedUnitInterval.carrier) × unitInterval =>
        (coneToCofiber (f.levelMap (n + 1))).toFun
          (smashQuotientMap (E.spaceAt (n + 1)) pointedUnitInterval
            (((E.ε n).toFun ps.1.1).toContinuousMap ps.2, ps.1.2)))
      apply (coneToCofiber (f.levelMap (n + 1))).continuous.comp
      apply (continuous_smashQuotientMap _ _).comp
      apply Continuous.prodMk
      · -- Continuous in ((a, t), s) ↦ ε_E(a)(s)
        -- ε_E(a) is a Path, and Path.toContinuousMap gives C(I, X)
        -- Evaluation C(I, X) × I → X is continuous
        -- First factor through the Path → C(I, X) embedding
        have hε : Continuous (fun a : (E.spaceAt n).carrier =>
            ((E.ε n).toFun a).toContinuousMap) := by
          -- Path.toContinuousMap is continuous (paths have the subspace topology from C(I, X))
          exact continuous_induced_dom.comp (E.ε n).continuous
        -- Now we need ((a,t), s) ↦ ε_E(a).toContinuousMap(s)
        have h1 : Continuous (fun ps : ((E.spaceAt n).carrier × pointedUnitInterval.carrier) × unitInterval =>
            (((E.ε n).toFun ps.1.1).toContinuousMap, ps.2)) := by
          apply Continuous.prodMk
          · exact hε.comp (continuous_fst.comp continuous_fst)
          · exact continuous_snd
        exact Continuous.comp continuous_eval h1
      · -- Continuous in ((a, t), s) ↦ t
        exact continuous_snd.comp continuous_fst
  map_basepoint := by
    show Quotient.lift _ _ (Quotient.mk _ (Sum.inl (F.spaceAt n).basepoint)) = _
    simp only [Quotient.lift_mk, cofiberStructureMapAux, cofiberStructureMapF]
    -- ε_F(basepoint) = constLoop
    have hbase : (F.ε n).toFun (F.spaceAt n).basepoint = constLoop (F.spaceAt (n + 1)) :=
      (F.ε n).map_basepoint
    simp only [hbase]
    -- Ω(cofiberInclusion)(constLoop) = constLoop
    apply Path.ext
    funext s
    simp only [loopSpaceMap, constLoop]
    exact (cofiberInclusion (f.levelMap (n + 1))).map_basepoint

/-- The cofiber spectrum of a spectrum map f : E → F.
    Level n is the mapping cone of f_n : E_n → F_n.
    Structure maps are induced from the compatibility of mapping cones
    with the suspension-loop adjunction. -/
noncomputable def cofiberSpectrum (f : E ⟶ F) : Spectrum where
  space := fun n => cofiberSpaceAt f n
  structureMap := fun n => cofiberStructureMap f n

/-- Notation for the cofiber spectrum. -/
scoped notation "Cf(" f ")" => cofiberSpectrum f

end CofiberSpectrum

/-! ## Cofiber Sequence of Spectra

The cofiber sequence E → F → Cf gives rise to a long exact sequence
of stable homotopy groups. -/

section CofiberSequence

variable (f : E ⟶ F)

/-- The inclusion of F into the cofiber spectrum Cf(f).
    At each level, this is the standard cofiber inclusion F_n → Cf_n. -/
def cofiberInclusionSpectrum (f : E ⟶ F) : F ⟶ cofiberSpectrum f where
  levelMap := fun n => cofiberInclusion (f.levelMap n)
  comm := fun n => by
    -- Need to show: F.ε n ≫ Ω(cofiberInclusion f_{n+1}) = cofiberInclusion f_n ≫ cofiberStructureMap f n
    -- Since cofiberStructureMap is currently defined using constLoop,
    -- this requires the proper definition
    sorry

/-- The connecting map from the cofiber spectrum to the shifted E spectrum.
    At each level, this is the connecting map Cf_n → Σ(E_n). -/
def connectingMapSpectrum (f : E ⟶ F) : cofiberSpectrum f ⟶ suspensionSpectrum (E.spaceAt 0) := by
  -- This requires more infrastructure about the shifted spectrum
  -- and how the connecting maps at each level assemble
  sorry

end CofiberSequence

/-! ## Long Exact Sequence for Stable Homotopy Groups

The main theorem: for a spectrum map f : E → F, there is a long exact sequence:
  ... → π_k(E) → π_k(F) → π_k(Cf) → π_{k-1}(E) → ...
-/

section LongExactSequence

variable (f : E ⟶ F)

/-- The induced map f_* : π_k(E) → π_k(F) on stable homotopy groups. -/
noncomputable def stableπ_f (k : ℤ) :
    StableHomotopyGroup E k → StableHomotopyGroup F k :=
  stableπInduced f k

/-- The induced map i_* : π_k(F) → π_k(Cf) from the cofiber inclusion. -/
noncomputable def stableπ_i (k : ℤ) :
    StableHomotopyGroup F k → StableHomotopyGroup (cofiberSpectrum f) k :=
  stableπInduced (cofiberInclusionSpectrum f) k

/-- Exactness at F: im(f_*) = ker(i_*).
    This states that a class in π_k(F) comes from π_k(E) iff it vanishes in π_k(Cf). -/
theorem exact_at_F (k : ℤ) :
    ∀ y : StableHomotopyGroup F k,
      (∃ x : StableHomotopyGroup E k, stableπ_f f k x = y) ↔
      stableπ_i f k y = StableHomotopyGroup.mk (cofiberSpectrum f) k
        (groupStartIndex k)
        (Nat.le_max_left _ _)
        ⟦GenLoop.const⟧ := by
  intro y
  constructor
  · -- Forward: image of f maps to zero in Cf
    intro ⟨x, hx⟩
    -- This follows from the cofiber sequence property at each level
    sorry
  · -- Backward: kernel of i can be lifted through f
    intro hy
    -- This requires the fiber sequence exactness
    sorry

/-- The long exact sequence property: the composition f_* followed by i_* is trivial.
    This is part of the exactness: im(f_*) ⊆ ker(i_*). -/
theorem longExactSequence_composition_trivial (k : ℤ) :
    ∀ x : StableHomotopyGroup E k,
      stableπ_i f k (stableπ_f f k x) = StableHomotopyGroup.mk (cofiberSpectrum f) k
        (groupStartIndex k)
        (Nat.le_max_left _ _)
        ⟦GenLoop.const⟧ := by
  -- This follows from the cofiber sequence property at each level:
  -- the composition E_n → F_n → Cf_n is nullhomotopic
  sorry

end LongExactSequence

/-! ## Distinguished Triangles (Preview)

The cofiber sequence defines distinguished triangles in the stable homotopy category.
This is the foundation for the triangulated structure.

A distinguished triangle is:
  E → F → Cf → E[1]

where E[1] is the shift (suspension) of E. -/

section DistinguishedTriangles

/-- The shift functor on spectra: E[1]_n = E_{n+1}.
    This is the categorical suspension in the stable homotopy category. -/
def shiftSpectrum (E : Spectrum) : Spectrum where
  space := fun n => E.spaceAt (n + 1)
  structureMap := fun n => E.ε (n + 1)

/-- Notation for shifted spectrum. -/
scoped notation E "[1]" => shiftSpectrum E

/-- A distinguished triangle consists of three spectrum maps forming a triangle. -/
structure DistinguishedTriangle where
  /-- First vertex -/
  E : Spectrum
  /-- Second vertex -/
  F : Spectrum
  /-- Third vertex (typically the cofiber) -/
  C : Spectrum
  /-- First map: E → F -/
  f : E ⟶ F
  /-- Second map: F → C -/
  g : F ⟶ C
  /-- Third map: C → E[1] (connecting map) -/
  h : C ⟶ shiftSpectrum E

/-- A cofiber triangle: E → F → Cf → E[1]. -/
noncomputable def cofiberTriangle (f : E ⟶ F) : DistinguishedTriangle := by
  refine {
    E := E
    F := F
    C := cofiberSpectrum f
    f := f
    g := cofiberInclusionSpectrum f
    h := ?h
  }
  -- The connecting map Cf → E[1]
  -- This requires showing that the connecting maps at each level assemble
  sorry

end DistinguishedTriangles

end Spectrum

end Topology
