/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.Topology.Spectra.HomotopyGroups

/-!
# Examples of Spectra

This file provides additional examples and properties of spectra beyond the basic
definitions in `Basic.lean`.

## Main Definitions

* Properties of suspension spectra
* Properties of the sphere spectrum
* Shift operation on spectra
* Functoriality of the suspension spectrum construction

## Mathematical Background

### Suspension Spectrum Σ^∞X
For a pointed space X, the suspension spectrum Σ^∞X has:
- Level n: Σ^n X (n-fold reduced suspension)
- Structure map: η : Σ^n X → Ω(Σ^{n+1} X) (adjunction unit)

### Sphere Spectrum 𝕊
The sphere spectrum 𝕊 = Σ^∞S⁰ is the suspension spectrum of the 0-sphere.
It is the unit for the smash product of spectra.

### Trivial Spectrum
All spaces are the one-point space. This is an Ω-spectrum (proved).

Note: Eilenberg-MacLane spectra are defined separately in `EilenbergMacLane.lean`.

## References

* Adams, "Stable Homotopy and Generalised Homology"
* May, "A Concise Course in Algebraic Topology", Chapter 22
-/

universe u

open CategoryTheory PointedTopSpace

namespace Topology

namespace Spectrum

/-! ## Properties of Suspension Spectra -/

section SuspensionSpectrum

variable (X Y : PointedTopSpace.{0})

/-- The level-0 space of the suspension spectrum is X itself. -/
theorem suspensionSpectrum_level_zero : (suspensionSpectrum X).spaceAt 0 = X := rfl

/-- The level-1 space of the suspension spectrum is ΣX. -/
theorem suspensionSpectrum_level_one : (suspensionSpectrum X).spaceAt 1 = Σ₊ X := rfl

/-- The level-n space of the suspension spectrum is Σ^n X. -/
theorem suspensionSpectrum_level_n (n : ℕ) :
    (suspensionSpectrum X).spaceAt n = iteratedSuspension n X := rfl

/-- The n-fold iterated suspension of a map. -/
def iteratedSuspensionMap {X Y : PointedTopSpace} (f : X ⟶ Y) :
    ∀ (n : ℕ), iteratedSuspension n X ⟶ iteratedSuspension n Y
  | 0 => f
  | n + 1 => suspensionMap (iteratedSuspensionMap f n)

/-- A pointed map f : X → Y induces a spectrum map Σ^∞f : Σ^∞X → Σ^∞Y. -/
noncomputable def suspensionSpectrumMap (f : X ⟶ Y) :
    suspensionSpectrum X ⟶ suspensionSpectrum Y where
  levelMap n := iteratedSuspensionMap f n
  comm n := by
    -- Need: ε_n ≫ Ω(Σ^∞f_{n+1}) = Σ^∞f_n ≫ ε_n
    -- This is the naturality of the suspension unit η
    -- E.ε n = suspensionUnit (iteratedSuspension n X)
    -- levelMap n = iteratedSuspensionMap f n
    -- levelMap (n+1) = suspensionMap (iteratedSuspensionMap f n)
    show suspensionUnit (iteratedSuspension n X) ≫
           loopSpaceMap (suspensionMap (iteratedSuspensionMap f n)) =
         iteratedSuspensionMap f n ≫ suspensionUnit (iteratedSuspension n Y)
    exact (suspensionUnit_natural (iteratedSuspensionMap f n)).symm

end SuspensionSpectrum

/-! ## Properties of the Sphere Spectrum -/

section SphereSpectrum

/-- The sphere spectrum is the suspension spectrum of S⁰. -/
theorem sphereSpectrum_def : sphereSpectrum = suspensionSpectrum PointedTopSpace.sphere0 := rfl

/-- The level-0 space of the sphere spectrum is S⁰. -/
theorem sphereSpectrum_level_zero : sphereSpectrum.spaceAt 0 = PointedTopSpace.sphere0 := rfl

/-- The level-n space of the sphere spectrum is the n-sphere (as n-fold suspension of S⁰). -/
theorem sphereSpectrum_level_n (n : ℕ) :
    sphereSpectrum.spaceAt n = iteratedSuspension n PointedTopSpace.sphere0 := rfl

end SphereSpectrum

/-! ## Trivial Spectrum Properties -/

section TrivialSpectrum

/-- All spaces of the trivial spectrum are the one-point space. -/
theorem trivial_spaceAt (n : ℕ) : trivial.spaceAt n = PointedTopSpace.point := rfl

/-! ### GenLoop over Unit is a subsingleton -/

/-- Any element of GenLoop over Unit is equal to the constant loop.
    This is because Unit has only one element, so all functions into it are constant. -/
theorem genLoop_unit_eq_const (k : ℕ) (γ : GenLoop (Fin k) Unit ()) :
    γ = GenLoop.const := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro _
  -- Both γ.val x and GenLoop.const.val x are of type Unit, hence equal
  rfl

/-- GenLoop over Unit is a subsingleton. -/
instance genLoop_unit_subsingleton (k : ℕ) : Subsingleton (GenLoop (Fin k) Unit ()) where
  allEq := fun a b => by
    rw [genLoop_unit_eq_const k a, genLoop_unit_eq_const k b]

/-- Any two elements of HomotopyGroup.Pi over Unit are equal. -/
theorem homotopyGroup_unit_eq (k : ℕ) (a b : HomotopyGroup.Pi k Unit ()) : a = b := by
  induction a using Quotient.ind with
  | _ γ₁ =>
    induction b using Quotient.ind with
    | _ γ₂ =>
      apply Quotient.sound
      have heq : γ₁ = γ₂ := Subsingleton.elim γ₁ γ₂
      rw [heq]

/-- HomotopyGroup.Pi over Unit is a subsingleton. -/
instance homotopyGroup_unit_subsingleton (k : ℕ) : Subsingleton (HomotopyGroup.Pi k Unit ()) where
  allEq := homotopyGroup_unit_eq k

/-! ### Path in Unit is a subsingleton -/

/-- Any path in Unit is equal to the constant path. -/
theorem path_unit_eq_refl {a b : Unit} (p : Path a b) : p = Path.refl () := by
  apply Path.ext
  funext t
  rfl

/-- Path () () in Unit is a subsingleton. -/
instance path_unit_subsingleton : Subsingleton (Path (X := Unit) () ()) where
  allEq := fun p q => by
    rw [path_unit_eq_refl p, path_unit_eq_refl q]

/-- GenLoop over Path () () is a subsingleton.
    This is because Path () () itself is a subsingleton. -/
instance genLoop_path_unit_subsingleton (k : ℕ) :
    Subsingleton (GenLoop (Fin k) (Path (X := Unit) () ()) (Path.refl ())) where
  allEq := fun a b => by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro _
    exact Subsingleton.elim _ _

/-- HomotopyGroup.Pi over Path () () is a subsingleton. -/
instance homotopyGroup_path_unit_subsingleton (k : ℕ) :
    Subsingleton (HomotopyGroup.Pi k (Path (X := Unit) () ()) (Path.refl ())) where
  allEq := fun a b => by
    induction a using Quotient.ind with
    | _ γ₁ =>
      induction b using Quotient.ind with
      | _ γ₂ =>
        apply Quotient.sound
        have heq : γ₁ = γ₂ := Subsingleton.elim γ₁ γ₂
        rw [heq]

/-- The trivial spectrum is an Ω-spectrum.
    This is because the loop space of a point is a point, and the structure map
    point → Ω(point) = point is the identity (up to isomorphism). -/
theorem trivial_isOmegaSpectrum : IsOmegaSpectrum trivial := by
  intro n k
  -- Both source and target homotopy groups are subsingletons (trivial)
  -- Source: HomotopyGroup.Pi k (trivial.spaceAt n).carrier (trivial.spaceAt n).basepoint
  --       = HomotopyGroup.Pi k Unit ()
  -- Target: HomotopyGroup.Pi k (loopSpace (trivial.spaceAt (n+1))).carrier ...
  --       = HomotopyGroup.Pi k (Path () ()) (Path.refl ())
  have hss_src : Subsingleton (HomotopyGroup.Pi k (trivial.spaceAt n).carrier
      (trivial.spaceAt n).basepoint) := by
    -- trivial.spaceAt n = point = of Unit ()
    unfold Spectrum.spaceAt trivial
    simp only [point, of]
    exact homotopyGroup_unit_subsingleton k

  have hss_tgt : Subsingleton (HomotopyGroup.Pi k (loopSpace (trivial.spaceAt (n+1))).carrier
      (loopSpace (trivial.spaceAt (n+1))).basepoint) := by
    unfold Spectrum.spaceAt trivial loopSpace LoopSpaceType constLoop
    simp only [point, of]
    exact homotopyGroup_path_unit_subsingleton k

  -- Both are nonempty - they contain the class of the constant loop
  have hne_src : Nonempty (HomotopyGroup.Pi k (trivial.spaceAt n).carrier
      (trivial.spaceAt n).basepoint) := by
    unfold Spectrum.spaceAt trivial
    simp only [point, of]
    exact ⟨⟦GenLoop.const⟧⟩

  have hne_tgt : Nonempty (HomotopyGroup.Pi k (loopSpace (trivial.spaceAt (n+1))).carrier
      (loopSpace (trivial.spaceAt (n+1))).basepoint) := by
    unfold Spectrum.spaceAt trivial loopSpace LoopSpaceType constLoop
    simp only [point, of]
    exact ⟨⟦GenLoop.const⟧⟩

  constructor
  · -- Injective: both groups are subsingletons
    intro a b _
    exact hss_src.elim a b
  · -- Surjective: take any element of source, it maps to the unique element
    intro b
    exact ⟨hne_src.some, hss_tgt.elim _ _⟩

end TrivialSpectrum

/-! ## Shifts of Spectra -/

section Shifts

/-- The shift of a spectrum by 1: (E[1])_n = E_{n+1}.
    This is the "desuspension" or "shift" operation on spectra. -/
def shiftSpectrum (E : Spectrum) : Spectrum where
  space n := E.space (n + 1)
  structureMap n := E.structureMap (n + 1)

/-- The iterated shift of a spectrum. -/
def iteratedShift (E : Spectrum) : ℕ → Spectrum
  | 0 => E
  | k + 1 => shiftSpectrum (iteratedShift E k)

/-- Shifting preserves the Ω-spectrum property. -/
theorem shiftSpectrum_isOmegaSpectrum (E : Spectrum) (hE : IsOmegaSpectrum E) :
    IsOmegaSpectrum (shiftSpectrum E) := by
  intro n
  exact hE (n + 1)

end Shifts

/-! ## Spectrum from Ω-Spectrum Data

For an Ω-spectrum, the structure maps are weak equivalences. This means we can
equivalently specify an Ω-spectrum by giving the spaces and showing the structure
maps are weak equivalences.
-/

section OmegaSpectrumConstruction

/-- Construct a spectrum from a sequence of spaces where the "delooping" maps
    f_n : X_n → ΩX_{n+1} are given. -/
def mkSpectrum (spaces : ℕ → PointedTopSpace)
    (structureMaps : ∀ n, spaces n ⟶ loopSpace (spaces (n + 1))) : Spectrum where
  space := spaces
  structureMap := structureMaps

/-- The constructed spectrum is an Ω-spectrum if all structure maps are weak equivalences. -/
theorem mkSpectrum_isOmega (spaces : ℕ → PointedTopSpace)
    (structureMaps : ∀ n, spaces n ⟶ loopSpace (spaces (n + 1)))
    (hWeak : ∀ n, IsWeakHomotopyEquivalence (structureMaps n)) :
    IsOmegaSpectrum (mkSpectrum spaces structureMaps) :=
  hWeak

end OmegaSpectrumConstruction

end Spectrum

end Topology
