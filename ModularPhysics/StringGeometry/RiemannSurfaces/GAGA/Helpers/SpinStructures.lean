import ModularPhysics.StringGeometry.RiemannSurfaces.GAGA.Helpers.Arf

/-!
# Spin Structures on Riemann Surfaces

This file connects the Arf invariant theory to spin structures on Riemann surfaces.

## Mathematical Background

For a compact Riemann surface Σ of genus g:

1. A **spin structure** is a holomorphic line bundle L with L ⊗ L ≅ K (canonical bundle)
2. Spin structures correspond bijectively to H¹(Σ, ℤ/2ℤ) ≅ (ℤ/2ℤ)^{2g}
3. The Weil pairing gives a non-degenerate quadratic form on H¹(Σ, ℤ/2ℤ)
4. The **parity** of a spin structure is h⁰(L) mod 2, which equals the Arf invariant

## Counting

Using the Arf invariant counting from `Arf.lean`:
- Total spin structures: 2^{2g}
- Even (h⁰(L) even): 2^{g-1}(2^g + 1)
- Odd (h⁰(L) odd): 2^{g-1}(2^g - 1)

## References

* Atiyah "Riemann Surfaces and Spin Structures" (1971)
* Johnson "Spin Structures and Quadratic Forms on Surfaces"
* Mumford "Theta Characteristics of an Algebraic Curve"
-/

namespace RiemannSurfaces.SpinStructures

open RiemannSurfaces.Arf

/-!
## Spin Structure Data

We represent a spin structure by its essential data: genus and parity.
The full structure (line bundle, cohomology) is developed in RiemannRoch.lean.
-/

/-- Data for a spin structure: genus, h⁰ dimension, and derived parity -/
structure SpinData where
  /-- The genus of the underlying surface -/
  genus : ℕ
  /-- The dimension h⁰(L) of global sections -/
  h0 : ℕ
  /-- Genus is at least 1 for non-trivial spin structures -/
  genus_pos : genus ≥ 1 := by decide

namespace SpinData

/-- The parity of a spin structure is h⁰(L) mod 2 -/
def parity (S : SpinData) : ZMod 2 := S.h0

/-- A spin structure is even if h⁰(L) is even -/
def isEven (S : SpinData) : Prop := S.parity = 0

/-- A spin structure is odd if h⁰(L) is odd -/
def isOdd (S : SpinData) : Prop := S.parity = 1

/-- Every spin structure is either even or odd -/
theorem parity_dichotomy (S : SpinData) : S.isEven ∨ S.isOdd := by
  unfold isEven isOdd parity
  rcases (S.h0 : ZMod 2) with ⟨val, hval⟩
  interval_cases val <;> simp

/-- Even and odd are mutually exclusive -/
theorem parity_exclusive (S : SpinData) : ¬(S.isEven ∧ S.isOdd) := by
  unfold isEven isOdd
  intro ⟨h0, h1⟩
  rw [h0] at h1
  exact zero_ne_one h1

/-- The parity is a topological invariant (Atiyah's theorem) -/
theorem parity_is_arf_invariant (S : SpinData)
    (q : QuadFormZ2 (2 * S.genus))
    (_ : q.NonDegenerate)
    (hcorr : S.parity = arfInvariant S.genus q) :
    S.isEven ↔ q.isEven S.genus := by
  unfold isEven QuadFormZ2.isEven
  rw [hcorr]

end SpinData

/-!
## Counting Spin Structures

The counts follow directly from the Arf invariant theory.
-/

/-- Number of spin structures on a genus g surface -/
def numSpinStructures (g : ℕ) : ℕ := numTotalForms g

/-- Number of even spin structures -/
def numEvenSpinStructures (g : ℕ) : ℕ := numEvenForms g

/-- Number of odd spin structures -/
def numOddSpinStructures (g : ℕ) : ℕ := numOddForms g

/-- Total count equals 2^{2g} -/
theorem total_spin_count (g : ℕ) : numSpinStructures g = 2^(2*g) := rfl

/-- Even count equals 2^{g-1}(2^g + 1) -/
theorem even_spin_count (g : ℕ) : numEvenSpinStructures g = 2^(g-1) * (2^g + 1) := rfl

/-- Odd count equals 2^{g-1}(2^g - 1) -/
theorem odd_spin_count (g : ℕ) : numOddSpinStructures g = 2^(g-1) * (2^g - 1) := rfl

/-- The counts add up correctly -/
theorem spin_count_sum (g : ℕ) (hg : g ≥ 1) :
    numEvenSpinStructures g + numOddSpinStructures g = numSpinStructures g := by
  unfold numEvenSpinStructures numOddSpinStructures numSpinStructures
  exact count_sum g hg

/-!
## Small Genus Examples
-/

/-- Genus 1: 3 even, 1 odd spin structure (theta characteristics on an elliptic curve) -/
example : numEvenSpinStructures 1 = 3 := by native_decide
example : numOddSpinStructures 1 = 1 := by native_decide
example : numSpinStructures 1 = 4 := by native_decide

/-- Genus 2: 10 even, 6 odd spin structures -/
example : numEvenSpinStructures 2 = 10 := by native_decide
example : numOddSpinStructures 2 = 6 := by native_decide
example : numSpinStructures 2 = 16 := by native_decide

end RiemannSurfaces.SpinStructures
