/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import ModularPhysics.StringGeometry.Supermanifolds.Superalgebra
import ModularPhysics.StringGeometry.Supermanifolds.SuperRingCat

/-!
# Sheaf of Superfunctions on Super Domains

This file defines the structure sheaf of the super domain ℝ^{p|q}.

## Mathematical Background

For a super domain ℝ^{p|q}, the structure sheaf assigns to each open U ⊆ ℝ^p:

  **O(U) = C^∞(U, ℝ) ⊗_ℝ ∧(ℝ^q)**

where:
- C^∞(U, ℝ) is the ring of smooth ℝ-valued functions on U
- ∧(ℝ^q) is the exterior algebra on q generators (finite-dimensional, dim = 2^q)

Sections have the form:
  f(x,θ) = Σ_I f_I(x) θ^I

where:
- I ranges over subsets of {1,...,q}
- f_I : U → ℝ are smooth functions (the coefficients)
- θ^I = θ^{i₁} ∧ ... ∧ θ^{i_k} for I = {i₁ < ... < i_k}

### Distinction: Fermionic Coordinates vs Grassmann Algebra

- **q** in ℝ^{p|q}: The number of fermionic coordinates θ₁,...,θ_q
- **Coefficients f_I**: In the local model, these are ℝ-valued

For transition maps and families of supermanifolds, the coefficients can be
Grassmann algebra-valued (involving additional odd parameters η₁,...,η_s).
This is essential for super Riemann surfaces.

### Key Properties

1. **Polynomial in θ**: Sections are polynomial (not power series) in θ because θ² = 0

2. **Supercommutativity**: For homogeneous elements f, g:
   fg = (-1)^{|f||g|} gf
   where |f| is the parity (0 for even, 1 for odd)

3. **Stalks are local**: The stalk O_x has maximal ideal
   m_x = { f : f_∅(x) = 0 }
   with residue field ℝ

## References

* Witten, E. "Notes On Supermanifolds And Integration" (arXiv:1209.2199)
* Deligne, P., Morgan, J. "Notes on Supersymmetry"
-/

noncomputable section

open scoped Topology
open CategoryTheory TopologicalSpace

namespace Supermanifolds

/-!
## Coefficient Ring

For the basic super domain ℝ^{p|q}, coefficients are in ℝ.
For families or transition maps, we parameterize by an arbitrary coefficient ring.
-/

/-- The underlying space for ℝ^p -/
abbrev RealSpace (p : ℕ) := Fin p → ℝ

/-!
## Multi-Index Structure

A multi-index I ⊆ {0,...,q-1} represents the monomial θ^I = θ^{i₁} ∧ ... ∧ θ^{i_k}
where I = {i₁ < ... < i_k}.
-/

/-- The parity of a multi-index: even if |I| is even, odd otherwise -/
def multiIndexParity (I : Finset (Fin q)) : Parity :=
  if I.card % 2 = 0 then Parity.even else Parity.odd

/-- The sign for reordering θ^I · θ^J to θ^{I∪J}.
    Returns 0 if I ∩ J ≠ ∅ (since θ_i² = 0).
    Otherwise returns (-1)^{inversions} where inversions counts pairs
    (i,j) with i ∈ I, j ∈ J, j < i. -/
def reorderSign {q : ℕ} (I J : Finset (Fin q)) : ℤ :=
  if I ∩ J = ∅ then
    let inversions := (I ×ˢ J).filter (fun ⟨i, j⟩ => j < i)
    (-1) ^ inversions.card
  else 0

/-!
## Structure Sheaf Sections

A section of the structure sheaf over U is a collection of smooth coefficient
functions {f_I : U → ℝ}_I indexed by multi-indices I ⊆ {0,...,q-1}.

This represents f(x,θ) = Σ_I f_I(x) θ^I.
-/

/-- A section of the structure sheaf of ℝ^{p|q} over an open set U ⊆ ℝ^p.

    Represented as a family of smooth coefficient functions f_I : U → ℝ
    for each multi-index I ⊆ {0,...,q-1}.

    The section represents: f(x,θ) = Σ_I f_I(x) θ^I -/
structure SuperSection (p q : ℕ) (U : Set (RealSpace p)) where
  /-- Coefficient f_I for each multi-index I ⊆ {0,...,q-1} -/
  coeffs : Finset (Fin q) → (RealSpace p → ℝ)
  /-- Each coefficient is smooth on U -/
  smooth : ∀ I, ContDiffOn ℝ ⊤ (coeffs I) U

namespace SuperSection

variable {p q : ℕ} {U : Set (RealSpace p)}

/-- Strong extensionality: two sections are equal if coefficient functions are equal.
    This is the definitional equality of the underlying data. -/
@[ext]
theorem ext {f g : SuperSection p q U}
    (h : ∀ I, f.coeffs I = g.coeffs I) : f = g := by
  cases f with | mk fc fs =>
  cases g with | mk gc gs =>
  simp only [mk.injEq]
  funext I
  exact h I

/-- Weak extensionality: two sections are equal if they agree on U.
    This requires that the sections were constructed to be equal outside U as well,
    which is the case for most natural constructions (addition, multiplication, etc.). -/
theorem ext_on {f g : SuperSection p q U}
    (h : ∀ I x, x ∈ U → f.coeffs I x = g.coeffs I x)
    (h_outside : ∀ I x, x ∉ U → f.coeffs I x = g.coeffs I x) : f = g := by
  ext I x
  by_cases hx : x ∈ U
  · exact h I x hx
  · exact h_outside I x hx

/-!
### Algebraic Operations

The algebraic operations on sections are defined pointwise using the
exterior algebra multiplication rules.
-/

/-- Zero section: all coefficients are zero -/
protected def zero : SuperSection p q U where
  coeffs _ _ := 0
  smooth _ := contDiffOn_const

/-- Unit section: 1 = θ^∅ (the empty product) -/
protected def one : SuperSection p q U where
  coeffs I := if I = ∅ then fun _ => 1 else fun _ => 0
  smooth I := by split_ifs <;> exact contDiffOn_const

/-- Addition: (f + g)_I = f_I + g_I -/
protected def add (f g : SuperSection p q U) : SuperSection p q U where
  coeffs I x := f.coeffs I x + g.coeffs I x
  smooth I := (f.smooth I).add (g.smooth I)

/-- Negation: (-f)_I = -f_I -/
protected def neg (f : SuperSection p q U) : SuperSection p q U where
  coeffs I x := -(f.coeffs I x)
  smooth I := (f.smooth I).neg

/-- Subtraction: (f - g)_I = f_I - g_I -/
protected def sub (f g : SuperSection p q U) : SuperSection p q U where
  coeffs I x := f.coeffs I x - g.coeffs I x
  smooth I := (f.smooth I).sub (g.smooth I)

/-- Scalar multiplication: (c • f)_I = c · f_I -/
protected def smul (c : ℝ) (f : SuperSection p q U) : SuperSection p q U where
  coeffs I x := c * f.coeffs I x
  smooth I := contDiffOn_const.mul (f.smooth I)

/-- Multiplication using exterior algebra rules:
    (f · g)_K = Σ_{I ∪ J = K, I ∩ J = ∅} sign(I,J) · f_I · g_J -/
protected def mul (f g : SuperSection p q U) : SuperSection p q U where
  coeffs K x :=
    Finset.univ.sum fun I =>
      Finset.univ.sum fun J =>
        if I ∪ J = K ∧ I ∩ J = ∅ then
          reorderSign I J * f.coeffs I x * g.coeffs J x
        else 0
  smooth K := by
    apply ContDiffOn.sum; intro I _
    apply ContDiffOn.sum; intro J _
    split_ifs with h
    · exact ((contDiffOn_const.mul (f.smooth I)).mul (g.smooth J))
    · exact contDiffOn_const

/-- Natural number scalar multiplication -/
protected def nsmul (n : ℕ) (f : SuperSection p q U) : SuperSection p q U where
  coeffs I x := n * f.coeffs I x
  smooth I := contDiffOn_const.mul (f.smooth I)

/-- Integer scalar multiplication -/
protected def zsmul (n : ℤ) (f : SuperSection p q U) : SuperSection p q U where
  coeffs I x := n * f.coeffs I x
  smooth I := contDiffOn_const.mul (f.smooth I)

instance : Zero (SuperSection p q U) := ⟨SuperSection.zero⟩
instance : One (SuperSection p q U) := ⟨SuperSection.one⟩
instance : Add (SuperSection p q U) := ⟨SuperSection.add⟩
instance : Neg (SuperSection p q U) := ⟨SuperSection.neg⟩
instance : Sub (SuperSection p q U) := ⟨SuperSection.sub⟩
instance : Mul (SuperSection p q U) := ⟨SuperSection.mul⟩
instance : SMul ℝ (SuperSection p q U) := ⟨SuperSection.smul⟩
instance : SMul ℕ (SuperSection p q U) := ⟨SuperSection.nsmul⟩
instance : SMul ℤ (SuperSection p q U) := ⟨SuperSection.zsmul⟩

/-!
### Simp Lemmas for Coefficients
-/

@[simp] theorem zero_coeffs' (I : Finset (Fin q)) (x : RealSpace p) :
    (SuperSection.zero : SuperSection p q U).coeffs I x = 0 := rfl

@[simp] theorem one_coeffs' (I : Finset (Fin q)) (x : RealSpace p) :
    (SuperSection.one : SuperSection p q U).coeffs I x = if I = ∅ then 1 else 0 := by
  simp only [SuperSection.one]; split_ifs <;> rfl

@[simp] theorem add_coeffs' (f g : SuperSection p q U) (I : Finset (Fin q)) (x : RealSpace p) :
    (SuperSection.add f g).coeffs I x = f.coeffs I x + g.coeffs I x := rfl

@[simp] theorem neg_coeffs' (f : SuperSection p q U) (I : Finset (Fin q)) (x : RealSpace p) :
    (SuperSection.neg f).coeffs I x = -(f.coeffs I x) := rfl

@[simp] theorem sub_coeffs' (f g : SuperSection p q U) (I : Finset (Fin q)) (x : RealSpace p) :
    (SuperSection.sub f g).coeffs I x = f.coeffs I x - g.coeffs I x := rfl

@[simp] theorem smul_coeffs' (c : ℝ) (f : SuperSection p q U) (I : Finset (Fin q)) (x : RealSpace p) :
    (SuperSection.smul c f).coeffs I x = c * f.coeffs I x := rfl

theorem mul_coeffs' (f g : SuperSection p q U) (K : Finset (Fin q)) (x : RealSpace p) :
    (SuperSection.mul f g).coeffs K x = Finset.univ.sum fun I =>
      Finset.univ.sum fun J =>
        if I ∪ J = K ∧ I ∩ J = ∅ then
          reorderSign I J * f.coeffs I x * g.coeffs J x
        else 0 := rfl

/-!
### The Body Map

The body of a section is its degree-0 component (the I = ∅ coefficient).
This represents evaluation at θ = 0.
-/

/-- The body of a section: the coefficient of θ^∅ = 1 -/
def body (f : SuperSection p q U) : RealSpace p → ℝ := f.coeffs ∅

/-- Body is smooth -/
theorem body_smooth (f : SuperSection p q U) : ContDiffOn ℝ ⊤ f.body U :=
  f.smooth ∅

/-- Body of 1 is the constant 1 -/
@[simp] theorem body_one : (SuperSection.one : SuperSection p q U).body = fun _ => 1 := by
  funext x; simp [body, SuperSection.one]

/-- Body of 0 is the constant 0 -/
@[simp] theorem body_zero : (SuperSection.zero : SuperSection p q U).body = fun _ => 0 := by
  funext x; simp [body, SuperSection.zero]

/-- Body is additive -/
@[simp] theorem body_add (f g : SuperSection p q U) :
    (SuperSection.add f g).body = fun x => f.body x + g.body x := by
  funext x; simp [body, SuperSection.add]

/-- Body is multiplicative -/
theorem body_mul (f g : SuperSection p q U) (x : RealSpace p) :
    (SuperSection.mul f g).body x = f.body x * g.body x := by
  simp only [body, mul_coeffs']
  rw [Finset.sum_eq_single ∅, Finset.sum_eq_single ∅]
  · simp [reorderSign]
  · intro J _ hJ
    simp only [Finset.empty_union, Finset.empty_inter]
    split_ifs with h
    · simp only [and_true] at h
      exact absurd h hJ
    · rfl
  · intro h; exact absurd (Finset.mem_univ ∅) h
  · intro I _ hI
    rw [Finset.sum_eq_zero]; intro J _
    split_ifs with h
    · have : I = ∅ := Finset.union_eq_empty.mp h.1 |>.1
      exact absurd this hI
    · rfl
  · intro h; exact absurd (Finset.mem_univ ∅) h

/-!
### Restriction

Restriction of sections to smaller open sets.
-/

/-- Restriction to a smaller open set -/
def restrict {V : Set (RealSpace p)} (hVU : V ⊆ U)
    (f : SuperSection p q U) : SuperSection p q V where
  coeffs := f.coeffs
  smooth I := (f.smooth I).mono hVU

@[simp] theorem restrict_coeffs {V : Set (RealSpace p)} (hVU : V ⊆ U)
    (f : SuperSection p q U) (I : Finset (Fin q)) :
    (f.restrict hVU).coeffs I = f.coeffs I := rfl

/-!
### Parity

Even and odd parts of sections.
-/

/-- A section is even if all odd-degree coefficients vanish -/
def isEven (f : SuperSection p q U) : Prop :=
  ∀ I, multiIndexParity I = Parity.odd → f.coeffs I = fun _ => 0

/-- A section is odd if all even-degree coefficients vanish -/
def isOdd (f : SuperSection p q U) : Prop :=
  ∀ I, multiIndexParity I = Parity.even → f.coeffs I = fun _ => 0

end SuperSection

/-!
## The Structure Presheaf

We define the presheaf of super sections on ℝ^p.
-/

/-- The presheaf of super sections on ℝ^p.

    This assigns to each open U the sections O(U) = C^∞(U,ℝ) ⊗ ∧(ℝ^q). -/
def superPresheaf (p q : ℕ) : TopCat.Presheaf (Type) (TopCat.of (RealSpace p)) where
  obj U := SuperSection p q U.unop
  map {U V} f := fun s => s.restrict (leOfHom f.unop)
  map_id U := by funext s; rfl
  map_comp {U V W} f g := by funext s; rfl

/-!
## Grassmann-Valued Coefficients for Transition Maps

For transition maps between charts and families of supermanifolds,
the coefficients can be Grassmann algebra-valued.

A transition map φ : U → ℝ^{p'|q} has:
- Even coordinates: x'_i = f^i_0(x) + θ^j f^i_j(x) + ...
- Odd coordinates: θ'_s = ψ^s_j(x) θ^j + ...

where the coefficients f^i_I and ψ^s_I can be in a Grassmann algebra
(e.g., for families parametrized by odd moduli).
-/

-- TODO: Define SuperMap with Grassmann-valued coefficients
-- This requires parametrizing by an external Grassmann algebra
-- for the coefficients, separate from the θ coordinates.

end Supermanifolds

end
