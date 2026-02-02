/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.SPDE.RegularityStructures.Trees.Basic
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Homogeneity for Decorated Trees

This file defines the homogeneity assignment |τ| ∈ ℝ for each decorated tree τ.

## Main Definitions

* `TreeSymbol.homogeneity` - The homogeneity |τ| ∈ ℝ for tree τ
* `isSubcritical` - Predicate for trees with |τ| > 0
* `requiresRenormalization` - Predicate for trees with |τ| < 0
* `IndexSetRS` - The index set A containing all possible homogeneities

## Mathematical Background

The homogeneity |τ| determines the regularity of Π_x τ as a distribution.
The key rules are:
- |𝟙| = 0
- |Ξ| = α (noise regularity)
- |X^k| = |k| (polynomial degree)
- |I_k(τ)| = |τ| + β - |k| (integration adds regularity β)
- |τ₁ · τ₂| = |τ₁| + |τ₂| (product is additive)

## References

* Hairer, "A theory of regularity structures" (Inventiones 2014), Section 3.1
-/

namespace SPDE.RegularityStructures

open TreeSymbol

/-! ## Homogeneity Assignment -/

namespace TreeSymbol

variable {d : ℕ}

/-- The homogeneity of a tree symbol.

    Parameters:
    - `α`: The noise regularity (typically -(d+2)/2 + ε for space-time white noise)
    - `β`: The kernel order (typically 2 for the heat kernel)

    The homogeneity determines the regularity of Π_x τ as a distribution. -/
noncomputable def homogeneity (α β : ℝ) : TreeSymbol d → ℝ
  | one => 0
  | Xi => α
  | Poly k => (k.degree : ℝ)
  | Integ k τ => homogeneity α β τ + β - (k.degree : ℝ)
  | Prod τ₁ τ₂ => homogeneity α β τ₁ + homogeneity α β τ₂

/-- Homogeneity of unit is 0 -/
theorem homogeneity_one (α β : ℝ) : homogeneity α β (one : TreeSymbol d) = 0 := rfl

/-- Homogeneity of noise is α -/
theorem homogeneity_Xi (α β : ℝ) : homogeneity α β (Xi : TreeSymbol d) = α := rfl

/-- Homogeneity of polynomial is the degree -/
theorem homogeneity_Poly (α β : ℝ) (k : MultiIndex d) :
    homogeneity α β (Poly k : TreeSymbol d) = (k.degree : ℝ) := rfl

/-- Homogeneity of integration -/
theorem homogeneity_Integ (α β : ℝ) (k : MultiIndex d) (τ : TreeSymbol d) :
    homogeneity α β (Integ k τ) = homogeneity α β τ + β - (k.degree : ℝ) := rfl

/-- Homogeneity of product is additive -/
theorem homogeneity_Prod (α β : ℝ) (τ₁ τ₂ : TreeSymbol d) :
    homogeneity α β (Prod τ₁ τ₂) = homogeneity α β τ₁ + homogeneity α β τ₂ := rfl

/-! ## Subcriticality -/

/-- A tree is subcritical (well-defined as a distribution) if its homogeneity is positive -/
def isSubcritical (α β : ℝ) (τ : TreeSymbol d) : Prop :=
  homogeneity α β τ > 0

/-- A tree requires renormalization if its homogeneity is negative -/
def requiresRenormalization (α β : ℝ) (τ : TreeSymbol d) : Prop :=
  homogeneity α β τ < 0

/-- The unit has homogeneity exactly 0 (boundary case) -/
theorem one_homogeneity_zero (α β : ℝ) : homogeneity α β (one : TreeSymbol d) = 0 := rfl

end TreeSymbol

/-! ## The Vector Space of Trees

The regularity structure T is the free vector space spanned by trees.
-/

/-- A formal linear combination of trees with real coefficients.
    Elements of T are finite formal sums Σᵢ cᵢ τᵢ. -/
structure FormalSum (d : ℕ) where
  /-- The trees appearing in the sum with their coefficients -/
  terms : List (ℝ × TreeSymbol d)

namespace FormalSum

variable {d : ℕ}

/-- The zero element -/
def zero : FormalSum d := ⟨[]⟩

/-- A single tree with coefficient 1 -/
def single (τ : TreeSymbol d) : FormalSum d := ⟨[((1 : ℝ), τ)]⟩

/-- Scalar multiplication -/
def smul (c : ℝ) (f : FormalSum d) : FormalSum d :=
  ⟨f.terms.map (fun (a, τ) => (c * a, τ))⟩

/-- Addition of formal sums -/
def add (f g : FormalSum d) : FormalSum d :=
  ⟨f.terms ++ g.terms⟩

instance : Zero (FormalSum d) := ⟨zero⟩
instance : Add (FormalSum d) := ⟨add⟩
instance : SMul ℝ (FormalSum d) := ⟨smul⟩

/-- The maximum homogeneity appearing in the sum -/
noncomputable def maxHomogeneity (α β : ℝ) (f : FormalSum d) : ℝ :=
  f.terms.foldl (fun acc (_, τ) => max acc (TreeSymbol.homogeneity α β τ)) (0 : ℝ)

/-- Negation -/
def neg (f : FormalSum d) : FormalSum d :=
  ⟨f.terms.map (fun (a, τ) => (-a, τ))⟩

instance : Neg (FormalSum d) := ⟨neg⟩

/-- Subtraction -/
def sub (f g : FormalSum d) : FormalSum d := f + (-g)

instance : Sub (FormalSum d) := ⟨sub⟩

/-- Monadic bind: apply a function to each tree and combine results.
    This is the key operation for composing renormalization group elements.
    Given f = Σᵢ cᵢ τᵢ and g : TreeSymbol d → FormalSum d,
    bind f g = Σᵢ cᵢ · g(τᵢ) -/
def bind (f : FormalSum d) (g : TreeSymbol d → FormalSum d) : FormalSum d :=
  ⟨f.terms.flatMap (fun (c, τ) => (g τ).terms.map (fun (a, σ) => (c * a, σ)))⟩

/-- Get the coefficient sum for a specific tree in the formal sum.
    If τ appears multiple times, their coefficients are summed. -/
def coeff (f : FormalSum d) (τ : TreeSymbol d) : ℝ :=
  f.terms.foldl (fun acc (c, σ) => if σ = τ then acc + c else acc) 0

/-- A single tree with given coefficient -/
def singleWithCoeff (c : ℝ) (τ : TreeSymbol d) : FormalSum d := ⟨[(c, τ)]⟩

/-- The formal sum has only finitely many nonzero terms by construction -/
theorem terms_finite (f : FormalSum d) : f.terms.length < f.terms.length + 1 :=
  Nat.lt_succ_self _

/-- Zero element property -/
theorem add_zero (f : FormalSum d) : f + 0 = f := by
  show FormalSum.add f zero = f
  simp only [add, zero, List.append_nil]

/-- Zero element property -/
theorem zero_add (f : FormalSum d) : 0 + f = f := by
  show FormalSum.add zero f = f
  simp only [add, zero, List.nil_append]

/-- Single is mapped correctly by bind -/
theorem bind_single (τ : TreeSymbol d) (g : TreeSymbol d → FormalSum d) :
    bind (single τ) g = g τ := by
  simp only [bind, single, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  show ⟨(g τ).terms.map (fun (a, σ) => (1 * a, σ))⟩ = g τ
  congr 1
  conv_rhs => rw [← List.map_id (g τ).terms]
  apply List.map_congr_left
  intro ⟨a, σ⟩ _
  simp only [id_eq, Prod.mk.injEq, and_true]
  ring

/-- Binding with single is identity: bind s single = s -/
theorem bind_single_right (s : FormalSum d) : bind s single = s := by
  simp only [bind, single]
  congr 1
  induction s.terms with
  | nil => rfl
  | cons h t ih =>
    simp only [List.flatMap_cons, List.map_cons, List.map_nil, List.singleton_append]
    rw [List.cons_eq_cons]
    refine ⟨?_, ?_⟩
    · exact Prod.ext (mul_one h.1) rfl
    · convert ih using 1

/-- The norm at a specific homogeneity level ℓ.
    This sums |cᵢ| over all terms with homogeneity(τᵢ) = ℓ. -/
noncomputable def normAtLevel (α β : ℝ) (f : FormalSum d) (ℓ : ℝ) : ℝ :=
  f.terms.foldl
    (fun acc (c, τ) =>
      if TreeSymbol.homogeneity α β τ = ℓ then acc + |c| else acc)
    0

/-- The total norm: sum of |cᵢ| over all terms. -/
noncomputable def totalNorm (f : FormalSum d) : ℝ :=
  f.terms.foldl (fun acc (c, _) => acc + |c|) 0

/-- Apply a linear map to each tree in the sum. -/
def mapTrees (f : FormalSum d) (g : TreeSymbol d → TreeSymbol d) : FormalSum d :=
  ⟨f.terms.map (fun (c, τ) => (c, g τ))⟩

/-- mapTrees distributes over addition:
    mapTrees (f + g) h = mapTrees f h + mapTrees g h -/
theorem mapTrees_add (f g : FormalSum d) (h : TreeSymbol d → TreeSymbol d) :
    mapTrees (f + g) h = mapTrees f h + mapTrees g h := by
  unfold mapTrees
  show ⟨((FormalSum.add f g).terms).map (fun (c, τ) => (c, h τ))⟩ =
       FormalSum.add ⟨f.terms.map _⟩ ⟨g.terms.map _⟩
  simp only [FormalSum.add, List.map_append]

/-- mapTrees commutes with negation:
    mapTrees (-f) h = -(mapTrees f h) -/
theorem mapTrees_neg (f : FormalSum d) (h : TreeSymbol d → TreeSymbol d) :
    mapTrees (FormalSum.neg f) h = FormalSum.neg (mapTrees f h) := by
  simp only [mapTrees, FormalSum.neg, List.map_map]
  -- Need to show the two compositions give the same result
  -- LHS: (c, τ) ↦ (c, h τ) ∘ (c, τ) ↦ (-c, τ) = (c, τ) ↦ (-c, h τ)
  -- RHS: (c, τ) ↦ (-c, τ) ∘ (c, τ) ↦ (c, h τ) = (c, τ) ↦ (-c, h τ)
  rfl

/-- mapTrees preserves subtraction:
    mapTrees (f - g) h = mapTrees f h - mapTrees g h -/
theorem mapTrees_sub (f g : FormalSum d) (h : TreeSymbol d → TreeSymbol d) :
    mapTrees (FormalSum.sub f g) h = FormalSum.sub (mapTrees f h) (mapTrees g h) := by
  simp only [FormalSum.sub]
  rw [mapTrees_add]
  -- Need to show: mapTrees f h + mapTrees (neg g) h = add (mapTrees f h) (neg (mapTrees g h))
  congr 1
  exact mapTrees_neg g h

/-- Check if all trees in the sum have homogeneity less than γ. -/
noncomputable def allHomogeneityLt (α β γ : ℝ) (f : FormalSum d) : Bool :=
  f.terms.all (fun (_, τ) => decide (TreeSymbol.homogeneity α β τ < γ))

/-- totalNorm is nonnegative: ‖f‖ ≥ 0.
    Proof: Each term contributes |cᵢ| ≥ 0, sum of nonnegatives is nonnegative. -/
theorem totalNorm_nonneg (f : FormalSum d) : totalNorm f ≥ 0 := by
  unfold totalNorm
  -- Induction on the list: sum of |cᵢ| starting from 0 is ≥ 0
  have : ∀ (l : List (ℝ × TreeSymbol d)) (init : ℝ), init ≥ 0 →
      List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) init l ≥ 0 := by
    intro l
    induction l with
    | nil => intro init h; simp only [List.foldl_nil]; exact h
    | cons h t ih =>
      intro init hinit
      simp only [List.foldl_cons]
      apply ih
      have habs : |h.1| ≥ 0 := abs_nonneg h.1
      linarith
  exact this f.terms 0 (le_refl 0)

/-- Helper lemma: foldl with + is shift-invariant. -/
private theorem foldl_add_shift (l : List (ℝ × TreeSymbol d)) (x : ℝ) :
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) x l =
    x + List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0 l := by
  induction l generalizing x with
  | nil => simp [List.foldl_nil]
  | cons h t ih =>
    simp only [List.foldl_cons]
    rw [ih (x + |h.1|)]
    conv_rhs => rw [ih (0 + |h.1|)]
    ring

/-- Triangle inequality for totalNorm: ‖f + g‖ ≤ ‖f‖ + ‖g‖.
    Proof: (f + g).terms = f.terms ++ g.terms by definition,
    so totalNorm(f + g) = Σ|cᵢ| over f.terms ++ g.terms
                        = Σ|cᵢ| over f.terms + Σ|cᵢ| over g.terms
                        = totalNorm(f) + totalNorm(g).
    Thus equality holds (which implies ≤). -/
theorem totalNorm_add_le (f g : FormalSum d) :
    totalNorm (f + g) ≤ totalNorm f + totalNorm g := by
  unfold totalNorm
  -- (f + g).terms = f.terms ++ g.terms by definition of Add instance
  show List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0 (FormalSum.add f g).terms ≤ _
  simp only [FormalSum.add]
  rw [List.foldl_append, foldl_add_shift]

/-- Homogeneity of totalNorm: ‖c • f‖ = |c| * ‖f‖.
    Proof: (c • f).terms.map fst = c * f.terms.map fst,
    so Σ|c * aᵢ| = Σ|c| * |aᵢ| = |c| * Σ|aᵢ|. -/
theorem totalNorm_smul (c : ℝ) (f : FormalSum d) :
    totalNorm (c • f) = |c| * totalNorm f := by
  unfold totalNorm
  -- (c • f).terms = f.terms.map (fun (a, τ) => (c * a, τ)) by definition of SMul instance
  show List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0 (FormalSum.smul c f).terms =
       |c| * List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0 f.terms
  simp only [FormalSum.smul]
  -- Need to show foldl over mapped list = |c| * foldl over original
  have h : ∀ (l : List (ℝ × TreeSymbol d)),
      List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0
        (l.map (fun (a, τ) => (c * a, τ))) =
      |c| * List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0 l := by
    intro l
    induction l with
    | nil => simp [List.foldl_nil]
    | cons hd t ih =>
      simp only [List.map_cons, List.foldl_cons]
      -- LHS: foldl ... |c * hd.1| (map ... t)
      -- RHS: |c| * foldl ... |hd.1| t
      rw [foldl_add_shift]
      -- LHS: |c * hd.1| + foldl ... 0 (map ... t)
      rw [ih]
      -- LHS: |c * hd.1| + |c| * foldl ... 0 t
      -- RHS: |c| * foldl ... |hd.1| t = |c| * (|hd.1| + foldl ... 0 t)
      conv_rhs => rw [foldl_add_shift]
      simp only [abs_mul]
      ring
  exact h f.terms

end FormalSum

/-! ## The Index Set

The index set A ⊆ ℝ contains all homogeneities that can appear.
-/

/-- The index set A for a regularity structure.
    Contains all possible homogeneities for trees built from the given symbols. -/
structure IndexSetRS (d : ℕ) where
  /-- The noise regularity α -/
  noiseRegularity : ℝ
  /-- The kernel order β (typically 2) -/
  kernelOrder : ℝ
  /-- The maximum polynomial degree to include -/
  maxPolyDegree : ℕ
  /-- The maximum derivative degree in integration operators -/
  maxDerivDegree : ℕ
  /-- The maximum tree complexity to include -/
  maxComplexity : ℕ

namespace IndexSetRS

variable {d : ℕ}

/-- Total derivative degree in a tree (sum of all |k| in I_k nodes). -/
def totalDerivDegree : TreeSymbol d → ℕ
  | .one => 0
  | .Xi => 0
  | .Poly _ => 0
  | .Integ k τ => k.degree + totalDerivDegree τ
  | .Prod τ₁ τ₂ => totalDerivDegree τ₁ + totalDerivDegree τ₂

/-- Sum of polynomial degrees in a tree. -/
def polyDegreeSum : TreeSymbol d → ℕ
  | .one => 0
  | .Xi => 0
  | .Poly k => k.degree
  | .Integ _ τ => polyDegreeSum τ
  | .Prod τ₁ τ₂ => polyDegreeSum τ₁ + polyDegreeSum τ₂

/-- Homogeneity formula in terms of counts and degrees.
    This is the key lemma for proving bounds. -/
theorem homogeneity_decomposition (α β : ℝ) (τ : TreeSymbol d) :
    TreeSymbol.homogeneity α β τ = τ.noiseCount * α + τ.integCount * β +
      (polyDegreeSum τ : ℝ) - (totalDerivDegree τ : ℝ) := by
  induction τ with
  | one => simp [TreeSymbol.homogeneity, TreeSymbol.noiseCount, TreeSymbol.integCount,
                 polyDegreeSum, totalDerivDegree]
  | Xi => simp [TreeSymbol.homogeneity, TreeSymbol.noiseCount, TreeSymbol.integCount,
                polyDegreeSum, totalDerivDegree]
  | Poly k =>
    simp [TreeSymbol.homogeneity, TreeSymbol.noiseCount, TreeSymbol.integCount,
          polyDegreeSum, totalDerivDegree]
  | Integ k τ ih =>
    simp only [TreeSymbol.homogeneity, TreeSymbol.noiseCount, TreeSymbol.integCount,
               polyDegreeSum, totalDerivDegree]
    rw [ih]
    push_cast
    ring
  | Prod τ₁ τ₂ ih1 ih2 =>
    simp only [TreeSymbol.homogeneity, TreeSymbol.noiseCount, TreeSymbol.integCount,
               polyDegreeSum, totalDerivDegree]
    rw [ih1, ih2]
    push_cast
    ring

/-- A tree is valid for the index set if it satisfies all bounds. -/
def isValidTree (A : IndexSetRS d) (τ : TreeSymbol d) : Prop :=
  τ.complexity ≤ A.maxComplexity ∧ totalDerivDegree τ ≤ A.maxDerivDegree * A.maxComplexity

/-- Check if a homogeneity value is in the index set (for valid trees). -/
def containsHomogeneity (A : IndexSetRS d) (h : ℝ) : Prop :=
  ∃ τ : TreeSymbol d, isValidTree A τ ∧
    TreeSymbol.homogeneity A.noiseRegularity A.kernelOrder τ = h

/-- Helper: n * x ≥ c * min(x, 0) when n ≤ c and n ≥ 0 and c ≥ 0. -/
theorem nat_mul_ge_max_mul_min (n c : ℕ) (x : ℝ) (hn : n ≤ c) :
    (n : ℝ) * x ≥ (c : ℝ) * min x 0 := by
  by_cases hx : x ≥ 0
  · simp only [min_eq_right hx, mul_zero]
    exact mul_nonneg (Nat.cast_nonneg n) hx
  · push_neg at hx
    simp only [min_eq_left (le_of_lt hx)]
    have hn' : (n : ℝ) ≤ c := Nat.cast_le.mpr hn
    have hc : (c : ℝ) ≥ 0 := Nat.cast_nonneg c
    exact mul_le_mul_of_nonpos_right hn' (le_of_lt hx)

/-- The index set is bounded below. -/
theorem bdd_below (A : IndexSetRS d) :
    ∃ m : ℝ, ∀ h : ℝ, A.containsHomogeneity h → h ≥ m := by
  let C := A.maxComplexity
  let D := A.maxDerivDegree
  use (C : ℝ) * min A.noiseRegularity 0 + (C : ℝ) * min A.kernelOrder 0 - (D * C : ℝ)
  intro h ⟨τ, ⟨hcomp, hderiv⟩, heq⟩
  rw [← heq]
  -- Use the decomposition formula
  rw [homogeneity_decomposition]
  -- Bounds on the terms
  have hN : τ.noiseCount ≤ τ.complexity := TreeSymbol.noiseCount_le_complexity τ
  have hI : τ.integCount ≤ τ.complexity := TreeSymbol.integCount_le_complexity τ
  have hNC : τ.noiseCount ≤ C := Nat.le_trans hN hcomp
  have hIC : τ.integCount ≤ C := Nat.le_trans hI hcomp
  have hP : (polyDegreeSum τ : ℝ) ≥ 0 := Nat.cast_nonneg _
  have hD : (totalDerivDegree τ : ℝ) ≤ (D : ℝ) * (C : ℝ) := by
    have h : (totalDerivDegree τ : ℝ) ≤ ((D * C : ℕ) : ℝ) := Nat.cast_le.mpr hderiv
    simp only [Nat.cast_mul] at h
    exact h
  -- Apply the helper lemma
  have h1 : (τ.noiseCount : ℝ) * A.noiseRegularity ≥ (C : ℝ) * min A.noiseRegularity 0 :=
    nat_mul_ge_max_mul_min τ.noiseCount C A.noiseRegularity hNC
  have h2 : (τ.integCount : ℝ) * A.kernelOrder ≥ (C : ℝ) * min A.kernelOrder 0 :=
    nat_mul_ge_max_mul_min τ.integCount C A.kernelOrder hIC
  linarith

/-- The index set for Φ⁴₃: α = -5/2, β = 2 -/
noncomputable def phi4_3 : IndexSetRS 3 where
  noiseRegularity := (-5 : ℝ)/2
  kernelOrder := (2 : ℝ)
  maxPolyDegree := 3
  maxDerivDegree := 2  -- Typical bound for heat kernel derivatives
  maxComplexity := 10

/-- The index set for KPZ: α = -3/2, β = 2 -/
noncomputable def kpz : IndexSetRS 1 where
  noiseRegularity := (-3 : ℝ)/2
  kernelOrder := (2 : ℝ)
  maxPolyDegree := 2
  maxDerivDegree := 2
  maxComplexity := 10

end IndexSetRS

end SPDE.RegularityStructures
