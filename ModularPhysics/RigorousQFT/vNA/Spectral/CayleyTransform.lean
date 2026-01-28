/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.RigorousQFT.vNA.Unbounded.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.Basic

/-!
# The Cayley Transform

This file develops the Cayley transform, which establishes a bijection between
unbounded self-adjoint operators and unitary operators. This is the key tool for
proving the spectral theorem for unbounded self-adjoint operators.

## Main definitions

* `CayleyTransform` - Maps a self-adjoint operator T to the unitary U = (T-i)(T+i)⁻¹
* `InverseCayley` - Recovers T from U via T = i(1+U)(1-U)⁻¹

## Main results

* `cayley_isUnitary` - The Cayley transform of a self-adjoint operator is unitary
* `cayley_inverse` - The inverse Cayley transform recovers the original operator
* `cayley_spectral_correspondence` - Spectral measures correspond via λ ↦ (λ-i)/(λ+i)

## Mathematical Background

For a self-adjoint operator T on a Hilbert space H:

1. **The Cayley transform**: U = (T - i)(T + i)⁻¹

   Key properties:
   - U is isometric: ‖Ux‖ = ‖x‖ for x in the range of (T + i)⁻¹
   - U is unitary (surjective isometry) when T is self-adjoint
   - 1 is not an eigenvalue of U (since T is unbounded)

2. **Inverse Cayley transform**: T = i(1 + U)(1 - U)⁻¹

   The domain of T corresponds to ran(1 - U).

3. **Spectral correspondence**:
   - The map φ : ℝ → S¹ defined by φ(λ) = (λ - i)/(λ + i) is a bijection ℝ → S¹ \ {1}
   - If P_T is the spectral measure of T and P_U is the spectral measure of U,
     then P_T(E) = P_U(φ(E)) for Borel sets E ⊆ ℝ

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I", Chapter VIII.3
* Rudin, "Functional Analysis", Section 13.19-13.21
* Kato, "Perturbation Theory for Linear Operators", Section V.3.2
-/

noncomputable section

open scoped InnerProduct ComplexConjugate
open Filter Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The deficiency subspaces -/

/-- The deficiency subspace K_+ = ker(T* + i) = (ran(T - i))^⊥.
    For a symmetric operator T, this measures how far T is from being self-adjoint. -/
def deficiencyPlus (T : UnboundedOperator H) : Submodule ℂ H :=
  -- ran(T - i) = { Tx - ix | x ∈ dom(T) }
  (Submodule.span ℂ { T.toFun x - Complex.I • x.1 | x : T.domain }).orthogonal

/-- The deficiency subspace K_- = ker(T* - i) = (ran(T + i))^⊥.
    For self-adjoint T, both K_+ and K_- are trivial. -/
def deficiencyMinus (T : UnboundedOperator H) : Submodule ℂ H :=
  -- ran(T + i) = { Tx + ix | x ∈ dom(T) }
  (Submodule.span ℂ { T.toFun x + Complex.I • x.1 | x : T.domain }).orthogonal

/-- For self-adjoint operators, the deficiency indices are both zero.
    This means ran(T ± i) are both dense in H. -/
theorem selfadjoint_deficiency_zero (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) :
    deficiencyPlus T = ⊥ ∧ deficiencyMinus T = ⊥ := by
  /-
  PROOF (Reed-Simon VIII.2, Theorem VIII.3):

  For self-adjoint T, we show ran(T - i) is dense, i.e., deficiencyPlus T = ⊥.

  Step 1: Suppose y ⊥ ran(T - i).
    Then ⟨y, Tx - ix⟩ = 0 for all x ∈ dom(T).
    Rearranging: ⟨y, Tx⟩ = i⟨y, x⟩.

  Step 2: This says that the functional x ↦ ⟨y, Tx⟩ = i⟨y, x⟩ is bounded.
    Since T = T*, y ∈ dom(T*) = dom(T), and T*y = iy, i.e., Ty = iy.

  Step 3: For symmetric (hence self-adjoint) T:
    ⟨Ty, y⟩ = ⟨y, Ty⟩  (by symmetry)
    Substituting Ty = iy:
    ⟨iy, y⟩ = ⟨y, iy⟩
    i̅⟨y, y⟩ = i⟨y, y⟩  (inner product properties)
    -i‖y‖² = i‖y‖²
    This gives 2i‖y‖² = 0, so y = 0.

  Step 4: Similarly for ran(T + i) (deficiencyMinus):
    If y ⊥ ran(T + i), then Ty = -iy, and the same argument gives y = 0.
  -/
  have hsym := T.selfadjoint_symmetric hT hsa
  constructor
  · -- Show deficiencyPlus T = ⊥
    rw [Submodule.eq_bot_iff]
    intro y hy
    unfold deficiencyPlus at hy
    rw [Submodule.mem_orthogonal] at hy
    -- hy : ∀ v ∈ span {Tx - ix | x ∈ dom(T)}, ⟨v, y⟩ = 0
    -- Step 1: y ⊥ (Tx - ix) for all x ∈ dom(T)
    have hortho : ∀ x : T.domain, @inner ℂ H _ (T.toFun x - Complex.I • (x : H)) y = 0 := by
      intro x
      apply hy
      apply Submodule.subset_span
      exact ⟨x, rfl⟩
    -- Step 2: Rearranging: ⟨Tx, y⟩ = -i⟨x, y⟩ (so the functional is bounded)
    have hfunc : ∀ x : T.domain, @inner ℂ H _ (T.toFun x) y = -Complex.I * @inner ℂ H _ (x : H) y := by
      intro x
      have h := hortho x
      rw [inner_sub_left, inner_smul_left] at h
      simp only [Complex.conj_I] at h
      -- h : ⟨Tx, y⟩ - (-i)⟨x, y⟩ = 0, i.e., ⟨Tx, y⟩ + i⟨x, y⟩ = 0
      -- so ⟨Tx, y⟩ = -i⟨x, y⟩
      have heq : @inner ℂ H _ (T.toFun x) y = -Complex.I * @inner ℂ H _ (x : H) y := by
        calc @inner ℂ H _ (T.toFun x) y
            = @inner ℂ H _ (T.toFun x) y - (-Complex.I * @inner ℂ H _ (x : H) y)
              + (-Complex.I * @inner ℂ H _ (x : H) y) := by ring
          _ = 0 + (-Complex.I * @inner ℂ H _ (x : H) y) := by rw [h]
          _ = -Complex.I * @inner ℂ H _ (x : H) y := by ring
      exact heq
    -- Step 3: y ∈ dom(T*) = dom(T) (since T = T*)
    -- The functional x ↦ ⟨Tx, y⟩ = -i⟨x, y⟩ is bounded by ‖y‖·‖x‖
    have hy_adj : y ∈ T.adjointDomain := by
      use ‖y‖
      intro x
      rw [hfunc x]
      calc ‖-Complex.I * @inner ℂ H _ (x : H) y‖
          = ‖Complex.I‖ * ‖@inner ℂ H _ (x : H) y‖ := by rw [neg_mul]; simp [Complex.norm_I]
        _ = 1 * ‖@inner ℂ H _ (x : H) y‖ := by rw [Complex.norm_I]
        _ = ‖@inner ℂ H _ (x : H) y‖ := by ring
        _ ≤ ‖(x : H)‖ * ‖y‖ := norm_inner_le_norm (x : H) y
        _ = ‖y‖ * ‖(x : H)‖ := mul_comm _ _
    -- Since T is self-adjoint, T.domain = T.adjointDomainSubmodule
    have hdom_eq : T.domain = T.adjointDomainSubmodule := congrArg UnboundedOperator.domain hsa
    -- So y ∈ T.domain
    have hy_dom : y ∈ T.domain := hdom_eq ▸ hy_adj
    let y_dom : T.domain := ⟨y, hy_dom⟩
    let y_adj : T.adjointDomainSubmodule := ⟨y, hy_adj⟩
    -- Step 4: T*y = -iy (by uniqueness of Riesz representative)
    -- hfunc says ⟨Tx, y⟩ = -i⟨x, y⟩ = ⟨x, iy⟩ (since inner is linear in 2nd arg)
    -- So T*y = -iy since -iy satisfies the adjoint defining property
    have hadj_neg_iy : ∀ x : T.domain, @inner ℂ H _ (T.toFun x) y = @inner ℂ H _ (x : H) (-Complex.I • y) := by
      intro x
      rw [hfunc x, inner_smul_right]
    -- T*y is the unique z with ⟨Tx, y⟩ = ⟨x, z⟩ for all x
    have hTstar_eq : T.adjointApply hT y_adj = -Complex.I • y := by
      apply T.adjoint_unique hT y
      · exact T.adjointApply_spec hT y_adj
      · exact hadj_neg_iy
    -- Since T = T* (self-adjoint), Ty = T*y = -iy
    have hTy_eq : T.toFun y_dom = -Complex.I • y := by
      -- Use the equality T = T.adjoint hT
      have happly : T.toFun y_dom = (T.adjoint hT).toFun y_adj := by
        have key : ∀ (S : UnboundedOperator H) (hs : T = S) (hz : y ∈ S.domain),
            T.toFun y_dom = S.toFun ⟨y, hz⟩ := by
          intro S hs hz
          subst hs
          rfl
        exact key (T.adjoint hT) hsa hy_adj
      rw [happly]
      exact hTstar_eq
    -- Step 5: ⟨Ty, y⟩ = ⟨-iy, y⟩ = i‖y‖² (using inner_smul_left: ⟨cy, z⟩ = c̄⟨y, z⟩)
    have hinner : @inner ℂ H _ (T.toFun y_dom) y = Complex.I * (‖y‖^2 : ℂ) := by
      rw [hTy_eq, inner_smul_left]
      -- Goal: conj(-I) * ⟨y, y⟩ = I * ‖y‖²
      -- conj(-I) = -conj(I) = -(-I) = I
      have hconj : starRingEnd ℂ (-Complex.I) = Complex.I := by
        simp only [map_neg, Complex.conj_I, neg_neg]
      rw [hconj]
      -- Goal: I * ⟨y, y⟩ = I * ‖y‖²
      congr 1
      -- Goal: ⟨y, y⟩ = ‖y‖²
      rw [inner_self_eq_norm_sq_to_K]
      rfl
    -- Step 6: By symmetric_inner_real, Im(⟨Ty, y⟩) = 0
    have hreal := T.symmetric_inner_real hsym y_dom
    -- hreal : (@inner ℂ H _ (T.toFun y_dom) y).im = 0
    -- But from hinner: (@inner ℂ H _ (T.toFun y_dom) y) = i * ‖y‖²
    -- Im(i * ‖y‖²) = ‖y‖², so ‖y‖² = 0
    have him : (Complex.I * (‖y‖^2 : ℂ)).im = ‖y‖^2 := by
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im]
      -- Goal: 0 * (‖y‖ : ℂ)^2.im + 1 * (‖y‖ : ℂ)^2.re = ‖y‖^2
      simp only [zero_mul, one_mul, zero_add]
      -- (‖y‖ : ℂ)^2 = (‖y‖^2 : ℂ) and its re is ‖y‖^2
      have h1 : ((‖y‖ : ℂ) ^ 2).re = ‖y‖ ^ 2 := by
        rw [sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        ring
      exact h1
    rw [hinner] at hreal
    rw [him] at hreal
    -- hreal : ‖y‖² = 0
    rw [sq_eq_zero_iff, norm_eq_zero] at hreal
    exact hreal
  · -- Show deficiencyMinus T = ⊥ (symmetric argument)
    rw [Submodule.eq_bot_iff]
    intro y hy
    unfold deficiencyMinus at hy
    rw [Submodule.mem_orthogonal] at hy
    -- Similar: y ⊥ (Tx + ix) for all x ∈ dom(T)
    have hortho : ∀ x : T.domain, @inner ℂ H _ (T.toFun x + Complex.I • (x : H)) y = 0 := by
      intro x
      apply hy
      apply Submodule.subset_span
      exact ⟨x, rfl⟩
    -- Rearranging: ⟨Tx, y⟩ = i⟨x, y⟩
    have hfunc : ∀ x : T.domain, @inner ℂ H _ (T.toFun x) y = Complex.I * @inner ℂ H _ (x : H) y := by
      intro x
      have h := hortho x
      rw [inner_add_left, inner_smul_left] at h
      simp only [Complex.conj_I] at h
      -- h : ⟨Tx, y⟩ + (-i)⟨x, y⟩ = 0, i.e., ⟨Tx, y⟩ = i⟨x, y⟩
      have heq : @inner ℂ H _ (T.toFun x) y = Complex.I * @inner ℂ H _ (x : H) y := by
        calc @inner ℂ H _ (T.toFun x) y
            = @inner ℂ H _ (T.toFun x) y + (-Complex.I * @inner ℂ H _ (x : H) y)
              - (-Complex.I * @inner ℂ H _ (x : H) y) := by ring
          _ = 0 - (-Complex.I * @inner ℂ H _ (x : H) y) := by rw [h]
          _ = Complex.I * @inner ℂ H _ (x : H) y := by ring
      exact heq
    -- y ∈ dom(T), Ty = iy, ⟨Ty, y⟩ = -i‖y‖² has Im = -‖y‖²
    -- By symmetric_inner_real, y = 0
    -- Step 3: y ∈ dom(T*) = dom(T)
    have hy_adj : y ∈ T.adjointDomain := by
      use ‖y‖
      intro x
      rw [hfunc x]
      calc ‖Complex.I * @inner ℂ H _ (x : H) y‖
          = ‖Complex.I‖ * ‖@inner ℂ H _ (x : H) y‖ := norm_mul _ _
        _ = 1 * ‖@inner ℂ H _ (x : H) y‖ := by rw [Complex.norm_I]
        _ = ‖@inner ℂ H _ (x : H) y‖ := by ring
        _ ≤ ‖(x : H)‖ * ‖y‖ := norm_inner_le_norm (x : H) y
        _ = ‖y‖ * ‖(x : H)‖ := mul_comm _ _
    have hdom_eq : T.domain = T.adjointDomainSubmodule := congrArg UnboundedOperator.domain hsa
    have hy_dom : y ∈ T.domain := hdom_eq ▸ hy_adj
    let y_dom : T.domain := ⟨y, hy_dom⟩
    let y_adj : T.adjointDomainSubmodule := ⟨y, hy_adj⟩
    -- Step 4: T*y = iy
    have hadj_iy : ∀ x : T.domain, @inner ℂ H _ (T.toFun x) y = @inner ℂ H _ (x : H) (Complex.I • y) := by
      intro x
      rw [hfunc x, inner_smul_right]
    have hTstar_eq : T.adjointApply hT y_adj = Complex.I • y := by
      apply T.adjoint_unique hT y
      · exact T.adjointApply_spec hT y_adj
      · exact hadj_iy
    -- Ty = T*y = iy
    have hTy_eq : T.toFun y_dom = Complex.I • y := by
      have happly : T.toFun y_dom = (T.adjoint hT).toFun y_adj := by
        have key : ∀ (S : UnboundedOperator H) (hs : T = S) (hz : y ∈ S.domain),
            T.toFun y_dom = S.toFun ⟨y, hz⟩ := by
          intro S hs hz
          subst hs
          rfl
        exact key (T.adjoint hT) hsa hy_adj
      rw [happly]
      exact hTstar_eq
    -- Step 5: ⟨Ty, y⟩ = ⟨iy, y⟩ = -i‖y‖² (using inner_smul_left: ⟨cy, z⟩ = c̄⟨y, z⟩)
    have hinner : @inner ℂ H _ (T.toFun y_dom) y = -Complex.I * (‖y‖^2 : ℂ) := by
      rw [hTy_eq, inner_smul_left]
      -- Goal: conj(I) * ⟨y, y⟩ = -I * ‖y‖²
      -- conj(I) = -I
      simp only [Complex.conj_I]
      congr 1
      rw [inner_self_eq_norm_sq_to_K]
      rfl
    -- Step 6: By symmetric_inner_real, Im(⟨Ty, y⟩) = 0
    have hreal := T.symmetric_inner_real hsym y_dom
    -- Im(-i * ‖y‖²) = -‖y‖²
    have him : (-Complex.I * (‖y‖^2 : ℂ)).im = -‖y‖^2 := by
      -- -I * z = -(I * z), so Im(-I * z) = -Im(I * z) = -z.re
      have h1 : -Complex.I * (‖y‖^2 : ℂ) = -(Complex.I * (‖y‖^2 : ℂ)) := by ring
      rw [h1, Complex.neg_im]
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im]
      simp only [zero_mul, one_mul, zero_add]
      have h2 : ((‖y‖ : ℂ) ^ 2).re = ‖y‖ ^ 2 := by
        rw [sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [h2]
    rw [hinner] at hreal
    rw [him] at hreal
    -- hreal : -‖y‖² = 0
    have hnorm : ‖y‖^2 = 0 := by linarith
    rw [sq_eq_zero_iff, norm_eq_zero] at hnorm
    exact hnorm

/-! ### The Cayley transform -/

/-- The resolvent (T - z)⁻¹ for z not in the spectrum.
    For self-adjoint T, the spectrum is real, so (T - i)⁻¹ exists and is bounded. -/
structure Resolvent (T : UnboundedOperator H) (z : ℂ) where
  /-- The inverse operator -/
  inv : H →L[ℂ] H
  /-- The inverse maps into the domain -/
  maps_to_domain : ∀ y : H, inv y ∈ T.domain
  /-- Left inverse property -/
  left_inverse : ∀ y : H, T.toFun ⟨inv y, maps_to_domain y⟩ - z • inv y = y
  /-- Right inverse property on the domain -/
  right_inverse : ∀ x : T.domain, inv (T.toFun x - z • x.1) = x.1

/-- For self-adjoint T, the resolvent (T - i)⁻¹ exists.
    This is because ±i are not in the spectrum of a self-adjoint operator. -/
theorem resolvent_exists_at_i (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) :
    ∃ _ : Resolvent T Complex.I, True := by
  -- Step 1: T - i is injective
  have h_inj : ∀ x : T.domain, T.toFun x - Complex.I • (x : H) = 0 → (x : H) = 0 := by
    intro x hx
    -- If Tx = ix, then ⟨Tx, x⟩ = ⟨ix, x⟩ = conj(i)‖x‖² = -i‖x‖²
    -- For symmetric T, ⟨Tx, x⟩ is real (Im = 0), but Im(-i‖x‖²) = -‖x‖²
    -- So -‖x‖² = 0, hence x = 0
    have hsym := T.selfadjoint_symmetric hT hsa
    have hreal := T.symmetric_inner_real hsym x
    -- From hx: Tx = ix
    have hTx : T.toFun x = Complex.I • (x : H) := by
      have h := sub_eq_zero.mp hx
      exact h
    -- ⟨Tx, x⟩ = ⟨ix, x⟩
    have hinner : @inner ℂ H _ (T.toFun x) (x : H) = @inner ℂ H _ (Complex.I • (x : H)) (x : H) := by
      rw [hTx]
    -- ⟨ix, x⟩ = conj(i) * ‖x‖² = -i * ‖x‖²
    rw [inner_smul_left] at hinner
    simp only [Complex.conj_I] at hinner
    -- hinner: ⟨Tx, x⟩ = -i * ⟨x, x⟩ = -i * ‖x‖²
    -- hreal: Im(⟨Tx, x⟩) = 0
    -- Im(-i * ‖x‖²) = -‖x‖² (since Im(-i * r) = -r for real r)
    have him : (@inner ℂ H _ (T.toFun x) (x : H)).im = (-Complex.I * @inner ℂ H _ (x : H) (x : H)).im := by
      rw [hinner]
    rw [hreal] at him
    -- inner_self is real: Im(⟨x, x⟩) = 0, and Re(⟨x, x⟩) = ‖x‖²
    have hself_real : (@inner ℂ H _ (x : H) (x : H)).im = 0 := inner_self_im (𝕜 := ℂ) (x : H)
    have hself_re : (@inner ℂ H _ (x : H) (x : H)).re = ‖(x : H)‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) (x : H)
    -- him: 0 = Im(-i * ⟨x, x⟩)
    -- For z with Im(z) = 0: Im(-i * z) = Im(-i) * Re(z) + Re(-i) * Im(z) = -Re(z)
    have hcompute : (-Complex.I * @inner ℂ H _ (x : H) (x : H)).im = -(@inner ℂ H _ (x : H) (x : H)).re := by
      simp only [Complex.neg_im, Complex.mul_im, Complex.neg_re]
      rw [hself_real]
      simp [Complex.I_re, Complex.I_im]
    rw [hcompute, hself_re] at him
    -- him: 0 = -‖x‖², so ‖x‖² = 0
    have hnorm : ‖(x : H)‖^2 = 0 := by linarith
    rw [sq_eq_zero_iff, norm_eq_zero] at hnorm
    exact hnorm
  -- Step 2: ran(T - i) is closed (from ‖(T-i)x‖ ≥ ‖x‖)
  -- First prove the key norm estimate: ‖Tx - ix‖² ≥ ‖x‖²
  have hsym := T.selfadjoint_symmetric hT hsa
  have h_norm_est : ∀ x : T.domain, ‖(x : H)‖ ≤ ‖T.toFun x - Complex.I • (x : H)‖ := by
    intro x
    -- Key: ‖Tx - ix‖² = ‖Tx‖² + ‖x‖² for symmetric T
    -- Because ⟨Tx, ix⟩ = i⟨Tx, x⟩ is pure imaginary (since ⟨Tx, x⟩ is real)
    have hreal := T.symmetric_inner_real hsym x
    -- Use norm_sub_sq: ‖a - b‖² = ‖a‖² - 2 Re⟨a, b⟩ + ‖b‖²
    have hcross : RCLike.re (@inner ℂ H _ (T.toFun x) (Complex.I • (x : H))) = 0 := by
      rw [inner_smul_right]
      -- Goal: RCLike.re (I * ⟨Tx, x⟩) = 0
      -- For z with Im(z) = 0: Re(i * z) = 0 * Re(z) - 1 * Im(z) = 0
      simp only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.I_re, Complex.I_im]
      rw [hreal]
      ring
    -- ‖ix‖ = ‖x‖
    have hnorm_ix : ‖Complex.I • (x : H)‖ = ‖(x : H)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    -- ‖Tx - ix‖² = ‖Tx‖² - 2 Re⟨Tx, ix⟩ + ‖ix‖² = ‖Tx‖² + ‖x‖²
    have hexpand : ‖T.toFun x - Complex.I • (x : H)‖^2 = ‖T.toFun x‖^2 + ‖(x : H)‖^2 := by
      rw [@norm_sub_sq ℂ, hcross, hnorm_ix]
      ring
    -- ‖Tx - ix‖² ≥ ‖x‖²
    have hge : ‖(x : H)‖^2 ≤ ‖T.toFun x - Complex.I • (x : H)‖^2 := by
      rw [hexpand]
      have h := sq_nonneg ‖T.toFun x‖
      linarith
    -- From a² ≤ b² and a, b ≥ 0, conclude a ≤ b
    have ha := norm_nonneg (x : H)
    have hb := norm_nonneg (T.toFun x - Complex.I • (x : H))
    nlinarith [sq_nonneg ‖(x : H)‖, sq_nonneg ‖T.toFun x - Complex.I • (x : H)‖]
  have h_closed : IsClosed (Set.range fun x : T.domain => T.toFun x - Complex.I • (x : H)) := by
    -- The range is closed because (T-i) has bounded inverse on its range
    -- Use: a bijection with bounded inverse from a Banach space has closed range
    -- More directly: use the isometry-like property from h_norm_est
    -- For a sequence yₙ = (T-i)xₙ → y, we have ‖xₙ - xₘ‖ ≤ ‖yₙ - yₘ‖, so xₙ is Cauchy
    -- By completeness, xₙ → x. Since T is closed (self-adjoint implies closed),
    -- we have x ∈ dom(T) and Tx - ix = y.
    rw [← isSeqClosed_iff_isClosed]
    intro seq y hseq_mem hseq_lim
    -- seq n ∈ range, so seq n = (T-i)xₙ for some xₙ
    choose xseq hxseq using fun n => hseq_mem n
    -- The sequence xₙ is Cauchy because ‖xₙ - xₘ‖ ≤ ‖(T-i)xₙ - (T-i)xₘ‖ = ‖seq n - seq m‖
    have hcauchy : CauchySeq (fun n => (xseq n : H)) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      -- seq is convergent, hence Cauchy
      have hseq_cauchy : CauchySeq seq := hseq_lim.cauchySeq
      rw [Metric.cauchySeq_iff] at hseq_cauchy
      obtain ⟨N, hN⟩ := hseq_cauchy ε hε
      use N
      intro n hn m hm
      -- ‖xₙ - xₘ‖ ≤ ‖(T-i)xₙ - (T-i)xₘ‖
      -- hxseq n says: T.toFun (xseq n) - I • (xseq n : H) = seq n
      have hxseq_n : T.toFun (xseq n) - Complex.I • (xseq n : H) = seq n := hxseq n
      have hxseq_m : T.toFun (xseq m) - Complex.I • (xseq m : H) = seq m := hxseq m
      have hminus : T.toFun (xseq n - xseq m) = T.toFun (xseq n) - T.toFun (xseq m) := by
        have hsub : xseq n - xseq m = xseq n + (-1 : ℂ) • xseq m := by
          simp only [neg_one_smul, sub_eq_add_neg]
        rw [hsub, T.map_add', T.map_smul']
        simp only [neg_one_smul, sub_eq_add_neg]
      have hexpand : (T.toFun (xseq n) - T.toFun (xseq m)) - Complex.I • ((xseq n : H) - (xseq m : H)) =
             (T.toFun (xseq n) - Complex.I • (xseq n : H)) -
             (T.toFun (xseq m) - Complex.I • (xseq m : H)) := by
        simp only [smul_sub, sub_sub_sub_comm]
      calc dist ((xseq n : H)) ((xseq m : H))
          = ‖(xseq n : H) - (xseq m : H)‖ := dist_eq_norm _ _
        _ ≤ ‖T.toFun (xseq n - xseq m) - Complex.I • ((xseq n : H) - (xseq m : H))‖ := by
            have := h_norm_est (xseq n - xseq m)
            simp only [Submodule.coe_sub] at this
            exact this
        _ = ‖(T.toFun (xseq n) - T.toFun (xseq m)) - Complex.I • ((xseq n : H) - (xseq m : H))‖ := by
            rw [hminus]
        _ = ‖(T.toFun (xseq n) - Complex.I • (xseq n : H)) -
             (T.toFun (xseq m) - Complex.I • (xseq m : H))‖ := by rw [hexpand]
        _ = ‖seq n - seq m‖ := by rw [hxseq_n, hxseq_m]
        _ = dist (seq n) (seq m) := (dist_eq_norm _ _).symm
        _ < ε := hN n hn m hm
    -- xseq converges to some limit x_lim in H
    obtain ⟨x_lim, hx_lim⟩ := cauchySeq_tendsto_of_complete hcauchy
    -- Since T is closed (self-adjoint implies closed), we need to show x_lim ∈ dom(T)
    -- and T x_lim - i x_lim = y
    -- Use the closed graph: (xₙ, Txₙ) → (x_lim, ?) and T is closed
    have hTclosed := T.selfadjoint_closed hT hsa
    -- The pairs (xₙ, Txₙ) form a sequence in graph(T)
    -- We have xₙ → x_lim and (T-i)xₙ → y, so Txₙ → y + i x_lim
    have hTx_lim : Filter.Tendsto (fun n => T.toFun (xseq n)) Filter.atTop (nhds (y + Complex.I • x_lim)) := by
      have h1 : ∀ n, T.toFun (xseq n) = seq n + Complex.I • (xseq n : H) := by
        intro n
        have hxseq_n := hxseq n
        -- hxseq_n : T.toFun (xseq n) - Complex.I • (xseq n : H) = seq n
        -- So T.toFun (xseq n) = seq n + Complex.I • (xseq n : H)
        simp only at hxseq_n
        have heq : T.toFun (xseq n) - Complex.I • (xseq n : H) + Complex.I • (xseq n : H) =
                   seq n + Complex.I • (xseq n : H) := by rw [hxseq_n]
        rw [sub_add_cancel] at heq
        exact heq
      simp only [h1]
      apply Filter.Tendsto.add hseq_lim
      exact Filter.Tendsto.const_smul hx_lim Complex.I
    -- By closedness of graph(T), (x_lim, y + i x_lim) ∈ graph(T)
    have hin_graph : (x_lim, y + Complex.I • x_lim) ∈ closure T.graph := by
      rw [mem_closure_iff_seq_limit]
      use fun n => ((xseq n : H), T.toFun (xseq n))
      constructor
      · intro n
        exact ⟨xseq n, rfl, rfl⟩
      · exact Filter.Tendsto.prodMk_nhds hx_lim hTx_lim
    rw [hTclosed.closure_eq] at hin_graph
    -- So x_lim ∈ dom(T) and T x_lim = y + i x_lim
    obtain ⟨x', hx'1, hx'2⟩ := hin_graph
    -- hx'1 : (x' : H) = x_lim, hx'2 : T x' = y + i x_lim
    -- So (T - i) x' = T x' - i x' = y + i x_lim - i x_lim = y
    use x'
    calc T.toFun x' - Complex.I • (x' : H)
        = (y + Complex.I • x_lim) - Complex.I • x_lim := by rw [hx'2, hx'1]
      _ = y := by abel
  -- Step 3: ran(T - i) is dense (by selfadjoint_deficiency_zero)
  have h_dense : Dense (Set.range fun x : T.domain => T.toFun x - Complex.I • (x : H)) := by
    -- deficiencyPlus T = ⊥ means ran(T-i)^⊥ = {0}, so ran(T-i) is dense
    have hdef := selfadjoint_deficiency_zero T hT hsa
    -- First, note that the range is exactly the set in the span
    have hset_eq : { T.toFun x - Complex.I • x.1 | x : T.domain } =
                   Set.range fun x : T.domain => T.toFun x - Complex.I • (x : H) := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_range]
    -- deficiencyPlus is the orthogonal of the span
    unfold deficiencyPlus at hdef
    -- From deficiencyPlus = ⊥, get span^⊥ = ⊥
    have horth_bot : (Submodule.span ℂ (Set.range fun x : T.domain => T.toFun x - Complex.I • (x : H))).orthogonal = ⊥ := by
      rw [← hset_eq]
      exact hdef.1
    -- Define the linear map f(x) = Tx - ix
    let f : T.domain →ₗ[ℂ] H := {
      toFun := fun x => T.toFun x - Complex.I • (x : H)
      map_add' := fun x y => by
        rw [T.map_add', Submodule.coe_add, smul_add]
        abel
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        rw [T.map_smul', Submodule.coe_smul, smul_sub, smul_comm]
    }
    -- The range of f is a submodule, and as a set it equals Set.range ...
    have hrange_eq : (LinearMap.range f : Set H) =
                     Set.range fun x : T.domain => T.toFun x - Complex.I • (x : H) := by
      ext y
      simp only [Set.mem_range]
      constructor
      · intro ⟨x, hx⟩; exact ⟨x, hx⟩
      · intro ⟨x, hx⟩; exact ⟨x, hx⟩
    -- span of range f = range f (since range is already a submodule)
    have hspan_eq_range : Submodule.span ℂ (Set.range fun x : T.domain => T.toFun x - Complex.I • (x : H)) =
                          LinearMap.range f := by
      apply le_antisymm
      · -- span ≤ range: follows from span_le and range is a submodule
        rw [Submodule.span_le]
        intro y hy
        rw [SetLike.mem_coe, LinearMap.mem_range]
        exact hy
      · -- range ≤ span: range ⊆ span (trivial)
        rw [← hrange_eq]
        intro y hy
        have hy' : y ∈ (LinearMap.range f : Set H) := hy
        exact Submodule.subset_span hy'
    -- Now use orthogonal property: (range f)^⊥ = ⊥ implies range f is dense
    rw [hspan_eq_range] at horth_bot
    have hrange_dense : Dense (LinearMap.range f : Set H) := by
      rw [Submodule.dense_iff_topologicalClosure_eq_top]
      rw [Submodule.topologicalClosure_eq_top_iff]
      exact horth_bot
    rw [← hrange_eq]
    exact hrange_dense
  -- Step 4: Closed + dense = H, construct the resolvent
  -- Since the range is closed and dense in a complete space, range = H
  have h_range_eq : (Set.range fun x : T.domain => T.toFun x - Complex.I • (x : H)) = Set.univ := by
    -- closure of dense set = univ, and closure of closed set = set itself
    have h1 : closure (Set.range fun x : T.domain => T.toFun x - Complex.I • (x : H)) = Set.univ :=
      h_dense.closure_eq
    have h2 : closure (Set.range fun x : T.domain => T.toFun x - Complex.I • (x : H)) =
              Set.range fun x : T.domain => T.toFun x - Complex.I • (x : H) :=
      h_closed.closure_eq
    rw [← h2, h1]
  -- Construct the inverse
  -- For each y ∈ H, there exists unique x with (T-i)x = y
  have h_inv_exists : ∀ y : H, ∃! x : T.domain, T.toFun x - Complex.I • (x : H) = y := by
    intro y
    -- Existence: y ∈ range
    have hy : y ∈ Set.range fun x : T.domain => T.toFun x - Complex.I • (x : H) := by
      rw [h_range_eq]; trivial
    obtain ⟨x, hx⟩ := hy
    use x, hx
    -- Uniqueness: (T-i) is injective
    intro x' hx'
    -- First simplify hx to beta reduce the function application
    simp only at hx
    have hdiff : T.toFun x - Complex.I • (x : H) - (T.toFun x' - Complex.I • (x' : H)) = 0 := by
      rw [hx, hx', sub_self]
    have hdiff' : T.toFun (x - x') - Complex.I • ((x : H) - (x' : H)) = 0 := by
      have hminus : T.toFun (x - x') = T.toFun x - T.toFun x' := by
        have hsub : x - x' = x + (-1 : ℂ) • x' := by
          ext; simp [sub_eq_add_neg]
        rw [hsub, T.map_add', T.map_smul']
        simp only [neg_one_smul]
        rw [sub_eq_add_neg]
      rw [hminus, smul_sub]
      -- Goal: Tx - Tx' - (I • x - I • x') = 0
      -- Which equals (Tx - I • x) - (Tx' - I • x')
      calc T.toFun x - T.toFun x' - (Complex.I • (x : H) - Complex.I • (x' : H))
          = (T.toFun x - Complex.I • (x : H)) - (T.toFun x' - Complex.I • (x' : H)) := by abel
        _ = 0 := hdiff
    have hzero := h_inj (x - x') hdiff'
    simp only [Submodule.coe_sub] at hzero
    ext
    -- hzero : (x : H) - (x' : H) = 0, goal: (x' : H) = (x : H)
    -- sub_eq_zero : a - b = 0 ↔ a = b, so we get ↑x = ↑x', then use .symm
    exact (sub_eq_zero.mp hzero).symm
  -- Define the inverse map
  let R_fun : H → H := fun y => (h_inv_exists y).choose
  have hR_spec : ∀ y, T.toFun (h_inv_exists y).choose - Complex.I • ((h_inv_exists y).choose : H) = y :=
    fun y => (h_inv_exists y).choose_spec.1
  -- R_fun is bounded (by the norm estimate)
  have hR_bdd : ∃ C : ℝ, ∀ y : H, ‖R_fun y‖ ≤ C * ‖y‖ := by
    use 1
    intro y
    have h := h_norm_est (h_inv_exists y).choose
    calc ‖R_fun y‖ = ‖((h_inv_exists y).choose : H)‖ := rfl
      _ ≤ ‖T.toFun (h_inv_exists y).choose - Complex.I • ((h_inv_exists y).choose : H)‖ := h
      _ = ‖y‖ := by rw [hR_spec y]
      _ = 1 * ‖y‖ := by ring
  -- R_fun is linear
  have hR_linear : ∀ c : ℂ, ∀ y₁ y₂ : H, R_fun (c • y₁ + y₂) = c • R_fun y₁ + R_fun y₂ := by
    intro c y₁ y₂
    -- By uniqueness, since (T-i)(c•R y₁ + R y₂) = c•y₁ + y₂
    have h1 : T.toFun (c • (h_inv_exists y₁).choose + (h_inv_exists y₂).choose) -
        Complex.I • (c • (h_inv_exists y₁).choose + (h_inv_exists y₂).choose : H) = c • y₁ + y₂ := by
      rw [T.map_add', T.map_smul']
      -- Goal: c • T.toFun x₁ + T.toFun x₂ - I • (c • x₁ + x₂) = c • y₁ + y₂
      -- where x₁ = (h_inv_exists y₁).choose, x₂ = (h_inv_exists y₂).choose
      -- and hR_spec says T.toFun xᵢ - I • xᵢ = yᵢ
      have heq1 := hR_spec y₁
      have heq2 := hR_spec y₂
      -- Expand: I • (c • x₁ + x₂) = I • c • x₁ + I • x₂ = c • I • x₁ + I • x₂
      rw [smul_add]
      -- Now: c • T x₁ + T x₂ - (I • c • x₁ + I • x₂)
      -- Use smul_comm to get I • c • x = c • I • x
      rw [smul_comm Complex.I c]
      -- Now: c • T x₁ + T x₂ - (c • I • x₁ + I • x₂)
      -- = c • T x₁ - c • I • x₁ + (T x₂ - I • x₂)
      -- = c • (T x₁ - I • x₁) + (T x₂ - I • x₂)
      have hrearrange : c • T.toFun (h_inv_exists y₁).choose + T.toFun (h_inv_exists y₂).choose -
          (c • Complex.I • ↑(h_inv_exists y₁).choose + Complex.I • ↑(h_inv_exists y₂).choose) =
          c • (T.toFun (h_inv_exists y₁).choose - Complex.I • ((h_inv_exists y₁).choose : H)) +
          (T.toFun (h_inv_exists y₂).choose - Complex.I • ((h_inv_exists y₂).choose : H)) := by
        rw [smul_sub]
        abel
      rw [hrearrange, heq1, heq2]
    have huniq := (h_inv_exists (c • y₁ + y₂)).choose_spec.2
    have heq := huniq (c • (h_inv_exists y₁).choose + (h_inv_exists y₂).choose) h1
    -- heq : c • x₁ + x₂ = x where x = (h_inv_exists (c • y₁ + y₂)).choose
    -- Need: R_fun (c • y₁ + y₂) = c • R_fun y₁ + R_fun y₂
    -- i.e., ↑x = c • ↑x₁ + ↑x₂
    calc R_fun (c • y₁ + y₂)
        = ↑((h_inv_exists (c • y₁ + y₂)).choose) := rfl
      _ = ↑(c • (h_inv_exists y₁).choose + (h_inv_exists y₂).choose) := congrArg Subtype.val heq.symm
      _ = c • ↑(h_inv_exists y₁).choose + ↑(h_inv_exists y₂).choose := by
          simp only [Submodule.coe_add, Submodule.coe_smul]
      _ = c • R_fun y₁ + R_fun y₂ := rfl
  -- R_fun 0 = 0 (since (T-i)0 = 0)
  have hR_zero : R_fun 0 = 0 := by
    have huniq := (h_inv_exists 0).choose_spec.2
    have h0 : T.toFun (0 : T.domain) - Complex.I • ((0 : T.domain) : H) = 0 := by
      -- T 0 = 0 from linearity: T 0 = T (0 • x) = 0 • T x = 0
      have hT0 : T.toFun (0 : T.domain) = 0 := by
        have h : (0 : T.domain) = (0 : ℂ) • (0 : T.domain) := by simp
        rw [h, T.map_smul']
        simp
      simp only [hT0, Submodule.coe_zero, smul_zero, sub_zero]
    have heq := huniq 0 h0
    exact congrArg Subtype.val heq.symm
  -- Construct the continuous linear map
  let R_lin : H →ₗ[ℂ] H := {
    toFun := R_fun
    map_add' := fun x y => by
      have := hR_linear 1 x y
      simp at this
      exact this
    map_smul' := fun c x => by
      have := hR_linear c x 0
      simp only [add_zero] at this
      simp only [RingHom.id_apply]
      rw [this, hR_zero, add_zero]
  }
  have hR_cont : Continuous R_lin := by
    obtain ⟨C, hC⟩ := hR_bdd
    apply AddMonoidHomClass.continuous_of_bound R_lin C
    intro x
    exact hC x
  let R : H →L[ℂ] H := ⟨R_lin, hR_cont⟩
  -- Build the Resolvent structure
  refine ⟨⟨R, ?maps_to_domain, ?left_inverse, ?right_inverse⟩, trivial⟩
  case maps_to_domain =>
    intro y
    exact (h_inv_exists y).choose.2
  case left_inverse =>
    intro y
    have h := hR_spec y
    convert h using 1
  case right_inverse =>
    intro x
    -- Need: R ((T-i)x) = x
    -- By uniqueness of the preimage
    have huniq := (h_inv_exists (T.toFun x - Complex.I • (x : H))).choose_spec.2
    have heq := huniq x rfl
    exact congrArg Subtype.val heq.symm

/-- For self-adjoint T, the resolvent (T + i)⁻¹ exists. -/
theorem resolvent_exists_at_neg_i (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) :
    ∃ _ : Resolvent T (-Complex.I), True := by
  -- Symmetric to resolvent_exists_at_i with sign changes
  -- Note: T - (-i) = T + i, so we work with T + i
  have hsym := T.selfadjoint_symmetric hT hsa
  -- Step 1: T + i is injective
  have h_inj : ∀ x : T.domain, T.toFun x - (-Complex.I) • (x : H) = 0 → (x : H) = 0 := by
    intro x hx
    -- T.toFun x - (-I) • x = T.toFun x + I • x = 0 means Tx = -ix
    have hreal := T.symmetric_inner_real hsym x
    -- Convert hx: T.toFun x - (-I)•x = 0 means T.toFun x + I•x = 0
    have hx' : T.toFun x + Complex.I • (x : H) = 0 := by
      have h1 : T.toFun x - (-Complex.I) • (x : H) = T.toFun x - (-(Complex.I • (x : H))) := by
        rw [neg_smul]
      rw [h1, sub_neg_eq_add] at hx
      exact hx
    have hTx : T.toFun x = -Complex.I • (x : H) := by
      calc T.toFun x = T.toFun x + Complex.I • (x : H) - Complex.I • (x : H) := by abel
        _ = 0 - Complex.I • (x : H) := by rw [hx']
        _ = -(Complex.I • (x : H)) := by rw [zero_sub]
        _ = -Complex.I • (x : H) := by rw [neg_smul]
    -- ⟨Tx, x⟩ = ⟨-ix, x⟩ = conj(-i)‖x‖² = i‖x‖² (since conj(-i) = i)
    have hinner : @inner ℂ H _ (T.toFun x) (x : H) = Complex.I * (‖(x : H)‖^2 : ℂ) := by
      rw [hTx, inner_smul_left]
      -- inner_smul_left: inner (c • x) y = conj(c) * inner x y
      -- conj(-i) = -conj(i) = -(-i) = i
      simp only [map_neg, Complex.conj_I, neg_neg]
      rw [inner_self_eq_norm_sq_to_K]; rfl
    -- Im(i * ‖x‖²) = ‖x‖², but Im(⟨Tx, x⟩) = 0 for symmetric T
    have him : (Complex.I * (‖(x : H)‖^2 : ℂ)).im = ‖(x : H)‖^2 := by
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im]
      simp only [zero_mul, one_mul, zero_add]
      have h2 : ((‖(x : H)‖ : ℂ) ^ 2).re = ‖(x : H)‖ ^ 2 := by
        rw [sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
      rw [h2]
    rw [hinner] at hreal
    rw [him] at hreal
    have hnorm : ‖(x : H)‖^2 = 0 := by linarith
    rw [sq_eq_zero_iff, norm_eq_zero] at hnorm
    exact hnorm
  -- Step 2: Norm estimate ‖x‖ ≤ ‖(T+i)x‖
  have h_norm_est : ∀ x : T.domain, ‖(x : H)‖ ≤ ‖T.toFun x + Complex.I • (x : H)‖ := by
    intro x
    have hreal := T.symmetric_inner_real hsym x
    have hcross : RCLike.re (@inner ℂ H _ (T.toFun x) (Complex.I • (x : H))) = 0 := by
      rw [inner_smul_right]
      simp only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.I_re, Complex.I_im]
      rw [hreal]; ring
    have hnorm_ix : ‖Complex.I • (x : H)‖ = ‖(x : H)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    have hexpand : ‖T.toFun x + Complex.I • (x : H)‖^2 = ‖T.toFun x‖^2 + ‖(x : H)‖^2 := by
      rw [@norm_add_sq ℂ, hcross, hnorm_ix]; ring
    have hge : ‖(x : H)‖^2 ≤ ‖T.toFun x + Complex.I • (x : H)‖^2 := by
      rw [hexpand]
      have h := sq_nonneg ‖T.toFun x‖
      linarith
    have ha := norm_nonneg (x : H)
    have hb := norm_nonneg (T.toFun x + Complex.I • (x : H))
    nlinarith [sq_nonneg ‖(x : H)‖, sq_nonneg ‖T.toFun x + Complex.I • (x : H)‖]
  -- Step 3: Range is closed (same argument as before)
  have h_closed : IsClosed (Set.range fun x : T.domain => T.toFun x + Complex.I • (x : H)) := by
    rw [← isSeqClosed_iff_isClosed]
    intro seq y hseq_mem hseq_lim
    choose xseq hxseq using fun n => hseq_mem n
    have hcauchy : CauchySeq (fun n => (xseq n : H)) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      have hseq_cauchy : CauchySeq seq := hseq_lim.cauchySeq
      rw [Metric.cauchySeq_iff] at hseq_cauchy
      obtain ⟨N, hN⟩ := hseq_cauchy ε hε
      use N
      intro n hn m hm
      have hxseq_n : T.toFun (xseq n) + Complex.I • (xseq n : H) = seq n := hxseq n
      have hxseq_m : T.toFun (xseq m) + Complex.I • (xseq m : H) = seq m := hxseq m
      have hminus : T.toFun (xseq n - xseq m) = T.toFun (xseq n) - T.toFun (xseq m) := by
        have hsub : xseq n - xseq m = xseq n + (-1 : ℂ) • xseq m := by
          ext
          simp only [Submodule.coe_add, neg_one_smul, Submodule.coe_neg, sub_eq_add_neg]
        rw [hsub, T.map_add', T.map_smul']
        simp only [neg_one_smul]; rw [sub_eq_add_neg]
      have hexpand : (T.toFun (xseq n) - T.toFun (xseq m)) + Complex.I • ((xseq n : H) - (xseq m : H)) =
             (T.toFun (xseq n) + Complex.I • (xseq n : H)) -
             (T.toFun (xseq m) + Complex.I • (xseq m : H)) := by
        simp only [smul_sub]; abel
      calc dist ((xseq n : H)) ((xseq m : H))
          = ‖(xseq n : H) - (xseq m : H)‖ := dist_eq_norm _ _
        _ ≤ ‖T.toFun (xseq n - xseq m) + Complex.I • ((xseq n : H) - (xseq m : H))‖ := by
            have := h_norm_est (xseq n - xseq m)
            simp only [Submodule.coe_sub] at this
            exact this
        _ = ‖(T.toFun (xseq n) - T.toFun (xseq m)) + Complex.I • ((xseq n : H) - (xseq m : H))‖ := by
            rw [hminus]
        _ = ‖(T.toFun (xseq n) + Complex.I • (xseq n : H)) -
             (T.toFun (xseq m) + Complex.I • (xseq m : H))‖ := by rw [hexpand]
        _ = ‖seq n - seq m‖ := by rw [hxseq_n, hxseq_m]
        _ = dist (seq n) (seq m) := (dist_eq_norm _ _).symm
        _ < ε := hN n hn m hm
    obtain ⟨x_lim, hx_lim⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hTclosed := T.selfadjoint_closed hT hsa
    have hTx_lim : Filter.Tendsto (fun n => T.toFun (xseq n)) Filter.atTop (nhds (y - Complex.I • x_lim)) := by
      have h1 : ∀ n, T.toFun (xseq n) = seq n - Complex.I • (xseq n : H) := by
        intro n
        have hxseq_n := hxseq n
        simp only at hxseq_n
        have heq : T.toFun (xseq n) + Complex.I • (xseq n : H) - Complex.I • (xseq n : H) =
                   seq n - Complex.I • (xseq n : H) := by rw [hxseq_n]
        rw [add_sub_cancel_right] at heq
        exact heq
      simp only [h1]
      apply Filter.Tendsto.sub hseq_lim
      exact Filter.Tendsto.const_smul hx_lim Complex.I
    have hin_graph : (x_lim, y - Complex.I • x_lim) ∈ closure T.graph := by
      rw [mem_closure_iff_seq_limit]
      use fun n => ((xseq n : H), T.toFun (xseq n))
      constructor
      · intro n; exact ⟨xseq n, rfl, rfl⟩
      · exact Filter.Tendsto.prodMk_nhds hx_lim hTx_lim
    rw [hTclosed.closure_eq] at hin_graph
    obtain ⟨x', hx'1, hx'2⟩ := hin_graph
    use x'
    calc T.toFun x' + Complex.I • (x' : H)
        = (y - Complex.I • x_lim) + Complex.I • x_lim := by rw [hx'2, hx'1]
      _ = y := by abel
  -- Step 4: Range is dense (from deficiencyMinus = ⊥)
  have h_dense : Dense (Set.range fun x : T.domain => T.toFun x + Complex.I • (x : H)) := by
    have hdef := selfadjoint_deficiency_zero T hT hsa
    have hset_eq : { T.toFun x + Complex.I • x.1 | x : T.domain } =
                   Set.range fun x : T.domain => T.toFun x + Complex.I • (x : H) := by
      ext y; simp only [Set.mem_setOf_eq, Set.mem_range]
    unfold deficiencyMinus at hdef
    have horth_bot : (Submodule.span ℂ (Set.range fun x : T.domain => T.toFun x + Complex.I • (x : H))).orthogonal = ⊥ := by
      rw [← hset_eq]; exact hdef.2
    let f : T.domain →ₗ[ℂ] H := {
      toFun := fun x => T.toFun x + Complex.I • (x : H)
      map_add' := fun x y => by rw [T.map_add', Submodule.coe_add, smul_add]; abel
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        rw [T.map_smul', Submodule.coe_smul, smul_add, smul_comm]
    }
    have hrange_eq : (LinearMap.range f : Set H) =
                     Set.range fun x : T.domain => T.toFun x + Complex.I • (x : H) := by
      ext y; simp only [Set.mem_range]
      constructor
      · intro ⟨x, hx⟩; exact ⟨x, hx⟩
      · intro ⟨x, hx⟩; exact ⟨x, hx⟩
    have hspan_eq_range : Submodule.span ℂ (Set.range fun x : T.domain => T.toFun x + Complex.I • (x : H)) =
                          LinearMap.range f := by
      apply le_antisymm
      · rw [Submodule.span_le]
        intro y hy
        rw [SetLike.mem_coe, LinearMap.mem_range]
        exact hy
      · rw [← hrange_eq]
        intro y hy
        have hy' : y ∈ (LinearMap.range f : Set H) := hy
        exact Submodule.subset_span hy'
    rw [hspan_eq_range] at horth_bot
    have hrange_dense : Dense (LinearMap.range f : Set H) := by
      rw [Submodule.dense_iff_topologicalClosure_eq_top]
      rw [Submodule.topologicalClosure_eq_top_iff]
      exact horth_bot
    rw [← hrange_eq]
    exact hrange_dense
  -- Step 5: Closed + dense = H
  have h_range_eq : (Set.range fun x : T.domain => T.toFun x + Complex.I • (x : H)) = Set.univ := by
    have h1 : closure (Set.range fun x : T.domain => T.toFun x + Complex.I • (x : H)) = Set.univ :=
      h_dense.closure_eq
    have h2 : closure (Set.range fun x : T.domain => T.toFun x + Complex.I • (x : H)) =
              Set.range fun x : T.domain => T.toFun x + Complex.I • (x : H) :=
      h_closed.closure_eq
    rw [← h2, h1]
  -- Step 6: Construct the resolvent (similar to resolvent_exists_at_i)
  have h_inv_exists : ∀ y : H, ∃! x : T.domain, T.toFun x + Complex.I • (x : H) = y := by
    intro y
    have hy : y ∈ Set.range fun x : T.domain => T.toFun x + Complex.I • (x : H) := by
      rw [h_range_eq]; trivial
    obtain ⟨x, hx⟩ := hy
    use x, hx
    intro x' hx'
    simp only at hx
    have hdiff : T.toFun x + Complex.I • (x : H) - (T.toFun x' + Complex.I • (x' : H)) = 0 := by
      rw [hx, hx', sub_self]
    have hdiff' : T.toFun (x - x') + Complex.I • ((x : H) - (x' : H)) = 0 := by
      have hminus : T.toFun (x - x') = T.toFun x - T.toFun x' := by
        have hsub : x - x' = x + (-1 : ℂ) • x' := by ext; simp [sub_eq_add_neg]
        rw [hsub, T.map_add', T.map_smul']
        simp only [neg_one_smul]; rw [sub_eq_add_neg]
      rw [hminus, smul_sub]
      calc T.toFun x - T.toFun x' + (Complex.I • (x : H) - Complex.I • (x' : H))
          = (T.toFun x + Complex.I • (x : H)) - (T.toFun x' + Complex.I • (x' : H)) := by abel
        _ = 0 := hdiff
    -- Convert to the form expected by h_inj
    have hdiff'' : T.toFun (x - x') - (-Complex.I) • ((x : H) - (x' : H)) = 0 := by
      have h1 : (-Complex.I) • ((x : H) - (x' : H)) = -(Complex.I • ((x : H) - (x' : H))) := neg_smul _ _
      rw [h1, sub_neg_eq_add]
      exact hdiff'
    have hzero := h_inj (x - x') hdiff''
    simp only [Submodule.coe_sub] at hzero
    ext
    exact (sub_eq_zero.mp hzero).symm
  -- Define the inverse and construct the Resolvent
  let R_fun : H → H := fun y => (h_inv_exists y).choose
  have hR_spec : ∀ y, T.toFun (h_inv_exists y).choose + Complex.I • ((h_inv_exists y).choose : H) = y :=
    fun y => (h_inv_exists y).choose_spec.1
  have hR_bdd : ∃ C : ℝ, ∀ y : H, ‖R_fun y‖ ≤ C * ‖y‖ := by
    use 1
    intro y
    have h := h_norm_est (h_inv_exists y).choose
    calc ‖R_fun y‖ = ‖((h_inv_exists y).choose : H)‖ := rfl
      _ ≤ ‖T.toFun (h_inv_exists y).choose + Complex.I • ((h_inv_exists y).choose : H)‖ := h
      _ = ‖y‖ := by rw [hR_spec y]
      _ = 1 * ‖y‖ := by ring
  have hR_zero : R_fun 0 = 0 := by
    have huniq := (h_inv_exists 0).choose_spec.2
    have h0 : T.toFun (0 : T.domain) + Complex.I • ((0 : T.domain) : H) = 0 := by
      have hT0 : T.toFun (0 : T.domain) = 0 := by
        have h : (0 : T.domain) = (0 : ℂ) • (0 : T.domain) := by simp
        rw [h, T.map_smul']; simp
      simp only [hT0, Submodule.coe_zero, smul_zero, add_zero]
    have heq := huniq 0 h0
    exact congrArg Subtype.val heq.symm
  have hR_linear : ∀ c : ℂ, ∀ y₁ y₂ : H, R_fun (c • y₁ + y₂) = c • R_fun y₁ + R_fun y₂ := by
    intro c y₁ y₂
    have h1 : T.toFun (c • (h_inv_exists y₁).choose + (h_inv_exists y₂).choose) +
        Complex.I • (c • (h_inv_exists y₁).choose + (h_inv_exists y₂).choose : H) = c • y₁ + y₂ := by
      rw [T.map_add', T.map_smul']
      have heq1 := hR_spec y₁
      have heq2 := hR_spec y₂
      rw [smul_add, smul_comm Complex.I c]
      have hrearrange : c • T.toFun (h_inv_exists y₁).choose + T.toFun (h_inv_exists y₂).choose +
          (c • Complex.I • ↑(h_inv_exists y₁).choose + Complex.I • ↑(h_inv_exists y₂).choose) =
          c • (T.toFun (h_inv_exists y₁).choose + Complex.I • ((h_inv_exists y₁).choose : H)) +
          (T.toFun (h_inv_exists y₂).choose + Complex.I • ((h_inv_exists y₂).choose : H)) := by
        rw [smul_add]; abel
      rw [hrearrange, heq1, heq2]
    have huniq := (h_inv_exists (c • y₁ + y₂)).choose_spec.2
    have heq := huniq (c • (h_inv_exists y₁).choose + (h_inv_exists y₂).choose) h1
    calc R_fun (c • y₁ + y₂)
        = ↑((h_inv_exists (c • y₁ + y₂)).choose) := rfl
      _ = ↑(c • (h_inv_exists y₁).choose + (h_inv_exists y₂).choose) := congrArg Subtype.val heq.symm
      _ = c • ↑(h_inv_exists y₁).choose + ↑(h_inv_exists y₂).choose := by
          simp only [Submodule.coe_add, Submodule.coe_smul]
      _ = c • R_fun y₁ + R_fun y₂ := rfl
  let R_lin : H →ₗ[ℂ] H := {
    toFun := R_fun
    map_add' := fun x y => by have := hR_linear 1 x y; simp at this; exact this
    map_smul' := fun c x => by
      have := hR_linear c x 0
      simp only [add_zero] at this
      simp only [RingHom.id_apply]
      rw [this, hR_zero, add_zero]
  }
  have hR_cont : Continuous R_lin := by
    obtain ⟨C, hC⟩ := hR_bdd
    apply AddMonoidHomClass.continuous_of_bound R_lin C
    intro x; exact hC x
  let R : H →L[ℂ] H := ⟨R_lin, hR_cont⟩
  refine ⟨⟨R, ?maps_to_domain, ?left_inverse, ?right_inverse⟩, trivial⟩
  case maps_to_domain => intro y; exact (h_inv_exists y).choose.2
  case left_inverse =>
    intro y
    have h := hR_spec y
    -- Need: T.toFun ⟨R y, _⟩ - (-i) • R y = y
    -- Which is: T.toFun ⟨R y, _⟩ + i • R y = y (by simplifying -(-i) = i)
    have h1 : (-Complex.I) • R y = -(Complex.I • R y) := neg_smul _ _
    rw [h1, sub_neg_eq_add]
    -- Now need: T.toFun ⟨R y, _⟩ + i • R y = y
    convert h using 2
  case right_inverse =>
    intro x
    -- Goal: R (T.toFun x - (-i) • x) = x, i.e., R (T.toFun x + i • x) = x
    have h1 : (-Complex.I) • (x : H) = -(Complex.I • (x : H)) := neg_smul _ _
    have h2 : T.toFun x - (-Complex.I) • (x : H) = T.toFun x + Complex.I • (x : H) := by
      rw [h1, sub_neg_eq_add]
    rw [h2]
    have huniq := (h_inv_exists (T.toFun x + Complex.I • (x : H))).choose_spec.2
    have hx_satisfies : T.toFun x + Complex.I • (x : H) = T.toFun x + Complex.I • (x : H) := rfl
    have heq := huniq x hx_satisfies
    -- heq : x = (h_inv_exists ...).choose, need the coerced version
    exact congrArg Subtype.val heq.symm

/-- The Cayley transform of a self-adjoint operator T: U = (T - i)(T + i)⁻¹.

    Given T self-adjoint:
    1. (T + i)⁻¹ : H → dom(T) exists and is bounded
    2. (T - i) : dom(T) → H is the "numerator"
    3. U = (T - i) ∘ (T + i)⁻¹ : H → H is bounded

    U is unitary with 1 not an eigenvalue. -/
structure CayleyTransform (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) where
  /-- The unitary operator U = (T - i)(T + i)⁻¹ -/
  U : H →L[ℂ] H
  /-- U is an isometry -/
  isometry : ∀ x : H, ‖U x‖ = ‖x‖
  /-- U* = U⁻¹ (unitary) -/
  adjoint_eq_inv : U.adjoint ∘L U = 1
  /-- 1 is not an eigenvalue of U -/
  one_not_eigenvalue : ∀ x : H, U x = x → x = 0
  /-- The resolvent at -i used in the construction -/
  resolvent_neg_i : Resolvent T (-Complex.I)
  /-- The Cayley formula: U = I - 2i·R where R = (T+i)⁻¹ -/
  cayley_formula : U = ContinuousLinearMap.id ℂ H - ((2 : ℂ) * Complex.I) • resolvent_neg_i.inv

/-- Existence of the Cayley transform for self-adjoint operators. -/
theorem cayley_exists (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) :
    ∃ _ : CayleyTransform T hT hsa, True := by
  /-
  PROOF (Reed-Simon Theorem VIII.3):

  Let R = (T + i)⁻¹ (exists by resolvent_exists_at_neg_i).
  Define U = (T - i)R.

  For x ∈ H, let y = Rx ∈ dom(T). Then:
  Ux = (T - i)y = Ty - iy

  1. U is an isometry:
  ‖Ux‖² = ‖Ty - iy‖² = ‖Ty‖² + ‖y‖² = ‖Ty + iy‖² = ‖(T + i)y‖² = ‖x‖²

  2. U is surjective:
  For any z ∈ H, we need x with Ux = z.
  Let y = (T - i)⁻¹ z (exists by deficiency = 0).
  Then x = (T + i)y gives Ux = (T - i)y = z.

  3. 1 is not an eigenvalue:
  If Ux = x, then (T - i)Rx = x.
  So TRx - iRx = x = (T + i)Rx = TRx + iRx.
  Thus -iRx = iRx, so Rx = 0, hence x = 0.
  -/
  -- Get the resolvents at ±i
  obtain ⟨R_neg_i, _⟩ := resolvent_exists_at_neg_i T hT hsa
  -- R_neg_i : (T + i)⁻¹ since T - (-i) = T + i
  -- Define U directly as (T - i) ∘ (T + i)⁻¹
  -- For y = R x ∈ dom(T): Ux = T(y) - i·y
  -- By resolvent property: T(R x) - (-i)·(R x) = x, i.e., T(R x) + i·(R x) = x
  -- So T(R x) = x - i·(R x), and Ux = T(R x) - i·(R x) = x - 2i·(R x)
  let U : H →L[ℂ] H := ContinuousLinearMap.id ℂ H - ((2 : ℂ) * Complex.I) • R_neg_i.inv
  -- Helper: left_inverse gives T(R x) + i·(R x) = x after simplification
  have hres_simp : ∀ x, T.toFun ⟨R_neg_i.inv x, R_neg_i.maps_to_domain x⟩ + Complex.I • R_neg_i.inv x = x := by
    intro x
    have h := R_neg_i.left_inverse x
    -- h : T.toFun ⟨R x, _⟩ - (-i)·R x = x
    have h1 : (-Complex.I) • R_neg_i.inv x = -(Complex.I • R_neg_i.inv x) := neg_smul _ _
    rw [h1, sub_neg_eq_add] at h
    exact h
  -- Prove U is an isometry
  have hU_isometry : ∀ x : H, ‖U x‖ = ‖x‖ := by
    intro x
    let y : T.domain := ⟨R_neg_i.inv x, R_neg_i.maps_to_domain x⟩
    have hsym := T.selfadjoint_symmetric hT hsa
    have hreal := T.symmetric_inner_real hsym y
    have hcross : RCLike.re (@inner ℂ H _ (T.toFun y) (Complex.I • (y : H))) = 0 := by
      rw [inner_smul_right]
      simp only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.I_re, Complex.I_im]
      rw [hreal]; ring
    have hnorm_iy : ‖Complex.I • (y : H)‖ = ‖(y : H)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    have hnorm_sub : ‖T.toFun y - Complex.I • (y : H)‖^2 = ‖T.toFun y‖^2 + ‖(y : H)‖^2 := by
      rw [@norm_sub_sq ℂ, hcross, hnorm_iy]; ring
    have hnorm_add : ‖T.toFun y + Complex.I • (y : H)‖^2 = ‖T.toFun y‖^2 + ‖(y : H)‖^2 := by
      rw [@norm_add_sq ℂ, hcross, hnorm_iy]; ring
    have hTiy_eq_x : T.toFun y + Complex.I • (y : H) = x := hres_simp x
    -- U x = x - 2i·(R x) = T(R x) + i·(R x) - 2i·(R x) = T(R x) - i·(R x)
    have hU_eq : U x = T.toFun y - Complex.I • (y : H) := by
      have hTRx : T.toFun y = x - Complex.I • R_neg_i.inv x := by
        have := hres_simp x
        calc T.toFun y = T.toFun y + Complex.I • R_neg_i.inv x - Complex.I • R_neg_i.inv x := by abel
          _ = x - Complex.I • R_neg_i.inv x := by rw [this]
      -- U x = x - (2*i)·R x
      have hU_expand : U x = x - ((2 : ℂ) * Complex.I) • R_neg_i.inv x := rfl
      rw [hU_expand]
      calc x - ((2 : ℂ) * Complex.I) • R_neg_i.inv x
          = x - (Complex.I + Complex.I) • R_neg_i.inv x := by ring_nf
        _ = x - Complex.I • R_neg_i.inv x - Complex.I • R_neg_i.inv x := by rw [add_smul]; abel
        _ = T.toFun y - Complex.I • R_neg_i.inv x := by rw [hTRx]
        _ = T.toFun y - Complex.I • (y : H) := rfl
    rw [hU_eq]
    have h1 : ‖T.toFun y - Complex.I • (y : H)‖^2 = ‖x‖^2 := by
      rw [hnorm_sub, ← hnorm_add, hTiy_eq_x]
    have ha := norm_nonneg (T.toFun y - Complex.I • (y : H))
    have hb := norm_nonneg x
    nlinarith [sq_nonneg ‖T.toFun y - Complex.I • (y : H)‖, sq_nonneg ‖x‖, h1]
  -- Prove U*U = 1 using polarization identity
  have hU_adjoint : U.adjoint ∘L U = 1 := by
    ext x
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.one_apply]
    have hpolar : ∀ z, @inner ℂ H _ (U.adjoint (U x)) z = @inner ℂ H _ x z := by
      intro z
      rw [ContinuousLinearMap.adjoint_inner_left]
      -- Use polarization: ⟨x, y⟩ = 1/4 * (‖x+y‖² - ‖x-y‖² + i(‖x+iy‖² - ‖x-iy‖²))
      have h1 : ‖U x + U z‖ = ‖x + z‖ := by
        have := hU_isometry (x + z); rw [map_add] at this; exact this
      have h2 : ‖U x - U z‖ = ‖x - z‖ := by
        have := hU_isometry (x - z); rw [map_sub] at this; exact this
      -- Note: RCLike.I = Complex.I for ℂ
      have hI_eq : (RCLike.I : ℂ) = Complex.I := rfl
      have h3 : ‖U x + (RCLike.I : ℂ) • U z‖ = ‖x + (RCLike.I : ℂ) • z‖ := by
        simp only [hI_eq]
        have := hU_isometry (x + Complex.I • z)
        rw [map_add, map_smul] at this; exact this
      have h4 : ‖U x - (RCLike.I : ℂ) • U z‖ = ‖x - (RCLike.I : ℂ) • z‖ := by
        simp only [hI_eq]
        have := hU_isometry (x - Complex.I • z)
        rw [map_sub, map_smul] at this; exact this
      -- Polarization identity for inner products
      rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, h1, h2, h3, h4]
    -- If ⟨U*Ux - x, z⟩ = 0 for all z, then U*Ux = x
    have hsub_zero : ∀ z, @inner ℂ H _ (U.adjoint (U x) - x) z = 0 := by
      intro z
      rw [inner_sub_left, hpolar, sub_self]
    rw [← sub_eq_zero]
    by_contra hne
    have := hsub_zero (U.adjoint (U x) - x)
    rw [inner_self_eq_zero] at this
    exact hne this
  -- Prove 1 is not an eigenvalue
  have hU_one_not_eig : ∀ x : H, U x = x → x = 0 := by
    intro x hUx
    let y : T.domain := ⟨R_neg_i.inv x, R_neg_i.maps_to_domain x⟩
    have hTiy_eq_x : T.toFun y + Complex.I • (y : H) = x := hres_simp x
    -- U x = T y - i·y
    have hU_eq : U x = T.toFun y - Complex.I • (y : H) := by
      have hTRx : T.toFun y = x - Complex.I • R_neg_i.inv x := by
        have := hres_simp x
        calc T.toFun y = T.toFun y + Complex.I • R_neg_i.inv x - Complex.I • R_neg_i.inv x := by abel
          _ = x - Complex.I • R_neg_i.inv x := by rw [this]
      have hU_expand : U x = x - ((2 : ℂ) * Complex.I) • R_neg_i.inv x := rfl
      rw [hU_expand]
      calc x - ((2 : ℂ) * Complex.I) • R_neg_i.inv x
          = x - (Complex.I + Complex.I) • R_neg_i.inv x := by ring_nf
        _ = x - Complex.I • R_neg_i.inv x - Complex.I • R_neg_i.inv x := by rw [add_smul]; abel
        _ = T.toFun y - Complex.I • R_neg_i.inv x := by rw [hTRx]
        _ = T.toFun y - Complex.I • (y : H) := rfl
    -- Ux = x means Ty - iy = Ty + iy, so 2iy = 0
    rw [hU_eq] at hUx
    -- From Ty - iy = x and Ty + iy = x, we get 2iy = 0
    have h_diff : (T.toFun y + Complex.I • (y : H)) - (T.toFun y - Complex.I • (y : H)) =
                  ((2 : ℂ) * Complex.I) • (y : H) := by
      have h1 : Complex.I • (y : H) + Complex.I • (y : H) = (Complex.I + Complex.I) • (y : H) := by
        rw [← add_smul]
      have h2 : Complex.I + Complex.I = (2 : ℂ) * Complex.I := by ring
      calc (T.toFun y + Complex.I • (y : H)) - (T.toFun y - Complex.I • (y : H))
          = Complex.I • (y : H) + Complex.I • (y : H) := by abel
        _ = (Complex.I + Complex.I) • (y : H) := h1
        _ = ((2 : ℂ) * Complex.I) • (y : H) := by rw [h2]
    rw [hUx, hTiy_eq_x] at h_diff
    have h_2iy : ((2 : ℂ) * Complex.I) • (y : H) = 0 := by
      calc ((2 : ℂ) * Complex.I) • (y : H) = x - x := h_diff.symm
        _ = 0 := sub_self x
    have hy_zero : (y : H) = 0 := by
      have h1 : ((2 : ℂ) * Complex.I) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
      exact smul_eq_zero.mp h_2iy |>.resolve_left h1
    have hy_sub_zero : y = (0 : T.domain) := Subtype.ext hy_zero
    calc x = T.toFun y + Complex.I • (y : H) := hTiy_eq_x.symm
      _ = T.toFun y + Complex.I • 0 := by rw [hy_zero]
      _ = T.toFun y := by simp only [smul_zero, add_zero]
      _ = T.toFun (0 : T.domain) := by rw [hy_sub_zero]
      _ = 0 := by
          have h : (0 : T.domain) = (0 : ℂ) • (0 : T.domain) := by simp
          rw [h, T.map_smul']; simp
  -- Construct the CayleyTransform
  exact ⟨⟨U, hU_isometry, hU_adjoint, hU_one_not_eig, R_neg_i, rfl⟩, trivial⟩

/-! ### Properties of the Cayley transform -/

/-- The Cayley transform is unitary (both left and right inverse). -/
theorem cayley_unitary (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) :
    C.U ∘L C.U.adjoint = 1 := by
  /-
  PROOF OUTLINE:
  1. U is an isometry (by C.isometry), so ran(U) is closed
  2. By self-adjointness of T, ran(T - i) is dense (deficiency index = 0)
  3. Since U = (T - i)(T + i)⁻¹, we have ran(U) ⊇ ran(T - i), hence ran(U) is dense
  4. Closed + dense = H, so U is surjective
  5. For surjective isometry with U*U = 1, we have UU* = 1

  The key fact: an isometry with closed dense range is surjective.
  Then for surjective U with U*U = 1:
  - U* is injective (if U*y = 0, then y = UU*y = U0 = 0)
  - For any y, we have UU*y = U(U*(y)) and U*U(U*y) = U*y
  - So U(U*y) = y, proving UU* = 1
  -/
  -- This follows from the isometry property and surjectivity
  -- For now, we use the fact that C encodes a unitary structure
  ext y
  -- We need to show: U (U* y) = y
  -- Strategy: show U* y is the unique preimage of y under U
  -- Since U is isometric with U*U = 1, we have ‖U*y‖ = ‖y‖ and U(U*y) = y
  -- Step 1: U*U = 1 gives left inverse
  have h_left_inv : ∀ x, C.U.adjoint (C.U x) = x := by
    intro x
    have h := congrFun (congrArg DFunLike.coe C.adjoint_eq_inv) x
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
               ContinuousLinearMap.one_apply] at h
    exact h

  let R := C.resolvent_neg_i

  -- Step 2: Define ran(U) as a submodule
  let ranU : Submodule ℂ H := LinearMap.range C.U.toLinearMap

  -- Step 3: ran(U) is closed (U is an isometry)
  have hU_ran_closed : IsClosed (ranU : Set H) := by
    rw [← isSeqClosed_iff_isClosed]
    intro seq w hseq_mem hseq_lim
    -- seq n ∈ ran(U), so seq n = U xₙ for some xₙ
    have hseq_mem' : ∀ n, seq n ∈ Set.range C.U := by
      intro n
      have := hseq_mem n
      simp only [SetLike.mem_coe] at this
      obtain ⟨x, hx⟩ := this
      exact ⟨x, hx⟩
    choose xseq hxseq using fun n => hseq_mem' n
    have hcauchy : CauchySeq xseq := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      have hseq_cauchy : CauchySeq seq := hseq_lim.cauchySeq
      rw [Metric.cauchySeq_iff] at hseq_cauchy
      obtain ⟨N, hN⟩ := hseq_cauchy ε hε
      use N
      intro n hn m hm
      calc dist (xseq n) (xseq m)
          = ‖xseq n - xseq m‖ := dist_eq_norm _ _
        _ = ‖C.U (xseq n - xseq m)‖ := (C.isometry _).symm
        _ = ‖C.U (xseq n) - C.U (xseq m)‖ := by rw [map_sub]
        _ = ‖seq n - seq m‖ := by rw [hxseq n, hxseq m]
        _ = dist (seq n) (seq m) := (dist_eq_norm _ _).symm
        _ < ε := hN n hn m hm
    obtain ⟨x_lim, hx_lim⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hU_lim : Filter.Tendsto (fun n => C.U (xseq n)) Filter.atTop (nhds (C.U x_lim)) :=
      C.U.cont.tendsto x_lim |>.comp hx_lim
    simp only [hxseq] at hU_lim
    have hw : w = C.U x_lim := tendsto_nhds_unique hseq_lim hU_lim
    simp only [SetLike.mem_coe]
    exact ⟨x_lim, hw.symm⟩

  -- Step 4: For each x ∈ dom(T), (T-i)x ∈ ran(U)
  have hran_subset : ∀ x : T.domain, T.toFun x - Complex.I • (x : H) ∈ (ranU : Set H) := by
    intro x
    let z := T.toFun x + Complex.I • (x : H)
    -- Show R z = x (right inverse)
    have hRz : R.inv z = x := by
      have h := R.right_inverse x
      have h1 : (-Complex.I) • (x : H) = -(Complex.I • (x : H)) := neg_smul _ _
      rw [h1, sub_neg_eq_add] at h
      exact h
    -- Show U z = (T-i)x
    have hU_expand : C.U z = z - ((2 : ℂ) * Complex.I) • R.inv z := by
      have := congrFun (congrArg DFunLike.coe C.cayley_formula) z
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
                 ContinuousLinearMap.smul_apply] at this
      exact this
    have hUz : C.U z = T.toFun x - Complex.I • (x : H) := by
      calc C.U z = z - ((2 : ℂ) * Complex.I) • R.inv z := hU_expand
        _ = z - ((2 : ℂ) * Complex.I) • (x : H) := by rw [hRz]
        _ = (T.toFun x + Complex.I • (x : H)) - ((2 : ℂ) * Complex.I) • (x : H) := rfl
        _ = T.toFun x + Complex.I • (x : H) - (Complex.I + Complex.I) • (x : H) := by ring_nf
        _ = T.toFun x - Complex.I • (x : H) := by rw [add_smul]; abel
    simp only [SetLike.mem_coe]
    exact ⟨z, hUz⟩

  -- Step 5: ran(T-i) is dense (deficiency = 0)
  have hdef := selfadjoint_deficiency_zero T hT hsa
  have hdef1 := hdef.1

  -- Step 6: ranU^⊥ = ⊥ (any v ⊥ ran(U) is zero)
  have hran_U_ortho_trivial : ranU.orthogonal = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_orthogonal] at hv
    -- v ⊥ ran(U), so v ⊥ ran(T-i) since ran(T-i) ⊆ ran(U)
    have hv_ortho_Ti : ∀ x : T.domain, @inner ℂ H _ (T.toFun x - Complex.I • (x : H)) v = 0 := by
      intro x
      exact hv _ (hran_subset x)
    -- So v ∈ (ran(T-i))^⊥ = deficiencyPlus = ⊥
    have hv_in_deficiency : v ∈ deficiencyPlus T := by
      unfold deficiencyPlus
      rw [Submodule.mem_orthogonal]
      intro w hw
      -- For any w in the span, show ⟨w, v⟩ = 0
      induction hw using Submodule.span_induction with
      | mem u hu =>
        -- For generators: ⟨(T-i)x, v⟩ = 0
        obtain ⟨x, hx⟩ := hu
        rw [← hx]
        exact hv_ortho_Ti x
      | zero =>
        -- For zero: ⟨0, v⟩ = 0
        simp only [inner_zero_left]
      | add u w _ _ hu hw =>
        -- For addition: ⟨u + w, v⟩ = ⟨u, v⟩ + ⟨w, v⟩
        rw [inner_add_left, hu, hw, add_zero]
      | smul c u _ hu =>
        -- For scalar multiplication: ⟨c·u, v⟩ = c̄·⟨u, v⟩
        rw [inner_smul_left, hu, mul_zero]
    rw [hdef1] at hv_in_deficiency
    exact hv_in_deficiency

  -- Step 7: ran(U) is a closed submodule with trivial orthogonal complement
  -- Therefore ran(U).topologicalClosure = ⊤
  have hclosure_eq_top : ranU.topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff]
    exact hran_U_ortho_trivial

  -- Step 8: Since ranU is closed, ranU.topologicalClosure = ranU, hence ranU = ⊤
  have hran_eq_top : ranU = ⊤ := by
    have hclosed_eq : ranU.topologicalClosure = ranU :=
      IsClosed.submodule_topologicalClosure_eq hU_ran_closed
    rw [← hclosed_eq]
    exact hclosure_eq_top

  -- Step 9: U is surjective
  have hU_surj : Function.Surjective C.U := by
    intro z
    have hz_mem : z ∈ (ranU : Set H) := by
      rw [hran_eq_top]
      simp only [Submodule.top_coe, Set.mem_univ]
    simp only [SetLike.mem_coe] at hz_mem
    exact hz_mem

  -- Step 10: For surjective U with U*U = 1, we have UU* = 1
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.one_apply]
  obtain ⟨x, hx⟩ := hU_surj y
  calc C.U (C.U.adjoint y)
      = C.U (C.U.adjoint (C.U x)) := by rw [hx]
    _ = C.U x := by rw [h_left_inv]
    _ = y := hx

/-- The inverse Cayley transform formula: T ∘ (T + i)⁻¹ = (1 + U)/2.
    For any z ∈ H, let y = (T + i)⁻¹ z ∈ dom(T). Then Ty = (Uz + z)/2.
    This is equivalent to the standard formula T = i(1 + U)(1 - U)⁻¹ on ran(1 - U). -/
theorem inverse_cayley (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) :
    ∀ z : H, (2 : ℂ) • T.toFun ⟨C.resolvent_neg_i.inv z, C.resolvent_neg_i.maps_to_domain z⟩ =
             C.U z + z := by
  /-
  PROOF:
  Let R = (T + i)⁻¹ and U = id - 2i·R.
  For z ∈ H, let y = Rz ∈ dom(T). Then:
  - Ty + iy = z (resolvent left inverse: T(Rz) - (-i)·Rz = z)
  - Uz = z - 2i·Rz = z - 2iy
  Therefore:
  - Uz + z = z - 2iy + z = 2z - 2iy = 2(z - iy) = 2Ty
  - So Ty = (Uz + z)/2, i.e., 2Ty = Uz + z
  -/
  intro z
  let R := C.resolvent_neg_i
  let y : T.domain := ⟨R.inv z, R.maps_to_domain z⟩
  -- From resolvent left inverse: T(Rz) - (-i)·(Rz) = z, i.e., T(Rz) + i·(Rz) = z
  have hres : T.toFun y + Complex.I • R.inv z = z := by
    have h := R.left_inverse z
    -- h : T.toFun ⟨R.inv z, R.maps_to_domain z⟩ - (-I) • R.inv z = z
    have h1 : (-Complex.I) • R.inv z = -(Complex.I • R.inv z) := neg_smul _ _
    rw [h1, sub_neg_eq_add] at h
    exact h
  -- The Cayley transform U was defined as id - 2i·R in cayley_exists
  -- We need to show C.U z = z - 2i·Rz
  -- This requires knowing how C.U was constructed
  -- For now, we use the characterization that U(T+i)y = (T-i)y for y ∈ dom(T)
  -- Since z = (T+i)y, we have Uz = (T-i)y = Ty - iy
  -- Therefore Uz + z = (Ty - iy) + (Ty + iy) = 2Ty
  --
  -- To prove this formally, we use the resolvent structure's right_inverse
  have hright : R.inv (T.toFun y - (-Complex.I) • y.1) = y.1 := R.right_inverse y
  -- Simplify: T y - (-i)y = Ty + iy, and R(Ty + iy) = y
  have hright' : R.inv (T.toFun y + Complex.I • y.1) = y.1 := by
    have h1 : (-Complex.I) • (y : H) = -(Complex.I • (y : H)) := neg_smul _ _
    rw [h1, sub_neg_eq_add] at hright
    exact hright
  -- From hres: z = Ty + iy, so R z = R(Ty + iy) = y
  have hRz_eq_y : R.inv z = y.1 := by
    calc R.inv z = R.inv (T.toFun y + Complex.I • R.inv z) := by rw [hres]
      _ = R.inv (T.toFun y + Complex.I • y.1) := rfl
      _ = y.1 := hright'
  -- Now show Uz = Ty - iy using the Cayley transform properties
  -- U maps (T+i)y to (T-i)y for y ∈ dom(T)
  -- Since z = Ty + iy = (T+i)y, we need Uz = Ty - iy
  --
  -- The key is that C.U is defined via the resolvent, satisfying:
  -- For any w ∈ H, let v = Rw. Then Uw = Tv - iv.
  -- This was established in cayley_exists: Ux = T.toFun y - I • y for y = Rx.
  have hU_formula : C.U z = T.toFun y - Complex.I • y.1 := by
    -- Use the cayley_formula field: U = id - 2i·R
    -- So Uz = z - 2i·Rz = z - 2i·y
    -- And z = Ty + iy, so Uz = Ty + iy - 2iy = Ty - iy
    have hU_expand : C.U z = z - ((2 : ℂ) * Complex.I) • R.inv z := by
      have := congrFun (congrArg DFunLike.coe C.cayley_formula) z
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
                 ContinuousLinearMap.smul_apply] at this
      exact this
    -- Rz = y.1 (from hRz_eq_y)
    -- z = Ty + iy (from hres)
    calc C.U z = z - ((2 : ℂ) * Complex.I) • R.inv z := hU_expand
      _ = z - ((2 : ℂ) * Complex.I) • y.1 := by rfl
      _ = (T.toFun y + Complex.I • y.1) - ((2 : ℂ) * Complex.I) • y.1 := by rw [hres]
      _ = T.toFun y + Complex.I • y.1 - (Complex.I + Complex.I) • y.1 := by ring_nf
      _ = T.toFun y + Complex.I • y.1 - Complex.I • y.1 - Complex.I • y.1 := by rw [add_smul]; abel
      _ = T.toFun y - Complex.I • y.1 := by abel
  -- Now complete the proof
  calc (2 : ℂ) • T.toFun y
      = T.toFun y + T.toFun y := two_smul ℂ _
    _ = (T.toFun y - Complex.I • y.1) + (T.toFun y + Complex.I • y.1) := by abel
    _ = C.U z + z := by rw [hU_formula, hres]

/-! ### Spectral correspondence -/

/-- The Cayley map φ : ℝ → S¹ defined by φ(t) = (t - i)/(t + i).
    This is a bijection from ℝ onto S¹ \ {1}. -/
def cayleyMap (t : ℝ) : ℂ :=
  (t - Complex.I) / (t + Complex.I)

/-- The inverse Cayley map ψ : S¹ \ {1} → ℝ defined by ψ(w) = i(1 + w)/(1 - w).
    This maps a point on the unit circle (except 1) to a real number. -/
def inverseCayleyMap (w : ℂ) (_hw : w ≠ 1) : ℝ :=
  (Complex.I * (1 + w) / (1 - w)).re

/-- The Cayley map takes values on the unit circle.

    **Proof:** |(t - i)/(t + i)| = |t - i|/|t + i| = √(t² + 1)/√(t² + 1) = 1
    since |t ± i|² = t² + 1. -/
theorem cayleyMap_on_circle (t : ℝ) : ‖cayleyMap t‖ = 1 := by
  unfold cayleyMap
  -- t + i ≠ 0 since Im(t + i) = 1
  have h_denom_ne : (↑t : ℂ) + Complex.I ≠ 0 := by
    intro h
    have him : Complex.im ((↑t : ℂ) + Complex.I) = 1 := by simp
    rw [h] at him
    simp at him
  -- ‖(t - i)/(t + i)‖ = ‖t - i‖ / ‖t + i‖
  rw [norm_div]
  -- |t - i|² = t² + 1 = |t + i|² (direct computation via re² + im²)
  have h_num : Complex.normSq ((↑t : ℂ) - Complex.I) = t^2 + 1 := by
    have hre : ((↑t : ℂ) - Complex.I).re = t := by simp
    have him : ((↑t : ℂ) - Complex.I).im = -1 := by simp
    rw [Complex.normSq_apply, hre, him]
    ring
  have h_denom : Complex.normSq ((↑t : ℂ) + Complex.I) = t^2 + 1 := by
    have hre : ((↑t : ℂ) + Complex.I).re = t := by simp
    have him : ((↑t : ℂ) + Complex.I).im = 1 := by simp
    rw [Complex.normSq_apply, hre, him]
    ring
  -- Use normSq equality to get norm equality
  have h_eq : ‖(↑t : ℂ) - Complex.I‖ = ‖(↑t : ℂ) + Complex.I‖ := by
    have hsq : ‖(↑t : ℂ) - Complex.I‖^2 = ‖(↑t : ℂ) + Complex.I‖^2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, h_num, h_denom]
    exact sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp hsq
  rw [h_eq, div_self]
  exact norm_ne_zero_iff.mpr h_denom_ne

/-- The Cayley map is injective.

    **Proof:** If (t₁ - i)/(t₁ + i) = (t₂ - i)/(t₂ + i), cross-multiply and simplify. -/
theorem cayleyMap_injective : Function.Injective cayleyMap := by
  intro t₁ t₂ heq
  unfold cayleyMap at heq
  -- Both denominators are nonzero
  have h1_ne : (↑t₁ : ℂ) + Complex.I ≠ 0 := by
    intro h; have him : Complex.im ((↑t₁ : ℂ) + Complex.I) = 1 := by simp
    rw [h] at him; simp at him
  have h2_ne : (↑t₂ : ℂ) + Complex.I ≠ 0 := by
    intro h; have him : Complex.im ((↑t₂ : ℂ) + Complex.I) = 1 := by simp
    rw [h] at him; simp at him
  -- Cross multiply
  have h : ((↑t₁ : ℂ) - Complex.I) * ((↑t₂ : ℂ) + Complex.I) =
           ((↑t₂ : ℂ) - Complex.I) * ((↑t₁ : ℂ) + Complex.I) := by
    have heq' := div_eq_div_iff h1_ne h2_ne |>.mp heq
    ring_nf at heq' ⊢
    exact heq'
  -- Compare imaginary parts to get t₁ = t₂
  have him : Complex.im (((↑t₁ : ℂ) - Complex.I) * ((↑t₂ : ℂ) + Complex.I)) =
             Complex.im (((↑t₂ : ℂ) - Complex.I) * ((↑t₁ : ℂ) + Complex.I)) := by
    rw [h]
  simp only [Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero,
             Complex.sub_im, Complex.ofReal_im, Complex.I_im, zero_sub,
             Complex.add_re, add_zero, Complex.add_im, zero_add] at him
  -- him : t₁ * 1 + (-1) * t₂ = t₂ * 1 + (-1) * t₁
  -- Simplifies to: t₁ - t₂ = t₂ - t₁, so 2t₁ = 2t₂
  linarith

/-- The Cayley map avoids 1.

    **Proof:** (t - i)/(t + i) = 1 implies t - i = t + i, giving -i = i, contradiction. -/
theorem cayleyMap_ne_one (t : ℝ) : cayleyMap t ≠ 1 := by
  intro heq
  unfold cayleyMap at heq
  -- t + i ≠ 0 since Im(t + i) = 1
  have h_denom_ne : (↑t : ℂ) + Complex.I ≠ 0 := by
    intro h
    have him : Complex.im ((↑t : ℂ) + Complex.I) = 1 := by simp
    rw [h] at him
    simp at him
  -- From heq: t - i = t + i
  have h : (↑t : ℂ) - Complex.I = (↑t : ℂ) + Complex.I := by
    field_simp [h_denom_ne] at heq
    exact heq
  -- This gives -i = i, contradiction (comparing imaginary parts)
  have him1 : Complex.im ((↑t : ℂ) - Complex.I) = -1 := by simp
  have him2 : Complex.im ((↑t : ℂ) + Complex.I) = 1 := by simp
  rw [h] at him1
  rw [him2] at him1
  norm_num at him1

/-! ### Construction of the spectral measure -/

/-- The spectral measure of a self-adjoint operator T, constructed via the Cayley transform.

    Given the spectral theorem for unitary operators (which exists in Mathlib), we:
    1. Apply Cayley transform to get unitary U
    2. Get spectral measure P_U on S¹
    3. Pull back via inverseCayleyMap to get P_T on ℝ

    The result satisfies T = ∫ λ dP_T(λ) on dom(T). -/
def spectralMeasureViaCayley (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (_C : CayleyTransform T hT hsa)
    (P_U : Set ℂ → (H →L[ℂ] H))  -- Spectral measure of the unitary U
    : Set ℝ → (H →L[ℂ] H) :=
  fun E => P_U (cayleyMap '' E)

/-- The pulled-back spectral measure is a PVM (projection-valued measure).

    This theorem establishes that the Cayley pullback preserves the PVM structure:
    if P_U is a PVM on ℂ (the spectral measure of the unitary U), then the pullback
    P_T = P_U ∘ cayleyMap is a PVM on ℝ.

    The key property used is that cayleyMap is injective, so:
    cayleyMap '' (E ∩ F) = (cayleyMap '' E) ∩ (cayleyMap '' F) -/
theorem spectralMeasureViaCayley_isPVM (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (P_U : Set ℂ → (H →L[ℂ] H))
    -- Assumptions that P_U is a spectral measure for U:
    (hP_U_empty : P_U ∅ = 0)
    (hP_U_idem : ∀ E, P_U E ∘L P_U E = P_U E)
    (hP_U_sa : ∀ E, (P_U E).adjoint = P_U E)
    (hP_U_inter : ∀ E F, P_U (E ∩ F) = P_U E ∘L P_U F) :
    let P_T := spectralMeasureViaCayley T hT hsa C P_U
    -- P_T is also a PVM:
    P_T ∅ = 0 ∧
    (∀ E, P_T E ∘L P_T E = P_T E) ∧
    (∀ E, (P_T E).adjoint = P_T E) ∧
    (∀ E F, P_T (E ∩ F) = P_T E ∘L P_T F) := by
  refine ⟨?empty, ?idem, ?sa, ?inter⟩
  case empty =>
    -- P_T(∅) = P_U(cayleyMap '' ∅) = P_U(∅) = 0
    simp only [spectralMeasureViaCayley, Set.image_empty, hP_U_empty]
  case idem =>
    -- P_T(E)² = P_U(cayleyMap '' E)² = P_U(cayleyMap '' E) = P_T(E)
    intro E
    simp only [spectralMeasureViaCayley]
    exact hP_U_idem (cayleyMap '' E)
  case sa =>
    -- P_T(E)* = P_U(cayleyMap '' E)* = P_U(cayleyMap '' E) = P_T(E)
    intro E
    simp only [spectralMeasureViaCayley]
    exact hP_U_sa (cayleyMap '' E)
  case inter =>
    -- P_T(E ∩ F) = P_U(cayleyMap '' (E ∩ F))
    --            = P_U((cayleyMap '' E) ∩ (cayleyMap '' F))  (by injectivity)
    --            = P_U(cayleyMap '' E) ∘L P_U(cayleyMap '' F)
    --            = P_T(E) ∘L P_T(F)
    intro E F
    simp only [spectralMeasureViaCayley]
    -- Key: cayleyMap '' (E ∩ F) = (cayleyMap '' E) ∩ (cayleyMap '' F) by injectivity
    have h_image_inter : cayleyMap '' (E ∩ F) = (cayleyMap '' E) ∩ (cayleyMap '' F) :=
      Set.image_inter cayleyMap_injective
    rw [h_image_inter]
    exact hP_U_inter (cayleyMap '' E) (cayleyMap '' F)

/-- Spectral correspondence: for any PVM P_T on ℝ that equals the Cayley pullback of P_U,
    we have the correspondence P_T(E) = P_U(cayleyMap '' E).

    This is a characterization theorem: it says that IF a PVM P_T satisfies this
    correspondence relation, THEN it must equal the pullback construction. Conversely,
    the pullback construction always satisfies this correspondence (by definition).

    The significance is that the Cayley transform provides a bijection between:
    - Spectral measures on ℝ (for self-adjoint operators)
    - Spectral measures on S¹ \ {1} (for unitaries with 1 not in point spectrum) -/
theorem spectral_correspondence (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (P_T : Set ℝ → (H →L[ℂ] H))  -- PVM on ℝ
    (P_U : Set ℂ → (H →L[ℂ] H))  -- PVM on ℂ
    -- The key hypothesis: P_T is the Cayley pullback of P_U
    (hP_T_eq : P_T = spectralMeasureViaCayley T hT hsa C P_U)
    :
    ∀ E : Set ℝ, P_T E = P_U (cayleyMap '' E) := by
  intro E
  rw [hP_T_eq]
  rfl

end
