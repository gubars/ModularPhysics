# vNA Module TODO

## Overview

This module develops von Neumann algebra foundations for rigorous QFT, including:
- Unbounded self-adjoint operators
- Spectral theory via Riesz-Markov-Kakutani (RMK)
- Stone's theorem for one-parameter unitary groups
- Modular theory (Tomita-Takesaki)

## Current Status

### Spectral Theory via RMK (Primary Approach)

The RMK-based approach constructs spectral measures using the Riesz representation theorem,
avoiding the circular dependencies of the traditional CFC approach.

| File | Status | Sorrys |
|------|--------|--------|
| `Spectral/SpectralFunctionalViaRMK.lean` | Complete | 0 |
| `Spectral/SpectralMeasurePolarizedViaRMK.lean` | Complete | 0 |
| `Spectral/SpectralTheoremViaRMK.lean` | Complete | 0 |
| `Spectral/SpectralViaCayleyRMK.lean` | **Complete** | 0 |
| `Spectral/TPConnection.lean` | **In Progress** | 4 (10 theorems proven, 4 remaining) |

### Completed Sorrys in SpectralViaCayleyRMK.lean

All three sorrys have been resolved:

1. ✅ **`hU_P_eq_P`**: Proved `U ∘L P({1}) = P({1})` using dominated convergence
   - Used decomposition: id = Re + i·Im on Circle
   - Proved Re·g_n → χ_{1} and Im·g_n → 0 pointwise
   - Applied `spectralFunctionalAux_tendsto_of_pointwise_general` for weak convergence

2. ✅ **`hP_eigenvector`**: Proved `U (P y) = P y`
   - Followed directly from `unitary_comp_spectralProjection_singleton_one`

3. ✅ **`spectralMeasureFromRMK_univ`**: Proved `P(ℝ) = 1`
   - Showed `μ_{x,y}({1}) = 0` using `P({1}) = 0` and sesquilinear form
   - Used measure additivity: `μ(univ) = μ({z ≠ 1}) + μ({1})`
   - Concluded `μ(cayleyToCircle '' univ) = ⟨x, y⟩`

### T-P Connection (Current Focus)

The file `Spectral/TPConnection.lean` establishes the crucial connection between a self-adjoint
operator T and its spectral measure P: the spectral representation `f(T) = ∫ f(λ) dP(λ)`.

**Completed (sorry-free):**
- `spectralMeasureDiagonalOnR`: Diagonal spectral measure on ℝ as pullback via cayleyToCircle
- `spectralMeasurePolarizedOnR`: Polarized spectral measure on ℝ
- `TP_connection_indicator`: T-P connection for indicator functions: `⟨x, P(E) y⟩ = μ^ℝ_{x,y}(E)`
- `spectralMeasureDiagonal_singleton_one_eq_zero`: μ_z({1}) = 0 for Cayley transforms
- `cfcViaInverseCayley_continuousOn`: Continuity on Circle \ {1}
- `integral_circle_eq_integral_minus_one`: ∫ g dμ = ∫_{Circle\{1}} g dμ (since μ({1}) = 0)

**Remaining sorrys (4):**
1. `integral_spectralMeasureDiagonalOnR_eq_circle`: Change of variables formula
   - ∫ f dμ^ℝ = ∫ g dμ^Circle where g = f ∘ inverseCayley (extended to Circle)
   - Requires MeasureTheory infrastructure for comap integrals

2. `TP_connection`: Main theorem connecting `⟨x, UnboundedCFC T f y⟩` to spectral integral
   - Requires extending `spectralMeasurePolarized_integral` from compactly supported to bounded continuous functions
   - Key insight: μ({1}) = 0 means integrals over Circle equal integrals over Circle \ {1}

3. `TP_connection_diagonal`: `‖f(T) z‖² = ∫_ℝ |f(λ)|² dμ^ℝ_z(λ)`
   - Follows from `TP_connection` by polarization

4. `spectral_theorem_TP_connection`: `⟨x, T y⟩ = μ^ℝ_{x,y}(ℝ)`
   - Requires showing `UnboundedCFC T id = T` on dom(T)

**Proof Strategy for TP_connection:**
1. `UnboundedCFC T f = cfc (cfcViaInverseCayley f) U` (by definition)
2. Use polarization: `⟨x, cfc g U y⟩ = (1/4)[Λ_{x+y}(g) - ...]`
3. Each `Λ_z(g) = Re⟨z, cfc g U z⟩ = ∫ g dμ_z` (by RMK for bounded continuous g)
4. Since `μ_z({1}) = 0`, integral over Circle = integral over Circle \ {1}
5. Change of variables: `∫_{Circle\{1}} g dμ^Circle = ∫_ℝ f dμ^ℝ` (g = f ∘ inverseCayley)

### Legacy Approach (Lower Priority)

The original approach uses CFC directly but has many sorrys due to circularity issues.

| File | Status | Sorrys |
|------|--------|--------|
| `Unbounded/Spectral.lean` | Needs Migration | 11 |
| `Unbounded/StoneTheorem.lean` | Needs Migration | 9 |
| `Spectral/FunctionalCalculusFromCFC.lean` | Superseded | 27 |
| `Spectral/FunctionalCalculusFromCFC/Basic.lean` | Superseded | 1 |

## Action Items

### High Priority

- [x] ~~Complete `hU_P_eq_P` using RMK infrastructure~~ ✅ DONE
- [x] ~~Complete `hP_eigenvector`~~ ✅ DONE
- [x] ~~Complete `spectralMeasureFromRMK_univ`~~ ✅ DONE

**The spectral theorem via RMK is now complete!** All proofs in the RMK chain are sorry-free.

### Medium Priority (Current Focus)

- [ ] **Complete `TP_connection` in `Spectral/TPConnection.lean`** ← ACTIVE
  - Extend `spectralMeasurePolarized_integral` to bounded continuous functions
  - Use dominated convergence with `spectralFunctionalAux_tendsto_of_pointwise_general`
  - Apply change of variables via `cayleyToCircle` bijection

- [ ] Fill `spectral_theorem` sorry in `Unbounded/Spectral.lean` using `TPConnection.lean`
  - Import `TPConnection.lean` and use `TP_connection_indicator` for PVM properties
  - Use `TP_connection` for the integral representation

- [ ] Migrate `Unbounded/StoneTheorem.lean` to use RMK-based spectral theorem
  - One-parameter unitary group construction from spectral measure
  - Generator extraction via Stone's theorem

### Low Priority

- [ ] Clean up or deprecate `FunctionalCalculusFromCFC.lean`
- [ ] Add documentation for the RMK approach
- [ ] Consider extracting common lemmas to separate files

## Path to Stone's Theorem

Stone's theorem establishes a 1-1 correspondence:
- **Forward**: Self-adjoint operator T → one-parameter unitary group U(t) = exp(itT)
- **Inverse**: One-parameter unitary group U(t) → self-adjoint generator A

### Forward Direction (from RMK spectral theorem)

The PVM algebraic properties via RMK are complete:
```
spectralMeasure_isPVM_via_RMK : ∀ T self-adjoint, ∃ P : PVM on ℝ (algebraic properties only)
```

**Note**: This proves P is a valid PVM (empty, univ, idempotent, selfAdjoint, multiplicative).
The T-P connection (T = ∫ λ dP(λ)) is NOT yet proven - see `spectral_theorem` in Spectral.lean.

The one-parameter unitary group is then defined via spectral integration:
```lean
U(t) := ∫ exp(itλ) dP(λ)
```

**Key steps to prove:**
1. `U(t)` is well-defined (spectral integral of bounded function)
2. `U(t)` is unitary: `U(t)* = U(-t)` (since `exp(itλ)* = exp(-itλ)`)
3. Group property: `U(s+t) = U(s) U(t)` (by CFC multiplicativity)
4. Strong continuity: `U(t)x → x` as `t → 0` (dominated convergence)
5. Generator recovery: `dU(t)/dt|_{t=0} = iT` on dom(T)

### Inverse Direction

Given a strongly continuous one-parameter unitary group U(t):

1. **Define the generator domain:**
   ```
   dom(A) = { x ∈ H : lim_{t→0} (U(t)x - x)/(it) exists }
   ```

2. **Show dom(A) is dense:**
   - For smooth φ with compact support, x_φ := ∫ φ(t) U(t)x dt ∈ dom(A)
   - Taking φ → δ gives density

3. **Show A is symmetric:**
   - ⟨Ax, y⟩ = lim_{t→0} ⟨(U(t)x - x)/(it), y⟩
   - Use U(t)* = U(-t) and inner product continuity

4. **Show A is self-adjoint (the hard part):**
   - Symmetry gives A ⊆ A*
   - Must show dom(A*) ⊆ dom(A)
   - Strategy: For y ∈ dom(A*), show ∫₀^t U(s)y ds ∈ dom(A)
     and differentiate to get y ∈ dom(A)

5. **Show U(t) = exp(itA):**
   - Define V(t) := exp(itA) from spectral theorem
   - Show V satisfies same ODE as U
   - Conclude V = U by uniqueness

### Implementation Strategy

After completing `SpectralViaCayleyRMK.lean`:

1. **New file: `StoneTheoremViaRMK.lean`**
   - Import `SpectralViaCayleyRMK.lean`
   - Define `exp_i_t_T : ℝ → (H →L[ℂ] H)` via spectral integral
   - Prove it forms a strongly continuous unitary group
   - Prove generator recovery theorem

2. **Migrate existing `StoneTheorem.lean`:**
   - Replace sorrys with proofs using RMK infrastructure
   - Key: use `spectralMeasureFromRMK` for the PVM
   - The generator domain computation uses spectral theory

### Dependencies

```
SpectralFunctionalViaRMK.lean           [complete]
         ↓
SpectralMeasurePolarizedViaRMK.lean     [complete]
         ↓
SpectralTheoremViaRMK.lean              [complete]
         ↓
CayleyTransform.lean                    [complete]
         ↓
SpectralViaCayleyRMK.lean               [complete] ✅
         ↓
TPConnection.lean                       [in progress, 4 sorrys] ← CURRENT FOCUS
         ↓
StoneTheoremViaRMK.lean                 [to be created]
         ↓
ModularTheory.lean                      [depends on Stone]
```

## Technical Notes

### Why RMK?

The traditional approach to spectral theory uses:
1. CFC for bounded normal operators → spectral projections
2. Cayley transform to reduce unbounded to bounded
3. But CFC itself uses spectral theory, creating circularity

The RMK approach breaks this by:
1. Defining spectral functional Λ_z(f) = Re⟨z, cfc(f, U) z⟩
2. Using RMK to get a measure μ_z from Λ_z
3. Extending to polarized measure μ_{x,y} via polarization
4. Defining P(E) via sesquilinear form: ⟨x, P(E) y⟩ = μ_{x,y}(E)

### Key Lemmas Available

**From RMK files (sorry-free):**
- `spectralFunctionalAux_tendsto_closed`: Dominated convergence for thickened indicators
- `spectralFunctionalAux_tendsto_of_pointwise_general`: Dominated convergence for bounded sequences
- `spectralProjection_polarized_product_closed`: ⟨P x, P y⟩ = μ_{x,y}(F)
- `spectralProjection_idempotent_closed`: P(F)² = P(F) for closed F
- `spectralMeasurePolarized_univ`: μ_{x,y}(Circle) = ⟨x, y⟩
- `spectralMeasurePolarized_integral`: U-P connection for compactly supported functions
- `one_not_eigenvalue`: For Cayley transform U, U x = x ⟹ x = 0

**From TPConnection.lean (sorry-free):**
- `spectralMeasureDiagonalOnR`: Pullback measure on ℝ via cayleyToCircle
- `TP_connection_indicator`: ⟨x, P(E) y⟩ = μ^ℝ_{x,y}(E) for indicator functions
- `spectralMeasureDiagonal_singleton_one_eq_zero`: μ_z({1}) = 0 for Cayley transforms
- `cfcViaInverseCayley_continuousOn`: cfcViaInverseCayley is continuous on Circle \ {1}
- `integral_circle_eq_integral_minus_one`: ∫ g dμ = ∫_{Circle\{1}} g dμ (since μ({1}) = 0)

## References

- Reed-Simon, "Methods of Modern Mathematical Physics I", Ch. VII-VIII
- Rudin, "Functional Analysis", Ch. 13
- Kato, "Perturbation Theory for Linear Operators", Ch. V
