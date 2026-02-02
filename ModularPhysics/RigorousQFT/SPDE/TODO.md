# SPDE Standard Approach - Status and TODO

This document tracks the status of the standard (non-hyperfinite) approach to SPDEs using classical probability and measure theory.

## Recent Updates (2026-02-01)

### Compilation Fixes (Session 2)

All files now compile. Key fixes made:

1. **BrownianMotion.lean**
   - Fixed `increment_variance` to use `simp only [sub_zero]` for type matching
   - Moved `trace` from structure field to separate `noncomputable def`
   - Fixed `ou_stationary_variance` proof using `Filter.tendsto_const_mul_atBot_of_neg`
   - Fixed `ou_variance_bounds` proof for conjunction
   - Simplified `conditional_variance` to not use ENNReal×ℝ multiplication

2. **RegularityStructures.lean**
   - Fixed tensor product representation with placeholder `tensorProduct` function
   - Fixed `level2_chen` theorem to use the new tensor product
   - Removed problematic simp calls

3. **SPDE.lean**
   - Renamed `IsClosed` to `IsClosedOperator` to avoid conflict with Mathlib
   - Added `noncomputable` to `generator` definitions
   - Fixed `smul_mem'` proof in semigroup generator construction

### Previous Fixes (Session 1)

Major fixes implemented to address critical mathematical errors:

### Completed Fixes

1. **LocalMartingale** (Basic.lean) - FIXED
   - Added proper `stopped_is_martingale` condition
   - The stopped process M^{τ_n} is now required to be a true martingale

2. **BrownianMotion** (BrownianMotion.lean) - FIXED
   - Changed `stationary_increments` from pathwise equality to distributional equality
   - Added `independent_increments` condition using Mathlib's `Indep`
   - Added `gaussian_increments` with proper `IsGaussian` structure
   - Increments are now properly characterized as N(0, t-s)

3. **TraceClassOperator** (BrownianMotion.lean) - FIXED
   - Added proper eigenvalue-based trace definition
   - Added `eigenvalues`, `eigenvalues_nonneg`, `eigenvalues_summable`
   - Trace is now properly defined as `∑' i, eigenvalues i`

4. **OrnsteinUhlenbeck** (BrownianMotion.lean) - FIXED
   - Changed `mean_reversion` from incorrect unconditional to conditional expectation
   - Added `conditional_variance` property
   - Added `gaussian_conditional` for Gaussian characterization

5. **Semimartingale** (StochasticIntegration.lean) - FIXED
   - Fixed `finite_variation` to use sum of increments `|A(tᵢ₊₁) - A(tᵢ)|`
   - Added proper `Partition`, `totalVariationOver`, `HasFiniteVariation` structures
   - Added `LebesgueStieltjesIntegral` structure for proper integration

6. **RoughPath** (RegularityStructures.lean) - FIXED
   - Fixed Chen relation to be multiplicative in tensor algebra
   - Added `TruncatedTensorAlgebra` structure with proper multiplication
   - Chen relation now correctly: X_{su} ⊗ X_{ut} = X_{st}
   - Level 2 Chen: X_{st}^{(2)} = X_{su}^{(2)} + X_{ut}^{(2)} + X_{su}^{(1)} ⊗ X_{ut}^{(1)}

7. **AbstractSPDE** (SPDE.lean) - FIXED
   - Added `UnboundedOperatorReal` structure for real Hilbert spaces
   - Added `C0Semigroup` structure with proper generator definition
   - Generator A is now properly unbounded (not `H →L[ℝ] H`)
   - Added Lipschitz and growth conditions for F and B

### New Infrastructure Created

1. **Probability/Basic.lean** - NEW
   - `SubSigmaAlgebra` structure
   - `IsGaussian` characterization via moments and characteristic function
   - `IndepRV`, `IndepFamily` for independence
   - `IndependentIncrements` for stochastic processes
   - Conditional expectation properties (tower, linearity, Jensen)
   - Moment bounds (Chebyshev, Markov, Doob)

---

## Current Status Summary

| File | Status | Sorrys | Notes |
|------|--------|--------|-------|
| Basic.lean | ✅ Compiles | 2 | LocalMartingale construction |
| BrownianMotion.lean | ✅ Compiles | 11 | Proper definitions, proofs pending |
| StochasticIntegration.lean | ✅ Compiles | 10 | Finite variation fixed |
| RegularityStructures.lean | ✅ Compiles | 7 | Chen relation fixed |
| SPDE.lean | ✅ Compiles | 6 | Unbounded operators added |
| Probability/Basic.lean | ✅ Compiles | ~15 | Infrastructure with sorry proofs |

**All files now compile successfully!** (as of 2026-02-01)

---

## Remaining Work

### ~~Priority 1: Compile All Files~~
- [x] Build BrownianMotion.lean and fix any errors - DONE
- [x] Build StochasticIntegration.lean and fix any errors - DONE
- [x] Build RegularityStructures.lean and fix any errors - DONE
- [x] Build SPDE.lean and fix any errors - DONE

### Priority 2: Fill In Sorries
Key sorries to address:

**Basic.lean:**
- `LocalMartingale.ofMartingale.stopped_is_martingale` - prove stopped martingale property

**BrownianMotion.lean:**
- `BrownianMotion.is_martingale` - Brownian motion is a martingale
- `BrownianMotion.quadratic_variation` - QV equals t
- `levy_characterization` - Lévy's characterization theorem

**StochasticIntegration.lean:**
- `SimpleProcess.isometry` - Itô isometry for simple processes
- `ito_formula` - explicit Itô formula
- `girsanov` - Girsanov's theorem
- `martingale_representation` - representation theorem

**Probability/Basic.lean:**
- Various conditional expectation properties
- Independence characterizations
- Moment inequalities

### Priority 3: Additional Infrastructure
- [ ] Stochastic integration construction (not just structure)
- [ ] Connection to Nonstandard approach
- [ ] Examples: stochastic heat equation, KPZ, Φ⁴

---

## File Dependencies

```
Probability/Basic.lean (standalone)
       ↓
Basic.lean (filtrations, martingales)
       ↓
BrownianMotion.lean (Wiener process)
       ↓
StochasticIntegration.lean (Itô calculus)
       ↓
RegularityStructures.lean (Hairer theory)
       ↓
SPDE.lean (abstract SPDEs)
```

---

## Mathematical Notes

### Correct Brownian Motion Definition
A process W_t is standard Brownian motion if:
1. W_0 = 0 a.s.
2. Continuous paths a.s.
3. **Independent increments**: W_t - W_s ⊥ F_s for s ≤ t
4. **Gaussian increments**: W_t - W_s ~ N(0, t-s)

Note: Stationarity follows from (4), not stated separately.

### Correct Chen Relation
For rough paths, Chen's relation is **multiplicative** in the tensor algebra:
- X_{su} ⊗ X_{ut} = X_{st}

For level 2 (the "area"):
- X_{st}^{(2)} = X_{su}^{(2)} + X_{ut}^{(2)} + X_{su}^{(1)} ⊗ X_{ut}^{(1)}

This is NOT additive - the tensor product term is crucial.

### Unbounded Operators
Semigroup generators like the Laplacian Δ are unbounded:
- Domain D(A) is dense in H
- A : D(A) → H is linear (not continuous as H → H)
- The semigroup S(t) = e^{tA} is bounded for each t

---

## References

- Karatzas, Shreve: "Brownian Motion and Stochastic Calculus"
- Revuz, Yor: "Continuous Martingales and Brownian Motion"
- Da Prato, Zabczyk: "Stochastic Equations in Infinite Dimensions"
- Hairer: "A theory of regularity structures" (Inventiones 2014)
- Friz, Hairer: "A Course on Rough Paths" (2020)
- Lyons, Caruana, Lévy: "Differential Equations Driven by Rough Paths"
