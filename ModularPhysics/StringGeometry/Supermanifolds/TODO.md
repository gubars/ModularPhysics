# Supermanifolds Folder - Issues to Fix

## Summary

The algebraic foundations (Superalgebra.lean, GrassmannAlgebra, Berezinian) are well-developed.
**SuperDomainAlgebra.lean** provides Ring/Algebra instances for SuperDomainFunction.
The main Supermanifold definition now uses proper SuperAlgebra structure.

**Recently Completed:**
- `supercommutative'` theorem - Koszul sign rule for homogeneous elements (PROVEN)
- `mul_assoc'` - Associativity of SuperDomainFunction multiplication (PROVEN)
- `partialEven` smoothness - PROVEN using ContDiff.fderiv_right
- **Supermanifold** now has proper sheaf conditions (locality + gluing)
- **Supermanifold** structure sheaf now returns `SuperAlgebra ℝ` with supercommutativity
- **SuperChart.sheafIso** now properly typed as `RingEquiv` to SuperDomainFunction
- **SuperCoordinates** now has proper parity conditions (evenCoords_even, oddCoords_odd)
- **SuperTransition** removed tautological `overlap_nonempty`, added proper diffeomorphism conditions

---

## Current State of Key Definitions

### Supermanifold (lines ~845-890)
**SIGNIFICANTLY IMPROVED:**
- `structureSheaf : (U : Set body) → IsOpen U → SuperAlgebra ℝ`
- `sections_supercomm : ∀ U hU, SuperCommutative (structureSheaf U hU)`
- Proper sheaf conditions: `sheaf_locality` and `sheaf_gluing`
- `localTriviality` gives RingEquiv to SuperDomainFunction

### SuperChart (lines ~920-942)
**IMPROVED:**
- `bodyCoord_injective`, `bodyCoord_continuous`, `bodyCoord_image_open` (proper conditions)
- `sheafIso : (M.structureSheaf domain domainOpen).carrier ≃+* SuperDomainFunction`

### SuperCoordinates (lines ~948-958)
**IMPROVED:**
- `evenCoords_even : ∀ i, evenCoords i ∈ (...).even`
- `oddCoords_odd : ∀ a, oddCoords a ∈ (...).odd`

### SuperTransition (lines ~980-1000)
**IMPROVED:**
- Removed tautological `overlap_nonempty`
- `bodyTransition_diffeo : ContDiff ℝ ⊤ ...`
- `bodyTransition_inv : ∃ (g : ...), ...`

---

## Remaining Issues

### 1. Sorrys Requiring Proofs

| Location | Declaration | Status | Difficulty |
|----------|-------------|--------|------------|
| ~1147 | `batchelor_theorem` | sorry | HIGH - Deep result |
| ~1262 | `batchelor_splitting` | sorry | HIGH - Deep result |
| ~1347 | `partialOdd_odd_derivation` | sorry | MEDIUM - Partially done |

### 2. Remaining Placeholders

#### LocallySuperRingedSpace (~line 224)
- `stalks_local : True` - Needs proper stalk definition as colimits

#### SupermanifoldMorphism (~line 909)
- `pullback_hom : True` - Pullback should be a graded algebra homomorphism

#### SuperAtlas (~line 973)
- `transitions_smooth : True` - Transition functions are smooth

#### SuperVectorBundle (~line 1370-1372)
- `localTriviality : True` - Local trivialization condition
- `transitions : True` - Transition functions in GL(r|s)

#### BerezinianBundle (~line 1435)
- `transitions_berezinian : True` - Transitions are Berezinians

---

## Recommendations for Next Steps

### Immediate
1. **Complete `partialOdd_odd_derivation`** - Proof structure is in place
2. **Fix BerezinIntegration sorrys** - Integration change of variables

### Short-term
3. **Implement LocallySuperRingedSpace.stalks_local** - Define stalks as colimits
4. **SuperVectorBundle local triviality** - Proper formulation

### Long-term
5. **Batchelor theorem** - Deep result requiring global analysis
6. **Full integration theory** - Berezin integral on general supermanifolds

---

## File Status Summary

| File | Status | Key Issues |
|------|--------|------------|
| Superalgebra.lean | Good | Complete algebraic foundations |
| SuperRingCat.lean | Good | Category of supercommutative algebras |
| SuperDomainAlgebra.lean | Good | Ring/Algebra instances proven |
| Supermanifolds.lean | Much Improved | Core definitions now proper, some sorrys remain |
| BerezinIntegration.lean | Partial | Integration sorrys, placeholder conditions |
| Helpers/SuperMatrix.lean | Good | Berezinian computation rigorous |

---

## Notes

- **Structure sheaf returns SuperAlgebra ℝ**: This ensures the ℤ/2-grading is part of the definition
- **Local triviality gives Grassmann structure**: The RingEquiv to SuperDomainFunction provides body/soul
- **supercommutative'** proven using reorderSign_comm and ring tactics
- **partialEven** proven using ContDiff.fderiv_right and clm_apply
