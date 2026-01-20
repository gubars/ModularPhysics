# ModularPhysics

Modular physics formalization in Lean 4 with Mathlib.

## Philosophy

This project has two distinct components with different methodological approaches:

### Core/ — Physics with Axioms

The `Core/` module aims to formalize physical theories (quantum mechanics, QFT, general relativity, etc.) using **new axioms** that capture physical principles not derivable from pure mathematics. Currently in early stages with basic structures sketched out.

### StringGeometry/ — Rigorous Formalization (No New Axioms)

The `StringGeometry/` module is a project of **rigorous mathematical formalization** that does **not introduce any new axioms**. All definitions and theorems build purely on Mathlib's foundations. Incomplete proofs use `sorry` rather than introducing axioms.

Currently developing basic definitions for:
- Riemann surfaces (basic definitions, some helper lemmas)
- Supermanifolds (Grassmann algebras, Berezinian structure)
- Super Riemann surfaces (early stages)

Many sorrys remain to be eliminated.

## Structure

```
ModularPhysics/
├── Basic.lean
├── Core/
│   ├── SpaceTime.lean
│   ├── SpaceTime/
│   │   ├── Basic.lean
│   │   ├── Minkowski.lean
│   │   ├── Causality.lean
│   │   ├── Metrics.lean
│   │   ├── Connections.lean
│   │   ├── Curvature.lean
│   │   ├── Geodesics.lean
│   │   ├── Curves.lean
│   │   ├── Hypersurfaces.lean
│   │   ├── Conformal.lean
│   │   └── Symmetries.lean
│   │
│   ├── Symmetries.lean
│   ├── Symmetries/
│   │   ├── Lorentz.lean
│   │   ├── Poincare.lean
│   │   ├── LieAlgebras.lean
│   │   ├── Representations.lean
│   │   └── Discrete.lean
│   │
│   ├── Quantum.lean
│   ├── Quantum/
│   │   ├── Basic.lean
│   │   ├── Operators.lean
│   │   ├── Measurement.lean
│   │   └── Composite.lean
│   │
│   ├── QuantumInformation.lean
│   ├── QuantumInformation/
│   │   ├── Entropy.lean
│   │   ├── Entanglement.lean
│   │   ├── Channels.lean
│   │   ├── Correlations.lean
│   │   ├── PartialTrace.lean
│   │   └── InformationTheorems.lean
│   │
│   ├── ClassicalMechanics.lean
│   ├── ClassicalMechanics/
│   │   ├── PhaseSpace.lean
│   │   ├── Lagrangian.lean
│   │   ├── Hamiltonian.lean
│   │   ├── Symmetries.lean
│   │   ├── CanonicalTransforms.lean
│   │   ├── Constraints.lean
│   │   ├── Integrable.lean
│   │   ├── HamiltonJacobi.lean
│   │   ├── Perturbation.lean
│   │   └── Chaos.lean
│   │
│   ├── ClassicalFieldTheory.lean
│   ├── ClassicalFieldTheory/
│   │   ├── Fields.lean
│   │   ├── Action.lean
│   │   ├── EulerLagrange.lean
│   │   ├── Noether.lean
│   │   ├── EnergyMomentum.lean
│   │   ├── Scalar.lean
│   │   ├── Electromagnetic.lean
│   │   ├── YangMills.lean
│   │   └── Solitons.lean
│   │
│   ├── FluidMechanics.lean
│   ├── FluidMechanics/
│   │   ├── Basic.lean
│   │   ├── Conservation.lean
│   │   ├── Euler.lean
│   │   ├── NavierStokes.lean
│   │   ├── Vorticity.lean
│   │   └── Compressible.lean
│   │
│   ├── GeneralRelativity.lean
│   ├── GeneralRelativity/
│   │   ├── EinsteinEquations.lean
│   │   ├── Schwarzschild.lean
│   │   ├── ReissnerNordstrom.lean
│   │   ├── Kerr.lean
│   │   ├── BlackHoles.lean
│   │   ├── Singularities.lean
│   │   ├── EnergyConditions.lean
│   │   ├── GravitationalWaves.lean
│   │   └── Cosmology.lean
│   │
│   ├── QuantumFieldTheory.lean
│   └── QFT/
│       ├── Wightman.lean
│       ├── Wightman/
│       │   ├── Axioms.lean
│       │   ├── Operators.lean
│       │   ├── WightmanFunctions.lean
│       │   └── Theorems.lean
│       │
│       ├── AQFT.lean
│       ├── AQFT/
│       │   ├── Axioms.lean
│       │   ├── LocalAlgebras.lean
│       │   ├── Representations.lean
│       │   └── Superselection.lean
│       │
│       ├── PathIntegral.lean
│       ├── PathIntegral/
│       │   ├── FieldConfigurations.lean
│       │   ├── ActionAndMeasure.lean
│       │   ├── PathIntegrals.lean
│       │   ├── FieldRedefinitions.lean
│       │   ├── Symmetries.lean
│       │   ├── Regularization.lean
│       │   ├── Semiclassical.lean
│       │   └── Supergeometry.lean
│       │
│       ├── Euclidean.lean
│       ├── Euclidean/
│       │   ├── SchwingerFunctions.lean
│       │   ├── OsterwalderSchrader.lean
│       │   ├── WickRotation.lean
│       │   └── Lattice.lean
│       │
│       ├── CFT.lean
│       ├── CFT/
│       │   ├── Basic.lean
│       │   ├── Bootstrap.lean
│       │   ├── Bootstrap/
│       │   │   ├── BootstrapEquations.lean
│       │   │   ├── CrossingSymmetry.lean
│       │   │   └── UnitarityBounds.lean
│       │   ├── TwoDimensional.lean
│       │   └── TwoDimensional/
│       │       ├── Virasoro.lean
│       │       ├── OPE.lean
│       │       ├── ConformalBlocks.lean
│       │       ├── ModularInvariance.lean
│       │       └── Examples.lean
│       │
│       ├── TQFT.lean
│       ├── TQFT/
│       │   ├── Axioms.lean
│       │   ├── Bordisms.lean
│       │   ├── ChernSimons.lean
│       │   ├── KnotInvariants.lean
│       │   ├── ModularTensorCategories.lean
│       │   └── QuantumGroups.lean
│       │
│       ├── KontsevichSegal.lean
│       ├── KontsevichSegal/
│       │   ├── Axioms.lean
│       │   ├── Bordisms.lean
│       │   └── StateSpaces.lean
│       │
│       ├── Smatrix.lean
│       ├── Smatrix/
│       │   ├── AsymptoticStates.lean
│       │   ├── LSZ.lean
│       │   └── HaagRuelle.lean
│       │
│       ├── RG.lean
│       ├── RG/
│       │   ├── Basic.lean
│       │   ├── WilsonianRG.lean
│       │   ├── GellMannLow.lean
│       │   └── EffectiveAction.lean
│       │
│       ├── BV.lean
│       └── BV/
│           ├── BRST.lean
│           ├── BatalinVilkovisky.lean
│           └── LInfinityAlgebra.lean
│
└── Papers/
    ├── Bell.lean
    ├── Coleman2D.lean
    ├── cTheorem.lean
    ├── Vafa-Witten.lean
    ├── Kolmogorov.lean
    ├── AMPS.lean
    └── Phi4_2D.lean
```

## Build

```
lake build
```

Requires Lean 4.27+ and Mathlib4.

## Status

**Both components are work in progress.**

- **Core/**: Axiomatic structure established for major physical theories. Proofs use `sorry` where full formalization is pending.
- **StringGeometry/**: Mathematical foundations under active development. Sorrys are being systematically eliminated.
