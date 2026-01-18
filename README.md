# ModularPhysics

Modular architecture for physics in Lean 4.

## Structure

ModularPhysics/Core/
├── SpaceTime/                    [Minkowski, causality, geodesics, curvature]
│   ├── Basic.lean
│   ├── Causality.lean
│   ├── Minkowski.lean
│   ├── Metrics.lean
│   ├── Connections.lean
│   ├── Curvature.lean
│   ├── Geodesics.lean
│   ├── Curves.lean
│   ├── Hypersurfaces.lean
│   ├── Conformal.lean
│   └── Symmetries.lean
│
├── Symmetries/                   [Lorentz, Poincare, discrete]
│   ├── Lorentz.lean
│   ├── Poincare.lean
│   ├── LieAlgebras.lean
│   ├── Representations.lean
│   └── Discrete.lean
│
├── Quantum/                      [Hilbert space, operators, measurement]
│   ├── Basic.lean
│   ├── Operators.lean
│   ├── Measurement.lean
│   └── Composite.lean
│
├── QuantumInformation/           [Entropy, entanglement, channels]
│   ├── Entropy.lean
│   ├── Entanglement.lean
│   ├── Channels.lean
│   ├── Correlations.lean
│   ├── PartialTrace.lean
│   └── InformationTheorems.lean
│
├── ClassicalMechanics/           [Lagrangian, Hamiltonian, phase space]
│   ├── PhaseSpace.lean
│   ├── Lagrangian.lean
│   ├── Hamiltonian.lean
│   ├── Symmetries.lean
│   ├── CanonicalTransforms.lean
│   ├── Constraints.lean
│   ├── Integrable.lean
│   ├── HamiltonJacobi.lean
│   ├── Perturbation.lean
│   └── Chaos.lean
│
├── ClassicalFieldTheory/         [Fields, actions, Maxwell, Yang-Mills]
│   ├── Fields.lean
│   ├── Action.lean
│   ├── EulerLagrange.lean
│   ├── Noether.lean
│   ├── EnergyMomentum.lean
│   ├── Scalar.lean
│   ├── Electromagnetic.lean
│   ├── YangMills.lean
│   └── Solitons.lean
│
├── FluidMechanics/               [Euler, Navier-Stokes, vorticity]
│   ├── Basic.lean
│   ├── Conservation.lean
│   ├── Euler.lean
│   ├── NavierStokes.lean
│   ├── Vorticity.lean
│   └── Compressible.lean
│
├── GeneralRelativity/            [Einstein equations, black holes, cosmology]
│   ├── EinsteinEquations.lean
│   ├── Schwarzschild.lean
│   ├── ReissnerNordstrom.lean
│   ├── Kerr.lean
│   ├── BlackHoles.lean
│   ├── Singularities.lean
│   ├── EnergyConditions.lean
│   ├── GravitationalWaves.lean
│   └── Cosmology.lean
│
└── QFT/                          [Multiple formulations of QFT]
    ├── Wightman/                 [Wightman axioms, operator formalism]
    │   ├── Axioms.lean
    │   ├── Operators.lean
    │   ├── WightmanFunctions.lean
    │   └── Theorems.lean
    │
    ├── AQFT/                     [Haag-Kastler, algebraic QFT]
    │   ├── Axioms.lean
    │   ├── LocalAlgebras.lean
    │   ├── Representations.lean
    │   └── Superselection.lean
    │
    ├── PathIntegral/             [Functional integrals]
    │   ├── FieldConfigurations.lean
    │   ├── ActionAndMeasure.lean
    │   ├── PathIntegrals.lean
    │   ├── FieldRedefinitions.lean
    │   ├── Symmetries.lean
    │   ├── Regularization.lean
    │   ├── Semiclassical.lean
    │   └── Supergeometry.lean
    │
    ├── Euclidean/                [Wick rotation, OS axioms]
    │   ├── SchwingerFunctions.lean
    │   ├── OsterwalderSchrader.lean
    │   ├── WickRotation.lean
    │   └── Lattice.lean
    │
    ├── CFT/                      [Conformal field theory]
    │   ├── Basic.lean
    │   ├── Bootstrap/            [Conformal bootstrap]
    │   │   ├── BootstrapEquations.lean
    │   │   ├── CrossingSymmetry.lean
    │   │   └── UnitarityBounds.lean
    │   ├── TwoDimensional/       [2D CFT]
    │   │   ├── Virasoro.lean
    │   │   ├── OPE.lean
    │   │   ├── ConformalBlocks.lean
    │   │   ├── ModularInvariance.lean
    │   │   └── Examples.lean
    │   ├── Bootstrap.lean
    │   └── TwoDimensional.lean
    │
    ├── TQFT/                     [Topological field theories]
    │   ├── Axioms.lean
    │   ├── Bordisms.lean
    │   ├── ChernSimons.lean
    │   ├── KnotInvariants.lean
    │   ├── ModularTensorCategories.lean
    │   └── QuantumGroups.lean
    │
    ├── KontsevichSegal/          [Rigorous path integrals]
    │   ├── Axioms.lean
    │   ├── Bordisms.lean
    │   └── StateSpaces.lean
    │
    ├── Wightman.lean
    ├── AQFT.lean
    ├── PathIntegral.lean
    ├── Euclidean.lean
    ├── CFT.lean
    ├── TQFT.lean
    ├── KontsevichSegal.lean
    └── EFT.lean

Top-level aggregator files:
├── SpaceTime.lean
├── Symmetries.lean
├── Quantum.lean
├── QuantumInformation.lean
├── ClassicalMechanics.lean
├── ClassicalFieldTheory.lean
├── FluidMechanics.lean
├── GeneralRelativity.lean
└── QuantumFieldTheory.lean

## Build

lake build

Requires Lean 4 and Mathlib4.

## Status

Work in progress. Core axioms implemented, examples and theorems coming.
Recent additions include a comprehensive Conformal Field Theory module.
