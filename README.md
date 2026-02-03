# ModularPhysics

A work-in-progress formalization of physics in Lean 4 with Mathlib.

## Philosophy

The project explores how physical theories can be expressed in a formal proof assistant. The `Core/` module captures the logical structure of physics using Lean's type system, while `StringGeometry/`, `StringAlgebra/`, `RigorousQFT/`, and `Topology/` pursue rigorous mathematical foundations.

In `Core/`, physical principles are encoded as axioms bundled into structures. At the moment its use is to parse the logical content of physics papers and to explore the interrelations between different physical frameworks without requiring complete mathematical foundations. Note that the use of "axiom" in the Lean environment is risky; while "axiom" is tolerated for now, eventually we will replace all "axiom" with "structure" or "def".

In `StringGeometry/`, `StringAlgebra/`, `RigorousQFT/`, and `Topology/`, the goal is different: all definitions and proofs build purely on Mathlib's foundations, with `sorry` used for incomplete proofs. Here "axiom" is strictly forbidden.

## Structure

```
ModularPhysics/
├── Core/
│   ├── ClassicalFieldTheory/
│   ├── ClassicalMechanics/
│   ├── FluidMechanics/
│   ├── GeneralRelativity/
│   ├── QFT/
│   │   ├── AQFT/
│   │   ├── BV/
│   │   ├── CFT/
│   │   │   ├── Bootstrap/
│   │   │   └── TwoDimensional/
│   │   ├── Euclidean/
│   │   ├── KontsevichSegal/
│   │   ├── PathIntegral/
│   │   ├── RG/
│   │   ├── Smatrix/
│   │   ├── TQFT/
│   │   └── Wightman/
│   ├── Quantum/
│   ├── QuantumInformation/
│   ├── SpaceTime/
│   └── Symmetries/
├── Papers/
│   └── GlimmJaffe/
│       ├── ClusterExpansion/
│       ├── Griffiths/
│       ├── Hypercontractivity/
│       └── ReflectionPositivity/
├── RigorousQFT/
│   ├── SPDE/
│   │   ├── EKMS/
│   │   ├── Examples/
│   │   ├── Nonstandard/
│   │   │   ├── Anderson/
│   │   │   ├── Foundation/
│   │   │   └── LoebMeasure/
│   │   ├── Probability/
│   │   └── RegularityStructures/
│   │       ├── Models/
│   │       └── Trees/
│   ├── vNA/
│   │   ├── MeasureTheory/
│   │   ├── Spectral/
│   │   │   └── FunctionalCalculusFromCFC/
│   │   └── Unbounded/
│   └── Wightman/
│       ├── Groups/
│       └── Spacetime/
├── StringAlgebra/
│   ├── Linfinity/
│   ├── MZV/
│   └── VOA/
├── StringGeometry/
│   ├── RiemannSurfaces/
│   │   ├── Algebraic/
│   │   │   ├── Cohomology/
│   │   │   └── Helpers/
│   │   ├── Analytic/
│   │   │   └── Helpers/
│   │   ├── Combinatorial/
│   │   │   └── Helpers/
│   │   ├── GAGA/
│   │   └── Topology/
│   ├── Supermanifolds/
│   │   ├── FPS/
│   │   ├── Helpers/
│   │   └── Sheaves/
│   └── SuperRiemannSurfaces/
└── Topology/
    ├── Homotopy/
    └── Spectra/
```

### StringGeometry

Develops mathematical foundations for string theory geometry. Current focus is definition of supermanifolds, integration, and super Riemann surfaces; moduli theory to be developed later.

### StringAlgebra

At a beginning stage with many placeholder definitions. Covers L-infinity algebras, multiple zeta values, and vertex operator algebras. Current focus is developing L-infinity algebra and BV formalism.

### RigorousQFT

At an early stage with many placeholders. Covers the Wightman axioms, von Neumann algebras, and stochastic PDE methods for constructive QFT. Current focus is developing functional analysis infrastructure and stochastic differential equations.
