# ModularPhysics

A work-in-progress formalization of physics in Lean 4 with Mathlib.

## Philosophy

The project explores how physical theories can be expressed in a formal proof assistant. The `Core/` module captures the logical structure of physics using Lean's type system, while `StringGeometry/` pursues rigorous mathematical foundations without new axioms.

In `Core/`, physical principles are encoded as axioms bundled into structures. For example, the Haag-Kastler axioms for algebraic QFT, the Osterwalder-Schrader axioms for Euclidean field theory, or the properties of modular tensor categories are declared axiomatically, and theorems are derived from these axioms. This approach captures the deductive structure of physical theories without requiring complete mathematical foundations for objects like path integral measures. The axioms are not meant to be provable from first principles; rather, they formalize what physicists assume to be true, allowing one to explore the logical consequences and interrelations between different physical frameworks.

The use of axioms carries a risk: inconsistent axioms would allow proving anything. To mitigate this, axioms are organized into structures that bundle related assumptions together, making dependencies explicit. When possible, axioms are formulated to match well-established physics results (theorems from constructive QFT, categorical equivalences, etc.) rather than ad hoc assumptions. The goal is not foundational certainty but a useful formal framework for exploring the logical structure of physics.

In `StringGeometry/`, the goal is different: all definitions and proofs build purely on Mathlib's foundations, with `sorry` used for incomplete proofs rather than new axioms.

## Structure

```
ModularPhysics/
├── Core/
│   ├── SpaceTime/
│   ├── Symmetries/
│   ├── Quantum/
│   ├── QuantumInformation/
│   ├── ClassicalMechanics/
│   ├── ClassicalFieldTheory/
│   ├── FluidMechanics/
│   ├── GeneralRelativity/
│   └── QFT/
│       ├── Wightman/
│       ├── AQFT/
│       ├── PathIntegral/
│       ├── Euclidean/
│       ├── CFT/
│       │   ├── Bootstrap/
│       │   └── TwoDimensional/
│       ├── TQFT/
│       ├── KontsevichSegal/
│       ├── Smatrix/
│       ├── RG/
│       └── BV/
├── Papers/
│   └── GlimmJaffe/
│       ├── ClusterExpansion/
│       ├── Griffiths/
│       ├── Hypercontractivity/
│       └── ReflectionPositivity/
└── StringGeometry/
    ├── RiemannSurfaces/
    │   ├── Helpers/
    │   ├── Algebraic/
    │   │   └── Helpers/
    │   ├── Analytic/
    │   │   └── Helpers/
    │   ├── Combinatorial/
    │   │   └── Helpers/
    │   └── Moduli/
    ├── Supermanifolds/
    │   └── Helpers/
    └── SuperRiemannSurfaces/
```

## Status

This is an early-stage project. The formalization is incomplete and many parts are placeholders or sketches.
