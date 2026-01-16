# ModularPhysics

Modular architecture for physics in Lean 4.

## Structure

Core/
  SpaceTime.lean       - Minkowski spacetime, Poincaré group
  Quantum.lean         - Hilbert spaces, operators
  Symmetries.lean      - Lie groups, representations
  QFT/
    Wightman.lean      - Wightman axioms
    TQFT.lean          - Topological QFT
    AQFT.lean          - Algebraic QFT
    EFT.lean           - Effective field theory
    Euclidean.lean     - Euclidean QFT

Papers/
  AMPS.lean            - Paper formalizations

## Build

lake build

Requires Lean 4 and Mathlib4.

## Status

Work in progress. Core axioms implemented, examples and theorems coming.