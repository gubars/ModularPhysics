/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Basic
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.LocalRings
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Divisors
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Sheaves.Coherent
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Sheaves.LineBundles
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Sheaves.Skyscraper
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Cohomology.SheafCohomology
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Cohomology.CurveVanishing
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.CanonicalSheaf
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Duality
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.RiemannRoch

/-!
# Scheme-Theoretic Foundations for Riemann Surfaces

This folder provides scheme-theoretic foundations for algebraic curves over ℂ,
using Mathlib's `Scheme` infrastructure to develop Riemann-Roch theory.

## Files

* `Basic.lean` - Defines `SmoothProjectiveCurve` using Mathlib's Scheme type
* `LocalRings.lean` - DVR structure and discrete valuations at each point
* `Divisors.lean` - Weil divisors on curves
* `Sheaves/Coherent.lean` - Coherent sheaves on curves
* `Sheaves/LineBundles.lean` - Line bundles and invertible sheaves
* `Sheaves/Skyscraper.lean` - Skyscraper sheaves for point exact sequences
* `Cohomology/SheafCohomology.lean` - Sheaf cohomology via derived functors
* `Cohomology/CurveVanishing.lean` - Vanishing theorems for curves
* `CanonicalSheaf.lean` - The canonical sheaf and canonical divisor
* `Duality.lean` - Serre duality on curves
* `RiemannRoch.lean` - The Riemann-Roch theorem

## Main Results

* `riemann_roch_euler` - χ(D) = deg(D) + 1 - g
* `riemann_roch_serre` - h⁰(D) - h⁰(K-D) = deg(D) + 1 - g

## Design Philosophy

All proofs are purely algebraic - no analytic methods are used.
-/
