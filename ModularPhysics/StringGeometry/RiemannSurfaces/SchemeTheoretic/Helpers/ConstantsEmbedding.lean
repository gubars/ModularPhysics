/-
Copyright (c) 2026 ModularPhysics Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import ModularPhysics.StringGeometry.RiemannSurfaces.SchemeTheoretic.Basic

/-!
# Properties of Constants Embedding

This file contains theorems about the embedding ℂ →+* K(C) defined in `Basic.lean`.

## Main Results

* `constantsEmbed_injective` - The embedding is injective (ℂ embeds into K(C))
* `constantsEmbed_ne_zero` - Nonzero constants map to nonzero elements
-/

open AlgebraicGeometry CategoryTheory

namespace RiemannSurfaces.SchemeTheoretic

namespace SmoothProjectiveCurve

variable (C : SmoothProjectiveCurve)

/-!
## Derived Instances
-/

/-- The function field is nontrivial (has 0 ≠ 1).

    This follows from being a field (which is an integral domain). -/
noncomputable instance functionFieldNontrivial : Nontrivial C.FunctionFieldType := by
  haveI : Field C.FunctionFieldType := inferInstanceAs (Field C.toScheme.functionField)
  exact Field.toNontrivial

/-!
## Properties of the Embedding
-/

/-- The embedding of constants is injective.

    **Mathematical content:**
    ℂ is a field, so any ring homomorphism from ℂ to a nontrivial ring is injective.

    **Proof:** Uses `RingHom.injective` for ring maps from fields. -/
theorem constantsEmbed_injective : Function.Injective C.constantsEmbed := by
  haveI : Nontrivial C.FunctionFieldType := C.functionFieldNontrivial
  exact RingHom.injective C.constantsEmbed

/-- The embedding preserves 1. -/
theorem constantsEmbed_one : C.constantsEmbed 1 = 1 :=
  C.constantsEmbed.map_one

/-- The embedding preserves multiplication. -/
theorem constantsEmbed_mul (x y : ℂ) :
    C.constantsEmbed (x * y) = C.constantsEmbed x * C.constantsEmbed y :=
  C.constantsEmbed.map_mul x y

/-- The embedding preserves addition. -/
theorem constantsEmbed_add (x y : ℂ) :
    C.constantsEmbed (x + y) = C.constantsEmbed x + C.constantsEmbed y :=
  C.constantsEmbed.map_add x y

/-- Nonzero constants map to nonzero elements in K(C). -/
theorem constantsEmbed_ne_zero {c : ℂ} (hc : c ≠ 0) :
    C.constantsEmbed c ≠ 0 := by
  intro h
  have : c = 0 := C.constantsEmbed_injective (h.trans C.constantsEmbed.map_zero.symm)
  exact hc this

end SmoothProjectiveCurve

end RiemannSurfaces.SchemeTheoretic
