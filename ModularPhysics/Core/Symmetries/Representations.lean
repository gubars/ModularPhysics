import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.DirectSum.Basic
import ModularPhysics.Core.Symmetries.Lorentz
import ModularPhysics.Core.Symmetries.Poincare

namespace ModularPhysics.Core.Symmetries

open SpaceTime

/-- Group representation on a vector space -/
structure Representation (G V : Type _) [Group G] [AddCommGroup V] [Module ℝ V] where
  toFun : G → V →ₗ[ℝ] V
  preserves_one : toFun 1 = LinearMap.id
  preserves_mul : ∀ g h, toFun (g * h) = (toFun g).comp (toFun h)

/-- Trivial representation -/
def trivialRep {G V : Type _} [Group G] [AddCommGroup V] [Module ℝ V] :
    Representation G V where
  toFun := fun _ => LinearMap.id
  preserves_one := rfl
  preserves_mul := by intros; rfl

/-- Irreducible representation -/
def isIrreducible {G V : Type _} [Group G] [AddCommGroup V] [Module ℝ V]
    (ρ : Representation G V) : Prop :=
  ∀ (W : Submodule ℝ V), (∀ g : G, W.map (ρ.toFun g) ≤ W) → W = ⊥ ∨ W = ⊤

/-- Tensor product of representations (axiomatized - use product as placeholder) -/
axiom tensorRep {G V W : Type _} [Group G] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] :
  Representation G V → Representation G W → Representation G (V × W)

/-- Direct sum of representations (axiomatized) -/
axiom directSumRep {G V W : Type _} [Group G] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] :
  Representation G V → Representation G W → Representation G (V × W)

/-- Dual representation (axiomatized) -/
axiom dualRep {G V : Type _} [Group G] [AddCommGroup V] [Module ℝ V] :
  Representation G V → Representation G (V →ₗ[ℝ] ℝ)

/-- Intertwiner (equivariant map between representations) -/
structure Intertwiner {G V W : Type _} [Group G] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (ρ : Representation G V) (σ : Representation G W) where
  toLinearMap : V →ₗ[ℝ] W
  equivariant : ∀ g : G, toLinearMap.comp (ρ.toFun g) = (σ.toFun g).comp toLinearMap

/-- Schur's lemma: intertwiners between irreps are isomorphisms or zero -/
axiom schur_lemma {G V W : Type _} [Group G] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (ρ : Representation G V) (σ : Representation G W)
    (hρ : isIrreducible ρ) (hσ : isIrreducible σ)
    (f : Intertwiner ρ σ) :
    Function.Bijective f.toLinearMap ∨ f.toLinearMap = 0

/-- Poincaré representation on scalar fields -/
axiom scalarFieldRep : Representation PoincareTransform (SpaceTimePoint → ℝ)

/-- Poincaré representation on vector fields -/
axiom vectorFieldRep : Representation PoincareTransform (SpaceTimePoint → Fin 4 → ℝ)

/-- Lorentz representation on spinors -/
axiom spinorRep : Representation LorentzTransform (Fin 2 → ℂ)

end ModularPhysics.Core.Symmetries
