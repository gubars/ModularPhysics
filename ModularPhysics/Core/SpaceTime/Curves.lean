import ModularPhysics.Core.SpaceTime.Metrics
import ModularPhysics.Core.SpaceTime.Minkowski
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ModularPhysics.Core.SpaceTime

/-- Curve through spacetime -/
def Curve := ℝ → SpaceTimePoint

/-- Tangent vector to curve -/
noncomputable def tangentVector (γ : Curve) (t : ℝ) : Fin 4 → ℝ :=
  fun μ => deriv (fun s => γ s μ) t

/-- Timelike curve (valid particle worldline) -/
def TimelikeCurve (metric : SpacetimeMetric) (γ : Curve) : Prop :=
  ∀ t, innerProduct metric (γ t) (tangentVector γ t) (tangentVector γ t) < 0

/-- Null curve (light ray) -/
def NullCurve (metric : SpacetimeMetric) (γ : Curve) : Prop :=
  ∀ t, innerProduct metric (γ t) (tangentVector γ t) (tangentVector γ t) = 0

/-- Spacelike curve (unphysical) -/
def SpacelikeCurve (metric : SpacetimeMetric) (γ : Curve) : Prop :=
  ∀ t, innerProduct metric (γ t) (tangentVector γ t) (tangentVector γ t) > 0

/-- Worldline (synonym for curve, emphasizing physical interpretation) -/
abbrev Worldline := Curve

/-- Timelike worldline (from old SpaceTime.lean for backward compatibility) -/
def TimelikeWorldline (γ : Worldline) : Prop :=
  TimelikeCurve minkowskiMetric γ

/-- Spacelike worldline -/
def SpacelikeWorldline (γ : Worldline) : Prop :=
  SpacelikeCurve minkowskiMetric γ

/-- Null worldline -/
def NullWorldline (γ : Worldline) : Prop :=
  NullCurve minkowskiMetric γ

/-- Four-velocity (tangent to worldline) -/
noncomputable def FourVelocity (γ : Worldline) (t : ℝ) : SpaceTimePoint :=
  tangentVector γ t

/-- Four-velocity is normalized for timelike worldlines -/
axiom fourVelocity_normalized (metric : SpacetimeMetric) (γ : Worldline) (t : ℝ)
    (h : TimelikeCurve metric γ) :
  innerProduct metric (γ t) (FourVelocity γ t) (FourVelocity γ t) = -1

/-- Four-velocity normalization in Minkowski space (backward compatibility) -/
axiom fourVelocity_timelike (γ : Worldline) (t : ℝ)
    (h : TimelikeWorldline γ) :
  minkowskiInnerProduct (FourVelocity γ t) (FourVelocity γ t) = -1

/-- Four-acceleration -/
noncomputable def FourAcceleration (γ : Worldline) (t : ℝ) : SpaceTimePoint :=
  fun μ => deriv (fun s => FourVelocity γ s μ) t

/-- Inertial observer (unaccelerated in Minkowski space) -/
def InertialObserver (γ : Worldline) : Prop :=
  TimelikeWorldline γ ∧
  ∀ t, deriv (FourVelocity γ) t = fun _ => 0

/-- Proper time along timelike curve -/
axiom properTimeAlongCurve (metric : SpacetimeMetric) (γ : Curve)
    (h : TimelikeCurve metric γ) : ℝ → ℝ → ℝ

end ModularPhysics.Core.SpaceTime
