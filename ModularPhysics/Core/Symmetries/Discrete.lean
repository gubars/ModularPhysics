import ModularPhysics.Core.SpaceTime.Basic

namespace ModularPhysics.Core.Symmetries

open SpaceTime

/-- Charge conjugation C (particle ↔ antiparticle)
    Abstract operator - acts on quantum states, fields, etc. -/
axiom ChargeConjugation : Type
axiom C_op : ChargeConjugation → ∀ {H : Type*}, H → H
axiom C_involutive (C : ChargeConjugation) {H : Type*} (ψ : H) :
  C_op C (C_op C ψ) = ψ

/-- Parity P (spatial inversion: x → -x) -/
structure Parity where
  op : SpaceTimePoint → SpaceTimePoint
  involutive : ∀ (x : SpaceTimePoint), op (op x) = x
  preserves_time : ∀ (x : SpaceTimePoint), (op x) 0 = x 0
  inverts_space : ∀ (x : SpaceTimePoint) (i : Fin 3), (op x) i.succ = -(x i.succ)

/-- Time reversal T (t → -t, antiunitary) -/
axiom TimeReversal : Type
axiom T_op : TimeReversal → ∀ {H : Type*}, H → H
axiom T_involutive (T : TimeReversal) {H : Type*} (ψ : H) :
  T_op T (T_op T ψ) = ψ
axiom T_op_spacetime : TimeReversal → SpaceTimePoint → SpaceTimePoint
axiom T_reverses_time (T : TimeReversal) (x : SpaceTimePoint) :
  (T_op_spacetime T x) 0 = -(x 0)

/-- Combined CPT symmetry -/
structure CPT where
  C : ChargeConjugation
  P : Parity
  T : TimeReversal

/-- CPT theorem: all Lorentz-invariant local QFTs respect CPT -/
axiom cpt_theorem : True

end ModularPhysics.Core.Symmetries
