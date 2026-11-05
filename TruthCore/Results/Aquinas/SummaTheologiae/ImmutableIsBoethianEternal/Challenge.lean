import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.BoethianEternity
namespace TruthCore.Results.Aquinas.SummaTheologiae.ImmutableIsBoethianEternal
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- ST I q.10 a.1 co. with q.9 a.1 co.: what is in potency in no respect has
neither beginning nor end of life and no succession in it, since each would put
it in potency in some respect. -/
theorem pureActInterminableTotaSimul {Being Respect Time State : Type} [LT Time]
    (InPotency : Being → Respect → Prop)
    (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State)
    (hSuccession : SuccessionRequiresPotencyReading InPotency LivesAt lifeStateAt)
    (hBoundary : LifeBoundaryRequiresPotencyReading InPotency LivesAt) :
    ∀ x, PureAct InPotency x →
      Interminable LivesAt x ∧ TotaSimul LivesAt lifeStateAt x := by
  sorry

/-- Whatever is in potency in no respect is Boethian-eternal: it possesses life
interminably and all at once. From the q.9 a.1 succession principle, the open
boundary premise and the open premise that pure act lives. This is the typed
specialization, not the primitive-`Eternal` statement the root routes use. -/
theorem immutableIsBoethianEternal {Being Respect Time State : Type} [LT Time]
    (InPotency : Being → Respect → Prop)
    (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State)
    (hSuccession : SuccessionRequiresPotencyReading InPotency LivesAt lifeStateAt)
    (hBoundary : LifeBoundaryRequiresPotencyReading InPotency LivesAt)
    (hLife : PureActLivesReading InPotency LivesAt) :
    ImmutableIsBoethianEternalReading InPotency LivesAt lifeStateAt := by
  sorry

/-! ### Controls: each premise is needed

All models have one being `()`, one respect, no potency (so the being is pure
act), and two times `false < true` (core's order on `Bool`). They are formal
non-entailment witnesses, not historical or theological counterworlds. -/

/-- Without the succession premise: a pure-act being that lives at both times
with different life-states (successive operation) satisfies the boundary and life
premises and is not Boethian-eternal. -/
theorem successionPremiseNeeded :
    ¬ ∀ (Being Respect Time State : Type) [LT Time]
      (InPotency : Being → Respect → Prop)
      (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State),
      LifeBoundaryRequiresPotencyReading InPotency LivesAt →
      PureActLivesReading InPotency LivesAt →
      ImmutableIsBoethianEternalReading InPotency LivesAt lifeStateAt := by
  sorry

/-- Without the boundary premise: a pure-act being that begins to live and keeps
one constant life-state satisfies the succession and life premises, yet its life
has a beginning. -/
theorem boundaryPremiseNeeded :
    ¬ ∀ (Being Respect Time State : Type) [LT Time]
      (InPotency : Being → Respect → Prop)
      (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State),
      SuccessionRequiresPotencyReading InPotency LivesAt lifeStateAt →
      PureActLivesReading InPotency LivesAt →
      ImmutableIsBoethianEternalReading InPotency LivesAt lifeStateAt := by
  sorry

/-- Without the life premise: an immutable being that never lives (as a number is
immutable but not living, q.10 a.1 ad 2) satisfies the succession and boundary
premises vacuously and is not Boethian-eternal. -/
theorem lifePremiseNeeded :
    ¬ ∀ (Being Respect Time State : Type) [LT Time]
      (InPotency : Being → Respect → Prop)
      (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State),
      SuccessionRequiresPotencyReading InPotency LivesAt lifeStateAt →
      LifeBoundaryRequiresPotencyReading InPotency LivesAt →
      ImmutableIsBoethianEternalReading InPotency LivesAt lifeStateAt := by
  sorry

/-- Joint model: all three premises hold and some being is pure act, so the
derivation is not vacuous; the pure-act being lives at both times in one
constant state. -/
theorem premisesJointlySatisfiable :
    ∃ (Being Respect Time State : Type) (_ : LT Time)
      (InPotency : Being → Respect → Prop)
      (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State),
      SuccessionRequiresPotencyReading InPotency LivesAt lifeStateAt ∧
      LifeBoundaryRequiresPotencyReading InPotency LivesAt ∧
      PureActLivesReading InPotency LivesAt ∧
      (∃ x, PureAct InPotency x) := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.ImmutableIsBoethianEternal
