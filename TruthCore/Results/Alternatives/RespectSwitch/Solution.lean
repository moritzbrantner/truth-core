import TruthCore.Alternatives.RespectSwitch

namespace TruthCore.Results.Alternatives.RespectSwitch
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Physics.Typed
open TruthCore.Alternatives.RespectSwitch

/-- The intermediate being is in potency in the incoming respect and in act
in the outgoing respect. The four explicit local premises therefore exclude
coincidence of the two respects. No regress premise, ordering of respects,
nonempty domain, or excluded middle is used. General alternating chains are
not excluded, and no single-respect assumption is inserted. -/
theorem consecutiveRespects {Being Respect : Type}
    (MovedIn InAct InPotency : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (hInMoved : MovingIsInTheMovedReading MovesIn MovedIn)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn InPotency)
    (hActual : MovesOnlyAsInActReading MovesIn InAct)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency) :
    ConsecutiveMoversHaveDistinctRespects MovesIn := by
  intro z y x r s hIncoming hOutgoing hSame
  subst s
  exact hNotBoth y r
    ⟨hActual y x r hOutgoing, hPotency y r (hInMoved z y r hIncoming)⟩

end TruthCore.Results.Alternatives.RespectSwitch
