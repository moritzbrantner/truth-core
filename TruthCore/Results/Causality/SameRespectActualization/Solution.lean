import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3

namespace TruthCore.Results.Causality.SameRespectActualization
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- ST I q.2 a.3 co., first-way intermediate. All three act/potency laws
remain hypotheses. The subject must be being moved in the SAME respect. -/
theorem noSelfMotion {Being Respect : Type}
    (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (InPotency InAct : Being → Respect → Prop)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn InPotency)
    (hAct : MovesOnlyAsInActReading MovesIn InAct)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency) :
    NothingMovesItselfInSameRespectReading MovedIn MovesIn := by
  intro x r hMoved hSelf
  exact hNotBoth x r ⟨hAct x x r hSelf, hPotency x r hMoved⟩

/-- The separate existence-of-a-mover premise plus no same-respect self-motion
makes that mover distinct. This supplies no mover for an unmoved subject. -/
theorem movedByAnother {Being Respect : Type}
    (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (hReduction : ReducedOnlyByAMoverReading MovedIn MovesIn)
    (hNoSelf : NothingMovesItselfInSameRespectReading MovedIn MovesIn) :
    MovedByAnotherReading MovedIn MovesIn := by
  intro x r hMoved
  obtain ⟨y, hMoves⟩ := hReduction x r hMoved
  refine ⟨y, ?_, hMoves⟩
  intro hEq
  subst hEq
  exact hNoSelf y r hMoved hMoves

end TruthCore.Results.Causality.SameRespectActualization
