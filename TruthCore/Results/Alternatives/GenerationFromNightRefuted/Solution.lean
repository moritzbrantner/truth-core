import TruthCore.Comparison.NightCosmogony
import TruthCore.Models.NightCosmogony
namespace TruthCore.Results.Alternatives.GenerationFromNightRefuted
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Alternatives.NightCosmogony
open TruthCore.Comparison.NightCosmogony

/-- Elimination of the Night cosmogony's bundle (#497), given three open
premises. If whatever is moved in a respect is moved by something in act in it
(*Met.* XII.6, 1071b28-29; IX.8, 1049b24-26; ST I q.3 a.1), nothing moved in a
respect moves itself in it (ST I q.2 a.3; Aristotle's "matter will not move
itself", *Met.* XII.6, 1071b29-31, says it only of matter), and an actual mover of another's potency is simply prior
to it (open bridge), then no potency that no being in act simply precedes is
actualized. The premise it rivals, `ActSimplyPriorToPotencyReading`, is not
used. -/
theorem generationFromNightFalse {Being Respect : Type}
    (InAct InPotency MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop)
    (hReduced : ReducedOnlyByABeingInActReading MovedIn MovesIn InAct)
    (hNoSelfMotion : NothingMovesItselfInSameRespectReading MovedIn MovesIn)
    (hMoverPrior : ActualMoverIsSimplyPriorReading InAct InPotency MovesIn PriorSimply) :
    GenerationFromNightFalse InAct InPotency MovedIn PriorSimply := by
  intro hTheory
  obtain ⟨x, r, ⟨hPotency, hUnpreceded⟩, hMoved⟩ := hTheory
  -- The actualized potency has a mover in act in that respect.
  obtain ⟨y, hMoves, hAct⟩ := hReduced x r hMoved
  -- That mover is not the moved thing itself.
  have hOther : y ≠ x := fun hSame => hNoSelfMotion x r hMoved (hSame ▸ hMoves)
  -- So it is a being in act in the respect that is simply prior to the potency.
  exact hUnpreceded y hAct (hMoverPrior y x r hPotency hMoves hAct hOther)

/-- The reduction premise is needed: in `MODEL-NIGHT-COSMOGONY-NO-REDUCTION` a
potency that nothing precedes is moved by nothing. -/
theorem needsReducedByBeingInAct :
    ¬ ∀ (Being Respect : Type) (InAct InPotency MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (PriorSimply : Being → Being → Prop),
      NothingMovesItselfInSameRespectReading MovedIn MovesIn →
        ActualMoverIsSimplyPriorReading InAct InPotency MovesIn PriorSimply →
          GenerationFromNightFalse InAct InPotency MovedIn PriorSimply := by
  intro h
  open TruthCore.Models.NightCosmogony.NoReduction in
  exact h Bool Unit model.InAct model.InPotency model.MovedIn model.MovesIn
    model.PriorSimply evaluation2 evaluation3 evaluation0

/-- The premise that nothing moved moves itself is needed: in
`MODEL-NIGHT-COSMOGONY-SELF-MOVER` the potency, also in act, moves itself. -/
theorem needsNoSelfMotion :
    ¬ ∀ (Being Respect : Type) (InAct InPotency MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (PriorSimply : Being → Being → Prop),
      ReducedOnlyByABeingInActReading MovedIn MovesIn InAct →
        ActualMoverIsSimplyPriorReading InAct InPotency MovesIn PriorSimply →
          GenerationFromNightFalse InAct InPotency MovedIn PriorSimply := by
  intro h
  open TruthCore.Models.NightCosmogony.SelfMover in
  exact h Bool Unit model.InAct model.InPotency model.MovedIn model.MovesIn
    model.PriorSimply evaluation1 evaluation3 evaluation0

/-- The bridge is needed: in `MODEL-NIGHT-COSMOGONY-OTHER-MOVER` another being,
in act, moves the potency without being simply prior to it. -/
theorem needsActualMoverPrior :
    ¬ ∀ (Being Respect : Type) (InAct InPotency MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (PriorSimply : Being → Being → Prop),
      ReducedOnlyByABeingInActReading MovedIn MovesIn InAct →
        NothingMovesItselfInSameRespectReading MovedIn MovesIn →
          GenerationFromNightFalse InAct InPotency MovedIn PriorSimply := by
  intro h
  open TruthCore.Models.NightCosmogony.OtherMover in
  exact h Bool Unit model.InAct model.InPotency model.MovedIn model.MovesIn
    model.PriorSimply evaluation1 evaluation2 evaluation0

/-- The bundle entails the recorded bare rival `PotencyPriorToActReading`. -/
theorem bundleEntailsRival :
    ∀ (Being Respect : Type) (InAct InPotency MovedIn : Being → Respect → Prop)
        (PriorSimply : Being → Being → Prop),
      GenerationFromNight InAct InPotency MovedIn PriorSimply →
        PotencyPriorToActReading InAct InPotency PriorSimply := by
  intro Being Respect InAct InPotency MovedIn PriorSimply hTheory
  obtain ⟨x, r, ⟨hPotency, hUnpreceded⟩, _⟩ := hTheory
  exact ⟨x, r, hPotency, hUnpreceded⟩

/-- The core does not refute the bare rival: in `MODEL-NIGHT-COSMOGONY-RESIDUAL`
an unpreceded potency is never actualized, and all three core premises hold. -/
theorem rivalSurvivesCore :
    ¬ ∀ (Being Respect : Type) (InAct InPotency MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (PriorSimply : Being → Being → Prop),
      ReducedOnlyByABeingInActReading MovedIn MovesIn InAct →
        NothingMovesItselfInSameRespectReading MovedIn MovesIn →
          ActualMoverIsSimplyPriorReading InAct InPotency MovesIn PriorSimply →
            ¬ PotencyPriorToActReading InAct InPotency PriorSimply := by
  intro h
  open TruthCore.Models.NightCosmogony.Residual in
  exact h Bool Unit model.InAct model.InPotency model.MovedIn model.MovesIn
    model.PriorSimply evaluation1 evaluation2 evaluation3 evaluation4

/-- The same elimination from root-path premises: a mover for whatever is moved,
every mover in act in its respect, and nothing in act and in potency in the
same respect, with the same bridge. -/
theorem coreFromRootPremises :
    ∀ (Being Respect : Type) (InAct InPotency MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (PriorSimply : Being → Being → Prop),
      ReducedOnlyByAMoverReading MovedIn MovesIn →
        MovesOnlyAsInActReading MovesIn InAct →
          NotActAndPotencyInSameRespectReading InAct InPotency →
            ActualMoverIsSimplyPriorReading InAct InPotency MovesIn PriorSimply →
              GenerationFromNightFalse InAct InPotency MovedIn PriorSimply := by
  intro Being Respect InAct InPotency MovedIn MovesIn PriorSimply
    hHasMover hMoverInAct hNotBoth hMoverPrior hTheory
  obtain ⟨x, r, ⟨hPotency, hUnpreceded⟩, hMoved⟩ := hTheory
  obtain ⟨y, hMoves⟩ := hHasMover x r hMoved
  have hAct : InAct y r := hMoverInAct y x r hMoves
  have hOther : y ≠ x := fun hSame => hNotBoth x r ⟨hSame ▸ hAct, hPotency⟩
  exact hUnpreceded y hAct (hMoverPrior y x r hPotency hMoves hAct hOther)

end TruthCore.Results.Alternatives.GenerationFromNightRefuted
