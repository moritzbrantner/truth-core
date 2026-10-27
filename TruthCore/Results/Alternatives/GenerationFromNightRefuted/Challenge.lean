import TruthCore.Comparison.NightCosmogony
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
  sorry

/-- The reduction premise is needed: in `MODEL-NIGHT-COSMOGONY-NO-REDUCTION` a
potency that nothing precedes is moved by nothing. -/
theorem needsReducedByBeingInAct :
    ¬ ∀ (Being Respect : Type) (InAct InPotency MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (PriorSimply : Being → Being → Prop),
      NothingMovesItselfInSameRespectReading MovedIn MovesIn →
        ActualMoverIsSimplyPriorReading InAct InPotency MovesIn PriorSimply →
          GenerationFromNightFalse InAct InPotency MovedIn PriorSimply := by
  sorry

/-- The premise that nothing moved moves itself is needed: in
`MODEL-NIGHT-COSMOGONY-SELF-MOVER` the potency, also in act, moves itself. -/
theorem needsNoSelfMotion :
    ¬ ∀ (Being Respect : Type) (InAct InPotency MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (PriorSimply : Being → Being → Prop),
      ReducedOnlyByABeingInActReading MovedIn MovesIn InAct →
        ActualMoverIsSimplyPriorReading InAct InPotency MovesIn PriorSimply →
          GenerationFromNightFalse InAct InPotency MovedIn PriorSimply := by
  sorry

/-- The bridge is needed: in `MODEL-NIGHT-COSMOGONY-OTHER-MOVER` another being,
in act, moves the potency without being simply prior to it. -/
theorem needsActualMoverPrior :
    ¬ ∀ (Being Respect : Type) (InAct InPotency MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (PriorSimply : Being → Being → Prop),
      ReducedOnlyByABeingInActReading MovedIn MovesIn InAct →
        NothingMovesItselfInSameRespectReading MovedIn MovesIn →
          GenerationFromNightFalse InAct InPotency MovedIn PriorSimply := by
  sorry

/-- The bundle entails the recorded bare rival `PotencyPriorToActReading`. -/
theorem bundleEntailsRival :
    ∀ (Being Respect : Type) (InAct InPotency MovedIn : Being → Respect → Prop)
        (PriorSimply : Being → Being → Prop),
      GenerationFromNight InAct InPotency MovedIn PriorSimply →
        PotencyPriorToActReading InAct InPotency PriorSimply := by
  sorry

/-- The core does not refute the bare rival: in `MODEL-NIGHT-COSMOGONY-RESIDUAL`
an unpreceded potency is never actualized, and all three core premises hold. -/
theorem rivalSurvivesCore :
    ¬ ∀ (Being Respect : Type) (InAct InPotency MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (PriorSimply : Being → Being → Prop),
      ReducedOnlyByABeingInActReading MovedIn MovesIn InAct →
        NothingMovesItselfInSameRespectReading MovedIn MovesIn →
          ActualMoverIsSimplyPriorReading InAct InPotency MovesIn PriorSimply →
            ¬ PotencyPriorToActReading InAct InPotency PriorSimply := by
  sorry

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
  sorry

end TruthCore.Results.Alternatives.GenerationFromNightRefuted
