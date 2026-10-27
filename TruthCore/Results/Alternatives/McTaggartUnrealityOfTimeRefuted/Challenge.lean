import TruthCore.Comparison.McTaggart
namespace TruthCore.Results.Alternatives.McTaggartUnrealityOfTimeRefuted
open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Alternatives.McTaggart
open TruthCore.Comparison.McTaggart

/-- Elimination of McTaggart's bundle on change (#497), given two open premises.
If opining is a being moved (Aristotle, *Physics* VIII.3, 254a27-30, a reputable
opinion) and whatever is moved changes (open bridge), then McTaggart's bundle
fails: by its own commitment someone judges or perceives, so someone changes, so
by its other commitment some event changes in its A-series determinations, which
its first commitment denies. The premise it rivals, `SomethingIsMovedReading`,
is not used. -/
theorem unrealityOfTimeFalse {Being Respect : Type}
    (MovedIn : Being → Respect → Prop) (ASeriesChanges : Being → Prop)
    (Opines : Being → Prop → Prop) (asOpinion : Prop → Respect)
    (Changes : Being → Prop)
    (hOpinionIsMotion : OpiningIsBeingMovedReading MovedIn Opines asOpinion)
    (hMotionIsChange : MotionIsChangeReading MovedIn Changes) :
    UnrealityOfTimeFalse ASeriesChanges Opines Changes := by
  sorry

/-- The premise that opining is a motion is needed: where one being opines,
nothing is moved and nothing changes, the bundle and the bridge hold. -/
theorem needsOpinionIsMotion :
    ¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (ASeriesChanges : Being → Prop) (Opines : Being → Prop → Prop)
        (Changes : Being → Prop),
      MotionIsChangeReading MovedIn Changes →
        UnrealityOfTimeFalse ASeriesChanges Opines Changes := by
  sorry

/-- The bridge that motion is change is needed: where one being opines and is
moved but nothing changes, the bundle holds and opining is a motion. -/
theorem needsMotionIsChange :
    ¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (ASeriesChanges : Being → Prop) (Opines : Being → Prop → Prop)
        (asOpinion : Prop → Respect) (Changes : Being → Prop),
      OpiningIsBeingMovedReading MovedIn Opines asOpinion →
        UnrealityOfTimeFalse ASeriesChanges Opines Changes := by
  sorry

/-- Link to the recorded rival: McTaggart's bundle with the bridge yields the
unattributed McTaggart-style rival `ChangeUnrealButAppearsReading` of
`SomethingIsMovedReading`, without the stronger bridge
`BeingMovedInvolvesASeriesChangeReading`. -/
theorem bundleYieldsChangeUnreal :
    ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (ASeriesChanges : Being → Prop) (Opines : Being → Prop → Prop)
        (Changes : Being → Prop),
      UnrealityOfTime ASeriesChanges Opines Changes →
        MotionIsChangeReading MovedIn Changes →
          ChangeUnrealButAppearsReading MovedIn Opines := by
  sorry

/-- The recorded McTaggart-style rival alone falls to the premise that opining
is a motion: its own second conjunct supplies an opiner, who is then moved. -/
theorem changeUnrealButAppearsRefuted :
    ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
        (Opines : Being → Prop → Prop) (asOpinion : Prop → Respect),
      OpiningIsBeingMovedReading MovedIn Opines asOpinion →
        ¬ ChangeUnrealButAppearsReading MovedIn Opines := by
  sorry

end TruthCore.Results.Alternatives.McTaggartUnrealityOfTimeRefuted
