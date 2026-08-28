import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter5

namespace TruthCore.Greek.Aristotle.Physics

/-- Change is said to occur in time in two senses: primarily in its proper time and
derivatively in a containing time, as in a year because it occurs in a day, in
Aristotle, *Physics* VI.6, 236b20-24.

Source: Aristotle, *Physics* VI.6, 236b20-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PrimaryDerivativeChangeTimeSensesReading
    (PrimaryTimeSense DerivativeContainingTimeSense : Prop) : Prop :=
  PrimaryTimeSense ∧ DerivativeContainingTimeSense

/-- For an arbitrary part produced by dividing the primary time of a motion, the
thing is either moving in that part or is not moving in it, in Aristotle,
*Physics* VI.6, 236b25-27.

Source: Aristotle, *Physics* VI.6, 236b25-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ArbitrarySubintervalMotionDichotomyReading
    (MovesInArbitrarySubinterval : Prop) : Prop :=
  MovesInArbitrarySubinterval ∨ ¬ MovesInArbitrarySubinterval

/-- If motion were absent from an arbitrary part of the proposed primary time, the
whole would either be rest or would contain the motion only derivatively and hence
would not be primary, in Aristotle, *Physics* VI.6, 236b27-32.

Source: Aristotle, *Physics* VI.6, 236b27-32 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NonmovingSubintervalExcludesPrimaryTimeReading
    (MovesInArbitrarySubinterval WholeTimeIsPrimary : Prop) : Prop :=
  ¬ MovesInArbitrarySubinterval → ¬ WholeTimeIsPrimary

/-- A thing moving in its primary time moves in every arbitrary subinterval of that
time in Aristotle, *Physics* VI.6, 236b20-32.

Source: Aristotle, *Physics* VI.6, 236b20-32 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionInEverySubintervalOfPrimaryTimeReading
    (WholeTimeIsPrimary MovesInArbitrarySubinterval : Prop) : Prop :=
  WholeTimeIsPrimary → MovesInArbitrarySubinterval

/-- Every thing that is changing must already have completed some change earlier in
its primary change-time in Aristotle, *Physics* VI.6, 236b32-237a3.

Source: Aristotle, *Physics* VI.6, 236b32-237a3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangingThingPreviouslyChangedReading
    (ThingIsChanging ThingHasPreviouslyChanged : Prop) : Prop :=
  ThingIsChanging → ThingHasPreviouslyChanged

/-- Having changed during an interval is attributed by taking that interval's
terminal now as its boundary in Aristotle, *Physics* VI.6, 237a3-6.

Source: Aristotle, *Physics* VI.6, 237a3-6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def HavingChangedAtTerminalNowReading
    (CompletedChangeIsBoundedByTerminalNow : Prop) : Prop :=
  CompletedChangeIsBoundedByTerminalNow

/-- Because every division bounds a time by nows, a changing thing has completed a
change in every temporal part of its primary change-time in Aristotle,
*Physics* VI.6, 237a6-10.

Source: Aristotle, *Physics* VI.6, 237a6-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EveryTimePartHasCompletedChangeReading
    (ChangesInPrimaryTime HasCompletedChangeInEveryTimePart : Prop) : Prop :=
  ChangesInPrimaryTime → HasCompletedChangeInEveryTimePart

/-- Since time is divisible and contains infinitely many nows at which changing
cannot occur but completed change can be predicated, a continuously changing thing
has completed infinitely many changes in Aristotle, *Physics* VI.6, 237a10-17.

Source: Aristotle, *Physics* VI.6, 237a10-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangingHasInfinitelyManyCompletionsReading
    (ThingChangesContinuously ThingHasInfinitelyManyCompletions : Prop) : Prop :=
  ThingChangesContinuously → ThingHasInfinitelyManyCompletions

/-- Every completed change from one state to another occurred in time in Aristotle,
*Physics* VI.6, 237a17-20.

Source: Aristotle, *Physics* VI.6, 237a17-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CompletedChangeOccurredInTimeReading
    (ThingHasChanged CompletedChangeOccurredInTime : Prop) : Prop :=
  ThingHasChanged → CompletedChangeOccurredInTime

/-- Because the time of a completed change is divisible, an earlier half contains
an intermediate completion and the thing was therefore changing before its
completion, in Aristotle, *Physics* VI.6, 237a20-30.

Source: Aristotle, *Physics* VI.6, 237a20-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DivisibleCompletionTimeYieldsPriorChangingReading
    (CompletedChangeOccurredInTime ThingWasChangingEarlier : Prop) : Prop :=
  CompletedChangeOccurredInTime → ThingWasChangingEarlier

/-- Every thing that has completed a change was changing earlier in Aristotle,
*Physics* VI.6, 237a17-30.

Source: Aristotle, *Physics* VI.6, 237a17-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangedThingWasPreviouslyChangingReading
    (ThingHasChanged ThingWasChangingEarlier : Prop) : Prop :=
  ThingHasChanged → ThingWasChangingEarlier

/-- When the path of change is a continuous magnitude, the infinitely divisible
intermediate magnitude makes the prior changing especially evident in Aristotle,
*Physics* VI.6, 237a30-35.

Source: Aristotle, *Physics* VI.6, 237a30-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContinuousChangePathHasDivisibleIntermediatesReading
    (ChangePathIsContinuous HasInfinitelyDivisibleIntermediates : Prop) : Prop :=
  ChangePathIsContinuous → HasInfinitelyDivisibleIntermediates

/-- The temporal proof that completed change was preceded by changing also applies
when the termini are non-continuous, including contraries and contradictories, in
Aristotle, *Physics* VI.6, 237b1-4.

Source: Aristotle, *Physics* VI.6, 237b1-4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TemporalProofCoversNoncontinuousTerminiReading
    (ChangeBetweenContrariesCovered ChangeByContradictionCovered : Prop) : Prop :=
  ChangeBetweenContrariesCovered ∧ ChangeByContradictionCovered

/-- Having changed is prior within changing, changing is prior within having
changed, and neither series has a first member because infinite division prevents
partless items from being consecutive, in Aristotle, *Physics* VI.6, 237b3-9.

Source: Aristotle, *Physics* VI.6, 237b3-9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangingChangedReciprocalPriorityNoFirstReading
    (ChangingHasPriorCompletion CompletionHasPriorChanging
      NeitherSeriesHasFirstMember : Prop) : Prop :=
  ChangingHasPriorCompletion ∧ CompletionHasPriorChanging ∧
    NeitherSeriesHasFirstMember

/-- For divisible continuous things, what has come to be was coming to be and what
is coming to be has something already come to be; the completed item may be a
proper part, as a foundation is part of a house, in Aristotle, *Physics* VI.6,
237b10-14.

Source: Aristotle, *Physics* VI.6, 237b10-14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GenerationReciprocityWithPartQualificationReading
    (GeneratedWasComingToBe ComingToBeHasGeneratedSomething
      GeneratedSomethingMayBeProperPart : Prop) : Prop :=
  GeneratedWasComingToBe ∧ ComingToBeHasGeneratedSomething ∧
    GeneratedSomethingMayBeProperPart

/-- For continuous things, what has been destroyed was being destroyed and what is
being destroyed has something already destroyed in Aristotle, *Physics* VI.6,
237b13-18.

Source: Aristotle, *Physics* VI.6, 237b13-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DestructionReciprocityReading
    (DestroyedWasBeingDestroyed BeingDestroyedHasDestroyedSomething : Prop) : Prop :=
  DestroyedWasBeingDestroyed ∧ BeingDestroyedHasDestroyedSomething

/-- The reciprocal sequences of coming-to-be and having-come-to-be, and of being
destroyed and having-been-destroyed, have no first member because every magnitude
and time involved is divisible in Aristotle, *Physics* VI.6, 237b18-22.

Source: Aristotle, *Physics* VI.6, 237b18-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GenerationDestructionReciprocityHasNoFirstMemberReading
    (GenerationSeriesHasNoFirstMember DestructionSeriesHasNoFirstMember : Prop) : Prop :=
  GenerationSeriesHasNoFirstMember ∧ DestructionSeriesHasNoFirstMember

end TruthCore.Greek.Aristotle.Physics
