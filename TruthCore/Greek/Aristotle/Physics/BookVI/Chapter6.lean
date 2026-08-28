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

end TruthCore.Greek.Aristotle.Physics
