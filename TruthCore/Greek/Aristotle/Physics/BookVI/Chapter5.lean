import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter4

namespace TruthCore.Greek.Aristotle.Physics

/-- What has completed a change is in the state into which it changed in Aristotle,
*Physics* VI.5, 235b6-18.

Source: Aristotle, *Physics* VI.5, 235b6-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CompletedChangeIsInTargetReading
    (CompletedChangeIsInTarget : Prop) : Prop :=
  CompletedChangeIsInTarget

/-- Changing is identical with, or followed by, departure from the source; completed
change therefore entails completed departure from it in Aristotle, *Physics* VI.5,
235b7-13.

Source: Aristotle, *Physics* VI.5, 235b7-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CompletedChangeLeavesSourceReading
    (ChangingLeavesSource CompletedChangeHasLeftSource : Prop) : Prop :=
  ChangingLeavesSource → CompletedChangeHasLeftSource

/-- In change by contradiction, what has changed from non-being to being has left
non-being and is in being; Aristotle extends the same completed-target result to all
changes in *Physics* VI.5, 235b13-20.

Source: Aristotle, *Physics* VI.5, 235b13-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContradictoryChangeShowsCompletedTargetReading
    (GeneratedHasLeftNonbeing GeneratedIsInBeing
      CompletedTargetResultExtendsToAllChanges : Prop) : Prop :=
  GeneratedHasLeftNonbeing ∧ GeneratedIsInBeing ∧
    CompletedTargetResultExtendsToAllChanges

/-- If a thing that has changed into a target were instead in an intermediate state,
continuity would make it still changing toward the target after it had already
changed there, which is impossible, in Aristotle, *Physics* VI.5, 235b20-27.

Source: Aristotle, *Physics* VI.5, 235b20-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IntermediateAfterCompletionWouldContinueChangeReading
    (CompletedThingInIntermediate StillChangingTowardCompletedTarget : Prop) : Prop :=
  CompletedThingInIntermediate → StillChangingTowardCompletedTarget

/-- What has come to be exists, and what has been destroyed does not exist, when
their changes are complete in Aristotle, *Physics* VI.5, 235b27-30.

Source: Aristotle, *Physics* VI.5, 235b27-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GeneratedExistsDestroyedDoesNotReading
    (GeneratedExists DestroyedExists : Prop) : Prop :=
  GeneratedExists ∧ ¬ DestroyedExists

/-- A first completion time is first in itself, not merely because some other part
of it is first, in Aristotle, *Physics* VI.5, 235b30-35.

Source: Aristotle, *Physics* VI.5, 235b30-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FirstCompletionTimePrimaryReading
    (CompletionTimeIsPrimary : Prop) : Prop :=
  CompletionTimeIsPrimary

/-- If a primary completion time were divisible, completion in either subinterval,
or changing throughout them, would yield something prior to the supposed first
completion in Aristotle, *Physics* VI.5, 235b34-236a5.

Source: Aristotle, *Physics* VI.5, 235b34-236a5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DivisibleCompletionTimeWouldNotBePrimaryReading
    (CompletionTimeDivisible CompletionTimeIsPrimary : Prop) : Prop :=
  CompletionTimeDivisible → ¬ CompletionTimeIsPrimary

/-- The primary time-boundary at which a change is complete is indivisible in
Aristotle, *Physics* VI.5, 235b30-236a5.

Source: Aristotle, *Physics* VI.5, 235b30-236a5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FirstCompletionTimeIndivisibleReading
    (CompletionTimeDivisible : Prop) : Prop :=
  ¬ CompletionTimeDivisible

/-- Generation and destruction are complete at an indivisible completion-boundary
in Aristotle, *Physics* VI.5, 236a3-6.

Source: Aristotle, *Physics* VI.5, 236a3-6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GenerationDestructionCompleteAtIndivisibleBoundaryReading
    (GenerationCompleteAtIndivisibleBoundary
      DestructionCompleteAtIndivisibleBoundary : Prop) : Prop :=
  GenerationCompleteAtIndivisibleBoundary ∧
    DestructionCompleteAtIndivisibleBoundary

/-- “The first time in which it has changed” may mean the boundary at which change
is completed or a supposed first time at which changing begins in Aristotle,
*Physics* VI.5, 236a7-12; only the completion sense has a first.

Source: Aristotle, *Physics* VI.5, 236a7-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FirstCompletionBeginningDistinctionReading
    (FirstCompletionBoundaryExists FirstBeginningIntervalExists : Prop) : Prop :=
  FirstCompletionBoundaryExists ∧ ¬ FirstBeginningIntervalExists

/-- A supposed first interval of changing cannot be indivisible, since that would
make adjacent nows and make the subject both resting and already changed at their
boundary, in Aristotle, *Physics* VI.5, 236a12-20.

Source: Aristotle, *Physics* VI.5, 236a12-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FirstChangingIntervalNotIndivisibleReading
    (FirstChangingIntervalIndivisible : Prop) : Prop :=
  ¬ FirstChangingIntervalIndivisible

/-- Any proposed first divisible interval of changing is self-defeating: division
shows changing in every subinterval, so a proper subinterval is already an interval
of changing, in Aristotle, *Physics* VI.5, 236a20-26.

Source: Aristotle, *Physics* VI.5, 236a20-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ProposedFirstChangingTimeNotFirstReading
    (ProposedFirstChangingTime : Prop) : Prop :=
  ProposedFirstChangingTime → ¬ ProposedFirstChangingTime

/-- There is no first extended time in which changing begins in Aristotle,
*Physics* VI.5, 236a12-26.

Source: Aristotle, *Physics* VI.5, 236a12-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoFirstChangingTimeReading
    (FirstChangingTimeExists : Prop) : Prop :=
  ¬ FirstChangingTimeExists

/-- Every changing subject is divisible, so if one part were the first changed part,
a smaller part would already have changed in an earlier half of its time, in
Aristotle, *Physics* VI.5, 236a26-35.

Source: Aristotle, *Physics* VI.5, 236a26-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ProposedFirstChangedPartHasEarlierSmallerPartReading
    (ProposedFirstChangedPart EarlierSmallerChangedPart : Prop) : Prop :=
  ProposedFirstChangedPart → EarlierSmallerChangedPart

/-- If an earlier smaller changed part exists, the proposed first changed part was
not first in Aristotle, *Physics* VI.5, 236a26-35.

Source: Aristotle, *Physics* VI.5, 236a26-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EarlierSmallerPartExcludesFirstChangedPartReading
    (EarlierSmallerChangedPart ProposedFirstChangedPart : Prop) : Prop :=
  EarlierSmallerChangedPart → ¬ ProposedFirstChangedPart

/-- No first part of a changing subject has completed the change in Aristotle,
*Physics* VI.5, 236a26-236b1.

Source: Aristotle, *Physics* VI.5, 236a26-236b1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoFirstChangedPartReading
    (ProposedFirstChangedPart : Prop) : Prop :=
  ¬ ProposedFirstChangedPart

end TruthCore.Greek.Aristotle.Physics
