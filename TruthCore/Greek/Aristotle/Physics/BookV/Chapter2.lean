import TruthCore.Greek.Aristotle.Physics.BookV.Chapter1

namespace TruthCore.Greek.Aristotle.Physics

/-- Substance has no motion in Aristotle, *Physics* V.2, 225b10-11, because none of
the things that are is contrary to substance. This concerns motion in the chapter's
restricted sense and does not deny substantial generation or corruption.

Source: Aristotle, *Physics* V.2, 225b10-11 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoMotionInSubstanceBecauseNoContraryReading
    (SubstanceHasContrary MotionBelongsToSubstance : Prop) : Prop :=
  ¬ SubstanceHasContrary ∧ ¬ MotionBelongsToSubstance

/-- Motion in relation is incidental in Aristotle, *Physics* V.2, 225b12-15: one
correlative may change while the other does not, although a relational predication of
the unchanged correlate becomes true or false.

Source: Aristotle, *Physics* V.2, 225b12-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RelativeMotionOnlyAccidentalReading
    (OneCorrelativeChanges OtherCorrelativeChanges
      RelationalPredicationCanBecomeTrueOrFalse RelativeMotionIsAccidental : Prop) : Prop :=
  OneCorrelativeChanges ∧ ¬ OtherCorrelativeChanges ∧
    RelationalPredicationCanBecomeTrueOrFalse ∧ RelativeMotionIsAccidental

/-- There is no motion in action and passion, mover and moved, in Aristotle,
*Physics* V.2, 225b15-16, because motion itself does not undergo motion and change
itself does not undergo change.

Source: Aristotle, *Physics* V.2, 225b15-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoMotionInActionOrPassionReading
    (MotionBelongsToActionOrPassion PerSeChangeOfChange : Prop) : Prop :=
  ¬ MotionBelongsToActionOrPassion ∧ ¬ PerSeChangeOfChange

/-- The first proposed sense of motion of motion fails in Aristotle, *Physics* V.2,
225b17-22: motion cannot itself be the underlying subject that heats, cools, changes
place, increases, or decreases, because change is not a subject.

Source: Aristotle, *Physics* V.2, 225b17-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangeCannotBeSubjectOfChangeReading
    (ChangeIsUnderlyingSubject ChangeCanHeatCoolMoveGrowOrDiminish : Prop) : Prop :=
  ¬ ChangeIsUnderlyingSubject ∧ ¬ ChangeCanHeatCoolMoveGrowOrDiminish

/-- The second proposed sense of change of change is possible only incidentally in
Aristotle, *Physics* V.2, 225b22-33. A subject may pass between states described by
changes, but the underlying subject changes to knowledge or ignorance; change itself
does not change in its own right.

Source: Aristotle, *Physics* V.2, 225b22-33 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangeOfChangeOnlyAccidentalReading
    (AccidentalChangeOfChangePossible PerSeChangeOfChangePossible : Prop) : Prop :=
  AccidentalChangeOfChangePossible ∧ ¬ PerSeChangeOfChangePossible

/-- First regress premise in Aristotle, *Physics* V.2, 225b34-226a6: if change itself
undergoes change, and generation itself generation, the proposed hierarchy proceeds
without limit.

Source: Aristotle, *Physics* V.2, 225b34-226a6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangeOfChangeLeadsToInfiniteRegressReading
    (PerSeChangeOfChange InfiniteRegress : Prop) : Prop :=
  PerSeChangeOfChange → InfiniteRegress

/-- Second regress premise in Aristotle, *Physics* V.2, 225b34-226a6: an infinite
hierarchy supplies no first stage and hence no following stage, so nothing can become,
move, or change on that hypothesis.

Source: Aristotle, *Physics* V.2, 225b34-226a6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteRegressPreventsAnyChangeReading
    (InfiniteRegress AnythingCanBecomeMoveOrChange : Prop) : Prop :=
  InfiniteRegress → ¬ AnythingCanBecomeMoveOrChange

/-- Regress conclusion in Aristotle, *Physics* V.2, 225b34-226a6: per se change of
change would make becoming, motion, and change impossible.

Source: Aristotle, *Physics* V.2, 225b34-226a6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangeOfChangePreventsAnyChangeReading
    (PerSeChangeOfChange AnythingCanBecomeMoveOrChange : Prop) : Prop :=
  PerSeChangeOfChange → ¬ AnythingCanBecomeMoveOrChange

/-- A further reductio in Aristotle, *Physics* V.2, 226a7-9: because becoming has
perishing as its contrary, what is becoming-becoming would be perishing at the very
moment it became becoming.

Source: Aristotle, *Physics* V.2, 226a7-9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BecomingOfBecomingEntailsSimultaneousPerishingReading
    (BecomingOfBecoming PerishingWhileBecoming : Prop) : Prop :=
  BecomingOfBecoming → PerishingWhileBecoming

/-- Becoming and change require underlying matter and distinct termini in Aristotle,
*Physics* V.2, 226a10-16. A process is the motion or becoming of some subject from
something to something else; the becoming of a process is not that process itself.

Source: Aristotle, *Physics* V.2, 226a10-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangeRequiresUnderlyingMatterAndDistinctProcessReading
    (BecomingAndChangeHaveUnderlyingMatter
      ProcessBelongsToSubjectFromSourceToGoal
      BecomingOfProcessIsThatProcess : Prop) : Prop :=
  BecomingAndChangeHaveUnderlyingMatter ∧
    ProcessBelongsToSubjectFromSourceToGoal ∧ ¬ BecomingOfProcessIsThatProcess

/-- If motion itself were moved, its supposed subject and goal would have to belong to
one of the three kinds of motion in Aristotle, *Physics* V.2, 226a17-18; for example,
locomotion would have to be altered or locally moved.

Source: Aristotle, *Physics* V.2, 226a17-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionOfMotionWouldRequireMotionKindSubjectAndGoalReading
    (MotionOfMotionRequiresMotionKindSubjectAndGoal : Prop) : Prop :=
  MotionOfMotionRequiresMotionKindSubjectAndGoal

/-- Aristotle's summary in *Physics* V.2, 226a19-22: of the incidental, partial,
and per se ways of being moved, change itself can change only incidentally, and
incidental change has already been excluded from the classification.

Source: Aristotle, *Physics* V.2, 226a19-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangeChangesOnlyIncidentallyAndIsExcludedReading
    (ChangeCanChangeOnlyIncidentally IncidentalChangeExcluded : Prop) : Prop :=
  ChangeCanChangeOnlyIncidentally ∧ IncidentalChangeExcluded

/-- Qualitative motion is alteration in Aristotle, *Physics* V.2, 226a23-27. The
relevant quality is passive quality, according to which a thing is affected or
unaffected, rather than the substantial quality expressed by a specific difference.

Source: Aristotle, *Physics* V.2, 226a23-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def QualityMotionIsAlterationInPassiveQualityReading
    (QualityMotionIsAlteration RelevantQualityIsPassive
      RelevantQualityIsSubstantialDifference : Prop) : Prop :=
  QualityMotionIsAlteration ∧ RelevantQualityIsPassive ∧
    ¬ RelevantQualityIsSubstantialDifference

/-- Quantitative motion has no single common name in Aristotle, *Physics* V.2,
226a28-31: motion toward complete magnitude is increase and motion away from it is
decrease.

Source: Aristotle, *Physics* V.2, 226a28-31 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def QuantityMotionIncreaseOrDecreaseReading
    (CommonQuantityMotionName IncreaseTowardCompleteMagnitude
      DecreaseAwayFromCompleteMagnitude : Prop) : Prop :=
  ¬ CommonQuantityMotionName ∧ IncreaseTowardCompleteMagnitude ∧
    DecreaseAwayFromCompleteMagnitude

/-- Local motion may be called locomotion generally in Aristotle, *Physics* V.2,
226a31-35, although strictly being carried applies to things unable to stop themselves
or unable to move themselves locally.

Source: Aristotle, *Physics* V.2, 226a31-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PlaceMotionCalledLocomotionStrictlyBeingCarriedReading
    (PlaceMotionGenerallyCalledLocomotion
      StrictlyCarriedCannotStopOrSelfMoveLocally : Prop) : Prop :=
  PlaceMotionGenerallyCalledLocomotion ∧ StrictlyCarriedCannotStopOrSelfMoveLocally

/-- Change to a greater or lesser degree within one kind is alteration in Aristotle,
*Physics* V.2, 226b1-9, because it is qualified motion from or toward a contrary.

Source: Aristotle, *Physics* V.2, 226b1-9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DegreeChangeWithinKindIsAlterationReading
    (GreaterOrLesserDegreeWithinKind QualifiedMotionFromOrTowardContrary
      SuchChangeIsAlteration : Prop) : Prop :=
  GreaterOrLesserDegreeWithinKind ∧ QualifiedMotionFromOrTowardContrary ∧
    SuchChangeIsAlteration

/-- Three senses of immovable in Aristotle, *Physics* V.2, 226b10-17: absolute
incapacity, difficulty or slowness in beginning to move, and failure to move when,
where, and as a naturally capable subject would. Only the third is rest, a privation
of motion in a subject capable of receiving motion.

Source: Aristotle, *Physics* V.2, 226b10-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ThreeSensesOfImmovableAndRestReading
    (AbsolutelyIncapableOfMotion HardOrSlowToBeginMoving
      NaturallyCapableButNotMovingAsNatural OnlyThirdSenseIsRest
      RestIsPrivationInMotionCapableSubject : Prop) : Prop :=
  (AbsolutelyIncapableOfMotion ∨ HardOrSlowToBeginMoving ∨
    NaturallyCapableButNotMovingAsNatural) ∧
    OnlyThirdSenseIsRest ∧ RestIsPrivationInMotionCapableSubject

end TruthCore.Greek.Aristotle.Physics
