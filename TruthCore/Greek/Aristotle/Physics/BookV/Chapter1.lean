import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter14

namespace TruthCore.Greek.Aristotle.Physics

/-- Three ways a subject changes in Aristotle, *Physics* V.1, 224a21-31: incidentally,
because one of its parts changes, or directly and in virtue of itself as the primary movable.

Source: Aristotle, *Physics* V.1, 224a21-31 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangingSubjectIncidentalPartOrDirectReading
    (SubjectChangesIncidentally SubjectChangesThroughPart
      SubjectChangesDirectlyAsPrimaryMovable : Prop) : Prop :=
  SubjectChangesIncidentally ∨ SubjectChangesThroughPart ∨
    SubjectChangesDirectlyAsPrimaryMovable

/-- Corresponding distinctions for movers in Aristotle, *Physics* V.1, 224a31-35: a
mover moves incidentally, through one of its parts, or directly in virtue of itself.

Source: Aristotle, *Physics* V.1, 224a31-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MoverIncidentalPartOrDirectReading
    (MoverActsIncidentally MoverActsThroughPart MoverActsDirectly : Prop) : Prop :=
  MoverActsIncidentally ∨ MoverActsThroughPart ∨ MoverActsDirectly

/-- Factors of motion in Aristotle, *Physics* V.1, 224a35-224b4: a primary mover, the
moved subject, time, and distinct starting-point and goal belong to every motion.

Source: Aristotle, *Physics* V.1, 224a35-224b4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionFactorsMoverMovedTimeSourceGoalReading
    (PrimaryMover MovedSubject TimeOfMotion SourceOfMotion GoalOfMotion
      EveryMotionFromSourceToGoal : Prop) : Prop :=
  PrimaryMover ∧ MovedSubject ∧ TimeOfMotion ∧ SourceOfMotion ∧ GoalOfMotion ∧
    EveryMotionFromSourceToGoal

/-- Locus of motion in Aristotle, *Physics* V.1, 224b1-6: motion is in the moved subject,
such as the wood, not in the form, place, or quantity that serves as terminus.

Source: Aristotle, *Physics* V.1, 224b1-6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionInMovedSubjectNotTerminusReading
    (MotionInMovedSubject MotionInForm MotionInPlace MotionInQuantity : Prop) : Prop :=
  MotionInMovedSubject ∧ ¬ MotionInForm ∧ ¬ MotionInPlace ∧ ¬ MotionInQuantity

/-- Goal-based naming in Aristotle, *Physics* V.1, 224b6-10: change receives its name
from its goal more than from its source, so corruption is change to nonbeing and generation
change to being.

Source: Aristotle, *Physics* V.1, 224b6-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangeNamedFromGoalGenerationCorruptionReading
    (ChangeNamedMoreFromGoal CorruptionIsChangeToNonbeing
      GenerationIsChangeToBeing : Prop) : Prop :=
  ChangeNamedMoreFromGoal ∧ CorruptionIsChangeToNonbeing ∧
    GenerationIsChangeToBeing

/-- Immovable termini in Aristotle, *Physics* V.1, 224b10-15: forms, affections, and places
to which things move are not themselves motions; whitening, rather than whiteness, is motion.

Source: Aristotle, *Physics* V.1, 224b10-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionTerminiImmovableWhiteningNotWhitenessReading
    (FormsAffectionsPlacesAsGoalsImmovable WhitenessIsMotion WhiteningIsMotion : Prop) : Prop :=
  FormsAffectionsPlacesAsGoalsImmovable ∧ ¬ WhitenessIsMotion ∧ WhiteningIsMotion

/-- Ways a terminus belongs to change in Aristotle, *Physics* V.1, 224b16-23: a goal may
belong incidentally, as a containing whole or part-relation, or directly in itself.

Source: Aristotle, *Physics* V.1, 224b16-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangeGoalIncidentalPartOrDirectReading
    (GoalBelongsIncidentally GoalBelongsThroughPartOrWhole GoalBelongsDirectly : Prop) : Prop :=
  GoalBelongsIncidentally ∨ GoalBelongsThroughPartOrWhole ∨ GoalBelongsDirectly

/-- Closing locus conclusion in Aristotle, *Physics* V.1, 224b23-26: motion is not in the
form but in what is moving, namely the movable insofar as it is in actuality.

Source: Aristotle, *Physics* V.1, 224b23-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionInMovableInActualityNotFormReading
    (MotionInMovableInActuality MotionInForm : Prop) : Prop :=
  MotionInMovableInActuality ∧ ¬ MotionInForm

/-- Exclusion of accidental change in Aristotle, *Physics* V.1, 224b26-29: accidental
change is set aside because it can occur in everything, at any time, and in any respect.

Source: Aristotle, *Physics* V.1, 224b26-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AccidentalChangeSetAsideAsUnrestrictedReading
    (AccidentalChangeCanBelongToAnythingAnytimeAnyRespect
      AccidentalChangeExcludedFromClassification : Prop) : Prop :=
  AccidentalChangeCanBelongToAnythingAnytimeAnyRespect →
    AccidentalChangeExcludedFromClassification

/-- Scope of non-accidental change in Aristotle, *Physics* V.1, 224b29-35: it occurs only
among contraries, intermediates, and contradictories.

Source: Aristotle, *Physics* V.1, 224b29-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NonAccidentalChangeOnlyOppositesReading
    (ChangeIsNonAccidental ChangeAmongContrariesIntermediatesOrContradictories : Prop) : Prop :=
  ChangeIsNonAccidental → ChangeAmongContrariesIntermediatesOrContradictories

/-- Intermediates as relative contraries in Aristotle, *Physics* V.1, 224b30-225a1: an
intermediate can serve as contrary to either extreme and each extreme as contrary to it.

Source: Aristotle, *Physics* V.1, 224b30-225a1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IntermediateFunctionsAsContraryToEitherExtremeReading
    (IntermediateContraryToLowerExtreme IntermediateContraryToUpperExtreme
      LowerExtremeContraryToIntermediate UpperExtremeContraryToIntermediate : Prop) : Prop :=
  IntermediateContraryToLowerExtreme ∧ IntermediateContraryToUpperExtreme ∧
    LowerExtremeContraryToIntermediate ∧ UpperExtremeContraryToIntermediate

/-- From-to structure in Aristotle, *Physics* V.1, 225a1-3: every change proceeds from
something earlier to something later.

Source: Aristotle, *Physics* V.1, 225a1-3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EveryChangeFromEarlierToLaterReading
    (EveryChangeFromSomethingToSomething FromIsEarlier ToIsLater : Prop) : Prop :=
  EveryChangeFromSomethingToSomething ∧ FromIsEarlier ∧ ToIsLater

/-- Four formal combinations in Aristotle, *Physics* V.1, 225a3-7: change may be described
as subject to subject, subject to nonsubject, nonsubject to subject, or nonsubject to
nonsubject, where subject is what is affirmatively expressed.

Source: Aristotle, *Physics* V.1, 225a3-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FourCandidateChangeCombinationsReading
    (SubjectToSubject SubjectToNonSubject NonSubjectToSubject
      NonSubjectToNonSubject : Prop) : Prop :=
  SubjectToSubject ∨ SubjectToNonSubject ∨ NonSubjectToSubject ∨
    NonSubjectToNonSubject

/-- Exclusion of the fourth combination in Aristotle, *Physics* V.1, 225a7-12:
nonsubject-to-nonsubject is not change because its terms stand in neither contrary nor
contradictory opposition.

Source: Aristotle, *Physics* V.1, 225a7-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NonSubjectToNonSubjectIsNotChangeReading
    (NonSubjectToNonSubjectIsChange : Prop) : Prop :=
  ¬ NonSubjectToNonSubjectIsChange

/-- Three-kind conclusion in Aristotle, *Physics* V.1, 225a7-12: change is subject to
subject, subject to nonsubject, or nonsubject to subject.

Source: Aristotle, *Physics* V.1, 225a7-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ThreeKindsOfChangeReading
    (SubjectToSubject SubjectToNonSubject NonSubjectToSubject : Prop) : Prop :=
  SubjectToSubject ∨ SubjectToNonSubject ∨ NonSubjectToSubject

/-- Generation classification in Aristotle, *Physics* V.1, 225a12-17: contradictory
change from nonsubject to subject is generation, unqualified when toward substance and
particular when toward an attribute such as white.

Source: Aristotle, *Physics* V.1, 225a12-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NonSubjectToSubjectIsGenerationReading
    (NonSubjectToSubjectIsGeneration UnqualifiedGenerationTowardSubstance
      ParticularGenerationTowardAttribute : Prop) : Prop :=
  NonSubjectToSubjectIsGeneration ∧ UnqualifiedGenerationTowardSubstance ∧
    ParticularGenerationTowardAttribute

/-- Corruption classification in Aristotle, *Physics* V.1, 225a17-20: subject to
nonsubject is corruption, unqualified when from substance to nonbeing and particular when
toward an opposed negation.

Source: Aristotle, *Physics* V.1, 225a17-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SubjectToNonSubjectIsCorruptionReading
    (SubjectToNonSubjectIsCorruption UnqualifiedCorruptionFromSubstance
      ParticularCorruptionTowardOpposedNegation : Prop) : Prop :=
  SubjectToNonSubjectIsCorruption ∧ UnqualifiedCorruptionFromSubstance ∧
    ParticularCorruptionTowardOpposedNegation

end TruthCore.Greek.Aristotle.Physics
