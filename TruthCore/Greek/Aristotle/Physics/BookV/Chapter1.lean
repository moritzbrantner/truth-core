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

end TruthCore.Greek.Aristotle.Physics
