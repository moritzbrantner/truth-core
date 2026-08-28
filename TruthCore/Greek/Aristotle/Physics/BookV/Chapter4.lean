import TruthCore.Greek.Aristotle.Physics.BookV.Chapter3

namespace TruthCore.Greek.Aristotle.Physics

/-- A motion is called one in several ways because one itself is said in several ways,
in Aristotle, *Physics* V.4, 227b3.

Source: Aristotle, *Physics* V.4, 227b3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionSaidOneInSeveralWaysReading
    (MotionSaidOneInSeveralWays : Prop) : Prop :=
  MotionSaidOneInSeveralWays

/-- Motion is generically one according to its category in Aristotle, *Physics* V.4,
227b4-6: every locomotion is generically one with every locomotion, while alteration
and locomotion differ in genus.

Source: Aristotle, *Physics* V.4, 227b4-6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GenericUnityOfMotionFollowsCategoryReading
    (AnyLocomotionsGenericallyOne
      AlterationAndLocomotionGenericallyOne : Prop) : Prop :=
  AnyLocomotionsGenericallyOne ∧ ¬ AlterationAndLocomotionGenericallyOne

/-- Motion is specifically one when it is generically one and occurs in an indivisible
species in Aristotle, *Physics* V.4, 227b7-12. Thus every whitening is specifically one
with every whitening, while whitening and blackening differ specifically.

Source: Aristotle, *Physics* V.4, 227b7-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SpecificUnityRequiresIndivisibleSpeciesReading
    (GenericallyOne InSameIndivisibleSpecies SpecificallyOne : Prop) : Prop :=
  GenericallyOne ∧ InSameIndivisibleSpecies ∧ SpecificallyOne

/-- When something is both genus and species, its motion may be specifically one in a
qualified but not unqualified way in Aristotle, *Physics* V.4, 227b12-15. Learning is
the example when knowledge is a species of apprehension and a genus of sciences.

Source: Aristotle, *Physics* V.4, 227b12-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GenusSpeciesYieldsQualifiedSpecificUnityReading
    (KindIsBothGenusAndSpecies SpecificallyOneQualifiedly
      SpecificallyOneUnqualifiedly : Prop) : Prop :=
  KindIsBothGenusAndSpecies ∧ SpecificallyOneQualifiedly ∧
    ¬ SpecificallyOneUnqualifiedly

/-- Repetition by one subject from the same source to the same goal does not suffice
for specific unity of motion in Aristotle, *Physics* V.4, 227b15-20. A specifically
different path makes circular and rectilinear motion, or rolling and walking, different
motions.

Source: Aristotle, *Physics* V.4, 227b15-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PathSpeciesDifferentiatesMotionDespiteSameTerminiReading
    (SameSubjectSourceAndGoal PathSpecificallyDifferent
      MotionsSpecificallyOne : Prop) : Prop :=
  SameSubjectSourceAndGoal ∧ PathSpecificallyDifferent ∧ ¬ MotionsSpecificallyOne

/-- Three factors belong to motion in Aristotle, *Physics* V.4, 227b21-25: what moves,
the respect in which it moves, such as place or affection, and when it moves, since
every motion occurs in time.

Source: Aristotle, *Physics* V.4, 227b21-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ThreeNumericalMotionFactorsReading
    (MovingSubject RespectOfMotion TimeOfMotion : Prop) : Prop :=
  MovingSubject ∧ RespectOfMotion ∧ TimeOfMotion

/-- A motion is one without qualification and numerically one only when its relevant
species is one and indivisible, its time is one and uninterrupted, and its moving
subject is one non-accidentally, in Aristotle, *Physics* V.4, 227b25-228a2.

Source: Aristotle, *Physics* V.4, 227b25-228a2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def UnqualifiedOneMotionRequiresSpeciesSubjectTimeUnityReading
    (OneIndivisibleSpecies OneUninterruptedTime
      OneNonAccidentalMovingSubject : Prop) : Prop :=
  OneIndivisibleSpecies ∧ OneUninterruptedTime ∧ OneNonAccidentalMovingSubject

/-- Two subjects restored to health simultaneously in the same way undergo motions
that are specifically one but not numerically one, in Aristotle, *Physics* V.4,
227b25-228a2.

Source: Aristotle, *Physics* V.4, 227b25-228a2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SharedHealingSpecificallyNotNumericallyOneReading
    (TwoSubjectsSameSimultaneousHealing SpecificallyOneMotion
      NumericallyOneMotion : Prop) : Prop :=
  TwoSubjectsSameSimultaneousHealing ∧ SpecificallyOneMotion ∧ ¬ NumericallyOneMotion

/-- Repeated specifically identical alterations of one subject at different times are
numerically one only if what ceased to be can return as numerically the same, in
Aristotle, *Physics* V.4, 228a3-6.

Source: Aristotle, *Physics* V.4, 228a3-6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RepeatedMotionUnityDependsOnNumericalRecurrenceReading
    (CeasedProcessCanReturnNumericallySame RepeatedMotionNumericallyOne : Prop) : Prop :=
  RepeatedMotionNumericallyOne ↔ CeasedProcessCanReturnNumericallySame

/-- Aristotle raises, without settling, whether health and other states and affections
are numerically one across times while their bodily subjects move and flow, in
*Physics* V.4, 228a6-12.

Source: Aristotle, *Physics* V.4, 228a6-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def StateUnityAcrossTimesPuzzleReading
    (BodilySubjectsMoveAndFlow StateMayRemainNumericallyOneAcrossTimes : Prop) : Prop :=
  BodilySubjectsMoveAndFlow ∧ StateMayRemainNumericallyOneAcrossTimes

/-- Numerically distinct states require numerically distinct activities, but one state
does not by itself ensure one activity, in Aristotle, *Physics* V.4, 228a12-17: walking
ceases and may later occur again.

Source: Aristotle, *Physics* V.4, 228a12-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DistinctStatesRequireDistinctActivitiesNotConverselyReading
    (StatesNumericallyDistinct ActivitiesNumericallyDistinct
      OneStateEnsuresOneActivity : Prop) : Prop :=
  (StatesNumericallyDistinct → ActivitiesNumericallyDistinct) ∧
    ¬ OneStateEnsuresOneActivity

/-- If a state recovered after an interval were numerically one and the same, the same
thing could perish and exist many times; Aristotle sets this puzzle outside the present
inquiry in *Physics* V.4, 228a17-19.

Source: Aristotle, *Physics* V.4, 228a17-19 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NumericallySameRecurringStatePerishesAndExistsRepeatedlyReading
    (RecurringStateNumericallySame SameThingPerishesAndExistsRepeatedly : Prop) : Prop :=
  RecurringStateNumericallySame → SameThingPerishesAndExistsRepeatedly

end TruthCore.Greek.Aristotle.Physics
