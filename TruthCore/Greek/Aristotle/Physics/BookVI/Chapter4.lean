import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter3

namespace TruthCore.Greek.Aristotle.Physics

/-- Every change is from something to something; a subject wholly at its terminus
has ceased changing, while one wholly at its source has not yet begun, in Aristotle,
*Physics* VI.4, 234b10-15.

Source: Aristotle, *Physics* VI.4, 234b10-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangeSourceTerminusStatusReading
    (EveryChangeFromSourceToTerminus WhollyAtTerminusNoLongerChanging
      WhollyAtSourceNotYetChanging : Prop) : Prop :=
  EveryChangeFromSourceToTerminus ∧ WhollyAtTerminusNoLongerChanging ∧
    WhollyAtSourceNotYetChanging

/-- While a subject is changing, one part must be at the source and another at the
first terminus of the change in Aristotle, *Physics* VI.4, 234b13-18.

Source: Aristotle, *Physics* VI.4, 234b13-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangingSubjectPartlySourcePartlyTerminusReading
    (PartAtSource PartAtFirstTerminus : Prop) : Prop :=
  PartAtSource ∧ PartAtFirstTerminus

/-- The relevant terminus is the first condition reached in the change, such as grey
from white rather than the remote extreme black, in Aristotle, *Physics* VI.4,
234b15-18.

Source: Aristotle, *Physics* VI.4, 234b15-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangeTerminusIsFirstReachedConditionReading
    (TerminusIsFirstReachedCondition NotNecessarilyRemoteExtreme : Prop) : Prop :=
  TerminusIsFirstReachedCondition ∧ NotNecessarilyRemoteExtreme

/-- Aristotle's inferential transition in *Physics* VI.4, 234b13-20: occupying the
source and first terminus in different parts entails that the changing subject is
divisible.

Source: Aristotle, *Physics* VI.4, 234b13-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PartlySourceTerminusImpliesChangingSubjectDivisibleReading
    (PartAtSource PartAtFirstTerminus ChangingSubjectDivisible : Prop) : Prop :=
  (PartAtSource ∧ PartAtFirstTerminus) → ChangingSubjectDivisible

/-- Every changing subject is divisible in Aristotle, *Physics* VI.4, 234b10-20.

Source: Aristotle, *Physics* VI.4, 234b10-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EveryChangingSubjectDivisibleReading
    (ChangingSubjectDivisible : Prop) : Prop :=
  ChangingSubjectDivisible

/-- Motion is divisible in two ways, by time and by the motions of the moving
subject's parts, in Aristotle, *Physics* VI.4, 234b20-24.

Source: Aristotle, *Physics* VI.4, 234b20-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionDivisibleByTimeAndSubjectPartsReading
    (MotionDivisibleByTime MotionDivisibleBySubjectPartMotions : Prop) : Prop :=
  MotionDivisibleByTime ∧ MotionDivisibleBySubjectPartMotions

/-- The motions of the subject's parts together constitute the motion of the whole
subject in Aristotle, *Physics* VI.4, 234b23-35.

Source: Aristotle, *Physics* VI.4, 234b23-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PartMotionsComposeWholeMotionReading
    (EachPartHasOwnMotion PartMotionsComposeWholeMotion : Prop) : Prop :=
  EachPartHasOwnMotion ∧ PartMotionsComposeWholeMotion

/-- Any remainder or excess beyond the motions of the parts would be a motion of
neither the whole, its parts, nor anything else, which is impossible, in Aristotle,
*Physics* VI.4, 234b35-235a8.

Source: Aristotle, *Physics* VI.4, 234b35-235a8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoSurplusBeyondPartMotionsReading
    (SurplusMotionBelongsToNothing SurplusMotionPossible : Prop) : Prop :=
  SurplusMotionBelongsToNothing → ¬ SurplusMotionPossible

/-- The whole subject's motion is the same as and equal to the composition of its
part-motions in Aristotle, *Physics* VI.4, 235a1-10.

Source: Aristotle, *Physics* VI.4, 235a1-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def WholeMotionEqualsComposedPartMotionsReading
    (WholeMotionSameAsComposedPartMotions
      WholeMotionEqualToComposedPartMotions : Prop) : Prop :=
  WholeMotionSameAsComposedPartMotions ∧ WholeMotionEqualToComposedPartMotions

/-- Every motion occurs in time, every time is divisible, and a smaller time contains
a smaller motion in Aristotle, *Physics* VI.4, 235a10-13.

Source: Aristotle, *Physics* VI.4, 235a10-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionOccursInDivisibleTimeReading
    (EveryMotionOccursInTime EveryTimeDivisible SmallerTimeHasSmallerMotion : Prop) : Prop :=
  EveryMotionOccursInTime ∧ EveryTimeDivisible ∧ SmallerTimeHasSmallerMotion

/-- Aristotle's temporal-divisibility transition in *Physics* VI.4, 235a10-13: the
divisibility of a motion's time and correspondence of smaller times with smaller
motions entails that the motion is divisible by time.

Source: Aristotle, *Physics* VI.4, 235a10-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DivisibleTimeImpliesMotionTemporallyDivisibleReading
    (EveryMotionOccursInTime EveryTimeDivisible SmallerTimeHasSmallerMotion
      EveryMotionTemporallyDivisible : Prop) : Prop :=
  (EveryMotionOccursInTime ∧ EveryTimeDivisible ∧ SmallerTimeHasSmallerMotion) →
    EveryMotionTemporallyDivisible

/-- Every motion is divisible according to time in Aristotle, *Physics* VI.4,
235a10-13.

Source: Aristotle, *Physics* VI.4, 235a10-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EveryMotionTemporallyDivisibleReading
    (EveryMotionTemporallyDivisible : Prop) : Prop :=
  EveryMotionTemporallyDivisible

/-- Time, motion, being-in-motion, the moving subject, and that in which the motion
occurs have corresponding divisions in Aristotle, *Physics* VI.4, 235a13-18.

Source: Aristotle, *Physics* VI.4, 235a13-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeMotionSubjectFieldCorrespondingDivisionsReading
    (TimeMotionDivisionsCorrespond MotionActivityDivisionsCorrespond
      SubjectFieldDivisionsCorrespond : Prop) : Prop :=
  TimeMotionDivisionsCorrespond ∧ MotionActivityDivisionsCorrespond ∧
    SubjectFieldDivisionsCorrespond

/-- The field of local motion is divisible in itself, whereas a qualitative field is
divisible incidentally through the divisible subject bearing it, in Aristotle,
*Physics* VI.4, 235a15-18.

Source: Aristotle, *Physics* VI.4, 235a15-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PlacePerSeQualityIncidentallyDivisibleReading
    (PlaceDivisiblePerSe QualityDivisibleIncidentally : Prop) : Prop :=
  PlaceDivisiblePerSe ∧ QualityDivisibleIncidentally

/-- Motion and its time imply one another's divisibility: dividing either yields a
corresponding smaller part of the other in Aristotle, *Physics* VI.4, 235a18-23.

Source: Aristotle, *Physics* VI.4, 235a18-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionTimeMutuallyDivisibleReading
    (MotionDivisible TimeDivisible : Prop) : Prop :=
  MotionDivisible ↔ TimeDivisible

/-- Being-in-motion is divisible according to divisions of the motion in Aristotle,
*Physics* VI.4, 235a23-27.

Source: Aristotle, *Physics* VI.4, 235a23-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BeingInMotionDivisibleWithMotionReading
    (MotionDivisible BeingInMotionDivisible : Prop) : Prop :=
  MotionDivisible → BeingInMotionDivisible

/-- The activities of moving according to the part-motions continuously compose the
whole activity of moving according to the whole motion in Aristotle, *Physics* VI.4,
235a27-34.

Source: Aristotle, *Physics* VI.4, 235a27-34 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PartActivitiesComposeWholeBeingInMotionReading
    (PartActivitiesContinuous WholeActivityComposedFromPartActivities : Prop) : Prop :=
  PartActivitiesContinuous ∧ WholeActivityComposedFromPartActivities

/-- Dividing any one of time, motion, being-in-motion, moving subject, or field of
change brings corresponding divisions of all the others in Aristotle, *Physics* VI.4,
235a34-235b2.

Source: Aristotle, *Physics* VI.4, 235a34-235b2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DividingOneChangeCorrelateDividesAllReading
    (DividingOneCorrelateDividesAll : Prop) : Prop :=
  DividingOneCorrelateDividesAll

/-- Finitude or infinity in time, motion, being-in-motion, subject, and field of
change correspond across the same coordinated structure in Aristotle, *Physics* VI.4,
235b2-5; their divisibility and infinity follow most directly from the changing
subject.

Source: Aristotle, *Physics* VI.4, 235b2-5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangeCorrelatesFinitudeInfinityCorrespondReading
    (FinitudeInfinityCorrespondAcrossChangeCorrelates
      DivisibilityInfinityFollowChieflyFromChangingSubject : Prop) : Prop :=
  FinitudeInfinityCorrespondAcrossChangeCorrelates ∧
    DivisibilityInfinityFollowChieflyFromChangingSubject

end TruthCore.Greek.Aristotle.Physics
