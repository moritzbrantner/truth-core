import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter3

namespace TruthCore.Greek.Aristotle.Physics

/-- Things are equal in speed when they move an equal amount in an equal time,
within the comparisons for which the relevant amounts are commensurable, in
Aristotle, *Physics* VII.4, 248a10-16.

The commensurability qualification follows the surrounding reductio and prevents
this criterion from itself asserting that every kind of motion is comparable.

Source: Aristotle, *Physics* VII.4, 248a10-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EqualSpeedRequiresEqualComparableAmountAndTimeReading
    (EqualComparableAmountInEqualTime EqualSpeed : Prop) : Prop :=
  EqualComparableAmountInEqualTime → EqualSpeed

/-- If every motion were comparable with every other, some alteration would be
equal to a locomotion when the two completed their respective changes in equal
times, in Aristotle, *Physics* VII.4, 248a10-14.

Source: Aristotle, *Physics* VII.4, 248a10-14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def UniversalComparabilityEntailsAlterationLocomotionEqualityReading
    (EveryMotionComparable AlterationEqualToLocomotion : Prop) : Prop :=
  EveryMotionComparable → AlterationEqualToLocomotion

/-- Equality between an alteration and a locomotion would require an affection to
be equal to a length, in Aristotle's cross-kind comparison reductio in *Physics*
VII.4, 248a13-15.

Source: Aristotle, *Physics* VII.4, 248a13-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AlterationLocomotionEqualityEntailsAffectionLengthEqualityReading
    (AlterationEqualToLocomotion AffectionEqualToLength : Prop) : Prop :=
  AlterationEqualToLocomotion → AffectionEqualToLength

/-- An affection cannot be equal to a length, in Aristotle, *Physics* VII.4,
248a14-16.

This is Aristotle's rejection of cross-category commensuration, not a claim that
affections lack every kind of magnitude or degree.

Source: Aristotle, *Physics* VII.4, 248a14-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoAffectionEqualToLengthReading
    (AffectionEqualToLength : Prop) : Prop :=
  ¬ AffectionEqualToLength

/-- Not every motion is comparable with every other motion, in Aristotle,
*Physics* VII.4, 248a10-18.

Source: Aristotle, *Physics* VII.4, 248a10-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NotEveryMotionComparableReading
    (EveryMotionComparable : Prop) : Prop :=
  ¬ EveryMotionComparable

/-- Treating motion on a circle and motion on a straight line as comparable would
ultimately require a curved line to be equal to a straight line, through the
faster/slower and equal-distance relations developed in the passage, in
Aristotle, *Physics* VII.4, 248a18-248b5.

Source: Aristotle, *Physics* VII.4, 248a18-248b5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CurvedStraightComparabilityEntailsLineEqualityReading
    (CurvedAndStraightComparable CurvedLineEqualToStraightLine : Prop) : Prop :=
  CurvedAndStraightComparable → CurvedLineEqualToStraightLine

/-- A curved line and a straight line are not comparable in the required sense,
and neither are the corresponding motions, in Aristotle, *Physics* VII.4,
248b5-7.

Source: Aristotle, *Physics* VII.4, 248b5-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CurvedStraightLinesAndMotionsNotComparableReading
    (CurvedAndStraightComparable CorrespondingMotionsComparable : Prop) : Prop :=
  ¬ CurvedAndStraightComparable ∧ ¬ CorrespondingMotionsComparable

end TruthCore.Greek.Aristotle.Physics
