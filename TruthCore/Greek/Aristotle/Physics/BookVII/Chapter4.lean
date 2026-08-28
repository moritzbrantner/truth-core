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

/-- Things to which a predicate is applied non-synonymously—without the same
meaning—are incomparable under that predicate, in Aristotle, *Physics* VII.4,
248b7-10.

Source: Aristotle, *Physics* VII.4, 248b7-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NonSynonymousPredicationsAreIncomparableReading
    (PredicateHasDifferentMeanings SubjectsComparableUnderPredicate : Prop) : Prop :=
  PredicateHasDifferentMeanings → ¬ SubjectsComparableUnderPredicate

/-- A stylus, wine, and a musical note are not comparable in sharpness because
`sharp` is homonymous across them, whereas two notes are comparable because
`sharp` has the same meaning for both, in Aristotle, *Physics* VII.4, 248b7-10.

Source: Aristotle, *Physics* VII.4, 248b7-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SharpnessHomonymyAndNoteComparisonReading
    (StylusWineNoteSharpnessIncomparable
      TwoNotesSharpnessComparableBecauseSameMeaning : Prop) : Prop :=
  StylusWineNoteSharpnessIncomparable ∧
    TwoNotesSharpnessComparableBecauseSameMeaning

/-- `Fast` may not have the same meaning for circular and rectilinear motion, and
still less for alteration and locomotion, in Aristotle, *Physics* VII.4,
248b10-12.

Source: Aristotle, *Physics* VII.4, 248b10-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SpeedMeaningDiffersAcrossMotionKindsReading
    (SpeedMeaningMayDifferCurveAndStraight
      SpeedMeaningDiffersMoreAlterationAndLocomotion : Prop) : Prop :=
  SpeedMeaningMayDifferCurveAndStraight ∧
    SpeedMeaningDiffersMoreAlterationAndLocomotion

/-- If shared non-homonymous meaning were sufficient for comparability, amounts
of water and air would be comparable under `much`, since the term has the same
meaning in both cases, in Aristotle's counterexample in *Physics* VII.4,
248b12-15.

Source: Aristotle, *Physics* VII.4, 248b12-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SharedMeaningSufficiencyWouldCompareWaterAndAirReading
    (SharedMeaningSufficientForComparability WaterAndAirAmountsComparable : Prop) : Prop :=
  SharedMeaningSufficientForComparability → WaterAndAirAmountsComparable

/-- Amounts of water and air are not comparable under `much`, despite the
apparently shared meaning of the predicate, in Aristotle, *Physics* VII.4,
248b12-15.

Source: Aristotle, *Physics* VII.4, 248b12-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def WaterAndAirAmountsNotComparableReading
    (WaterAndAirAmountsComparable : Prop) : Prop :=
  ¬ WaterAndAirAmountsComparable

/-- Shared non-homonymous meaning is not by itself sufficient for comparability,
in Aristotle, *Physics* VII.4, 248b12-16.

This conclusion preserves the passage's counterexample while leaving open
Aristotle's subsequent suggestion that apparently shared accounts may themselves
conceal homonymy.

Source: Aristotle, *Physics* VII.4, 248b12-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SharedMeaningNotSufficientForComparabilityReading
    (SharedMeaningSufficientForComparability : Prop) : Prop :=
  ¬ SharedMeaningSufficientForComparability

/-- Even the common ratio `two to one` for double does not make all instances of
double comparable, in Aristotle, *Physics* VII.4, 248b14-16.

Source: Aristotle, *Physics* VII.4, 248b14-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SharedDoubleRatioDoesNotEnsureComparabilityReading
    (DoubleHasSharedTwoToOneRatio AllDoublesComparable : Prop) : Prop :=
  DoubleHasSharedTwoToOneRatio ∧ ¬ AllDoublesComparable

/-- Aristotle warns that even accounts or definitions may be homonymous: `much`
can involve different specifications of the quantity exceeded, and `equal`,
`one`, and consequently `two` may likewise conceal different meanings, in
*Physics* VII.4, 248b16-21.

Source: Aristotle, *Physics* VII.4, 248b16-21 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ApparentlySharedAccountsMayBeHomonymousReading
    (AccountsMayBeHomonymous
      MuchEqualOneAndTwoMayConcealDifferentMeanings : Prop) : Prop :=
  AccountsMayBeHomonymous ∧
    MuchEqualOneAndTwoMayConcealDifferentMeanings

end TruthCore.Greek.Aristotle.Physics
