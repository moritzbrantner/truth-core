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

/-- A horse and a dog are comparable in whiteness because the relevant primary
recipient is the same—the surface—and likewise comparable in magnitude under the
corresponding common recipient, in Aristotle, *Physics* VII.4, 248b21-24.

Source: Aristotle, *Physics* VII.4, 248b21-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def HorseDogComparableThroughSamePrimaryRecipientReading
    (SameRelevantPrimaryRecipient HorseDogWhitenessComparable
      HorseDogMagnitudeComparable : Prop) : Prop :=
  SameRelevantPrimaryRecipient ∧ HorseDogWhitenessComparable ∧
    HorseDogMagnitudeComparable

/-- Water and voice are not comparable because the relevant property belongs in
different primary recipients, in Aristotle, *Physics* VII.4, 248b24-25.

Source: Aristotle, *Physics* VII.4, 248b24-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def WaterVoiceIncomparableDifferentPrimaryRecipientsReading
    (DifferentPrimaryRecipients WaterAndVoiceComparable : Prop) : Prop :=
  DifferentPrimaryRecipients ∧ ¬ WaterAndVoiceComparable

/-- Treating difference of recipient as sufficient to explain every difference
would collapse all properties into one property instantiated in different
subjects, making equal, sweet, and white the same in different bearers, in
Aristotle's objection in *Physics* VII.4, 248b25-249a2.

Source: Aristotle, *Physics* VII.4, 248b25-249a2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RecipientDifferenceAloneRisksPropertyCollapseReading
    (RecipientDifferenceAloneMakesPropertiesOne
      EqualSweetAndWhiteWouldBecomeSameProperty : Prop) : Prop :=
  RecipientDifferenceAloneMakesPropertiesOne ∧
    EqualSweetAndWhiteWouldBecomeSameProperty

/-- A recipient is not an arbitrary recipient of an arbitrary property; each
property has its own primary recipient, in Aristotle, *Physics* VII.4, 249a1-3.

Source: Aristotle, *Physics* VII.4, 249a1-3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EachPropertyHasOwnPrimaryRecipientReading
    (NotEverySubjectReceivesEveryProperty EachPropertyHasOwnPrimaryRecipient : Prop) : Prop :=
  NotEverySubjectReceivesEveryProperty ∧ EachPropertyHasOwnPrimaryRecipient

/-- From the contrast between comparisons sharing a primary recipient and cases
with different recipients, together with the specificity of each property's
primary recipient, Aristotle derives that comparables must share meaning and have
no relevant difference either in what is compared or in its primary subject, in
*Physics* VII.4, 248b21-249a5.

Source: Aristotle, *Physics* VII.4, 248b21-249a5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PrimaryRecipientContrastEntailsComparabilityConditionsReading
    (SameRelevantPrimaryRecipient DifferentPrimaryRecipients
      EachPropertyHasOwnPrimaryRecipient ComparablesUseSameMeaning
      NoRelevantDifferenceInComparedProperty
      NoRelevantDifferenceInPrimaryRecipient : Prop) : Prop :=
  (SameRelevantPrimaryRecipient ∧ DifferentPrimaryRecipients ∧
      EachPropertyHasOwnPrimaryRecipient) →
    (ComparablesUseSameMeaning ∧ NoRelevantDifferenceInComparedProperty ∧
      NoRelevantDifferenceInPrimaryRecipient)

/-- Comparable things must use the predicate with the same meaning and have no
relevant difference either in the determinate property compared or in its primary
recipient, in Aristotle, *Physics* VII.4, 249a3-5.

These are recorded as necessary conditions, not as a sufficient decision
procedure for every comparison.

Source: Aristotle, *Physics* VII.4, 249a3-5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ComparabilityRequiresSameMeaningPropertyAndSubjectReading
    (ComparablesUseSameMeaning NoRelevantDifferenceInComparedProperty
      NoRelevantDifferenceInPrimaryRecipient : Prop) : Prop :=
  ComparablesUseSameMeaning ∧ NoRelevantDifferenceInComparedProperty ∧
    NoRelevantDifferenceInPrimaryRecipient

/-- Subjects are not compared as more colored merely qua generic color, since
color divides into kinds; they are compared under a determinate color such as
white, in Aristotle, *Physics* VII.4, 249a4-7.

Source: Aristotle, *Physics* VII.4, 249a4-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GenericColorNotComparableButWhiteComparableReading
    (GenericColorDegreeComparable DeterminateWhiteDegreeComparable : Prop) : Prop :=
  ¬ GenericColorDegreeComparable ∧ DeterminateWhiteDegreeComparable

/-- Alteration and locomotion cannot be equal or equal in speed merely because
each completes some amount in the same time, in Aristotle, *Physics* VII.4,
249a7-10.

Source: Aristotle, *Physics* VII.4, 249a7-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AlterationAndLocomotionNotEqualSpeedReading
    (AlterationEqualToLocomotion AlterationAndLocomotionEqualSpeed : Prop) : Prop :=
  ¬ AlterationEqualToLocomotion ∧ ¬ AlterationAndLocomotionEqualSpeed

/-- The explanation of the failed cross-kind speed comparisons is that motion has
species, in Aristotle, *Physics* VII.4, 249a10-15.

Source: Aristotle, *Physics* VII.4, 249a10-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionHasSpeciesReading
    (MotionHasSpecies : Prop) : Prop :=
  MotionHasSpecies

/-- If that on which locomotion occurs is divided into species, locomotion has
corresponding species, in Aristotle's proposed explanation in *Physics* VII.4,
249a13-17.

This conditional is weaker than the V.4 claim about different paths with the same
subject, source, and goal, so the two statements retain independent identities.

Source: Aristotle, *Physics* VII.4, 249a13-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PathSpeciesConditionallyDifferentiateLocomotionReading
    (PathsHaveDifferentSpecies LocomotionsHaveDifferentSpecies : Prop) : Prop :=
  PathsHaveDifferentSpecies → LocomotionsHaveDifferentSpecies

/-- Aristotle also tests whether locomotion differs with the means of motion—feet
yielding walking and wings flight—or instead with the shapes traced, in
*Physics* VII.4, 249a15-18.

The alternatives remain dialectical rather than being collapsed into a single
settled criterion.

Source: Aristotle, *Physics* VII.4, 249a15-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MeansAndShapeAsPossibleLocomotionDifferencesReading
    (FeetYieldWalking WingsYieldFlight
      ShapeMayInsteadDifferentiateLocomotion : Prop) : Prop :=
  FeetYieldWalking ∧ WingsYieldFlight ∧
    ShapeMayInsteadDifferentiateLocomotion

/-- Given that motion has species, equal speed requires no difference in species
of the motions compared, in Aristotle, *Physics* VII.4, 249a18-20.

Source: Aristotle, *Physics* VII.4, 249a18-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionSpeciesAccountEntailsEqualSpeedSpeciesIdentityReading
    (MotionHasSpecies MotionsEqualSpeed MotionsDifferInSpecies : Prop) : Prop :=
  MotionHasSpecies → (MotionsEqualSpeed → ¬ MotionsDifferInSpecies)

/-- Motions that differ in species are not equal in speed under the comparison
criterion Aristotle is developing, in *Physics* VII.4, 249a18-20.

This does not deny that a later mathematical framework could assign numerical
rates across categories; it records Aristotle's required comparison class.

Source: Aristotle, *Physics* VII.4, 249a18-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SpeciesDifferentMotionsNotEqualSpeedReading
    (MotionsDifferInSpecies MotionsEqualSpeed : Prop) : Prop :=
  MotionsDifferInSpecies → ¬ MotionsEqualSpeed

/-- A genus is not always one undifferentiated item; it may conceal a plurality of
kinds, in Aristotle, *Physics* VII.4, 249a20-22.

Source: Aristotle, *Physics* VII.4, 249a20-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GenusMayConcealMultipleKindsReading
    (GenusMayConcealMultipleKinds : Prop) : Prop :=
  GenusMayConcealMultipleKinds

/-- Homonymous uses may be far apart, share some similarity, or lie close by
genus or analogy, and the latter can escape notice as homonymy, in Aristotle,
*Physics* VII.4, 249a20-24.

Source: Aristotle, *Physics* VII.4, 249a20-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def HomonymiesVaryInDistanceAndSimilarityReading
    (SomeHomonymiesFarApart SomeShareSimilarity
      SomeCloseByGenusOrAnalogy CloseHomonymyMayEscapeNotice : Prop) : Prop :=
  SomeHomonymiesFarApart ∧ SomeShareSimilarity ∧
    SomeCloseByGenusOrAnalogy ∧ CloseHomonymyMayEscapeNotice

/-- The criterion for species difference remains under examination: whether the
same item in a different recipient, or different items in different recipients,
marks another species, and whether apparent difference is merely recipient-
relative or absolute, in Aristotle, *Physics* VII.4, 249a24-29.

Source: Aristotle, *Physics* VII.4, 249a24-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionSpeciesBoundaryRequiresFurtherCriterionReading
    (SameInDifferentRecipientMayMarkSpeciesDifference
      DifferentInDifferentRecipientsMayMarkSpeciesDifference
      MustDistinguishRecipientRelativeFromAbsoluteDifference : Prop) : Prop :=
  SameInDifferentRecipientMayMarkSpeciesDifference ∧
    DifferentInDifferentRecipientsMayMarkSpeciesDifference ∧
    MustDistinguishRecipientRelativeFromAbsoluteDifference

/-- Healing supplies Aristotle's first example of equal-speed alteration: healing
is alteration, people may heal quickly, slowly, or together, and equal-time
instances may therefore be called equal in speed, in *Physics* VII.4,
249a29-249b3.

Source: Aristotle, *Physics* VII.4, 249a29-249b3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def HealingCanSupplyEqualSpeedAlterationReading
    (HealingIsAlteration PeopleHealFastSlowOrTogether
      EqualTimeHealingCanBeEqualSpeed : Prop) : Prop :=
  HealingIsAlteration ∧ PeopleHealFastSlowOrTogether ∧
    EqualTimeHealingCanBeEqualSpeed

/-- Qualitative alteration is compared by similarity rather than by the equality
properly said of quantity, in Aristotle, *Physics* VII.4, 249b1-4.

Source: Aristotle, *Physics* VII.4, 249b1-4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def QualityComparisonUsesSimilarityNotEqualityReading
    (QualitiesComparedBySimilarity QualitiesNotComparedByEquality : Prop) : Prop :=
  QualitiesComparedBySimilarity ∧ QualitiesNotComparedByEquality

/-- Aristotle provisionally calls alterations equal in speed when the same
alteration occurs in equal times, in *Physics* VII.4, 249b3-5.

Source: Aristotle, *Physics* VII.4, 249b3-5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SameAlterationEqualTimeCriterionReading
    (SameAlteration EqualTime EqualSpeed : Prop) : Prop :=
  SameAlteration → EqualTime → EqualSpeed

/-- Health is the same affection and may be present similarly in two recipients;
it is not itself more or less health, in Aristotle, *Physics* VII.4, 249b5-8.

Source: Aristotle, *Physics* VII.4, 249b5-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def HealthSameAndSimilarlyPresentReading
    (HealthIsSame HealthNeitherMoreNorLess HealthSimilarlyPresent : Prop) : Prop :=
  HealthIsSame ∧ HealthNeitherMoreNorLess ∧ HealthSimilarlyPresent

/-- Whitening and healing involve different affections, for which Aristotle finds
no common item that is the same, equal, or similar, in *Physics* VII.4,
249b7-10.

This records the local comparison problem without generalizing it to every pair
of different affections.

Source: Aristotle, *Physics* VII.4, 249b7-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def WhiteningHealingAffectionsDifferentNoCommonComparisonReading
    (WhiteningHealingAffectionsDifferent NoSameEqualOrSimilarMeasure : Prop) : Prop :=
  WhiteningHealingAffectionsDifferent ∧ NoSameEqualOrSimilarMeasure

/-- In Aristotle's analysis, different affections make the corresponding
alterations different in species, in *Physics* VII.4, 249b8-12.

Source: Aristotle, *Physics* VII.4, 249b8-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DifferentAffectionsEntailDifferentAlterationSpeciesReading
    (AffectionsDifferent AlterationsDifferInSpecies : Prop) : Prop :=
  AffectionsDifferent → AlterationsDifferInSpecies

/-- Whitening and healing are different species of alteration under Aristotle's
affection-sensitive division, in *Physics* VII.4, 249b8-12.

Source: Aristotle, *Physics* VII.4, 249b8-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def WhiteningHealingDifferentAlterationSpeciesReading
    (WhiteningHealingAlterationsDifferInSpecies : Prop) : Prop :=
  WhiteningHealingAlterationsDifferInSpecies

/-- The comparison inquiry therefore requires determining the species of both
alteration and locomotion, in Aristotle, *Physics* VII.4, 249b10-12.

Source: Aristotle, *Physics* VII.4, 249b10-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MustEnumerateAlterationLocomotionSpeciesReading
    (MustEnumerateAlterationSpecies MustEnumerateLocomotionSpecies : Prop) : Prop :=
  MustEnumerateAlterationSpecies ∧ MustEnumerateLocomotionSpecies

/-- When the things moved in their own right differ in species, genus, or number,
their motions differ at the corresponding level, in *Physics* VII.4,
249b12-15.

The restriction to motions belonging to their subjects in their own right
excludes merely accidental motion.

Source: Aristotle, *Physics* VII.4, 249b12-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PerSeMovedSubjectDifferencesTransferToMotionsReading
    (SubjectsDifferInSpecies SubjectsDifferInGenus SubjectsDifferInNumber
      MotionsDifferInSpecies MotionsDifferInGenus MotionsDifferInNumber : Prop) : Prop :=
  (SubjectsDifferInSpecies → MotionsDifferInSpecies) ∧
    (SubjectsDifferInGenus → MotionsDifferInGenus) ∧
    (SubjectsDifferInNumber → MotionsDifferInNumber)

/-- Aristotle's proposed two-factor analysis makes sameness or difference of an
alteration track the affection, while equality or inequality tracks the amount
altered, in *Physics* VII.4, 249b15-20.

Source: Aristotle, *Physics* VII.4, 249b15-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AlterationIdentityAndEqualityTrackAffectionAndSubjectReading
    (SameAffection DifferentAffection EqualAffectedAmount UnequalAffectedAmount
      SameAlteration DifferentAlteration EqualAlteration UnequalAlteration : Prop) : Prop :=
  (SameAffection → SameAlteration) ∧
    (DifferentAffection → DifferentAlteration) ∧
    (EqualAffectedAmount → EqualAlteration) ∧
    (UnequalAffectedAmount → UnequalAlteration)

/-- Under Aristotle's two-factor analysis, the same affection in equal affected
amounts yields alterations that are both the same and equal, in *Physics*
VII.4, 249b15-20.

Source: Aristotle, *Physics* VII.4, 249b15-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SameAffectionEqualSubjectAlterationsReading
    (SameAffection EqualAffectedAmount SameAlteration EqualAlteration : Prop) : Prop :=
  SameAffection ∧ EqualAffectedAmount → SameAlteration ∧ EqualAlteration

/-- The same comparison question must be examined for generation and corruption,
in Aristotle, *Physics* VII.4, 249b20.

Source: Aristotle, *Physics* VII.4, 249b20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GenerationCorruptionRequireSameComparisonInquiryReading
    (GenerationRequiresComparisonInquiry
      CorruptionRequiresComparisonInquiry : Prop) : Prop :=
  GenerationRequiresComparisonInquiry ∧ CorruptionRequiresComparisonInquiry

/-- Generations are equal in speed when the same indivisible kind is produced in
equal times; Aristotle's example is human rather than the wider genus animal,
in *Physics* VII.4, 249b20-23.

Here "indivisible" records the source's taxonomic comparison class, not spatial
or numerical indivisibility.

Source: Aristotle, *Physics* VII.4, 249b20-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EqualSpeedGenerationSameIndivisibleKindEqualTimeReading
    (SameIndivisibleKind EqualTime EqualSpeedGeneration
      HumanSuppliesComparisonKind AnimalGenusTooBroad : Prop) : Prop :=
  (SameIndivisibleKind → EqualTime → EqualSpeedGeneration) ∧
    HumanSuppliesComparisonKind ∧ AnimalGenusTooBroad

/-- When different kinds are generated in equal times, Aristotle lacks a pair of
comparison terms in which their difference corresponds to qualitative
unlikeness, in *Physics* VII.4, 249b23-24.

Source: Aristotle, *Physics* VII.4, 249b23-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DifferentGeneratedKindsLackUnlikenessStyleMeasureReading
    (DifferentKindsGeneratedInEqualTime
      NoComparisonPairCorrespondsToUnlikeness : Prop) : Prop :=
  DifferentKindsGeneratedInEqualTime ∧
    NoComparisonPairCorrespondsToUnlikeness

/-- If substance is number, greater and lesser number may be said within one
species, but Aristotle says that the common comparison relation is unnamed, in
*Physics* VII.4, 249b24-26.

The numerical account of substance remains the antecedent of a conditional; it
is not asserted as Aristotle's adopted premise here.

Source: Aristotle, *Physics* VII.4, 249b24-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SubstanceNumberComparisonConditionalAndUnnamedReading
    (SubstanceIsNumber GreaterLesserNumberWithinSameSpecies
      CommonComparisonRelationUnnamed : Prop) : Prop :=
  SubstanceIsNumber →
    GreaterLesserNumberWithinSameSpecies ∧ CommonComparisonRelationUnnamed

/-- Qualitative degree is expressed by "more," whereas quantitative excess is
expressed by "greater," in Aristotle, *Physics* VII.4, 249b24-26.

Source: Aristotle, *Physics* VII.4, 249b24-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def QualityQuantityDegreeVocabularyDiffersReading
    (QualityUsesMore QuantityUsesGreater : Prop) : Prop :=
  QualityUsesMore ∧ QuantityUsesGreater

end TruthCore.Greek.Aristotle.Physics
