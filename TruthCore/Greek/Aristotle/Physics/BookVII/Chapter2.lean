import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter1

namespace TruthCore.Greek.Aristotle.Physics

/-- The first mover meant as the source from which motion begins, rather than the
final cause, is together with what it moves: nothing lies between them, in
Aristotle, *Physics* VII.2, 243a3-5.

Source: Aristotle, *Physics* VII.2, 243a3-5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PrimaryMoverAsSourceIsTogetherWithMovedReading
    (MoverIsSourceRatherThanFinalCause NothingBetweenMoverAndMoved : Prop) : Prop :=
  MoverIsSourceRatherThanFinalCause ∧ NothingBetweenMoverAndMoved

/-- Local, qualitative, and quantitative motion correspond respectively to a
locomoting mover, an altering mover, and a mover causing growth or diminution, in
Aristotle, *Physics* VII.2, 243a5-10.

Source: Aristotle, *Physics* VII.2, 243a5-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ThreeMotionsHaveThreeMoverKindsReading
    (LocomotionHasLocomotingMover AlterationHasAlteringMover
      QuantityChangeHasGrowingOrDiminishingMover : Prop) : Prop :=
  LocomotionHasLocomotingMover ∧ AlterationHasAlteringMover ∧
    QuantityChangeHasGrowingOrDiminishingMover

/-- Locomotion is primary among the three motions considered in Aristotle,
*Physics* VII.2, 243a10-11.

Source: Aristotle, *Physics* VII.2, 243a10-11 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def LocomotionPrimaryAmongThreeMotionsReading
    (LocomotionIsPrimary : Prop) : Prop :=
  LocomotionIsPrimary

/-- Everything undergoing locomotion is moved either by itself or by something
else, in Aristotle, *Physics* VII.2, 243a11-15.

Source: Aristotle, *Physics* VII.2, 243a11-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def LocomotionSelfMovedOrMovedByOtherReading
    (SelfMoved MovedByOther : Prop) : Prop :=
  SelfMoved ∨ MovedByOther

/-- In self-moved things the first mover is internal, so mover and moved are
together with nothing between them, in Aristotle, *Physics* VII.2, 243a11-15.

Source: Aristotle, *Physics* VII.2, 243a11-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SelfMovedLocomotionHasNoIntermediateReading
    (SelfMoved NothingBetweenMoverAndMoved : Prop) : Prop :=
  SelfMoved → NothingBetweenMoverAndMoved

/-- Locomotion caused by another falls under pulling, pushing, carrying, or
twirling, in Aristotle, *Physics* VII.2, 243a15-18.

Source: Aristotle, *Physics* VII.2, 243a15-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ExternalLocomotionHasFourModesReading
    (MovedByOther Pulling Pushing Carrying Twirling : Prop) : Prop :=
  MovedByOther → (Pulling ∧ Pushing ∧ Carrying ∧ Twirling)

/-- Pushing-on, pushing-off, throwing, pushing apart, pushing together, and the
relevant bodily intake and expulsion motions reduce to varieties of pushing or
pulling, in Aristotle, *Physics* VII.2, 243a18-243b13.

Source: Aristotle, *Physics* VII.2, 243a18-243b13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DerivedLocomotionsReduceToPushingOrPullingReading
    (DerivedLocomotionsReduceToPushingOrPulling : Prop) : Prop :=
  DerivedLocomotionsReduceToPushingOrPulling

/-- Carrying proceeds through pulling, pushing, or twirling, while twirling itself
combines pulling one part with pushing another, in Aristotle, *Physics* VII.2,
243b13-244a4.

Source: Aristotle, *Physics* VII.2, 243b13-244a4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CarryingAndTwirlingReduceToPullPushReading
    (CarryingUsesPullPushOrTwirl TwirlingCombinesPullAndPush : Prop) : Prop :=
  CarryingUsesPullPushOrTwirl ∧ TwirlingCombinesPullAndPush

/-- Aristotle's transition from the four exhaustive external modes to contact:
their reductions and the definitions of pushing and pulling exclude an
intermediate between local mover and moved, in *Physics* VII.2, 244a4-244b2.

Source: Aristotle, *Physics* VII.2, 244a4-244b2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ExternalLocomotionModesEntailNoIntermediateReading
    (Pulling Pushing Carrying Twirling NothingBetweenMoverAndMoved : Prop) : Prop :=
  (Pulling ∧ Pushing ∧ Carrying ∧ Twirling) → NothingBetweenMoverAndMoved

/-- No intermediate lies between a thing undergoing locomotion and its mover, in
Aristotle, *Physics* VII.2, 243a11-244b2.

Source: Aristotle, *Physics* VII.2, 243a11-244b2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoIntermediateBetweenLocalMoverAndMovedReading
    (NothingBetweenMoverAndMoved : Prop) : Prop :=
  NothingBetweenMoverAndMoved

/-- Alteration occurs through the passive sensible qualities, illustrated by
heating, sweetening, condensation, drying, and whitening in animate and inanimate
bodies, in Aristotle, *Physics* VII.2, 244b2-13.

Source: Aristotle, *Physics* VII.2, 244b2-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AlterationInPassiveSensibleQualitiesReading
    (AlterationConcernsPassiveSensibleQualities
      AnimateAndInanimateBodiesAlterInTheseQualities : Prop) : Prop :=
  AlterationConcernsPassiveSensibleQualities ∧
    AnimateAndInanimateBodiesAlterInTheseQualities

/-- Actual sensation is a motion through the body in which the sense is affected;
animate things share inanimate alterations but also undergo sensory alterations
that inanimate things do not, in Aristotle, *Physics* VII.2, 244b13-245a1.

Source: Aristotle, *Physics* VII.2, 244b13-245a1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SensationIsBodilyMotionAndAnimateAlterationReading
    (ActualSensationIsMotionThroughBody SenseIsAffected
      AnimateHasSensoryAlterationsAbsentFromInanimate : Prop) : Prop :=
  ActualSensationIsMotionThroughBody ∧ SenseIsAffected ∧
    AnimateHasSensoryAlterationsAbsentFromInanimate

/-- Inanimate alteration may escape notice, and animate alteration may also escape
notice when it does not occur in the senses, in Aristotle, *Physics* VII.2,
244b28-245a3.

Source: Aristotle, *Physics* VII.2, 244b28-245a3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AlterationMayEscapeNoticeOutsideSensationReading
    (InanimateAlterationMayEscapeNotice
      NonsensoryAnimateAlterationMayEscapeNotice : Prop) : Prop :=
  InanimateAlterationMayEscapeNotice ∧
    NonsensoryAnimateAlterationMayEscapeNotice

/-- In sensible alteration the last alterer and first altered are adjacent through
continuous media: air joins source and body, light joins color and sight, air is
primary for hearing and smell, and flavor is together with taste, in Aristotle,
*Physics* VII.2, 245a3-11.

Source: Aristotle, *Physics* VII.2, 245a3-11 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SensibleAlterationExtremesAdjacentThroughMediaReading
    (LastAltererAndFirstAlteredAdjacent : Prop) : Prop :=
  LastAltererAndFirstAlteredAdjacent

/-- Adjacency of the last alterer and first altered excludes an intermediate
between them in Aristotle's alteration argument in *Physics* VII.2, 245a3-11.

Source: Aristotle, *Physics* VII.2, 245a3-11 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AlterationAdjacencyEntailsNoIntermediateReading
    (LastAltererAndFirstAlteredAdjacent NothingBetweenAltererAndAltered : Prop) : Prop :=
  LastAltererAndFirstAlteredAdjacent → NothingBetweenAltererAndAltered

/-- No intermediate lies between what undergoes alteration and what alters it, in
Aristotle, *Physics* VII.2, 244b2-245a11.

Source: Aristotle, *Physics* VII.2, 244b2-245a11 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoIntermediateBetweenAltererAndAlteredReading
    (NothingBetweenAltererAndAltered : Prop) : Prop :=
  NothingBetweenAltererAndAltered

/-- Growth occurs when the primary grower attaches so that the whole becomes one,
and diminution when something belonging to the diminishing thing detaches, in
Aristotle, *Physics* VII.2, 245a11-16.

Source: Aristotle, *Physics* VII.2, 245a11-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GrowthAttachesAndDiminutionDetachesReading
    (GrowerAttachesIntoOneWhole DiminutionThroughDetachment : Prop) : Prop :=
  GrowerAttachesIntoOneWhole ∧ DiminutionThroughDetachment

/-- The grower or diminisher is continuous with what grows or diminishes, so no
intermediate lies between them, in Aristotle, *Physics* VII.2, 245a11-16.

Source: Aristotle, *Physics* VII.2, 245a11-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoIntermediateInGrowthOrDiminutionReading
    (NothingBetweenQuantitativeMoverAndMoved : Prop) : Prop :=
  NothingBetweenQuantitativeMoverAndMoved

/-- Across locomotion, alteration, and quantitative change, nothing lies between
the moved subject and the primary mover that is last with respect to it, in
Aristotle, *Physics* VII.2, 245a16-245b2.

Source: Aristotle, *Physics* VII.2, 245a16-245b2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoIntermediateAcrossThreeMotionKindsReading
    (NothingBetweenLocalMoverAndMoved NothingBetweenAltererAndAltered
      NothingBetweenQuantitativeMoverAndMoved : Prop) : Prop :=
  NothingBetweenLocalMoverAndMoved ∧ NothingBetweenAltererAndAltered ∧
    NothingBetweenQuantitativeMoverAndMoved

end TruthCore.Greek.Aristotle.Physics
