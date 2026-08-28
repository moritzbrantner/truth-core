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

end TruthCore.Greek.Aristotle.Physics
