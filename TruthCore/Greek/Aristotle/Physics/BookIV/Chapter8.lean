import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter7

namespace TruthCore.Greek.Aristotle.Physics

/-- Natural-direction objection in Aristotle, *Physics* IV.8, 214b12-18: simple bodies have
distinct natural locomotions—fire upward and earth downward toward the middle—so void cannot
be the cause of locomotion.

Source: Aristotle, *Physics* IV.8, 214b12-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalDirectionsShowVoidNotLocomotionCauseReading
    (SimpleBodiesHaveDistinctNaturalDirections
      VoidIsCauseOfLocomotion : Prop) : Prop :=
  SimpleBodiesHaveDistinctNaturalDirections → ¬ VoidIsCauseOfLocomotion

/-- Direction and rest puzzle in Aristotle, *Physics* IV.8, 214b18-24: if void is bodyless
place, there is no account of where an inserted body will move or how it will remain, since
it cannot move into the whole undifferentiated void.

Source: Aristotle, *Physics* IV.8, 214b18-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SeparatedVoidCannotDirectOrRestBodyReading
    (VoidIsBodylessPlace InsertedBodyHasDeterminateDirectionInVoid
      InsertedBodyHasGroundForRestInVoid : Prop) : Prop :=
  VoidIsBodylessPlace →
    ¬ InsertedBodyHasDeterminateDirectionInVoid ∧
      ¬ InsertedBodyHasGroundForRestInVoid

/-- Whole-part objection in Aristotle, *Physics* IV.8, 214b24-29: putting a body as a whole
in a separate permanent place does not put its unseparated parts in places rather than in the
whole; if no separate place exists, no such void exists either.

Source: Aristotle, *Physics* IV.8, 214b24-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def WholePartObjectionToSeparatedVoidReading
    (WholeInSeparatePermanentPlace UnseparatedPartsInSeparatePlaces
      SeparatePlaceExists SeparatedVoidExists : Prop) : Prop :=
  (WholeInSeparatePermanentPlace → ¬ UnseparatedPartsInSeparatePlaces) ∧
    (¬ SeparatePlaceExists → ¬ SeparatedVoidExists)

/-- Indifference-to-direction objection in Aristotle, *Physics* IV.8, 214b29-35: because
void as void admits no difference, nothing has a reason to move more or less toward one
region, so the very void alleged necessary for motion would instead require rest.

Source: Aristotle, *Physics* IV.8, 214b29-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def UndifferentiatedVoidWouldRequireRestReading
    (VoidAdmitsNoDirectionalDifference
      BodyHasReasonToMoveTowardOneVoidRegion
      BodyMustRestInVoid : Prop) : Prop :=
  VoidAdmitsNoDirectionalDifference →
    ¬ BodyHasReasonToMoveTowardOneVoidRegion ∧ BodyMustRestInVoid

/-- Directional facts in Aristotle, *Physics* IV.8, 215a6-13: infinite void has no up, down,
or middle, and void as privation has no directional differentiation.

Source: Aristotle, *Physics* IV.8, 215a6-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VoidHasNoDirectionalDifferentiationReading
    (InfiniteVoidHasUpDownOrMiddle VoidHasDirectionalDifferentiation : Prop) : Prop :=
  ¬ InfiniteVoidHasUpDownOrMiddle ∧ ¬ VoidHasDirectionalDifferentiation

/-- Bridge from directional indifference in Aristotle, *Physics* IV.8, 215a6-13: because
natural locomotion is differentiated, a void with no up, down, middle, or directional
difference cannot host natural motion.

Source: Aristotle, *Physics* IV.8, 215a1-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VoidLacksNaturalMotionReading
    (InfiniteVoidHasUpDownOrMiddle VoidHasDirectionalDifferentiation
      NaturalMotionInVoid : Prop) : Prop :=
  (¬ InfiniteVoidHasUpDownOrMiddle ∧ ¬ VoidHasDirectionalDifferentiation) →
    ¬ NaturalMotionInVoid

/-- Dependence of non-natural motion in Aristotle, *Physics* IV.8, 215a1-6: all motion is
natural or compulsory, and compulsory motion contrary to nature is posterior to natural
motion; if natural motion is absent, no motion remains.

Source: Aristotle, *Physics* IV.8, 215a1-6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoNaturalMotionEntailsNoMotionReading
    (NaturalMotionInVoid AnyMotionInVoid : Prop) : Prop :=
  ¬ NaturalMotionInVoid → ¬ AnyMotionInVoid

/-- Conclusion of Aristotle's directional reductio in *Physics* IV.8, 214b29-215a13: no
motion is possible in a separated, undifferentiated void.

Source: Aristotle, *Physics* IV.8, 214b29-215a13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoMotionInSeparatedVoidReading (AnyMotionInVoid : Prop) : Prop :=
  ¬ AnyMotionInVoid

/-- Projectile objection in Aristotle, *Physics* IV.8, 215a13-19: thrown bodies continue
after loss of contact through mutual replacement or a pushed medium; neither mechanism exists
in void, leaving no account of continued projectile motion there.

Source: Aristotle, *Physics* IV.8, 215a13-19 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ProjectileContinuationMechanismsAbsentInVoidReading
    (ProjectilesContinueAfterContact MutualReplacementContinuesProjectile
      PushedMediumContinuesProjectile ContinuationMechanismExistsInVoid : Prop) : Prop :=
  ProjectilesContinueAfterContact ∧
    (MutualReplacementContinuesProjectile ∨ PushedMediumContinuesProjectile) ∧
      ¬ ContinuationMechanismExistsInVoid

/-- No-stopping-point reductio in Aristotle, *Physics* IV.8, 215a19-22: void supplies no
reason for a moving body to stop here rather than there, so absent a stronger impediment it
must either remain at rest or continue without limit.

Source: Aristotle, *Physics* IV.8, 215a19-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VoidProvidesNoStoppingPointReading
    (VoidProvidesDeterminateStoppingReason StrongerImpedimentIntervenes
      BodyRemainsAtRest BodyMovesWithoutLimit : Prop) : Prop :=
  ¬ VoidProvidesDeterminateStoppingReason ∧ ¬ StrongerImpedimentIntervenes →
    BodyRemainsAtRest ∨ BodyMovesWithoutLimit

/-- Equal-yield objection in Aristotle, *Physics* IV.8, 215a22-24: if motion toward void is
explained by its yielding, void yields alike everywhere and a body should move in every
direction.

Source: Aristotle, *Physics* IV.8, 215a22-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VoidEqualYieldImpliesAllDirectionsReading
    (VoidYieldsEquallyEverywhere BodyWouldMoveInEveryDirection : Prop) : Prop :=
  VoidYieldsEquallyEverywhere → BodyWouldMoveInEveryDirection

end TruthCore.Greek.Aristotle.Physics
