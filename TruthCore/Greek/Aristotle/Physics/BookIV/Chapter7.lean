import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter6

namespace TruthCore.Greek.Aristotle.Physics

/-- Ordinary derivation of void in Aristotle, *Physics* IV.7, 213b30-214a5: void is thought
to be place containing nothing because all beings are taken as bodies and all bodies as
tangible, with tangibility reduced to weight or lightness; hence a region without heavy or
light body is inferred to be void.

Source: Aristotle, *Physics* IV.7, 213b30-214a5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def OrdinaryVoidDerivationReading
    (AllBeingsTakenAsBodies AllBodiesTakenAsTangible
      TangibleBodyHasWeightOrLightness
      RegionWithoutHeavyOrLightBodyInferredVoid : Prop) : Prop :=
  AllBeingsTakenAsBodies ∧ AllBodiesTakenAsTangible ∧
    TangibleBodyHasWeightOrLightness → RegionWithoutHeavyOrLightBodyInferredVoid

/-- Two uses of "void" in Aristotle, *Physics* IV.7, 214a5-13: it can mean what is not full
of body perceptible to touch, tested by capacity to receive a tangible body despite possible
colour or sound, or what contains no particular corporeal substance.

Source: Aristotle, *Physics* IV.7, 214a5-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TwoMeaningsOfVoidReading
    (VoidAsNotFullOfTangibleBody VoidDependsOnCapacityForTangibleBody
      ColorOrSoundAloneDoesNotSettleVoid
      VoidAsLackingParticularCorporealSubstance : Prop) : Prop :=
  VoidAsNotFullOfTangibleBody ∧ VoidDependsOnCapacityForTangibleBody ∧
    ColorOrSoundAloneDoesNotSettleVoid ∧
      VoidAsLackingParticularCorporealSubstance

/-- Rejection of void as matter in Aristotle, *Physics* IV.7, 214a13-16: those who identify
void and place with bodily matter speak incorrectly because matter is inseparable from things,
whereas the void under inquiry is supposed separable.

Source: Aristotle, *Physics* IV.7, 214a13-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VoidIsNotBodilyMatterReading
    (MatterSeparableFromThings VoidUnderInquiryIsSeparable
      VoidIsBodilyMatter : Prop) : Prop :=
  ¬ MatterSeparableFromThings ∧ VoidUnderInquiryIsSeparable →
    ¬ VoidIsBodilyMatter

/-- Consequence of Aristotle's account of place in *Physics* IV.7, 214a16-20: if void would
be place deprived of body and is intended as an interval distinct from body, then void in
that sense exists neither separated nor unseparated.

Source: Aristotle, *Physics* IV.7, 214a16-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BodilessIntervalVoidDoesNotExistReading
    (SeparatedBodilessIntervalVoidExists
      UnseparatedBodilessIntervalVoidExists : Prop) : Prop :=
  ¬ SeparatedBodilessIntervalVoidExists ∧
    ¬ UnseparatedBodilessIntervalVoidExists

/-- Why void appears plausible in Aristotle, *Physics* IV.7, 214a20-26: the same replacement
and locomotion considerations that make place seem distinct from occupants lead proponents
to treat void as the place in which motion occurs and thus as a cause of motion.

Source: Aristotle, *Physics* IV.7, 214a20-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionMakesVoidAppearPlausibleReading
    (PlaceAppearsDistinctFromOccupants
      VoidTreatedAsWhereMotionOccurs VoidTreatedAsCauseOfMotion : Prop) : Prop :=
  PlaceAppearsDistinctFromOccupants ∧
    VoidTreatedAsWhereMotionOccurs ∧ VoidTreatedAsCauseOfMotion

/-- Aristotle's first counterexample in *Physics* IV.7, 214a26-28: a full body can undergo
qualitative change.

Source: Aristotle, *Physics* IV.7, 214a26-28 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FullBodyCanQualitativelyChangeReading
    (FullBodyCanQualitativelyChange : Prop) : Prop :=
  FullBodyCanQualitativelyChange

/-- Inferential bridge in Aristotle, *Physics* IV.7, 214a26-28: if a full body can undergo
qualitative change, motion does not generally require void.

Source: Aristotle, *Physics* IV.7, 214a26-28 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FullChangeShowsVoidUnnecessaryForMotionReading
    (FullBodyCanQualitativelyChange VoidNecessaryForMotion : Prop) : Prop :=
  FullBodyCanQualitativelyChange → ¬ VoidNecessaryForMotion

/-- Conclusion of Aristotle's general counterexample in *Physics* IV.7, 214a26-28: void is
not necessary for motion in general. Local motion receives a distinct argument immediately
afterward.

Source: Aristotle, *Physics* IV.7, 214a26-28 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VoidNotNecessaryForMotionReading (VoidNecessaryForMotion : Prop) : Prop :=
  ¬ VoidNecessaryForMotion

/-- Local motion without void in Aristotle, *Physics* IV.7, 214a28-31: bodies can yield and
replace one another simultaneously without a separable interval, as rotations in continuous
media and liquids illustrate.

Source: Aristotle, *Physics* IV.7, 214a28-31 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MutualReplacementAllowsMotionWithoutVoidReading
    (BodiesMutuallyYieldAndReplace
      ContinuousAndLiquidRotationsExemplifyReplacement
      SeparableIntervalRequiredForLocalMotion : Prop) : Prop :=
  BodiesMutuallyYieldAndReplace ∧
    ContinuousAndLiquidRotationsExemplifyReplacement ∧
      ¬ SeparableIntervalRequiredForLocalMotion

/-- Replies to compression, growth, and ash in Aristotle, *Physics* IV.7, 214a31-214b11:
compression may expel what is within rather than enter void, and growth may occur through
alteration; the growth and ash cases raise a general dilemma without proving void, and if
growth everywhere required void every body would have to be void throughout.

Source: Aristotle, *Physics* IV.7, 214a31-214b11 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CompressionGrowthAshDoNotEstablishVoidReading
    (CompressionMayExpelContainedBody GrowthMayOccurByAlteration
      GrowthAndAshRaiseGeneralProblem GrowthAndAshProveVoid
      UniversalVoidGrowthWouldMakeEveryBodyVoid : Prop) : Prop :=
  CompressionMayExpelContainedBody ∧ GrowthMayOccurByAlteration ∧
    GrowthAndAshRaiseGeneralProblem ∧ ¬ GrowthAndAshProveVoid ∧
      UniversalVoidGrowthWouldMakeEveryBodyVoid

end TruthCore.Greek.Aristotle.Physics
