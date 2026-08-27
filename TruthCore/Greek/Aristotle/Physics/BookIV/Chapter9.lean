import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter8

namespace TruthCore.Greek.Aristotle.Physics

/-- Reported rarity-density argument in Aristotle, *Physics* IV.9, 216b22-30: proponents
take rare and dense bodies, and the possibility of compression and expansion, to show that
void exists. This records their dialectical case rather than Aristotle's own conclusion.

Source: Aristotle, *Physics* IV.9, 216b22-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RarityDensityArgumentForVoidReading
    (RareAndDenseExist CompressionAndExpansionOccur VoidExists : Prop) : Prop :=
  RareAndDenseExist ∧ CompressionAndExpansionOccur → VoidExists

/-- The reported no-compression dilemma in Aristotle, *Physics* IV.9, 216b24-30: without
compression and expansion, motion would cease, the whole would bulge, equal reverse changes
of air and water would be required, or void would have to exist.

Source: Aristotle, *Physics* IV.9, 216b24-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoCompressionDilemmaReading
    (CompressionAndExpansionOccur MotionCeases WholeBulges
      EqualReverseAirWaterChangeRequired VoidRequired : Prop) : Prop :=
  ¬ CompressionAndExpansionOccur →
    MotionCeases ∨ WholeBulges ∨
      EqualReverseAirWaterChangeRequired ∨ VoidRequired

/-- Rejection of one meaning of rarity in Aristotle, *Physics* IV.9, 216b30-33: if “rare”
means containing many separated voids, then rarity in that sense is impossible because a
separated void or independently extended place is impossible.

Source: Aristotle, *Physics* IV.9, 216b30-33 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RareAsManySeparatedVoidsImpossibleReading
    (RareContainsManySeparatedVoids RareInSeparatedVoidSenseExists : Prop) : Prop :=
  RareContainsManySeparatedVoids → ¬ RareInSeparatedVoidSenseExists

/-- Restricted consequence of void internal to the rare in Aristotle, *Physics* IV.9,
216b33-217a4: this less impossible hypothesis would explain only upward motion and would act
as an upward carrier, not as a void region in which motion occurs.

Source: Aristotle, *Physics* IV.9, 216b33-217a4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InternalVoidWouldOnlyCarryUpwardReading
    (InternalVoidExists VoidCausesAllMotion VoidCausesOnlyUpwardMotion
      VoidIsMediumOfMotion VoidCarriesContiguousBodyUpward : Prop) : Prop :=
  InternalVoidExists →
    ¬ VoidCausesAllMotion ∧ VoidCausesOnlyUpwardMotion ∧
      ¬ VoidIsMediumOfMotion ∧ VoidCarriesContiguousBodyUpward

/-- Place consequence in Aristotle's moving-void objection, *Physics* IV.9, 217a3-5: if
void itself had locomotion, there would have to be a place into which that void moves.

Source: Aristotle, *Physics* IV.9, 217a3-5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VoidMotionEntailsPlaceForVoidReading
    (VoidMoves PlaceForVoidExists : Prop) : Prop :=
  VoidMoves → PlaceForVoidExists

/-- Aristotle's “void of a void” rejection in *Physics* IV.9, 217a3-5: no place exists
into which void could move, since that destination would itself be void of void.

Source: Aristotle, *Physics* IV.9, 217a3-5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PlaceForMovingVoidImpossibleReading (PlaceForVoidExists : Prop) : Prop :=
  ¬ PlaceForVoidExists

/-- Conclusion of the place reductio in Aristotle, *Physics* IV.9, 217a3-10: void itself
cannot move.

Source: Aristotle, *Physics* IV.9, 217a3-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VoidCannotMoveReading (VoidMoves : Prop) : Prop :=
  ¬ VoidMoves

/-- Downward-motion objection in Aristotle, *Physics* IV.9, 217a5-6: treating internal void
as what carries rare things upward gives no corresponding account of heavy bodies moving
downward.

Source: Aristotle, *Physics* IV.9, 217a5-6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InternalVoidFailsToExplainHeavyDownwardMotionReading
    (InternalVoidExplainsHeavyDownwardMotion : Prop) : Prop :=
  ¬ InternalVoidExplainsHeavyDownwardMotion

/-- Speed reductio for internal void in Aristotle, *Physics* IV.9, 217a6-10: if increasing
rarity and void made upward motion faster, complete void should move fastest; yet its speed
would be incomparable and the preceding argument makes void incapable of motion.

Source: Aristotle, *Physics* IV.9, 217a6-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CompleteVoidMotionSpeedReductioReading
    (MoreInternalVoidMakesUpwardMotionFaster
      CompleteVoidWouldMoveFastest VoidSpeedsAreComparable VoidMoves : Prop) : Prop :=
  MoreInternalVoidMakesUpwardMotionFaster →
    CompleteVoidWouldMoveFastest ∧ ¬ VoidSpeedsAreComparable ∧ ¬ VoidMoves

/-- Aristotle's concession in *Physics* IV.9, 217a10-20: although void is denied, the
pressure behind the proponents' dilemma is genuine—without rarefaction and condensation,
straight motion and unequal-volume transformations leave bulging, compensating change, or
immobility as consequences.

Source: Aristotle, *Physics* IV.9, 217a10-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoCompressionProblemIsGenuineReading
    (NoCompressionProblemIsGenuine
      NoCompressionEntailsBulgingCompensationOrImmobility : Prop) : Prop :=
  NoCompressionProblemIsGenuine ∧
    NoCompressionEntailsBulgingCompensationOrImmobility

/-- Aristotle's matter principle in *Physics* IV.9, 217a20-27: one matter underlies hot,
cold, and other natural contraries; actual states arise from what is potential, and matter,
though inseparable from the contraries, differs from them in being and may be numerically one
for colour, heat, and cold.

Source: Aristotle, *Physics* IV.9, 217a20-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def OneMatterUnderliesNaturalContrariesReading
    (OneMatterUnderliesNaturalContraries
      ActualStateArisesFromPotentialState
      MatterInseparableButDifferentInBeingFromContraries : Prop) : Prop :=
  OneMatterUnderliesNaturalContraries ∧ ActualStateArisesFromPotentialState ∧
    MatterInseparableButDifferentInBeingFromContraries

/-- Extension of the matter principle in Aristotle, *Physics* IV.9, 217a27-33: the same
matter is potentially the matter of both a large and a small body.

Source: Aristotle, *Physics* IV.9, 217a27-33 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SameMatterPotentiallyLargeAndSmallReading
    (SameMatterIsPotentiallyLargeAndSmall : Prop) : Prop :=
  SameMatterIsPotentiallyLargeAndSmall

/-- Inferential bridge in Aristotle's account, *Physics* IV.9, 217a27-217b10: because the
same matter is potentially both large and small, its contraction or expansion does not
require the addition of void.

Source: Aristotle, *Physics* IV.9, 217a27-217b10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SameMatterPotentialityExcludesAddedVoidReading
    (SameMatterIsPotentiallyLargeAndSmall
      CompressionOrExpansionRequiresAddedVoid : Prop) : Prop :=
  SameMatterIsPotentiallyLargeAndSmall →
    ¬ CompressionOrExpansionRequiresAddedVoid

/-- Conclusion of Aristotle's positive response in *Physics* IV.9, 217a20-217b10:
compression and expansion do not require added void.

Source: Aristotle, *Physics* IV.9, 217a20-217b10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CompressionAndExpansionDoNotRequireVoidReading
    (CompressionOrExpansionRequiresAddedVoid : Prop) : Prop :=
  ¬ CompressionOrExpansionRequiresAddedVoid

/-- Water-air transformation in Aristotle, *Physics* IV.9, 217a27-33: the same matter
becomes air from water and water from air without acquiring an addition, actualizing what it
was potentially while changing between larger and smaller volume.

Source: Aristotle, *Physics* IV.9, 217a27-33 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def WaterAirTransformationUsesSameMatterWithoutAdditionReading
    (WaterAndAirHaveSameMatter MatterAcquiresAdditionInTransformation
      PotentialStateBecomesActual VolumeChangesLargeOrSmall : Prop) : Prop :=
  WaterAndAirHaveSameMatter ∧ ¬ MatterAcquiresAdditionInTransformation ∧
    PotentialStateBecomesActual ∧ VolumeChangesLargeOrSmall

/-- Degree analogies in Aristotle, *Physics* IV.9, 217a33-217b8: becoming hotter does not
insert a previously non-hot part, just as changing a circle's curvature introduces no
straight gap and every portion of flame remains hot and white.

Source: Aristotle, *Physics* IV.9, 217a33-217b8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContinuousDegreeChangeNeedsNoInsertedPartReading
    (GreaterHeatNeedsNoInsertedNonHotPart
      CurvatureChangeNeedsNoStraightGap
      EveryFlamePartRemainsHotAndWhite : Prop) : Prop :=
  GreaterHeatNeedsNoInsertedNonHotPart ∧ CurvatureChangeNeedsNoStraightGap ∧
    EveryFlamePartRemainsHotAndWhite

/-- Dense-rare unity in Aristotle, *Physics* IV.9, 217b8-12: the same thing is dense and
rare and the two states have one matter; the dense is heavy and the rare light.

Source: Aristotle, *Physics* IV.9, 217b8-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DenseAndRareHaveOneMatterReading
    (DenseAndRareAreStatesOfSameThing DenseAndRareHaveOneMatter
      DenseIsHeavy RareIsLight : Prop) : Prop :=
  DenseAndRareAreStatesOfSameThing ∧ DenseAndRareHaveOneMatter ∧
    DenseIsHeavy ∧ RareIsLight

/-- Two dense-rare associations in Aristotle, *Physics* IV.9, 217b12-20: heavy and hard
appear dense while light and soft appear rare, but lead and iron show that heaviness and
hardness do not coincide; contraction and expansion remain changes of the same matter.

Source: Aristotle, *Physics* IV.9, 217b12-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DenseRareAssociationsRequireDistinctionReading
    (HeavyAndHardAppearDense LightAndSoftAppearRare
      HeavyAndHardAlwaysCoincide SameMatterContractsAndExpands : Prop) : Prop :=
  HeavyAndHardAppearDense ∧ LightAndSoftAppearRare ∧
    ¬ HeavyAndHardAlwaysCoincide ∧ SameMatterContractsAndExpands

/-- Negative conclusion in Aristotle, *Physics* IV.9, 217b20-23: void exists neither
separately, nor without qualification, nor in the rare, nor potentially.

Source: Aristotle, *Physics* IV.9, 217b20-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VoidAbsentSeparatelyInRareAndPotentiallyReading
    (SeparatedVoidExists UnqualifiedVoidExists VoidExistsInRare
      VoidExistsPotentially : Prop) : Prop :=
  ¬ SeparatedVoidExists ∧ ¬ UnqualifiedVoidExists ∧
    ¬ VoidExistsInRare ∧ ¬ VoidExistsPotentially

/-- Aristotle's qualified closing usage in *Physics* IV.9, 217b22-28: only if one insists
on calling the cause of locomotion “void” could the matter of heavy and light bear that name;
dense and rare produce locomotion under that contrariety, while hard and soft concern
passivity, impassivity, and qualitative change instead.

Source: Aristotle, *Physics* IV.9, 217b22-28 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def QualifiedVoidAsMatterOfHeavyAndLightReading
    (VoidMeansCauseOfLocomotion MatterOfHeavyAndLightMayBeCalledVoid
      DenseRareContrarietyProducesLocomotion
      HardSoftContrarietyProducesQualitativeChange : Prop) : Prop :=
  VoidMeansCauseOfLocomotion →
    MatterOfHeavyAndLightMayBeCalledVoid ∧
      DenseRareContrarietyProducesLocomotion ∧
        HardSoftContrarietyProducesQualitativeChange

end TruthCore.Greek.Aristotle.Physics
