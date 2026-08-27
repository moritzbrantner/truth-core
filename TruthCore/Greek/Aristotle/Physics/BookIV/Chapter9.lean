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

end TruthCore.Greek.Aristotle.Physics
