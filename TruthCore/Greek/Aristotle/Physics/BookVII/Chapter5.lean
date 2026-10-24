import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter4

namespace TruthCore.Greek.Aristotle.Physics

/-- A mover always moves something, does so in time, and moves it through some
distance; while it is moving, some distance has been traversed in some time, in
Aristotle, *Physics* VII.5, 249b27-30.

Source: Aristotle, *Physics* VII.5, 249b27-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MoverMotionHasSubjectTimeDistanceReading
    (MoverActsOnSomething MotionOccursInTime MotionTraversesSomeDistance
      ActiveMovingHasCompletedSomeMotion : Prop) : Prop :=
  MoverActsOnSomething ∧ MotionOccursInTime ∧
    MotionTraversesSomeDistance ∧ ActiveMovingHasCompletedSomeMotion

/-- If a force moves a load through a distance in a time, the same force moves
half the load through twice the distance in the same time, in Aristotle,
*Physics* VII.5, 249b30-250a3.

This records Aristotle's stated proportional rule in its own setup; the
threshold qualifications later in the chapter are not erased.

Source: Aristotle, *Physics* VII.5, 249b30-250a3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SameForceHalfLoadDoubleDistanceSameTimeReading
    (BaselineForceLoadDistanceTime
      SameForceHalfLoadDoubleDistanceSameTime : Prop) : Prop :=
  BaselineForceLoadDistanceTime →
    SameForceHalfLoadDoubleDistanceSameTime

/-- If a force moves a load through a distance in a time, the same force moves
half the load through that distance in half the time, in Aristotle, *Physics*
VII.5, 249b30-250a3.

Source: Aristotle, *Physics* VII.5, 249b30-250a3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SameForceHalfLoadSameDistanceHalfTimeReading
    (BaselineForceLoadDistanceTime
      SameForceHalfLoadSameDistanceHalfTime : Prop) : Prop :=
  BaselineForceLoadDistanceTime →
    SameForceHalfLoadSameDistanceHalfTime

/-- Halving both force and load preserves their force-to-load ratio, in
Aristotle's proportional setup in *Physics* VII.5, 250a3-8.

Source: Aristotle, *Physics* VII.5, 250a3-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def HalfForceHalfLoadPreserveForceLoadRatioReading
    (HalfForceAndHalfLoad ForceLoadRatioPreserved : Prop) : Prop :=
  HalfForceAndHalfLoad → ForceLoadRatioPreserved

/-- Within Aristotle's proportional setup, preserving the force-to-load ratio
preserves the traversed distance and elapsed time, in *Physics* VII.5,
250a3-8.

Source: Aristotle, *Physics* VII.5, 250a3-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PreservedForceLoadRatioEntailsSameDistanceTimeReading
    (ForceLoadRatioPreserved SameDistanceAndTime : Prop) : Prop :=
  ForceLoadRatioPreserved → SameDistanceAndTime

/-- Halving both force and load therefore preserves the distance traversed in
the same time, within Aristotle's proportional setup in *Physics* VII.5,
250a3-8.

Source: Aristotle, *Physics* VII.5, 250a3-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def HalfForceHalfLoadSameMotionReading
    (HalfForceAndHalfLoad SameDistanceAndTime : Prop) : Prop :=
  HalfForceAndHalfLoad → SameDistanceAndTime

/-- Inverse proportional scaling is not necessary: a fixed force need not move
twice the load half the distance in the same time, and half a force need not
move the original load a proportional distance or in a proportional time, in
Aristotle, *Physics* VII.5, 250a8-15.

Source: Aristotle, *Physics* VII.5, 250a8-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InverseProportionalScalingNotNecessaryReading
    (DoubleLoadHalfDistanceNecessary
      HalfForceFixedLoadProportionalMotionNecessary : Prop) : Prop :=
  ¬ DoubleLoadHalfDistanceNecessary ∧
    ¬ HalfForceFixedLoadProportionalMotionNecessary

/-- A fractional force may produce no motion at all, so the motion produced by a
whole force does not guarantee any proportionate effect from every fraction of
that force, in Aristotle, *Physics* VII.5, 250a15-18.

Source: Aristotle, *Physics* VII.5, 250a15-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PartForceMayProduceNoMotionReading
    (WholeForceProducesMotion PartForceProducesSomeMotion : Prop) : Prop :=
  WholeForceProducesMotion ∧ ¬ PartForceProducesSomeMotion

/-- If the total hauling force and the ship's traversed distance could both be
divided without a threshold into shares matching the number of haulers, one
person would move the ship, Aristotle's reductio in *Physics* VII.5,
250a18-20.

Source: Aristotle, *Physics* VII.5, 250a18-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def UniversalForceDivisionEntailsSingleHaulerMovesShipReading
    (ForceAndDistanceDivideWithoutThreshold SingleHaulerMovesShip : Prop) : Prop :=
  ForceAndDistanceDivideWithoutThreshold → SingleHaulerMovesShip

/-- If every part of a quantity of millet made a sound, every such part would
have to move air in the sound-producing way, in the argument Aristotle rejects
in *Physics* VII.5, 250a20-23.

Source: Aristotle, *Physics* VII.5, 250a20-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EveryMilletPartSoundingEntailsEveryPartMovesAirReading
    (EveryMilletPartMakesSound EveryMilletPartMovesAir : Prop) : Prop :=
  EveryMilletPartMakesSound → EveryMilletPartMovesAir

/-- It may fail that every millet part moves the air moved by the falling whole,
in Aristotle, *Physics* VII.5, 250a20-23.

This is the threshold possibility Aristotle uses against Zeno; it does not say
that no isolated grain can ever move air.

Source: Aristotle, *Physics* VII.5, 250a20-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NotEveryMilletPartMovesAirReading
    (EveryMilletPartMovesAir : Prop) : Prop :=
  ¬ EveryMilletPartMovesAir

/-- Zeno's conclusion that every part of the millet makes a sound is false under
Aristotle's threshold analysis, in *Physics* VII.5, 250a20-23.

Source: Aristotle, *Physics* VII.5, 250a20-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NotEveryMilletPartMakesSoundReading
    (EveryMilletPartMakesSound : Prop) : Prop :=
  ¬ EveryMilletPartMakesSound

/-- A part within the whole millet measure exists there only potentially, which
blocks transferring to it the effect it might have if separately actual, in
Aristotle, *Physics* VII.5, 250a23-25.

Source: Aristotle, *Physics* VII.5, 250a23-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PartExistsOnlyPotentiallyWithinWholeReading
    (PartExistsPotentiallyInWhole
      SeparateActualEffectNeedNotOccurInWhole : Prop) : Prop :=
  PartExistsPotentiallyInWhole ∧ SeparateActualEffectNeedNotOccurInWhole

/-- When two movers separately move their respective loads through a given
distance in a given time, the combined forces move the combined loads through
the same distance in the same time, in Aristotle, *Physics* VII.5,
250a25-28.

Source: Aristotle, *Physics* VII.5, 250a25-28 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CombinedMoversMoveCombinedLoadsSameDistanceTimeReading
    (SeparateMoversMoveRespectiveLoadsSameDistanceTime
      CombinedMoversMoveCombinedLoadsSameDistanceTime : Prop) : Prop :=
  SeparateMoversMoveRespectiveLoadsSameDistanceTime →
    CombinedMoversMoveCombinedLoadsSameDistanceTime

/-- Alteration and growth admit the same kind of agent, patient, amount, and
time analysis Aristotle has just applied to locomotion, in *Physics* VII.5,
250a28-250b2.

Source: Aristotle, *Physics* VII.5, 250a28-250b2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AlterationGrowthAdmitAgentPatientAmountTimeAnalysisReading
    (AlterationAdmitsAnalysis GrowthAdmitsAnalysis : Prop) : Prop :=
  AlterationAdmitsAnalysis ∧ GrowthAdmitsAnalysis

/-- Growth has a determinate increaser, a determinate thing increased, a
quantity of increase, and an elapsed time, in Aristotle, *Physics* VII.5,
250a28-30.

Source: Aristotle, *Physics* VII.5, 250a28-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GrowthHasAgentPatientAmountTimeReading
    (Increaser ThingIncreased AmountOfIncrease TimeOfIncrease : Prop) : Prop :=
  Increaser ∧ ThingIncreased ∧ AmountOfIncrease ∧ TimeOfIncrease

/-- Alteration has a determinate alterer, a determinate thing altered, a degree
of alteration, and an elapsed time, in Aristotle, *Physics* VII.5,
250a30-250b2.

Source: Aristotle, *Physics* VII.5, 250a30-250b2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AlterationHasAgentPatientDegreeTimeReading
    (Alterer ThingAltered DegreeOfAlteration TimeOfAlteration : Prop) : Prop :=
  Alterer ∧ ThingAltered ∧ DegreeOfAlteration ∧ TimeOfAlteration

/-- Within Aristotle's stated proportional description, double alteration
corresponds to double time in both directions, in *Physics* VII.5, 250b1-3.

This does not assert that every fractional altering force crosses the threshold
needed to cause any alteration.

Source: Aristotle, *Physics* VII.5, 250b1-3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DoubleAlterationDoubleTimeReciprocityReading
    (DoubleTime DoubleAlteration : Prop) : Prop :=
  (DoubleTime → DoubleAlteration) ∧
    (DoubleAlteration → DoubleTime)

/-- Aristotle's proportional description pairs half the affected object with
half the time and twice the affected object with the same time, in *Physics*
VII.5, 250b2-4.

Source: Aristotle, *Physics* VII.5, 250b2-4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AlterationObjectTimeScalingReading
    (HalfObjectInHalfTime HalfTimeForHalfObject
      DoubleObjectInSameTime : Prop) : Prop :=
  HalfObjectInHalfTime ∧ HalfTimeForHalfObject ∧
    DoubleObjectInSameTime

/-- Half an altering or growing agent may cause no alteration or growth at all,
just as a sub-threshold force may fail to move a weight, in Aristotle,
*Physics* VII.5, 250b4-7.

Source: Aristotle, *Physics* VII.5, 250b4-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def HalfAltererGrowerMayProduceNoChangeReading
    (HalfAltererProducesAnyAlteration HalfGrowerProducesAnyGrowth : Prop) : Prop :=
  ¬ HalfAltererProducesAnyAlteration ∧
    ¬ HalfGrowerProducesAnyGrowth

/-- If a guaranteed proportional effect from half an altering or growing agent
would require some alteration or growth, Aristotle's threshold possibility
excludes both guarantees, in *Physics* VII.5, 250b4-7.

Source: Aristotle, *Physics* VII.5, 250b4-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoGuaranteedHalfAgentProportionalChangeReading
    (HalfAltererProducesAnyAlteration HalfGrowerProducesAnyGrowth
      GuaranteedHalfAltererProportionalEffect
      GuaranteedHalfGrowerProportionalEffect : Prop) : Prop :=
  (GuaranteedHalfAltererProportionalEffect →
      HalfAltererProducesAnyAlteration) →
    (GuaranteedHalfGrowerProportionalEffect →
      HalfGrowerProducesAnyGrowth) →
    ¬ GuaranteedHalfAltererProportionalEffect ∧
      ¬ GuaranteedHalfGrowerProportionalEffect

end TruthCore.Greek.Aristotle.Physics
