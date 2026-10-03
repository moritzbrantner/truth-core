import TruthCore.Greek.Aristotle.Physics.BookV.Chapter5

namespace TruthCore.Greek.Aristotle.Physics

/-- Motion has another motion as its contrary without qualification in Aristotle,
*Physics* V.6, 229b23-26, while rest is also opposed to motion because it is a privation;
each kind of motion is opposed by rest of that kind.

Source: Aristotle, *Physics* V.6, 229b23-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionStrictlyContraryMotionRestOpposedAsPrivationReading
    (MotionStrictlyContraryToMotion RestOpposedAsPrivation
      EachMotionKindOpposedBySameKindRest : Prop) : Prop :=
  MotionStrictlyContraryToMotion ∧ RestOpposedAsPrivation ∧
    EachMotionKindOpposedBySameKindRest

/-- For motion from one contrary to the other, rest at the starting contrary is
opposed to that motion, while rest at the other contrary is opposed to the reverse
motion, in Aristotle, *Physics* V.6, 229b26-31.

Source: Aristotle, *Physics* V.6, 229b26-31 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RestAtSourceOpposesMotionAwayReading
    (RestAtFirstOpposesMotionFromFirstToContrary
      RestAtContraryOpposesReverseMotion : Prop) : Prop :=
  RestAtFirstOpposesMotionFromFirstToContrary ∧
    RestAtContraryOpposesReverseMotion

/-- States of rest in contrary subjects are contrary to one another in Aristotle,
*Physics* V.6, 229b31-230a2, as rest in health is contrary to rest in disease.

Source: Aristotle, *Physics* V.6, 229b31-230a2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RestsInContrariesAreContraryReading
    (RestsInContrariesAreContrary : Prop) : Prop :=
  RestsInContrariesAreContrary

/-- Rest in a terminus is contrary to motion away from that terminus, not motion toward
it, in Aristotle, *Physics* V.6, 230a2-7. Motion toward where a thing rests is instead
a coming to rest or occurs together with it.

Source: Aristotle, *Physics* V.6, 230a2-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RestAtTerminusOpposesMotionAwayNotTowardReading
    (RestOpposesMotionAway RestOpposesMotionToward
      MotionTowardTerminatesInComingToRest : Prop) : Prop :=
  RestOpposesMotionAway ∧ ¬ RestOpposesMotionToward ∧
    MotionTowardTerminatesInComingToRest

/-- Where something has no contrary, changes from and to it are opposed but there is
no motion or rest, only absence of change, in Aristotle, *Physics* V.6, 230a8-18.

Source: Aristotle, *Physics* V.6, 230a8-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoContraryHasOpposedChangesButOnlyAbsenceOfChangeReading
    (ChangesFromAndToOpposed MotionExists RestExists AbsenceOfChangeExists : Prop) : Prop :=
  ChangesFromAndToOpposed ∧ ¬ MotionExists ∧ ¬ RestExists ∧ AbsenceOfChangeExists

/-- Reductio premise in Aristotle, *Physics* V.6, 230a8-18: if absence of change in
being were rest, then generation and corruption would have to be motions.

Source: Aristotle, *Physics* V.6, 230a8-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AbsenceAsRestWouldMakeGenerationCorruptionMotionsReading
    (AbsenceOfChangeIsRest GenerationIsMotion CorruptionIsMotion : Prop) : Prop :=
  AbsenceOfChangeIsRest → (GenerationIsMotion ∧ CorruptionIsMotion)

/-- Reductio conclusion in Aristotle, *Physics* V.6, 230a8-18: absence of change in
being is like rest but must not be called rest, because generation and corruption are
excluded from motion.

Source: Aristotle, *Physics* V.6, 230a8-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AbsenceOfChangeIsNotRestReading
    (AbsenceOfChangeIsRest : Prop) : Prop :=
  ¬ AbsenceOfChangeIsRest

/-- Aristotle raises a puzzle in *Physics* V.6, 230a19-25: local motion and rest are
called natural or unnatural, whereas alteration, increase, decrease, generation, and
corruption do not initially appear divided in the same way.

Source: Aristotle, *Physics* V.6, 230a19-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalUnnaturalNonlocalChangePuzzleReading
    (LocalMotionRestNaturalOrUnnatural
      NonlocalChangesInitiallyNotSoDivided : Prop) : Prop :=
  LocalMotionRestNaturalOrUnnatural ∧ NonlocalChangesInitiallyNotSoDivided

/-- Convalescence is initially no more natural or unnatural than falling ill, nor
whitening than blackening, and likewise for increase/decrease and generation/corruption,
in Aristotle, *Physics* V.6, 230a19-31; ageing shows that corruption may be natural.

Source: Aristotle, *Physics* V.6, 230a19-31 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NonlocalOppositesNotSimplyNaturalUnnaturalReading
    (AlterationOppositesSimplyNaturalVersusUnnatural
      QuantitativeOppositesSimplyNaturalVersusUnnatural
      GenerationNaturalCorruptionUnnatural NaturalAgeing : Prop) : Prop :=
  ¬ AlterationOppositesSimplyNaturalVersusUnnatural ∧
    ¬ QuantitativeOppositesSimplyNaturalVersusUnnatural ∧
    ¬ GenerationNaturalCorruptionUnnatural ∧ NaturalAgeing

/-- If violence is contrary to nature, violent corruption, generation, increase, and
decrease may stand against their natural counterparts in Aristotle, *Physics* V.6,
230a31-230b2. Rapid maturation supplies the quantitative example.

Source: Aristotle, *Physics* V.6, 230a31-230b2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ViolentAndNaturalNonlocalChangesOpposedReading
    (ViolenceIsUnnatural ViolentCorruptionOpposesNaturalCorruption
      ViolentGenerationOpposesNaturalGeneration
      ViolentGrowthDecreaseOpposeNaturalCounterparts : Prop) : Prop :=
  ViolenceIsUnnatural →
    (ViolentCorruptionOpposesNaturalCorruption ∧
      ViolentGenerationOpposesNaturalGeneration ∧
      ViolentGrowthDecreaseOpposeNaturalCounterparts)

/-- Alterations too may be natural or unnatural in Aristotle, *Physics* V.6,
230b2-6, as patients throw off fevers naturally on critical days or unnaturally at
other times.

Source: Aristotle, *Physics* V.6, 230b2-6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AlterationsCanBeNaturalOrUnnaturalReading
    (NaturalAlterationsExist UnnaturalAlterationsExist : Prop) : Prop :=
  NaturalAlterationsExist ∧ UnnaturalAlterationsExist

/-- Corruptions can be contrary to one another in a qualified respect, such as one
being pleasant and another painful, but not simply qua corruptions, in Aristotle,
*Physics* V.6, 230b6-9.

Source: Aristotle, *Physics* V.6, 230b6-9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CorruptionsContraryQualifiedlyNotUnqualifiedlyReading
    (CorruptionsContraryInQualifiedRespect
      CorruptionsContraryWithoutQualification : Prop) : Prop :=
  CorruptionsContraryInQualifiedRespect ∧ ¬ CorruptionsContraryWithoutQualification

/-- Upward and downward local motions are contrary in Aristotle, *Physics* V.6,
230b10-14; fire naturally moves upward while earth naturally moves downward, so their
natural motions exemplify this contrariety.

Source: Aristotle, *Physics* V.6, 230b10-14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FireEarthNaturalMotionsContraryReading
    (FireNaturallyMovesUp EarthNaturallyMovesDown
      TheirNaturalMotionsAreContrary : Prop) : Prop :=
  FireNaturallyMovesUp ∧ EarthNaturallyMovesDown ∧ TheirNaturalMotionsAreContrary

/-- A thing's natural local motion is contrary to its unnatural local motion in
Aristotle, *Physics* V.6, 230b13-20, as fire's natural upward motion is contrary to
its unnatural downward motion.

Source: Aristotle, *Physics* V.6, 230b13-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SameSubjectNaturalUnnaturalMotionsContraryReading
    (NaturalMotionContraryToUnnaturalMotionOfSameSubject : Prop) : Prop :=
  NaturalMotionContraryToUnnaturalMotionOfSameSubject

/-- Unnatural rest is contrary to the same subject's natural motion in Aristotle,
*Physics* V.6, 230b15-20: earth's unnatural rest above is contrary to its natural
downward motion.

Source: Aristotle, *Physics* V.6, 230b15-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def UnnaturalRestOpposesNaturalMotionSameSubjectReading
    (UnnaturalRestContraryToNaturalMotionOfSameSubject : Prop) : Prop :=
  UnnaturalRestContraryToNaturalMotionOfSameSubject

/-- Aristotle's puzzle in *Physics* V.6, 230b21-27: if every non-eternal rest comes
to be through coming to rest, violently raised earth seems to have to come to rest
while it is still being forced upward, even though forced motion behaves oppositely
to what is coming to rest.

Source: Aristotle, *Physics* V.6, 230b21-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NonEternalRestComingToRestPuzzleReading
    (EveryNonEternalRestComesToBeThroughComingToRest
      ViolentlyRaisedEarthChallengesThatAccount : Prop) : Prop :=
  EveryNonEternalRestComesToBeThroughComingToRest ∧
    ViolentlyRaisedEarthChallengesThatAccount

/-- Coming to rest either is motion toward a thing's own place or accompanies that
motion in Aristotle, *Physics* V.6, 230b27-28.

Source: Aristotle, *Physics* V.6, 230b27-28 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ComingToRestTowardProperPlaceReading
    (ComingToRestIsMotionTowardProperPlace
      ComingToRestAccompaniesMotionTowardProperPlace : Prop) : Prop :=
  ComingToRestIsMotionTowardProperPlace ∨
    ComingToRestAccompaniesMotionTowardProperPlace

/-- The puzzle behind Aristotle's comparison in *Physics* V.6, 230b28-231a2: a
thing moving away from a place retains its starting condition only qualifiedly, while
treating rest there as unqualifiedly contrary to the motion would make contraries
belong to it together.

Source: Aristotle, *Physics* V.6, 230b28-231a2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MovingAwayOriginPuzzleReading
    (MovingAwayRetainsOriginOnlyQualifiedly
      UnqualifiedRestOppositionWouldMakeContrariesCoexist : Prop) : Prop :=
  MovingAwayRetainsOriginOnlyQualifiedly ∧
    UnqualifiedRestOppositionWouldMakeContrariesCoexist

/-- Aristotle's inferential transition in *Physics* V.6, 230b28-231a2: the qualified
persistence of the starting condition, together with the simultaneous-contraries
puzzle, supports the conclusion that motion is more contrary to motion than rest is.

Source: Aristotle, *Physics* V.6, 230b28-231a2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MovingAwayPuzzleImpliesMotionMoreContraryReading
    (MovingAwayRetainsOriginOnlyQualifiedly
      UnqualifiedRestOppositionWouldMakeContrariesCoexist
      MotionMoreContraryToMotionThanRest : Prop) : Prop :=
  (MovingAwayRetainsOriginOnlyQualifiedly ∧
      UnqualifiedRestOppositionWouldMakeContrariesCoexist) →
    MotionMoreContraryToMotionThanRest

/-- Motion is more contrary to motion than rest is to motion in Aristotle,
*Physics* V.6, 231a1-2.

Source: Aristotle, *Physics* V.6, 231a1-2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionMoreContraryThanRestReading
    (MotionMoreContraryToMotionThanRest : Prop) : Prop :=
  MotionMoreContraryToMotionThanRest

/-- In Ross's bracketed alternative ending to *Physics* V.6, 231a5-10, unnatural
motion has a corresponding unnatural rest opposed to it; otherwise something held
at rest by force would rest without ever having come to rest.

Source: Aristotle, *Physics* V.6, 231a5-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def UnnaturalMotionHasOpposingUnnaturalRestReading
    (UnnaturalMotionHasOpposingUnnaturalRest : Prop) : Prop :=
  UnnaturalMotionHasOpposingUnnaturalRest

/-- In Ross's bracketed alternative ending to *Physics* V.6, 231a10-17, fire's
unnatural downward motion is contrary both to earth's natural downward motion and to
fire's natural upward motion, but in different respects; analogous distinctions hold
for rests.

Source: Aristotle, *Physics* V.6, 231a10-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DownwardFireContraryInTwoWaysReading
    (DownwardFireContraryToDownwardEarth
      DownwardFireContraryToUpwardFire ContrarietiesDifferInRespect
      AnalogousDistinctionsHoldForRests : Prop) : Prop :=
  DownwardFireContraryToDownwardEarth ∧
    DownwardFireContraryToUpwardFire ∧ ContrarietiesDifferInRespect ∧
    AnalogousDistinctionsHoldForRests

end TruthCore.Greek.Aristotle.Physics
