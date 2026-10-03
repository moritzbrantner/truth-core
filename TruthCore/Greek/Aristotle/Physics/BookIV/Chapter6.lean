import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter5

namespace TruthCore.Greek.Aristotle.Physics

/-- Agenda and method in Aristotle, *Physics* IV.6, 213a12-24: the physicist must ask whether
void exists, how, and what it is, beginning from arguments for it, arguments against it, and
common opinions, just as in the inquiry into place.

Source: Aristotle, *Physics* IV.6, 213a12-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PhysicalInquiryIntoVoidReading
    (PhysicistMustDetermineWhetherVoidExists
      PhysicistMustDetermineHowVoidExists PhysicistMustDetermineWhatVoidIs
      InquirySurveysProponents OpponentsAndCommonOpinionsSurveyed : Prop) : Prop :=
  PhysicistMustDetermineWhetherVoidExists ∧
    PhysicistMustDetermineHowVoidExists ∧ PhysicistMustDetermineWhatVoidIs ∧
      InquirySurveysProponents ∧ OpponentsAndCommonOpinionsSurveyed

/-- Void, full, and place in Aristotle, *Physics* IV.6, 213a15-20: proponents treat one
receptive thing as full while it holds a body and void when deprived of it, so void, full,
and place share a subject while differing in what it is to be each.

Source: Aristotle, *Physics* IV.6, 213a15-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VoidFullPlaceSameSubjectDifferentBeingReading
    (ReceptacleFullWhenHoldingBody ReceptacleVoidWhenDeprivedOfBody
      VoidFullPlaceShareSubject VoidFullPlaceDifferInBeing : Prop) : Prop :=
  ReceptacleFullWhenHoldingBody ∧ ReceptacleVoidWhenDeprivedOfBody ∧
    VoidFullPlaceShareSubject ∧ VoidFullPlaceDifferInBeing

/-- Aristotle's criticism in *Physics* IV.6, 213a23-31: Anaxagoras and similar opponents
show by wineskins and clepsydras that air is something, but this refutes only loose speech
calling air-filled regions empty, not the intended notion of void.

Source: Aristotle, *Physics* IV.6, 213a23-31 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AirExperimentsMissVoidTargetReading
    (WineskinsAndClepsydrasShowAirIsSomething
      CommonSpeechCallsAirFilledRegionVoid
      ShowingAirExistsRefutesIntendedVoid : Prop) : Prop :=
  WineskinsAndClepsydrasShowAirIsSomething ∧
    CommonSpeechCallsAirFilledRegionVoid ∧
      ¬ ShowingAirExistsRefutesIntendedVoid

/-- The real target of void inquiry in Aristotle, *Physics* IV.6, 213a28-213b2: people mean
an interval without sensible body; the issue is whether an actual or separable interval
distinct from bodies breaks the continuity of the whole, as in Democritus and Leucippus, or
exists outside the continuous whole.

Source: Aristotle, *Physics* IV.6, 213a28-213b2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IntendedVoidAsBodilessIntervalReading
    (VoidMeansIntervalWithoutSensibleBody
      QuestionConcernsActualOrSeparableIntervalDistinctFromBodies
      AtomistsAffirmContinuityBreakingIntervals
      PossibleVoidOutsideContinuousWholeAtIssue : Prop) : Prop :=
  VoidMeansIntervalWithoutSensibleBody ∧
    QuestionConcernsActualOrSeparableIntervalDistinctFromBodies ∧
      AtomistsAffirmContinuityBreakingIntervals ∧
        PossibleVoidOutsideContinuousWholeAtIssue

/-- Premise used by proponents in Aristotle, *Physics* IV.6, 213b2-15: local motion and
increase occur.

Source: Aristotle, *Physics* IV.6, 213b2-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def LocalMotionAndIncreaseOccurReading (LocalMotionAndIncreaseOccur : Prop) : Prop :=
  LocalMotionAndIncreaseOccur

/-- The proponents' inferential bridge in Aristotle, *Physics* IV.6, 213b2-15: because a
full region cannot receive another body without coincident bodies, local motion and increase
would be impossible without void; hence their occurrence is taken to require void.

Source: Aristotle, *Physics* IV.6, 213b2-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionArgumentRequiresVoidReading
    (LocalMotionAndIncreaseOccur VoidExists : Prop) : Prop :=
  LocalMotionAndIncreaseOccur → VoidExists

/-- Conclusion attributed to void proponents in Aristotle, *Physics* IV.6, 213b2-15: void
exists. This is a dialectical conclusion reported by Aristotle, not yet his own position.

Source: Aristotle, *Physics* IV.6, 213b2-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def VoidExistsReading (VoidExists : Prop) : Prop := VoidExists

/-- Melissus' opposed use of the motion-void connection in Aristotle, *Physics* IV.6,
213b12-15: motion would require void, but void is not among existing things, so the whole is
immovable.

Source: Aristotle, *Physics* IV.6, 213b12-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MelissusInfersWholeImmovableReading
    (MotionRequiresVoid VoidExists WholeIsImmovable : Prop) : Prop :=
  MotionRequiresVoid ∧ ¬ VoidExists → WholeIsImmovable

/-- Compression argument reported in Aristotle, *Physics* IV.6, 213b15-19: contraction and
the claim that a cask can receive both its wine and the wineskins are taken to show that a
compressed body contracts into internal voids.

Source: Aristotle, *Physics* IV.6, 213b15-19 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CompressionSuggestsInternalVoidsReading
    (BodiesContractAndCompress CaskReceivesWineAndWineskins
      CompressionOccursIntoInternalVoids : Prop) : Prop :=
  BodiesContractAndCompress ∧ CaskReceivesWineAndWineskins →
    CompressionOccursIntoInternalVoids

/-- Growth and ash arguments reported in Aristotle, *Physics* IV.6, 213b19-23: because
nutriment is body and two bodies cannot coincide, growth is said to require void; ashes
absorbing as much water as an empty vessel are offered as corroboration.

Source: Aristotle, *Physics* IV.6, 213b19-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GrowthAndAshSuggestVoidReading
    (NutrimentIsBody TwoBodiesCannotCoincide GrowthRequiresVoid
      AshesAbsorbVesselVolumeOfWater AshExperimentSupportsVoid : Prop) : Prop :=
  (NutrimentIsBody ∧ TwoBodiesCannotCoincide → GrowthRequiresVoid) ∧
    AshesAbsorbVesselVolumeOfWater ∧ AshExperimentSupportsVoid

/-- Pythagorean void doctrine reported in Aristotle, *Physics* IV.6, 213b23-29: the heaven
inhales void from infinite breath, and void separates successive natures and primarily
distinguishes numbers.

Source: Aristotle, *Physics* IV.6, 213b23-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PythagoreanVoidDoctrineReading
    (HeavenInhalesVoidFromInfiniteBreath VoidSeparatesSuccessiveNatures
      VoidPrimarilyDistinguishesNumbers : Prop) : Prop :=
  HeavenInhalesVoidFromInfiniteBreath ∧ VoidSeparatesSuccessiveNatures ∧
    VoidPrimarilyDistinguishesNumbers

end TruthCore.Greek.Aristotle.Physics
