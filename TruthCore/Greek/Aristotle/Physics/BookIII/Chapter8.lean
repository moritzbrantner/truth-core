import TruthCore.Greek.Aristotle.Physics.BookIII.Chapter7

namespace TruthCore.Greek.Aristotle.Physics

/--
Rebuttal in Aristotle, *Physics* III.8, 208a8-11: unending coming-to-be does not require an
actually infinite sensible body. Generation can continue through replacement—the passing
away of one thing being the coming-to-be of another—while the whole remains finite.

The formal proposition records the modal conclusion without turning Aristotle's generation
model into a general conservation law.

Source: Aristotle, *Physics* III.8, 208a8-11 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def UnendingGenerationDoesNotRequireActualInfiniteBodyReading
    (ActualInfiniteBodyNecessaryForUnendingGeneration : Prop) : Prop :=
  ¬ ActualInfiniteBodyNecessaryForUnendingGeneration

/--
Conceptual distinction in Aristotle, *Physics* III.8, 208a11-14: touching and being limited
are not the same relation. Touching is relative to something touched, whereas being limited
is not thereby a relation to an arbitrary external toucher.

Source: Aristotle, *Physics* III.8, 208a11-14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TouchingNotIdenticalWithBeingLimitedReading
    (TouchingIdenticalWithBeingLimited : Prop) : Prop :=
  ¬ TouchingIdenticalWithBeingLimited

/--
Anti-mental-projection reading of Aristotle, *Physics* III.8, 208a14-20: the ability to
magnify something without limit in thought does not entail a corresponding increase or
infinite magnitude in the thing itself.

The proposition targets the claimed entailment, allowing thought and reality to coincide in
particular cases for independent reasons.

Source: Aristotle, *Physics* III.8, 208a14-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MentalMagnificationDoesNotEntailRealMagnitudeReading
    (MentalMagnificationEntailsRealMagnitude : Prop) : Prop :=
  ¬ MentalMagnificationEntailsRealMagnitude

/--
Successive-infinity reading of Aristotle, *Physics* III.8, 208a20-21: time, motion, and
thinking can be called infinite in a successive sense, because the part presently taken does
not remain as a completed totality while further parts occur.

Source: Aristotle, *Physics* III.8, 208a20-21 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TimeMotionThoughtInfiniteBySuccessionReading
    (TimeSuccessivelyInfinite : Prop)
    (MotionSuccessivelyInfinite : Prop)
    (ThoughtSuccessivelyInfinite : Prop) : Prop :=
  TimeSuccessivelyInfinite ∧
    MotionSuccessivelyInfinite ∧
    ThoughtSuccessivelyInfinite

/--
Final magnitude qualification in Aristotle, *Physics* III.8, 208a21-22: neither continued
reduction/division nor unlimited magnification in thought yields a completed actually
infinite magnitude.

This is intentionally compatible with III.6-7, where division is potentially infinite.
The rejected propositions here are completed-magnitude outcomes, not indefinite divisibility.

Source: Aristotle, *Physics* III.8, 208a21-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoCompletedInfiniteMagnitudeByReductionOrThoughtReading
    (CompletedInfiniteMagnitudeByReduction : Prop)
    (CompletedInfiniteMagnitudeByThought : Prop) : Prop :=
  ¬ CompletedInfiniteMagnitudeByReduction ∧
    ¬ CompletedInfiniteMagnitudeByThought

end TruthCore.Greek.Aristotle.Physics
