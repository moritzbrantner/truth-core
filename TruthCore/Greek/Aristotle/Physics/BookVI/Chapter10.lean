import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter9

namespace TruthCore.Greek.Aristotle.Physics

/-- Aristotle uses “partless” here for what is indivisible in quantity in
*Physics* VI.10, 240b8-14. This local definition does not identify every other
sense of indivisibility used elsewhere in the work.

Source: Aristotle, *Physics* VI.10, 240b8-14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PartlessMeansQuantitativelyIndivisibleReading
    (Partless QuantitativelyIndivisible : Prop) : Prop :=
  Partless ↔ QuantitativelyIndivisible

/-- A quantitatively indivisible item can be moved incidentally by being contained
in a moving body or by moving with a whole of which it is a part, in Aristotle,
*Physics* VI.10, 240b8-14.

Source: Aristotle, *Physics* VI.10, 240b8-14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IndivisibleCanMoveIncidentallyWithWholeReading
    (ContainedInMovingWhole CanMoveIncidentally : Prop) : Prop :=
  ContainedInMovingWhole → CanMoveIncidentally

/-- The motion belonging to a part in its own right differs from the motion it has
through the whole, as the unequal speeds at different radii of a sphere illustrate,
in Aristotle, *Physics* VI.10, 240b14-19.

Source: Aristotle, *Physics* VI.10, 240b14-19 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PartOwnAndWholeDerivedMotionsDifferReading
    (PartMotionsDiffer : Prop) : Prop :=
  PartMotionsDiffer

/-- During the proposed primary interval in which an indivisible changes from one
state to another, it must be at the source, at the target, or partly at each, in
Aristotle, *Physics* VI.10, 240b20-26.

Source: Aristotle, *Physics* VI.10, 240b20-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IndivisiblePrimaryChangeStateTrichotomyReading
    (AtSource AtTarget SplitAcrossStates : Prop) : Prop :=
  AtSource ∨ AtTarget ∨ SplitAcrossStates

/-- An indivisible cannot be partly in each endpoint state during change, since
that condition would make it divisible, in Aristotle, *Physics* VI.10, 240b25-27.

Source: Aristotle, *Physics* VI.10, 240b25-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IndivisibleExcludesSplitAcrossStatesReading
    (SplitAcrossStates : Prop) : Prop :=
  ¬ SplitAcrossStates

/-- Being at the target throughout the proposed change interval would mean that
the change is already complete rather than still under way, in Aristotle,
*Physics* VI.10, 240b27-28.

Source: Aristotle, *Physics* VI.10, 240b27-28 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TargetStateExcludesOngoingChangeReading
    (AtTarget ChangeComplete OngoingChange : Prop) : Prop :=
  (AtTarget → ChangeComplete) ∧ (ChangeComplete → ¬ OngoingChange)

/-- Remaining at the source throughout the proposed interval counts as rest, and
rest excludes the proposed ongoing change, in Aristotle, *Physics* VI.10,
240b28-30.

Source: Aristotle, *Physics* VI.10, 240b28-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SourceStateThroughIntervalExcludesChangeReading
    (AtSource Rests OngoingChange : Prop) : Prop :=
  (AtSource → Rests) ∧ (Rests → ¬ OngoingChange)

/-- A quantitatively indivisible item cannot move or change in its own right, in
Aristotle, *Physics* VI.10, 240b20-30. Incidental motion with a containing whole is
left open by the chapter's preceding distinction.

Source: Aristotle, *Physics* VI.10, 240b20-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IndivisibleCannotChangePerSeReading
    (IndivisibleChangesPerSe : Prop) : Prop :=
  ¬ IndivisibleChangesPerSe

/-- Per-se motion of an indivisible would be possible only if time were composed
of nows, so that it was always found already changed in a now but never changing,
in Aristotle, *Physics* VI.10, 240b30-241a1.

Source: Aristotle, *Physics* VI.10, 240b30-241a1 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IndivisibleMotionWouldRequireTimeFromNowsReading
    (IndivisibleMovesPerSe TimeComposedOfNows : Prop) : Prop :=
  IndivisibleMovesPerSe → TimeComposedOfNows

/-- Before a moving thing can traverse a distance greater than itself, it must
first traverse a distance equal to or less than itself, in Aristotle,
*Physics* VI.10, 241a6-10.

Source: Aristotle, *Physics* VI.10, 241a6-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MoverMustFirstTraverseEqualOrLessReading
    (MovesPerSe FirstTraversalEqualOrLess : Prop) : Prop :=
  MovesPerSe → FirstTraversalEqualOrLess

/-- Because an indivisible has no smaller quantitative part, its hypothesized
first traversal cannot be less than itself and would therefore have to equal
itself, in Aristotle, *Physics* VI.10, 241a9-11.

Source: Aristotle, *Physics* VI.10, 241a9-11 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IndivisibleFirstTraversalMustEqualItselfReading
    (FirstTraversalEqualOrLess FirstTraversalEqual : Prop) : Prop :=
  FirstTraversalEqualOrLess → FirstTraversalEqual

/-- Repeated traversals each equal to a moving point would make the point measure
the whole line and so make the line composed of points, in Aristotle,
*Physics* VI.10, 241a10-13.

Source: Aristotle, *Physics* VI.10, 241a10-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RepeatedPointTraversalsWouldComposeLineReading
    (PointMovesPerSe FirstTraversalEqualsPoint LineComposedOfPoints : Prop) : Prop :=
  PointMovesPerSe ∧ FirstTraversalEqualsPoint → LineComposedOfPoints

/-- No point or other quantitatively indivisible item can move in its own right,
in Aristotle, *Physics* VI.10, 241a6-26.

Source: Aristotle, *Physics* VI.10, 241a6-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoIndivisibleCanMovePerSeReading
    (IndivisibleMovesPerSe : Prop) : Prop :=
  ¬ IndivisibleMovesPerSe

/-- Given that motion occurs in divisible time rather than in a now, a proposed
motion in which an indivisible traverses its own extent yields a smaller time and
therefore a traversal smaller than that extent, in Aristotle, *Physics* VI.10,
241a14-22.

Source: Aristotle, *Physics* VI.10, 241a14-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DivisibleTimeMotionYieldsSmallerThanIndivisibleReading
    (EveryMotionOccursInTime EveryTimeDivisible SmallerTimeHasSmallerMotion
      MotionInNow IndivisibleMovesPerSe SmallerThanIndivisible : Prop) : Prop :=
  (EveryMotionOccursInTime ∧ EveryTimeDivisible ∧ SmallerTimeHasSmallerMotion) →
    ¬ MotionInNow → IndivisibleMovesPerSe → SmallerThanIndivisible

/-- A traversal smaller than an indivisible's own extent would divide what was
stipulated to be indivisible and is therefore impossible, in Aristotle,
*Physics* VI.10, 241a20-23.

Source: Aristotle, *Physics* VI.10, 241a20-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IndivisibilityExcludesSmallerTraversalReading
    (SmallerThanIndivisible : Prop) : Prop :=
  ¬ SmallerThanIndivisible

/-- The possibility of motion in a now and the possibility of motion of an
indivisible stand or fall together under Aristotle's argument in *Physics* VI.10,
241a23-26.

Source: Aristotle, *Physics* VI.10, 241a23-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionInNowAndIndivisibleMotionSameAccountReading
    (SameAccountApplies : Prop) : Prop :=
  SameAccountApplies

/-- Every change is from something to something, whether the opposition is
contradictory or contrary, in Aristotle, *Physics* VI.10, 241a26-28.

Source: Aristotle, *Physics* VI.10, 241a26-28 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EveryChangeFromSomethingToSomethingReading
    (EveryChangeFromSourceToTerminus : Prop) : Prop :=
  EveryChangeFromSourceToTerminus

/-- Affirmation and negation bound contradictory changes: generation terminates
in being and destruction in non-being, in Aristotle, *Physics* VI.10, 241a28-31.

Source: Aristotle, *Physics* VI.10, 241a28-31 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContradictoryChangesHaveAffirmativeNegativeTerminiReading
    (AffirmationAndNegationAreTermini GenerationTerminatesInBeing
      DestructionTerminatesInNonbeing : Prop) : Prop :=
  AffirmationAndNegationAreTermini ∧ GenerationTerminatesInBeing ∧
    DestructionTerminatesInNonbeing

/-- Contrary changes are bounded by their contrary extremes, including alteration
from contraries, in Aristotle, *Physics* VI.10, 241a31-34.

Source: Aristotle, *Physics* VI.10, 241a31-34 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContraryChangesBoundedByContraryExtremesReading
    (ContrariesAreChangeExtremes AlterationProceedsFromContraries : Prop) : Prop :=
  ContrariesAreChangeExtremes ∧ AlterationProceedsFromContraries

/-- Growth is bounded by the naturally complete size proper to the thing, while
diminution is departure from that size, in Aristotle, *Physics* VI.10,
241a34-241b2.

Source: Aristotle, *Physics* VI.10, 241a34-241b2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GrowthAndDiminutionNaturalMagnitudeTerminiReading
    (GrowthTerminatesAtNaturallyCompleteMagnitude
      DiminutionDepartsFromThatMagnitude : Prop) : Prop :=
  GrowthTerminatesAtNaturallyCompleteMagnitude ∧
    DiminutionDepartsFromThatMagnitude

/-- Locomotion is not bounded in the same way by contrary extremes, because not
every locomotion is between contraries, in Aristotle, *Physics* VI.10, 241b2-4.

Source: Aristotle, *Physics* VI.10, 241b2-4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def LocomotionNotAlwaysBoundedByContrariesReading
    (EveryLocomotionBetweenContraries : Prop) : Prop :=
  ¬ EveryLocomotionBetweenContraries

/-- If a moving thing actually changes to some endpoint, that endpoint must be one
to which change is possible, in Aristotle, *Physics* VI.10, 241b4-9.

Source: Aristotle, *Physics* VI.10, 241b4-9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ActualChangeEndpointMustBePossibleReading
    (ActualChangeEndpointPossible : Prop) : Prop :=
  ActualChangeEndpointPossible

/-- An infinite extent cannot be traversed, in Aristotle, *Physics* VI.10,
241b9-11.

Source: Aristotle, *Physics* VI.10, 241b9-11 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteExtentCannotBeTraversedReading
    (InfiniteExtentTraversable : Prop) : Prop :=
  ¬ InfiniteExtentTraversable

/-- Aristotle's inferential transition in *Physics* VI.10, 241a26-241b12: being
from something to something, having only possible actual termini, and the
untraversability of an infinite extent exclude a change whose termini are wholly
indeterminate.

Source: Aristotle, *Physics* VI.10, 241a26-241b12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangeTerminusPremisesExcludeIndeterminateInfinityReading
    (EveryChangeFromSourceToTerminus ActualEndpointPossible
      InfiniteExtentTraversable ChangeLacksDeterminateTermini : Prop) : Prop :=
  EveryChangeFromSourceToTerminus → ActualEndpointPossible →
    ¬ InfiniteExtentTraversable → ¬ ChangeLacksDeterminateTermini

/-- No change is infinite in the sense of lacking determinate termini, in
Aristotle, *Physics* VI.10, 241a26-241b12.

Source: Aristotle, *Physics* VI.10, 241a26-241b12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoChangeInfiniteThroughIndeterminateTerminiReading
    (ChangeLacksDeterminateTermini : Prop) : Prop :=
  ¬ ChangeLacksDeterminateTermini

/-- Infinity through indeterminate termini is distinct from the question whether
one and the same motion can be infinite in duration, in Aristotle,
*Physics* VI.10, 241b10-14.

Source: Aristotle, *Physics* VI.10, 241b10-14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TerminusInfinityDistinctFromTemporalInfinityReading
    (TheTwoInfinityQuestionsAreDistinct : Prop) : Prop :=
  TheTwoInfinityQuestionsAreDistinct

/-- A succession of locomotion, alteration, growth, and generation could keep
motion occurring forever, but would not constitute one motion, in Aristotle,
*Physics* VI.10, 241b14-18.

Source: Aristotle, *Physics* VI.10, 241b14-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def HeterogeneousSuccessionCanBeEverlastingNotOneMotionReading
    (SuccessionCanKeepMotionAlwaysOccurring CannotConstituteOneMotion : Prop) : Prop :=
  SuccessionCanKeepMotionAlwaysOccurring ∧ CannotConstituteOneMotion

/-- If one and the same motion is infinite in time, it must be circular
locomotion, in Aristotle, *Physics* VI.10, 241b18-20. The chapter states this
restriction here without supplying a new derivation of circular motion's
continuity.

Source: Aristotle, *Physics* VI.10, 241b18-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def OnlyCircularLocomotionCanBeOneMotionInfiniteInTimeReading
    (OneMotion InfiniteInTime CircularLocomotion : Prop) : Prop :=
  OneMotion ∧ InfiniteInTime → CircularLocomotion

end TruthCore.Greek.Aristotle.Physics
