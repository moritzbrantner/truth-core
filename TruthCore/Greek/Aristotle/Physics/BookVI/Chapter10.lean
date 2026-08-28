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

end TruthCore.Greek.Aristotle.Physics
