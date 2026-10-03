import TruthCore.Greek.Aristotle.Physics.BookV.Chapter4

namespace TruthCore.Greek.Aristotle.Physics

/-- Five candidate ways motions might be contrary in Aristotle, *Physics* V.5,
229a7-16: respectively from and to the same thing, from contraries, to contraries,
from a contrary and to its opposite, or reverse motions between contraries.

Source: Aristotle, *Physics* V.5, 229a7-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FiveCandidateContraryMotionRelationsReading
    (FromAndToSame FromContraries ToContraries FromContraryAndToOpposite
      ReverseBetweenContraries : Prop) : Prop :=
  FromAndToSame ∨ FromContraries ∨ ToContraries ∨
    FromContraryAndToOpposite ∨ ReverseBetweenContraries

/-- Motion from a contrary and motion to its opposite are descriptions of one motion,
not contrary motions, in Aristotle, *Physics* V.5, 229a17-20. Changing from health and
changing to disease differ in account without being two opposed occurrences.

Source: Aristotle, *Physics* V.5, 229a17-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FromContraryAndToOppositeSameMotionNotContraryReading
    (DescriptionsBelongToSameMotion MotionsContrary : Prop) : Prop :=
  DescriptionsBelongToSameMotion ∧ ¬ MotionsContrary

/-- Motion toward a contrary, more than motion from a contrary, grounds contrariety in
Aristotle, *Physics* V.5, 229a20-30; motions are correspondingly named more from their
goals than from their starting-points.

Source: Aristotle, *Physics* V.5, 229a20-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GoalRatherThanSourceGroundsMotionContrarietyReading
    (GoalsContrary MotionsContrary MotionsNamedMoreFromGoals : Prop) : Prop :=
  (GoalsContrary → MotionsContrary) ∧ MotionsNamedMoreFromGoals

/-- Reverse motions from one contrary to the other have contrary goals in Aristotle,
*Physics* V.5, 229a31-229b8, as health-to-disease and disease-to-health do.

Source: Aristotle, *Physics* V.5, 229a31-229b8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ReverseMotionsHaveContraryGoalsReading
    (ReverseMotionsHaveContraryGoals : Prop) : Prop :=
  ReverseMotionsHaveContraryGoals

/-- Contrary motions are reverse motions from one contrary to the other in Aristotle,
*Physics* V.5, 229a31-229b8.

Source: Aristotle, *Physics* V.5, 229a31-229b8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ReverseMotionsBetweenContrariesAreContraryReading
    (ReverseMotionsContrary : Prop) : Prop :=
  ReverseMotionsContrary

/-- Inductive examples of contrary motions in Aristotle, *Physics* V.5,
229a31-229b8: falling ill and recovering, being taught and being led into error, and
locomotions upward/downward, right/left, and forward/backward.

Source: Aristotle, *Physics* V.5, 229a31-229b8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ExamplesOfContraryMotionsReading
    (IllnessRecoveryContrary TeachingErrorContrary UpDownContrary
      RightLeftContrary ForwardBackwardContrary : Prop) : Prop :=
  IllnessRecoveryContrary ∧ TeachingErrorContrary ∧ UpDownContrary ∧
    RightLeftContrary ∧ ForwardBackwardContrary

/-- A process merely toward a contrary, with no starting subject specified, is change
but not motion in Aristotle, *Physics* V.5, 229b9-12.

Source: Aristotle, *Physics* V.5, 229b9-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def UnspecifiedSourceToContraryChangeNotMotionReading
    (ProcessIsChange ProcessIsMotion : Prop) : Prop :=
  ProcessIsChange ∧ ¬ ProcessIsMotion

/-- Where something has no contrary, change from it and change to it are opposed, as
generation to corruption and loss to gain, but these are changes rather than motions,
in Aristotle, *Physics* V.5, 229b12-14.

Source: Aristotle, *Physics* V.5, 229b12-14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoContraryChangesOpposedFromAndToReading
    (ThingHasContrary ChangesFromAndToOpposed ChangesAreMotions : Prop) : Prop :=
  ¬ ThingHasContrary ∧ ChangesFromAndToOpposed ∧ ¬ ChangesAreMotions

end TruthCore.Greek.Aristotle.Physics
