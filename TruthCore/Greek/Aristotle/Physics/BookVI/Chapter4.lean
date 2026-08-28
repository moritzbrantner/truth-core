import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter3

namespace TruthCore.Greek.Aristotle.Physics

/-- Every change is from something to something; a subject wholly at its terminus
has ceased changing, while one wholly at its source has not yet begun, in Aristotle,
*Physics* VI.4, 234b10-15.

Source: Aristotle, *Physics* VI.4, 234b10-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangeSourceTerminusStatusReading
    (EveryChangeFromSourceToTerminus WhollyAtTerminusNoLongerChanging
      WhollyAtSourceNotYetChanging : Prop) : Prop :=
  EveryChangeFromSourceToTerminus ∧ WhollyAtTerminusNoLongerChanging ∧
    WhollyAtSourceNotYetChanging

/-- While a subject is changing, one part must be at the source and another at the
first terminus of the change in Aristotle, *Physics* VI.4, 234b13-18.

Source: Aristotle, *Physics* VI.4, 234b13-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangingSubjectPartlySourcePartlyTerminusReading
    (PartAtSource PartAtFirstTerminus : Prop) : Prop :=
  PartAtSource ∧ PartAtFirstTerminus

/-- The relevant terminus is the first condition reached in the change, such as grey
from white rather than the remote extreme black, in Aristotle, *Physics* VI.4,
234b15-18.

Source: Aristotle, *Physics* VI.4, 234b15-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ChangeTerminusIsFirstReachedConditionReading
    (TerminusIsFirstReachedCondition NotNecessarilyRemoteExtreme : Prop) : Prop :=
  TerminusIsFirstReachedCondition ∧ NotNecessarilyRemoteExtreme

/-- Aristotle's inferential transition in *Physics* VI.4, 234b13-20: occupying the
source and first terminus in different parts entails that the changing subject is
divisible.

Source: Aristotle, *Physics* VI.4, 234b13-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PartlySourceTerminusImpliesChangingSubjectDivisibleReading
    (PartAtSource PartAtFirstTerminus ChangingSubjectDivisible : Prop) : Prop :=
  (PartAtSource ∧ PartAtFirstTerminus) → ChangingSubjectDivisible

/-- Every changing subject is divisible in Aristotle, *Physics* VI.4, 234b10-20.

Source: Aristotle, *Physics* VI.4, 234b10-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EveryChangingSubjectDivisibleReading
    (ChangingSubjectDivisible : Prop) : Prop :=
  ChangingSubjectDivisible

/-- Motion is divisible in two ways, by time and by the motions of the moving
subject's parts, in Aristotle, *Physics* VI.4, 234b20-24.

Source: Aristotle, *Physics* VI.4, 234b20-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionDivisibleByTimeAndSubjectPartsReading
    (MotionDivisibleByTime MotionDivisibleBySubjectPartMotions : Prop) : Prop :=
  MotionDivisibleByTime ∧ MotionDivisibleBySubjectPartMotions

/-- The motions of the subject's parts together constitute the motion of the whole
subject in Aristotle, *Physics* VI.4, 234b23-35.

Source: Aristotle, *Physics* VI.4, 234b23-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PartMotionsComposeWholeMotionReading
    (EachPartHasOwnMotion PartMotionsComposeWholeMotion : Prop) : Prop :=
  EachPartHasOwnMotion ∧ PartMotionsComposeWholeMotion

/-- Any remainder or excess beyond the motions of the parts would be a motion of
neither the whole, its parts, nor anything else, which is impossible, in Aristotle,
*Physics* VI.4, 234b35-235a8.

Source: Aristotle, *Physics* VI.4, 234b35-235a8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoSurplusBeyondPartMotionsReading
    (SurplusMotionBelongsToNothing SurplusMotionPossible : Prop) : Prop :=
  SurplusMotionBelongsToNothing → ¬ SurplusMotionPossible

/-- The whole subject's motion is the same as and equal to the composition of its
part-motions in Aristotle, *Physics* VI.4, 235a1-10.

Source: Aristotle, *Physics* VI.4, 235a1-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def WholeMotionEqualsComposedPartMotionsReading
    (WholeMotionSameAsComposedPartMotions
      WholeMotionEqualToComposedPartMotions : Prop) : Prop :=
  WholeMotionSameAsComposedPartMotions ∧ WholeMotionEqualToComposedPartMotions

end TruthCore.Greek.Aristotle.Physics
