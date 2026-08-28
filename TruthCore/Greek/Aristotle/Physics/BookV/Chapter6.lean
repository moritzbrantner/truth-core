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

end TruthCore.Greek.Aristotle.Physics
