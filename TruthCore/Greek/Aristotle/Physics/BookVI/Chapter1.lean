import TruthCore.Greek.Aristotle.Physics.BookV.Chapter6

namespace TruthCore.Greek.Aristotle.Physics

/-- Aristotle distinguishes continuous, touching, and successive items in *Physics*
VI.1, 231a21-24: continuous things have one common extremity, touching things have
their extremities together, and successive things have nothing homogeneous between.

Source: Aristotle, *Physics* VI.1, 231a21-24 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContinuousTouchingSuccessiveDistinctionReading
    (ContinuousHaveOneExtremity TouchingHaveExtremitiesTogether
      SuccessiveHaveNothingHomogeneousBetween : Prop) : Prop :=
  ContinuousHaveOneExtremity ∧ TouchingHaveExtremitiesTogether ∧
    SuccessiveHaveNothingHomogeneousBetween

/-- Aristotle's compositional premise in *Physics* VI.1, 231a24-231b6: if a
continuum were composed of indivisibles, those indivisibles would have to form the
continuum through continuity or contact.

Source: Aristotle, *Physics* VI.1, 231a24-231b6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContinuumFromIndivisiblesRequiresContinuityOrContactReading
    (ContinuumComposedOfIndivisibles
      IndivisiblesComposeContinuumThroughContinuityOrContact : Prop) : Prop :=
  ContinuumComposedOfIndivisibles →
    IndivisiblesComposeContinuumThroughContinuityOrContact

/-- Indivisibles cannot compose a continuum through continuity or contact in
Aristotle, *Physics* VI.1, 231a24-231b6. Indivisibles have no distinct extremities,
and whole-to-whole contact does not yield a continuum with distinct parts.

Source: Aristotle, *Physics* VI.1, 231a24-231b6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IndivisiblesCannotComposeContinuumByContinuityOrContactReading
    (IndivisiblesComposeContinuumThroughContinuityOrContact : Prop) : Prop :=
  ¬ IndivisiblesComposeContinuumThroughContinuityOrContact

/-- No continuum is composed of indivisibles in Aristotle, *Physics* VI.1,
231a24-231b6; in particular, a line is not composed of points.

Source: Aristotle, *Physics* VI.1, 231a24-231b6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContinuumNotComposedOfIndivisiblesReading
    (ContinuumComposedOfIndivisibles : Prop) : Prop :=
  ¬ ContinuumComposedOfIndivisibles

/-- A point is not successive to a point, nor a now to a now, in Aristotle,
*Physics* VI.1, 231b6-12, because a line always lies between points and time between
nows; points and nows therefore cannot compose length or time by succession.

Source: Aristotle, *Physics* VI.1, 231b6-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PointAndNowNotSuccessiveReading
    (PointSuccessiveToPoint NowSuccessiveToNow : Prop) : Prop :=
  ¬ PointSuccessiveToPoint ∧ ¬ NowSuccessiveToNow

/-- Every continuum is divisible into things that are themselves always further
divisible, not into indivisibles, in Aristotle, *Physics* VI.1, 231b12-18.

Source: Aristotle, *Physics* VI.1, 231b12-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EveryContinuumDivisibleIntoAlwaysDivisiblesReading
    (EveryContinuumDivisibleIntoAlwaysDivisibles : Prop) : Prop :=
  EveryContinuumDivisibleIntoAlwaysDivisibles

end TruthCore.Greek.Aristotle.Physics
