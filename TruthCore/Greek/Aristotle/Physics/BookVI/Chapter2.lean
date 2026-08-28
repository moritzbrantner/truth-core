import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter1

namespace TruthCore.Greek.Aristotle.Physics

/-- Every magnitude is divisible into magnitudes in Aristotle, *Physics* VI.2,
232a23-27, because every magnitude is continuous and no continuum is composed of
indivisibles.

Source: Aristotle, *Physics* VI.2, 232a23-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EveryMagnitudeDivisibleIntoMagnitudesReading
    (EveryMagnitudeDivisibleIntoMagnitudes : Prop) : Prop :=
  EveryMagnitudeDivisibleIntoMagnitudes

/-- The faster mover traverses a greater distance in an equal time in Aristotle,
*Physics* VI.2, 232a27-32.

Source: Aristotle, *Physics* VI.2, 232a27-32 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FasterTraversesGreaterDistanceInEqualTimeReading
    (FasterTraversesGreaterDistanceInEqualTime : Prop) : Prop :=
  FasterTraversesGreaterDistanceInEqualTime

/-- The faster mover can traverse a greater distance in less time than the slower
mover in Aristotle, *Physics* VI.2, 232a32-232b5.

Source: Aristotle, *Physics* VI.2, 232a32-232b5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FasterTraversesGreaterDistanceInLessTimeReading
    (FasterTraversesGreaterDistanceInLessTime : Prop) : Prop :=
  FasterTraversesGreaterDistanceInLessTime

/-- The time in which one mover traverses an equal distance relative to another is
either equal, less, or greater in Aristotle's trichotomy argument in *Physics* VI.2,
232b12-20.

Source: Aristotle, *Physics* VI.2, 232b12-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EqualDistanceTimeComparisonTrichotomyReading
    (EqualTime LessTime GreaterTime : Prop) : Prop :=
  EqualTime ∨ LessTime ∨ GreaterTime

/-- For equal distance, the faster mover takes neither equal nor greater time than
the slower mover, since those alternatives would make it equal in speed or slower,
in Aristotle, *Physics* VI.2, 232b12-20.

Source: Aristotle, *Physics* VI.2, 232b12-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FasterExcludesEqualOrGreaterTimeForEqualDistanceReading
    (EqualTime GreaterTime : Prop) : Prop :=
  ¬ EqualTime ∧ ¬ GreaterTime

/-- The faster mover traverses an equal distance in less time than the slower mover
in Aristotle, *Physics* VI.2, 232b5-20.

Source: Aristotle, *Physics* VI.2, 232b5-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FasterTraversesEqualDistanceInLessTimeReading
    (LessTime : Prop) : Prop :=
  LessTime

end TruthCore.Greek.Aristotle.Physics
