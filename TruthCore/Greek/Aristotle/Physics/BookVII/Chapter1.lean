import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter10

namespace TruthCore.Greek.Aristotle.Physics

/-- If a moving thing does not have the source of its motion in itself, it is
plainly moved by something else, in Aristotle, *Physics* VII.1, 241b24-27.

Source: Aristotle, *Physics* VII.1, 241b24-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoInternalMotionPrincipleRequiresOtherMoverReading
    (LacksInternalMotionPrinciple MovedBySomethingElse : Prop) : Prop :=
  LacksInternalMotionPrinciple → MovedBySomethingElse

/-- For the internal-principle case, Aristotle selects a whole moving in its own
right rather than merely because something belonging to it moves, in *Physics*
VII.1, 241b27-33.

Source: Aristotle, *Physics* VII.1, 241b27-33 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PrimaryPerSeMotionNotMerelyPartMotionReading
    (MovesPerSeAndPrimarily MovesMerelyThroughPart : Prop) : Prop :=
  MovesPerSeAndPrimarily → ¬ MovesMerelyThroughPart

/-- The absence of an external mover does not by itself settle which internal
part is mover and which is moved, so it does not establish undifferentiated
self-motion of the whole, in Aristotle, *Physics* VII.1, 241b33-35.

Source: Aristotle, *Physics* VII.1, 241b33-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoExternalMoverDoesNotSettleInternalMoverMovedReading
    (InferenceToUndifferentiatedSelfMotionInvalid : Prop) : Prop :=
  InferenceToUndifferentiatedSelfMotionInvalid

/-- If a thing comes to rest because something else has ceased moving, that
dependence shows that the thing is moved by something, in Aristotle,
*Physics* VII.1, 242a1-4.

Source: Aristotle, *Physics* VII.1, 242a1-4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RestDependenceEntailsMovedBySomethingReading
    (PartRestDeterminesWholeRest WholeMovedBySomething : Prop) : Prop :=
  PartRestDeterminesWholeRest → WholeMovedBySomething

/-- Dividing a primary per-se moving whole shows that if the selected part does
not move, the whole does not move; otherwise only the other part would be moving
and the whole would not be moving primarily in its own right, in Aristotle,
*Physics* VII.1, 242a4-13.

Source: Aristotle, *Physics* VII.1, 242a4-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DivisiblePrimaryMoverHasRestDeterminingPartReading
    (MovingSubjectDivisible PartRestDeterminesWholeRest : Prop) : Prop :=
  MovingSubjectDivisible → PartRestDeterminesWholeRest

/-- Every moving thing is moved by something, in Aristotle, *Physics* VII.1,
241b24-242a15. “Something” does not yet identify the first mover reached by the
chapter's following regress argument.

Source: Aristotle, *Physics* VII.1, 241b24-242a15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EveryMovingThingMovedBySomethingReading
    (EveryMovingThingMovedBySomething : Prop) : Prop :=
  EveryMovingThingMovedBySomething

end TruthCore.Greek.Aristotle.Physics
