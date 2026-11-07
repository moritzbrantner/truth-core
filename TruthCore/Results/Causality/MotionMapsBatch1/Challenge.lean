import TruthCore.Causality.MotionMapsBatch1

namespace TruthCore.Results.Causality.MotionMapsBatch1
open TruthCore.Causality.MotionMapsBatch1
open TruthCore.Latin.Aquinas.SummaTheologiae
  (SecondMoversMoveOnlyAsMovedReading SecondMoversMoveAsMovedInRelevantRespectReading
    CreatedAgentIsAppliedToActByGodReading GradesFoundInThingsReading)
open TruthCore.Greek.Aristotle.Physics (BeingMovedIsActualizationOfPotencyReading)
open TruthCore.Logic.CogitoSubject (ThoughtOccurs EveryThoughtHasSubject)

/-- Weak per se reading from the instrument analysis: a mover moved in a relevant
respect is an instrument, and an instrument moves only as moved. -/
theorem relevantRespectFromInstrument {B R : Type} (MovedIn : B → R → Prop)
    (MovesIn : B → B → R → Prop) (MovesAsMoved : B → B → Prop)
    (RelevantTo : B → B → R → R → Prop) (ByOwnForm : B → B → Prop)
    (hInstrument : MovedMoverIsInstrument MovedIn MovesIn RelevantTo ByOwnForm)
    (hPrincipal : InstrumentMovesByPrincipalPower MovesIn ByOwnForm MovesAsMoved) :
    SecondMoversMoveAsMovedInRelevantRespectReading MovedIn MovesIn MovesAsMoved RelevantTo := by
  sorry

/-- Strong per se reading from the weak one plus the scope bridge. -/
theorem onlyAsMovedFromRelevantRespect {B R : Type} (MovedIn : B → R → Prop)
    (MovesIn : B → B → R → Prop) (MovesAsMoved : B → B → Prop)
    (RelevantTo : B → B → R → R → Prop)
    (hWeak : SecondMoversMoveAsMovedInRelevantRespectReading MovedIn MovesIn MovesAsMoved
      RelevantTo)
    (hScope : RelevantRespectCoversEveryMovedMover MovedIn MovesIn RelevantTo) :
    SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved := by
  sorry

/-- A creature's acting actualizes a potency of its own as such; by *Physics*
III.1 that is being moved, so every created agent that moves is moved. -/
theorem createdAgentMovedFromNewActuality {B R : Type} (MovedIn : B → R → Prop)
    (MovesIn : B → B → R → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (God : B → Prop) (InPotency ActualizedQuaPotential : B → R → Prop)
    (hNew : CreatureActingIsNewActuality MovesIn CausesIn esse God InPotency
      ActualizedQuaPotential)
    (hMotion : BeingMovedIsActualizationOfPotencyReading MovedIn InPotency
      ActualizedQuaPotential) :
    CreatedAgentIsAppliedToActByGodReading MovedIn MovesIn CausesIn esse God := by
  sorry

/-- A creature is in potency to its operation, and acting actualizes that
potency as such: so its acting is a new actuality. -/
theorem newActualityFromOperationPotency {B R : Type} (MovesIn : B → B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) (God : B → Prop)
    (OperationOf : B → B → R → R → Prop) (InPotency ActualizedQuaPotential : B → R → Prop)
    (hPotency : CreatureInPotencyToItsOperation MovesIn CausesIn esse God OperationOf
      InPotency)
    (hActing : ActingActualizesOperationPotency MovesIn OperationOf ActualizedQuaPotential) :
    CreatureActingIsNewActuality MovesIn CausesIn esse God InPotency ActualizedQuaPotential := by
  sorry

/-- Grades are found in things: some thought occurs, it has a bearer, the bearer
lives, something actual merely exists, the living is more noble than it, and a
grade of nobility is a grade of goodness and truth. -/
theorem gradesFromCogito {E B R : Type} (Occurs : E → Prop) (Bears : B → E → Prop)
    (Lives Actual : B → Prop) (MoreIn : R → B → B → Prop) (bonum verum nobile : R)
    (hOccurs : ThoughtOccurs Occurs)
    (hSubject : EveryThoughtHasSubject Occurs Bears)
    (hLives : ThinkerLives Occurs Bears Lives)
    (hStone : SomethingMerelyExists Actual Lives)
    (hNoble : LivingMoreNobleThanMerelyExisting MoreIn nobile Actual Lives)
    (hConvert : NobilityGradeConvertible MoreIn bonum verum nobile) :
    GradesFoundInThingsReading MoreIn bonum verum nobile := by
  sorry

open TruthCore.Causality.MotionMapsBatch1.Control

/-- The batch controls (`MOTION-MAPS-BATCH1-CONTROLS`). -/
theorem controls : Certificate := by
  sorry

end TruthCore.Results.Causality.MotionMapsBatch1
