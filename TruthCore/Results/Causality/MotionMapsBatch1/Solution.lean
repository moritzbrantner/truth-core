module

public import TruthCore.Causality.MotionMapsBatch1

@[expose] public section

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
    SecondMoversMoveAsMovedInRelevantRespectReading MovedIn MovesIn MovesAsMoved RelevantTo :=
  fun y x r r' hne hMoves hMoved hRel =>
    hPrincipal y x r hMoves (hInstrument y x r r' hne hMoves hMoved hRel)

/-- Strong per se reading from the weak one plus the scope bridge. -/
theorem onlyAsMovedFromRelevantRespect {B R : Type} (MovedIn : B → R → Prop)
    (MovesIn : B → B → R → Prop) (MovesAsMoved : B → B → Prop)
    (RelevantTo : B → B → R → R → Prop)
    (hWeak : SecondMoversMoveAsMovedInRelevantRespectReading MovedIn MovesIn MovesAsMoved
      RelevantTo)
    (hScope : RelevantRespectCoversEveryMovedMover MovedIn MovesIn RelevantTo) :
    SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved :=
  fun y x r hne hMoves hSome =>
    let ⟨r', hMoved, hRel⟩ := hScope y x r hne hMoves hSome
    hWeak y x r r' hne hMoves hMoved hRel

/-- A creature's acting actualizes a potency of its own as such; by *Physics*
III.1 that is being moved, so every created agent that moves is moved. -/
theorem createdAgentMovedFromNewActuality {B R : Type} (MovedIn : B → R → Prop)
    (MovesIn : B → B → R → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (God : B → Prop) (InPotency ActualizedQuaPotential : B → R → Prop)
    (hNew : CreatureActingIsNewActuality MovesIn CausesIn esse God InPotency
      ActualizedQuaPotential)
    (hMotion : BeingMovedIsActualizationOfPotencyReading MovedIn InPotency
      ActualizedQuaPotential) :
    CreatedAgentIsAppliedToActByGodReading MovedIn MovesIn CausesIn esse God :=
  fun g y hGod hne hCaused ⟨x, r, hMoves⟩ =>
    let ⟨r', hPot, hAct⟩ := hNew g y hGod hne hCaused x r hMoves
    ⟨r', (hMotion y r').2 ⟨hPot, hAct⟩⟩

/-- A creature is in potency to its operation, and acting actualizes that
potency as such: so its acting is a new actuality. -/
theorem newActualityFromOperationPotency {B R : Type} (MovesIn : B → B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) (God : B → Prop)
    (OperationOf : B → B → R → R → Prop) (InPotency ActualizedQuaPotential : B → R → Prop)
    (hPotency : CreatureInPotencyToItsOperation MovesIn CausesIn esse God OperationOf
      InPotency)
    (hActing : ActingActualizesOperationPotency MovesIn OperationOf ActualizedQuaPotential) :
    CreatureActingIsNewActuality MovesIn CausesIn esse God InPotency ActualizedQuaPotential :=
  fun g y hGod hne hCaused x r hMoves =>
    let ⟨o, hOp, hPot⟩ := hPotency g y hGod hne hCaused x r hMoves
    ⟨o, hPot, hActing y x r o hMoves hOp⟩

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
    GradesFoundInThingsReading MoreIn bonum verum nobile :=
  let ⟨e, he⟩ := hOccurs
  let ⟨s, hs⟩ := hSubject e he
  let ⟨z, hz, hzl⟩ := hStone
  have hMore := hNoble s z (hLives s e he hs) hz hzl
  ⟨⟨s, z, (hConvert s z hMore).1⟩, ⟨s, z, (hConvert s z hMore).2⟩, ⟨s, z, hMore⟩⟩

section Controls
open TruthCore.Causality.MotionMapsBatch1.Control

private theorem omitInstrument : OmitInstrument :=
  ⟨fun h => h true false () () (fun h => nomatch h) ⟨rfl, rfl⟩ rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩,
    fun _ _ _ hMoves hNot => hNot hMoves,
    fun h => h true false () () (fun h => nomatch h) ⟨rfl, rfl⟩ rfl ⟨rfl, rfl⟩⟩

private theorem omitPrincipal : OmitPrincipal :=
  ⟨fun _ _ _ _ _ _ _ _ h => h,
    fun h => h true false () ⟨rfl, rfl⟩ id,
    fun h => h true false () () (fun h => nomatch h) ⟨rfl, rfl⟩ rfl ⟨rfl, rfl⟩⟩

private theorem omitWeak : OmitWeak :=
  ⟨fun h => h true false () () (fun h => nomatch h) ⟨rfl, rfl⟩ rfl ⟨rfl, rfl⟩,
    fun _ _ _ _ hMoves ⟨r', hMoved⟩ => ⟨r', hMoved, hMoves⟩,
    fun h => h true false () (fun h => nomatch h) ⟨rfl, rfl⟩ ⟨(), rfl⟩⟩

private theorem omitScope : OmitScope :=
  ⟨fun _ _ _ _ _ _ _ h => h.elim,
    fun h => (h true false () (fun h => nomatch h) ⟨rfl, rfl⟩ ⟨(), rfl⟩).elim fun _ h => h.2,
    fun h => h true false () (fun h => nomatch h) ⟨rfl, rfl⟩ ⟨(), rfl⟩⟩

private theorem omitNew : OmitNew :=
  ⟨fun h => (h true false rfl (fun h => nomatch h) ⟨rfl, rfl⟩ true () ⟨rfl, rfl⟩).elim fun _ h => h.1,
    fun _ _ => ⟨False.elim, fun h => h.1⟩,
    fun h => (h true false rfl (fun h => nomatch h) ⟨rfl, rfl⟩ ⟨true, (), rfl, rfl⟩).elim fun _ h => h⟩

private theorem omitMotion : OmitMotion :=
  ⟨fun _ _ _ _ hCaused _ _ _ => ⟨(), hCaused.2, hCaused.2⟩,
    fun h => ((h false ()).2 ⟨rfl, rfl⟩).elim,
    fun h => (h true false rfl (fun h => nomatch h) ⟨rfl, rfl⟩ ⟨true, (), rfl, rfl⟩).elim fun _ h => h⟩

private theorem omitPotency : OmitPotency :=
  ⟨fun h => (h true false rfl (fun h => nomatch h) ⟨rfl, rfl⟩ true () ⟨rfl, rfl⟩).elim fun _ h => h.1,
    fun _ _ _ _ _ h => h.elim,
    fun h => (h true false rfl (fun h => nomatch h) ⟨rfl, rfl⟩ true () ⟨rfl, rfl⟩).elim fun _ h => h.1⟩

private theorem omitActing : OmitActing :=
  ⟨fun _ _ _ _ hCaused _ _ _ => ⟨(), hCaused.2, hCaused.2⟩,
    fun h => h false true () () ⟨rfl, rfl⟩ rfl,
    fun h => (h true false rfl (fun h => nomatch h) ⟨rfl, rfl⟩ true () ⟨rfl, rfl⟩).elim fun _ h => h.2⟩

private theorem gradesWitness : GradesWitness :=
  ⟨⟨(), trivial⟩, fun _ _ => ⟨true, rfl⟩, fun _ _ _ h => h, ⟨false, rfl, fun h => nomatch h⟩,
    fun _ _ hx hz _ => ⟨hx, hz⟩, fun _ _ h => ⟨h, h⟩,
    ⟨⟨true, false, rfl, rfl⟩, ⟨true, false, rfl, rfl⟩, ⟨true, false, rfl, rfl⟩⟩⟩

private theorem notGradesNoMore : ¬ GradesFoundInThingsReading noMore () () () :=
  fun ⟨⟨_, _, h⟩, _⟩ => h

private theorem omitOccurs : OmitOccurs :=
  ⟨fun ⟨_, h⟩ => h, fun _ h => h.elim, fun _ _ h => h.elim, ⟨false, trivial, id⟩,
    fun _ _ h => h.elim, fun _ _ h => h.elim, notGradesNoMore⟩

private theorem omitSubject : OmitSubject :=
  ⟨⟨(), trivial⟩, fun h => (h () trivial).elim fun _ h => h, fun _ _ _ h => h.elim,
    ⟨false, trivial, id⟩, fun _ _ h => h.elim, fun _ _ h => h.elim, notGradesNoMore⟩

private theorem omitLives : OmitLives :=
  ⟨⟨(), trivial⟩, fun _ _ => ⟨true, rfl⟩, fun h => h true () trivial rfl, ⟨false, trivial, id⟩,
    fun _ _ h => h.elim, fun _ _ h => h.elim, notGradesNoMore⟩

private theorem omitStone : OmitStone :=
  ⟨⟨(), trivial⟩, fun _ _ => ⟨true, rfl⟩, fun _ _ _ _ => trivial,
    fun ⟨_, _, h⟩ => h trivial, fun _ _ _ _ h => (h trivial).elim, fun _ _ h => h.elim,
    notGradesNoMore⟩

private theorem omitNoble : OmitNoble :=
  ⟨⟨(), trivial⟩, fun _ _ => ⟨true, rfl⟩, fun _ _ _ h => h, ⟨false, rfl, fun h => nomatch h⟩,
    fun h => h true false rfl rfl (fun h => nomatch h), fun _ _ h => h.elim, notGradesNoMore⟩

private theorem omitConvert : OmitConvert :=
  ⟨⟨(), trivial⟩, fun _ _ => ⟨true, rfl⟩, fun _ _ _ h => h, ⟨false, rfl, fun h => nomatch h⟩,
    fun _ _ hx hz _ => ⟨rfl, hx, hz⟩,
    fun h => absurd (h true false ⟨rfl, rfl, rfl⟩).1.1 (fun h => nomatch h),
    fun ⟨⟨_, _, h⟩, _⟩ => absurd h.1 (fun h => nomatch h)⟩

/-- The batch controls (`MOTION-MAPS-BATCH1-CONTROLS`). -/
theorem controls : Certificate :=
  ⟨gradesWitness, omitInstrument, omitPrincipal, omitWeak, omitScope, omitNew, omitMotion,
    omitPotency, omitActing, omitOccurs, omitSubject, omitLives, omitStone, omitNoble,
    omitConvert⟩

end Controls

end TruthCore.Results.Causality.MotionMapsBatch1
