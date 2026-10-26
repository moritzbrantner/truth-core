import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3Interpretation
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question5.Article1
import TruthCore.Greek.Aristotle.MetaphysicsIX
import TruthCore.Greek.Aristotle.Physics

/-!
The act/potency premises shared by every root route of the case (#352), taken
together as one typed theory, and formal facts about how they hang together.

**Vocabulary.** One `ActPotencyModel` interprets every act/potency predicate
the case uses at once, with the same types and parameters as the source
readings it collects:

* `Being`, `Respect` — beings, and the respects (perfections) in which a being
  is in act, in potency or moved; `esse` is the respect of being.
* `InAct x r`, `InPotency x r` — `x` is in act / in potency in respect `r`.
* `MovedIn x r`, `MovesIn y x r` — motion as reduction from potency to act
  (`DEF-MOTION-AS-REDUCTION`).
* `PriorSimply y x` — `y` is simply prior to `x` (ST I q.3 a.1).
* `GoodIn x r` — `x` is good in respect `r` (ST I q.5 a.1, with `Has := InAct`
  as in the case's attribute proofs).
* `MovesAsMoved y x` — `y` moves `x` only as moved (the per se link).

Every predicate is a primitive of the model, never a definition. In particular
`InPotency` is **not** defined as "able but not actual", and `MovedIn` is not
defined as "potential and being actualized": either definition would make one
of the premises below analytic (`ActPotencyDefinitionalAnalysesConservative`).

**Premises.** The eight target premises of #352 are the source readings
`NotActAndPotencyInSameRespectReading` (1), `ActualityOnlyInsofarAsBeingReading`
(2), `ActSimplyPriorToPotencyReading` (3), `GoodnessIsActualityReading` (4),
`MovesOnlyAsInActReading` (5), `ReducedOnlyByAMoverReading` (6),
`MovedOnlyAsInPotencyReading` (7) and `SecondMoversMoveOnlyAsMovedReading` (8),
read in one model. The *prima via*'s observation premise
(`SomethingIsMovedReading`) and regress premise
(`NoInfinitePerSeMoverSeriesReading`) are added to every model, so that the
facts below hold in worlds that contain motion.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

open TruthCore.Greek.Aristotle.Metaphysics (PotencyIsUnactualizedCapacityReading)
open TruthCore.Greek.Aristotle.Physics (BeingMovedIsActualizationOfPotencyReading)

/-- One interpretation of all the act/potency vocabulary of the case. -/
structure ActPotencyModel where
  Being : Type
  Respect : Type
  esse : Respect
  InAct : Being → Respect → Prop
  InPotency : Being → Respect → Prop
  MovedIn : Being → Respect → Prop
  MovesIn : Being → Being → Respect → Prop
  PriorSimply : Being → Being → Prop
  GoodIn : Being → Respect → Prop
  MovesAsMoved : Being → Being → Prop

namespace ActPotencyModel

variable (M : ActPotencyModel)

/-- Something is being moved (*sensu constat*). -/
def Sense : Prop := SomethingIsMovedReading M.MovedIn

/-- The per se series of moved movers is well-founded. -/
def Regress : Prop := NoInfinitePerSeMoverSeriesReading M.MovesAsMoved

/-- (1) Nothing is in act and in potency in the same respect. -/
def NonSimultaneity : Prop := NotActAndPotencyInSameRespectReading M.InAct M.InPotency

/-- (2) Whatever is in act in some respect has being. -/
def ActualityAsBeing : Prop := ActualityOnlyInsofarAsBeingReading M.InAct M.esse

/-- (3) Whatever is in potency in a respect is simply posterior to a being in
act in it. -/
def ActPrior : Prop := ActSimplyPriorToPotencyReading M.InAct M.InPotency M.PriorSimply

/-- (4) Good in a respect exactly when in act in it. -/
def GoodnessAsAct : Prop := GoodnessIsActualityReading M.GoodIn M.InAct

/-- (5) A mover is in act in the respect in which it moves. -/
def MoverInAct : Prop := MovesOnlyAsInActReading M.MovesIn M.InAct

/-- (6) Whatever is moved has a mover in that respect. -/
def HasMover : Prop := ReducedOnlyByAMoverReading M.MovedIn M.MovesIn

/-- (7) Whatever is moved in a respect is in potency in it. -/
def MovedInPotency : Prop := MovedOnlyAsInPotencyReading M.MovedIn M.InPotency

/-- (8) A moved mover other than the moved thing is a per se link. -/
def SecondMovers : Prop :=
  SecondMoversMoveOnlyAsMovedReading M.MovedIn M.MovesIn M.MovesAsMoved

end ActPotencyModel

open ActPotencyModel in
/-- Formal fact: none of the eight act/potency premises of #352 follows from
the other seven, even together with the observation that something is moved
and the well-foundedness of the per se series. For each premise there is a
model of all the others in which it fails.

This is independence from the *tested* premises only: no target premise is
derivable from the other seven (with sensible motion and the well-founded
series). It does not show that a derivation needs new vocabulary. Further
premises over the same predicates could suffice; for example
`InPotency x r → MovedIn x r` and `MovesIn y x r → PriorSimply y x`, with
`HasMover` and `MoverInAct`, entail `ActPrior`. Any such added premise is
itself a new open premise. -/
def ActPotencyPremisesIndependent : Prop :=
  (¬ ∀ M : ActPotencyModel, M.Sense → M.Regress → M.ActualityAsBeing → M.ActPrior →
      M.GoodnessAsAct → M.MoverInAct → M.HasMover → M.MovedInPotency →
      M.SecondMovers → M.NonSimultaneity) ∧
  (¬ ∀ M : ActPotencyModel, M.Sense → M.Regress → M.NonSimultaneity → M.ActPrior →
      M.GoodnessAsAct → M.MoverInAct → M.HasMover → M.MovedInPotency →
      M.SecondMovers → M.ActualityAsBeing) ∧
  (¬ ∀ M : ActPotencyModel, M.Sense → M.Regress → M.NonSimultaneity →
      M.ActualityAsBeing → M.GoodnessAsAct → M.MoverInAct → M.HasMover →
      M.MovedInPotency → M.SecondMovers → M.ActPrior) ∧
  (¬ ∀ M : ActPotencyModel, M.Sense → M.Regress → M.NonSimultaneity →
      M.ActualityAsBeing → M.ActPrior → M.MoverInAct → M.HasMover →
      M.MovedInPotency → M.SecondMovers → M.GoodnessAsAct) ∧
  (¬ ∀ M : ActPotencyModel, M.Sense → M.Regress → M.NonSimultaneity →
      M.ActualityAsBeing → M.ActPrior → M.GoodnessAsAct → M.HasMover →
      M.MovedInPotency → M.SecondMovers → M.MoverInAct) ∧
  (¬ ∀ M : ActPotencyModel, M.Sense → M.Regress → M.NonSimultaneity →
      M.ActualityAsBeing → M.ActPrior → M.GoodnessAsAct → M.MoverInAct →
      M.MovedInPotency → M.SecondMovers → M.HasMover) ∧
  (¬ ∀ M : ActPotencyModel, M.Sense → M.Regress → M.NonSimultaneity →
      M.ActualityAsBeing → M.ActPrior → M.GoodnessAsAct → M.MoverInAct →
      M.HasMover → M.SecondMovers → M.MovedInPotency) ∧
  (¬ ∀ M : ActPotencyModel, M.Sense → M.Regress → M.NonSimultaneity →
      M.ActualityAsBeing → M.ActPrior → M.GoodnessAsAct → M.MoverInAct →
      M.HasMover → M.MovedInPotency → M.SecondMovers)

/-- Formal fact, the guard against definitional smuggling (#352): the two
definitional analyses of potency and of being moved make premises (1) and (7)
analytic, and they are *conservative* over them.

* Θ.6's analysis (`PotencyIsUnactualizedCapacityReading`: potency in `r` is
  ability for `r` without act in `r`) entails non-simultaneity; and whenever
  non-simultaneity holds, some ability predicate satisfies the analysis
  (take ability to be potency itself).
* Physics III.1's analysis (`BeingMovedIsActualizationOfPotencyReading`: being
  moved in `r` is being potentially `r` with that potency being actualized)
  entails that whatever is moved is in potency; and whenever that premise holds,
  some actualization predicate satisfies the analysis (take it to be being
  moved).

So adopting either definition does not discharge the premise it makes analytic.
The open question only moves to the definition's fidelity, and the definition
says more than the premise only once its new primitive (`CanBe`,
`ActualizedQuaPotential`) is constrained by further sourced axioms. -/
def ActPotencyDefinitionalAnalysesConservative : Prop :=
  (∀ (Being Respect : Type) (InAct InPotency CanBe : Being → Respect → Prop),
      PotencyIsUnactualizedCapacityReading InAct InPotency CanBe →
      NotActAndPotencyInSameRespectReading InAct InPotency) ∧
  (∀ (Being Respect : Type) (InAct InPotency : Being → Respect → Prop),
      NotActAndPotencyInSameRespectReading InAct InPotency →
      ∃ CanBe : Being → Respect → Prop,
        PotencyIsUnactualizedCapacityReading InAct InPotency CanBe) ∧
  (∀ (Being Respect : Type) (MovedIn InPotency ActualizedQuaPotential : Being → Respect → Prop),
      BeingMovedIsActualizationOfPotencyReading MovedIn InPotency ActualizedQuaPotential →
      MovedOnlyAsInPotencyReading MovedIn InPotency) ∧
  (∀ (Being Respect : Type) (MovedIn InPotency : Being → Respect → Prop),
      MovedOnlyAsInPotencyReading MovedIn InPotency →
      ∃ ActualizedQuaPotential : Being → Respect → Prop,
        BeingMovedIsActualizationOfPotencyReading MovedIn InPotency ActualizedQuaPotential)

/-- Formal fact about the literal reading of *nisi per aliquod ens in actu*
(`ReducedOnlyByABeingInActReading`):

* the case's two premises "whatever is moved has a mover" and "every mover is in
  act in the respect" together entail it;
* it entails "whatever is moved has a mover";
* it does not entail "every mover is in act": a moved thing may have one mover
  in act and another not;
* even with every *prima via* premise it does not entail act's simple priority
  (ST I q.3 a.1), although Aquinas gives it as the reason for that priority: a
  being may be in potency in a respect in which nothing is moved and nothing is
  in act. -/
def BeingInActReadingFacts : Prop :=
  (∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop) (InAct : Being → Respect → Prop),
      ReducedOnlyByAMoverReading MovedIn MovesIn →
      MovesOnlyAsInActReading MovesIn InAct →
      ReducedOnlyByABeingInActReading MovedIn MovesIn InAct) ∧
  (∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop) (InAct : Being → Respect → Prop),
      ReducedOnlyByABeingInActReading MovedIn MovesIn InAct →
      ReducedOnlyByAMoverReading MovedIn MovesIn) ∧
  (¬ ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop) (InAct : Being → Respect → Prop),
      ReducedOnlyByABeingInActReading MovedIn MovesIn InAct →
      MovesOnlyAsInActReading MovesIn InAct) ∧
  (¬ ∀ M : ActPotencyModel, M.Sense → M.Regress → M.NonSimultaneity →
      M.MoverInAct → M.HasMover → M.MovedInPotency → M.SecondMovers →
      ReducedOnlyByABeingInActReading M.MovedIn M.MovesIn M.InAct → M.ActPrior)

/-- Formal fact: each premise of the *prima via* from the being-in-act reading
(`PrimaViaFromBeingInAct.primaViaFromBeingInAct`: sensible motion, moved only as
in potency, reduced only by a being in act, non-simultaneity, second movers,
no infinite per se series) is needed. Dropping any one leaves a model of the
others in which there is no mover moved by none. The models reuse
`MotionModel` and ignore its `RelevantTo` field. -/
def PrimaViaFromBeingInActPremisesNeeded : Prop :=
  (¬ ∀ M : MotionModel,
      MovedOnlyAsInPotencyReading M.MovedIn M.InPotency →
      ReducedOnlyByABeingInActReading M.MovedIn M.MovesIn M.InAct →
      NotActAndPotencyInSameRespectReading M.InAct M.InPotency →
      SecondMoversMoveOnlyAsMovedReading M.MovedIn M.MovesIn M.MovesAsMoved →
      NoInfinitePerSeMoverSeriesReading M.MovesAsMoved → AbsoluteConclusion M) ∧
  (¬ ∀ M : MotionModel,
      SomethingIsMovedReading M.MovedIn →
      ReducedOnlyByABeingInActReading M.MovedIn M.MovesIn M.InAct →
      NotActAndPotencyInSameRespectReading M.InAct M.InPotency →
      SecondMoversMoveOnlyAsMovedReading M.MovedIn M.MovesIn M.MovesAsMoved →
      NoInfinitePerSeMoverSeriesReading M.MovesAsMoved → AbsoluteConclusion M) ∧
  (¬ ∀ M : MotionModel,
      SomethingIsMovedReading M.MovedIn →
      MovedOnlyAsInPotencyReading M.MovedIn M.InPotency →
      NotActAndPotencyInSameRespectReading M.InAct M.InPotency →
      SecondMoversMoveOnlyAsMovedReading M.MovedIn M.MovesIn M.MovesAsMoved →
      NoInfinitePerSeMoverSeriesReading M.MovesAsMoved → AbsoluteConclusion M) ∧
  (¬ ∀ M : MotionModel,
      SomethingIsMovedReading M.MovedIn →
      MovedOnlyAsInPotencyReading M.MovedIn M.InPotency →
      ReducedOnlyByABeingInActReading M.MovedIn M.MovesIn M.InAct →
      SecondMoversMoveOnlyAsMovedReading M.MovedIn M.MovesIn M.MovesAsMoved →
      NoInfinitePerSeMoverSeriesReading M.MovesAsMoved → AbsoluteConclusion M) ∧
  (¬ ∀ M : MotionModel,
      SomethingIsMovedReading M.MovedIn →
      MovedOnlyAsInPotencyReading M.MovedIn M.InPotency →
      ReducedOnlyByABeingInActReading M.MovedIn M.MovesIn M.InAct →
      NotActAndPotencyInSameRespectReading M.InAct M.InPotency →
      NoInfinitePerSeMoverSeriesReading M.MovesAsMoved → AbsoluteConclusion M) ∧
  (¬ ∀ M : MotionModel,
      SomethingIsMovedReading M.MovedIn →
      MovedOnlyAsInPotencyReading M.MovedIn M.InPotency →
      ReducedOnlyByABeingInActReading M.MovedIn M.MovesIn M.InAct →
      NotActAndPotencyInSameRespectReading M.InAct M.InPotency →
      SecondMoversMoveOnlyAsMovedReading M.MovedIn M.MovesIn M.MovesAsMoved →
      AbsoluteConclusion M)

end TruthCore.Latin.Aquinas.SummaTheologiae
