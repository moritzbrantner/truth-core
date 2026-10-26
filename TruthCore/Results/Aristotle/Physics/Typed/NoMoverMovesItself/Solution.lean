import TruthCore.Greek.Aristotle.Physics
import TruthCore.Greek.Aristotle.Physics.Typed.Motion
namespace TruthCore.Results.Aristotle.Physics.Typed.NoMoverMovesItself
open TruthCore.Greek.Aristotle.Physics
open TruthCore.Greek.Aristotle.Physics.Typed
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- No mover moves itself in the respect in which it moves. If `y` moved `y` in
`r`, then `y` would be in act in `r` (it moves only as in act), `y` would be being
moved in `r` (*Physics* III.3: the motion is in the moved), hence in potency in `r`
(*Physics* III.1: being moved is the actualization of a potency qua potency); but
nothing is in act and in potency in the same respect. -/
theorem noMoverMovesItself {Being : Type} {Respect : Type}
    (MovedIn InPotency ActualizedQuaPotential InAct : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (hAnalysis : BeingMovedIsActualizationOfPotencyReading MovedIn InPotency
      ActualizedQuaPotential)
    (hInMoved : MovingIsInTheMovedReading MovesIn MovedIn)
    (hInAct : MovesOnlyAsInActReading MovesIn InAct)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency) :
    NoMoverMovesItselfInItsRespectReading MovesIn := by
  -- INF-ARIST-PHYS-III-1-3-NO-MOVER-MOVES-ITSELF
  intro y x r hMoves hSame
  subst hSame
  have hAct : InAct y r := hInAct y y r hMoves
  have hMoved : MovedIn y r := hInMoved y y r hMoves
  have hPot : InPotency y r := ((hAnalysis y r).mp hMoved).1
  exact hNotBoth y r ⟨hAct, hPot⟩

/-- Each of the four premises is needed: dropping any one leaves a one-element
model of the other three in which something moves itself. -/
theorem premisesNeeded :
    (¬ ∀ (Being Respect : Type) (MovedIn InPotency InAct : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop),
      MovingIsInTheMovedReading MovesIn MovedIn →
      MovesOnlyAsInActReading MovesIn InAct →
      NotActAndPotencyInSameRespectReading InAct InPotency →
      NoMoverMovesItselfInItsRespectReading MovesIn) ∧
    (¬ ∀ (Being Respect : Type) (MovedIn InPotency ActualizedQuaPotential InAct :
        Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop),
      BeingMovedIsActualizationOfPotencyReading MovedIn InPotency ActualizedQuaPotential →
      MovesOnlyAsInActReading MovesIn InAct →
      NotActAndPotencyInSameRespectReading InAct InPotency →
      NoMoverMovesItselfInItsRespectReading MovesIn) ∧
    (¬ ∀ (Being Respect : Type) (MovedIn InPotency ActualizedQuaPotential InAct :
        Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop),
      BeingMovedIsActualizationOfPotencyReading MovedIn InPotency ActualizedQuaPotential →
      MovingIsInTheMovedReading MovesIn MovedIn →
      NotActAndPotencyInSameRespectReading InAct InPotency →
      NoMoverMovesItselfInItsRespectReading MovesIn) ∧
    (¬ ∀ (Being Respect : Type) (MovedIn InPotency ActualizedQuaPotential InAct :
        Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop),
      BeingMovedIsActualizationOfPotencyReading MovedIn InPotency ActualizedQuaPotential →
      MovingIsInTheMovedReading MovesIn MovedIn →
      MovesOnlyAsInActReading MovesIn InAct →
      NoMoverMovesItselfInItsRespectReading MovesIn) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- without III.1: moved and in act, but in no potency
    intro h
    exact h Unit Unit (fun _ _ => True) (fun _ _ => False)
      (fun _ _ => True) (fun _ _ _ => True)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ hb => hb.2)
      () () () trivial rfl
  · -- without III.3: it moves itself but nothing is being moved
    intro h
    exact h Unit Unit (fun _ _ => False) (fun _ _ => False) (fun _ _ => False)
      (fun _ _ => True) (fun _ _ _ => True)
      (fun _ _ => ⟨fun hm => hm.elim, fun hp => hp.1.elim⟩)
      (fun _ _ _ _ => trivial) (fun _ _ hb => hb.2)
      () () () trivial rfl
  · -- without act: moved and in potency, but in no act
    intro h
    exact h Unit Unit (fun _ _ => True) (fun _ _ => True) (fun _ _ => True)
      (fun _ _ => False) (fun _ _ _ => True)
      (fun _ _ => ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩)
      (fun _ _ _ _ => trivial) (fun _ _ hb => hb.1)
      () () () trivial rfl
  · -- without non-simultaneity: in act and in potency at once
    intro h
    exact h Unit Unit (fun _ _ => True) (fun _ _ => True) (fun _ _ => True)
      (fun _ _ => True) (fun _ _ _ => True)
      (fun _ _ => ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
      () () () trivial rfl

end TruthCore.Results.Aristotle.Physics.Typed.NoMoverMovesItself
