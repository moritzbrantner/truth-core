import TruthCore.Latin.Aquinas.InMetaphysicam.BookIX
import TruthCore.Causality.TemporalPrimaVia
import TruthCore.Results.Causality.TemporalPrimaVia.Controls.Solution
namespace TruthCore.Results.Aquinas.InMetaphysicam.PrimumMovensPureAct
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct)
open TruthCore.Latin.Aquinas.InMetaphysicam (MoverMovedAtNoTimeIsInActOnlyReading)
open TruthCore.Causality.TemporalPrimaVia
open TruthCore.Case.Catholicism (FirstUnmovedMoverIsPureAct IsFirstUnmovedMover)

theorem primumMovensPureAct {B R T : Type} (Moved InPotency : T → B → R → Prop)
    (Moves : T → B → B → R → Prop)
    (hInActOnly : MoverMovedAtNoTimeIsInActOnlyReading Moved Moves InPotency)
    (hBridge : SliceFirstMoverMovedAtNoTimeBridge Moved Moves) (t : T) :
    FirstUnmovedMoverIsPureAct (Moved t) (Moves t) (PureAct (InPotency t)) := by
  intro f hFirst
  exact hInActOnly t f hFirst.1 (hBridge t f hFirst)

theorem primumMovensFacts :
    (¬ ∀ (B R T : Type) (Moved InPotency : T → B → R → Prop)
      (Moves : T → B → B → R → Prop),
      MoverMovedAtNoTimeIsInActOnlyReading Moved Moves InPotency →
      ∀ t, FirstUnmovedMoverIsPureAct (Moved t) (Moves t) (PureAct (InPotency t))) ∧
    (¬ ∀ (B R T : Type) (Moved InPotency : T → B → R → Prop)
      (Moves : T → B → B → R → Prop),
      SliceFirstMoverMovedAtNoTimeBridge Moved Moves →
      ∀ t, FirstUnmovedMoverIsPureAct (Moved t) (Moves t) (PureAct (InPotency t))) ∧
    (∃ (B R T : Type) (Moved InPotency : T → B → R → Prop)
      (Moves : T → B → B → R → Prop),
      MoverMovedAtNoTimeIsInActOnlyReading Moved Moves InPotency ∧
      SliceFirstMoverMovedAtNoTimeBridge Moved Moves ∧
      ∃ t f, IsFirstUnmovedMover (Moved t) (Moves t) f) := by
  obtain ⟨_, _, _, _, neverMoved, notPure⟩ := TruthCore.Results.Causality.TemporalPrimaVia.Controls.feedback
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply notPure
    refine h _ _ _ fbMoved fbPotency fbMoves ?_ 1
    intro t f moves unmoved
    obtain ⟨x, r, hMoves⟩ := moves
    exact absurd ⟨f, ⟨t, x, r, hMoves⟩, unmoved⟩ neverMoved
  · intro h
    have pure := h Unit Unit Unit (fun _ _ _ => False) (fun _ _ _ => True)
      (fun _ _ _ _ => True) (fun _ _ hFirst _ _ moved => moved) ()
    exact pure () ⟨⟨(), (), trivial⟩, fun _ moved => moved⟩ () trivial
  · refine ⟨Unit, Unit, Unit, fun _ _ _ => False, fun _ _ _ => False,
      fun _ _ _ _ => True, ?_, ?_, (), (), ⟨(), (), trivial⟩, fun _ moved => moved⟩
    · intro _ _ _ _ _ potency
      exact potency
    · intro _ _ _ _ _ moved
      exact moved
end TruthCore.Results.Aquinas.InMetaphysicam.PrimumMovensPureAct
