module

public import TruthCore.Causality.SelfMotionSeparation

@[expose] public section
namespace TruthCore.Results.Causality.SelfMotionSeparation
open TruthCore.Causality.SelfMotionSeparation

/-- Sufficient interface to the unchanged root consumer. Both bridges are OPEN. -/
theorem distinctPart {B : Type u} {C : Type v}
    (Part : B → B → Prop) (Moves : B → B → C → Prop)
    (Moved : B → C → Prop) (Integrated : B → B → B → C → Prop)
    (hParts : DiagonalHasWholeParts Part Moves Moved Integrated)
    (hTransfer : InternalMoverMovesWhole Part Moves Integrated) :
    TruthCore.Causality.CausalMapsBatch1.SelfMoverMovesByADistinctPart Moves Part := by
  intro x c h
  obtain ⟨p, q, hp, hpx, hq, hqx, hpq, hm, hi⟩ := (hParts x c ⟨h⟩).parts
  exact ⟨p, hp, hpx, hTransfer x p q c hp hpx hq hqx hpq hm hi⟩

/-- Explicit finite controls, including both missing-bridge counterexamples. -/
theorem controls : Control.Certificate := by
  have internal : WholeParts Control.Part Control.Internal Control.Moved
      Control.Integrated Control.Obj.whole () := by
    refine ⟨rfl, Control.Obj.motor, Control.Obj.limb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first | decide | (dsimp only [Control.Part, Control.Internal, Control.Lifted, Control.Integrated]; decide)
  have lifted : WholeParts Control.Part Control.Lifted Control.Moved
      Control.Integrated Control.Obj.whole () := by
    refine ⟨rfl, Control.Obj.motor, Control.Obj.limb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first | decide | (dsimp only [Control.Part, Control.Internal, Control.Lifted, Control.Integrated]; decide)
  refine ⟨⟨internal, ?_, ?_⟩, ⟨lifted, ?_, ?_⟩, ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · intro h; cases h.moves.1
  · intro ⟨p, _, h⟩; cases p <;> cases h.2
  · intro h; cases h.moves.1
  · exact ⟨rfl, Or.inr rfl⟩
  · exact ⟨rfl, rfl⟩
  · intro x p q c hp hpx hq hqx hpq hm hi
    exact False.elim (hpx (hm.1.trans hp.1.symm))
  · intro h
    obtain ⟨p, q, hp, hpx, hq, hqx, hpq, hm, hi⟩ := h.parts
    exact hpx (hm.1.trans hp.1.symm)
  · intro h
    obtain ⟨p, hp, hpx, hm⟩ := h Control.Obj.whole () ⟨rfl, rfl⟩
    exact hpx (hm.1.trans hp.1.symm)
  · intro x c h
    cases h.moves with
    | inl hi => cases hi.1.symm.trans hi.2
    | inr hd =>
      cases hd.1
      cases c
      refine ⟨rfl, Control.Obj.motor, Control.Obj.limb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        first | decide | (dsimp only [Control.Part, Control.Joined, Control.Internal, Control.Integrated]; decide)
  · intro h
    obtain ⟨p, hp, hpx, hm⟩ := h Control.Obj.whole () (Or.inr ⟨rfl, rfl⟩)
    cases hm with
    | inl hi => cases hi.2
    | inr hd => exact hpx (hd.1.trans hp.1.symm)
  · intro x c h
    cases h.moves with
    | inl hj =>
      cases hj with
      | inl hi => cases hi.1.symm.trans hi.2
      | inr hd =>
        cases hd.1
        cases c
        refine ⟨rfl, Control.Obj.motor, Control.Obj.limb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          first | decide | (dsimp only [Control.Part, Control.Full, Control.Joined, Control.Internal, Control.Integrated]; decide)
    | inr ht => cases ht.1.symm.trans ht.2
  · intro x p q c hp hpx hq hqx hpq hm hi
    exact Or.inr ⟨hi.2.1, hi.1⟩
  · exact ⟨Or.inl (Or.inr ⟨rfl, rfl⟩)⟩
  · intro h; exact h.whole_moved
  · intro h
    obtain ⟨p, q, hp, hpx, hq, hqx, hpq, hm, hi⟩ := h.parts
    exact hi

end TruthCore.Results.Causality.SelfMotionSeparation
