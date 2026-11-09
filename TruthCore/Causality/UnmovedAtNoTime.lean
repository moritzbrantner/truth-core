module

public import TruthCore.Results.Causality.TemporalPrimaVia.Controls.Solution

/-! UNMOVED_3 quantifies over the entire supplied clock and every supplied
respect. It asserts neither existence throughout time nor impossibility of
motion. The motion predicate retains the existing temporal prima via meaning;
its applicability to reality remains open. -/

@[expose] public section

namespace TruthCore.Causality.UnmovedAtNoTime

open TruthCore.Causality.TemporalPrimaVia
open TruthCore.Case.Catholicism

/-- Moved at no time: no reduction from potency to act in any respect at any
supplied time. No clock order, nonemptiness, motion or pure-act premise is added. -/
def MovedAtNoTime {B : Sort u} {R : Sort v} {T : Sort w}
    (Moved : T → B → R → Prop) (f : B) : Prop :=
  ∀ t r, ¬ Moved t f r

/-- All-time absence specializes at any selected time. -/
theorem at_time {B : Sort u} {R : Sort v} {T : Sort w}
    {Moved : T → B → R → Prop} {f : B} (h : MovedAtNoTime Moved f) (t : T) :
    ∀ r, ¬ Moved t f r := h t

/-- The already open bridge supplies exactly this predicate, without proving
that the bridge holds. -/
theorem of_slice_bridge {B R T : Type} {Moved : T → B → R → Prop}
    {Moves : T → B → B → R → Prop}
    (bridge : SliceFirstMoverMovedAtNoTimeBridge Moved Moves) (t : T) (f : B)
    (first : IsFirstUnmovedMover (Moved t) (Moves t) f) : MovedAtNoTime Moved f :=
  bridge t f first

/-- A nonvacuous positive control on the full integer clock: chain being 0
moves being 1 at time 0 and is never moved. This is a stipulated model only. -/
theorem chain_witness :
    (∃ x r, chainMoves 0 0 x r) ∧ MovedAtNoTime chainMoved 0 := by
  constructor
  · exact ⟨1, 1, by simp [chainMoves]⟩
  · intro t r moved
    exact moved.2.2 rfl

/-- The existing feedback model has a first mover at time 1 that is moved at
 time 2. Thus neither the time slice nor the time-free predicate instantiated
at that slice supplies all-time absence. -/
theorem feedback_separation :
    IsFirstUnmovedMover (fbMoved 1) (fbMoves 1) false ∧
    ¬ MovedAtNoTime fbMoved false := by
  constructor
  · exact TruthCore.Results.Causality.TemporalPrimaVia.Controls.feedback.2.2.1
  · intro never
    exact never 2 true (Or.inr ⟨rfl, rfl, rfl⟩)

end TruthCore.Causality.UnmovedAtNoTime
