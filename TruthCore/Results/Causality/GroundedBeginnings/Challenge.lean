import TruthCore.Causality.GroundedBeginnings
import TruthCore.Results.Causality.InertEmptiness.Solution
import TruthCore.Results.Causality.BegunComingToBe.Solution

namespace TruthCore.Results.Causality.GroundedBeginnings
open TruthCore.Causality.GroundedBeginnings
open TruthCore.Causality.InertEmptiness (EmptinessStaysEmpty ConcreteEmptyAt)
open TruthCore.Modal.TemporalHistory (History)

/-- Traced "from nothing, nothing comes" from three principles about grounds.
Fix a history `v` and an earlier moment `s`, and walk down the grounds of a
concrete thing present after `s` by well-founded induction: a thing present at
`s` ends the chain; a thing absent at `s` has begun, so it has a concrete
ground, which is present at `s` (ending the chain) or at some moment after `s`
(where the induction hypothesis applies). -/
theorem nothingFromNothing {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (grounds : W → B → B → Prop)
    (hBegin : BeginningsGrounded h Concrete grounds)
    (hNotCeased : GroundsNotCeasedBeforeAbsence h Concrete grounds)
    (hWF : PresentGroundingWellFounded h Concrete grounds) :
    NothingFromNothing h Concrete grounds := by
  sorry

/-- The traced form strengthens inert emptiness (premise A2): it puts a
concrete thing at every moment earlier than a populated one. -/
theorem inertOfNothingFromNothing {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (grounds : W → B → B → Prop)
    (hTraced : NothingFromNothing h Concrete grounds) :
    EmptinessStaysEmpty h Concrete := by
  sorry

/-- Inert emptiness (premise A2) from the three grounding principles, through
the traced form. -/
theorem inertOfGroundedBeginnings {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (grounds : W → B → B → Prop)
    (hBegin : BeginningsGrounded h Concrete grounds)
    (hNotCeased : GroundsNotCeasedBeforeAbsence h Concrete grounds)
    (hWF : PresentGroundingWellFounded h Concrete grounds) :
    EmptinessStaysEmpty h Concrete := by
  sorry

open TruthCore.Causality.InertEmptiness.Control (exNihilo initialState rooted all)
open TruthCore.Causality.BegunComingToBe.Control (zeno predecessorGrounds)

/-- Omission, strictness, no-re-import and nonvacuity controls. Facts about
`exNihilo`, `initialState`, `rooted` and `zeno` already checked in
`InertEmptiness.controls` and `BegunComingToBe.controls` are reused. -/
theorem controls : Control.Certificate := by
  sorry

end TruthCore.Results.Causality.GroundedBeginnings
