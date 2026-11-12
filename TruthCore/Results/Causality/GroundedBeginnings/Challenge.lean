import TruthCore.Causality.GroundedBeginnings
import TruthCore.Results.Causality.InertEmptiness.Solution
import TruthCore.Results.Causality.BegunComingToBe.Solution

namespace TruthCore.Results.Causality.GroundedBeginnings
open TruthCore.Causality.GroundedBeginnings
open TruthCore.Causality.InertEmptiness (EmptinessStaysEmpty ConcreteEmptyAt)
open TruthCore.Modal.TemporalHistory (History)

/-- Traced "from nothing, nothing comes" from two principles about grounds.
Fix a history `v` and an earlier moment `s`, and walk down grounds by
well-founded induction among things that come to be after `s`: a thing present
at `s` ends the chain; a thing absent at `s` has begun, so it has a concrete
ground present at `s` (ending the chain) or, absent at `s`, present at some
moment after `s`, where the induction hypothesis applies. -/
theorem nothingFromNothing {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (grounds : W → B → B → Prop)
    (hLasting : BeginningsHaveLastingGround h Concrete grounds)
    (hWF : PostAbsenceGroundingWellFounded h Concrete grounds) :
    NothingFromNothing h Concrete grounds := by
  sorry

/-- The traced form strengthens inert emptiness (premise A2): it puts a
concrete thing at every moment earlier than a populated one. -/
theorem inertOfNothingFromNothing {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (grounds : W → B → B → Prop)
    (hTraced : NothingFromNothing h Concrete grounds) :
    EmptinessStaysEmpty h Concrete := by
  sorry

/-- Inert emptiness (premise A2) from the two grounding principles, through
the traced form. -/
theorem inertOfGroundedBeginnings {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (grounds : W → B → B → Prop)
    (hLasting : BeginningsHaveLastingGround h Concrete grounds)
    (hWF : PostAbsenceGroundingWellFounded h Concrete grounds) :
    EmptinessStaysEmpty h Concrete := by
  sorry

/-- Well-founded grounding among all present concrete things gives it among
those that come to be after any moment: the latter relation is a subrelation. -/
theorem postAbsenceOfPresent {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (grounds : W → B → B → Prop)
    (hWF : PresentGroundingWellFounded h Concrete grounds) :
    PostAbsenceGroundingWellFounded h Concrete grounds := by
  sorry

open TruthCore.Causality.InertEmptiness.Control (exNihilo initialState rooted all)
open TruthCore.Causality.BegunComingToBe.Control (zeno predecessorGrounds)

/-- Omission, strictness, no-modal-content and nonvacuity controls. Facts about
`exNihilo`, `initialState`, `rooted` and `zeno` already checked in
`InertEmptiness.controls` and `BegunComingToBe.controls` are reused. -/
theorem controls : Control.Certificate := by
  sorry

end TruthCore.Results.Causality.GroundedBeginnings
