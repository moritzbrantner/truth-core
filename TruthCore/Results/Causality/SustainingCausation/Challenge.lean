import TruthCore.Causality.SustainingCausation

namespace TruthCore.Results.Causality.SustainingCausation
open TruthCore.Causality.SustainingCausation
open TruthCore.Causality.GroundedBeginnings (BeginningsHaveLastingGround)
open TruthCore.Causality.DeiFiliusAttributeField (Primitives)
open TruthCore.Causality.DeiFiliusImmenseIncomprehensible
  (IsImmenseAsInfiniteCauseOfAll InfiniteCauseOfAllIsImmense)
open TruthCore.Modal.TemporalHistory (History)

/-- From the contact principle: whatever sustains every other thing is present,
by giving it being, to every other thing at every moment at which that thing is
present. The sustainer gives `x` being at each such `t`, and a giver is present
when it gives. -/
theorem sustainerOfAllIsPresentToAll {W B T : Type} (h : History W B T)
    (G : BeingGiving W B T) (hContact : GiverPresentWhenGiving h G) :
    SustainerOfAllIsPresentToAll h G := by
  sorry

/-- The presence step of the immensity sense bridge, derived: whatever is
IMMENSE_2 is, in every history, present by giving being to every other thing
whenever it is. Its creator conjunct makes it a cause of the being of every
other thing in act as to being; what is present is in act as to being; the
sustaining reading turns each such cause into a sustainer; and the contact
principle puts the sustainer at each moment at which its effect is. The
infinity conjunct is not used. -/
theorem immense2PresentToAll {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (InAct : B → Respect → Prop) (CausesIn : B → B → Respect → Prop)
    (esse : Respect) (Infinite : B → Prop)
    (hSustaining : CausingBeingIsSustaining h G CausesIn esse)
    (hInAct : PresentIsInActAsToBeing h InAct esse)
    (hContact : GiverPresentWhenGiving h G) :
    Immense2PresentToAll h G InAct CausesIn esse Infinite := by
  sorry

/-- The immensity sense bridge IMMENSE_2 → IMMENSE_1 (`8bf775e9`) from the typed
presence step and the narrowed bridge that carries the rest (place,
containment, measure, the other modes of presence, immediacy). -/
theorem immenseSenseBridgeOfSustainingPresence {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (InAct : B → Respect → Prop) (CausesIn : B → B → Respect → Prop)
    (esse : Respect) (Infinite : B → Prop) (D : Primitives B)
    (hSustaining : CausingBeingIsSustaining h G CausesIn esse)
    (hInAct : PresentIsInActAsToBeing h InAct esse)
    (hContact : GiverPresentWhenGiving h G)
    (hNarrow : PresentInfiniteCauseOfAllIsImmense h G InAct CausesIn esse Infinite D) :
    InfiniteCauseOfAllIsImmense InAct CausesIn esse Infinite D := by
  sorry

/-- Strength order: the immensity sense bridge entails its narrowed form, whose
antecedent adds presence to all. -/
theorem narrowedOfImmenseSenseBridge {W B T Respect : Type} (h : History W B T)
    (G : BeingGiving W B T) (InAct : B → Respect → Prop) (CausesIn : B → B → Respect → Prop)
    (esse : Respect) (Infinite : B → Prop) (D : Primitives B)
    (hBridge : InfiniteCauseOfAllIsImmense InAct CausesIn esse Infinite D) :
    PresentInfiniteCauseOfAllIsImmense h G InAct CausesIn esse Infinite D := by
  sorry

/-- Lasting ground (A2ab) from sustaining causes. A concrete thing absent at `s`
and present at `t > s` has a concrete sustaining cause; it gives the thing being
at `t`, so by the contact principle it is present at `t`, which is after `s`;
and it is a ground. -/
theorem lastingGroundOfSustainingCauses {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (G : BeingGiving W B T) (grounds : W → B → B → Prop)
    (hCause : BeginningsHaveSustainingCause h Concrete G)
    (hGround : SustainersAreGrounds h G grounds)
    (hContact : GiverPresentWhenGiving h G) :
    BeginningsHaveLastingGround h Concrete grounds := by
  sorry

/-- Lasting ground (A2ab) from originating causes, given that any two moments
are comparable and concrete presence has no gaps. A concrete thing absent at `s`
and present at `t > s` has a concrete originating cause, which gives it being at
a first moment `b` of its presence and so (contact) is present at `b`. The moment
`b` is not `s` (the thing is absent at `s`) and not before `s` (it would then be
present at `b` and `t` and absent between them), so it is after `s`. -/
theorem lastingGroundOfOriginatingCauses {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (G : BeingGiving W B T) (grounds : W → B → B → Prop)
    (hCause : BeginningsHaveOriginatingCause h Concrete G)
    (hGround : OriginatorsAreGrounds h G grounds)
    (hContact : GiverPresentWhenGiving h G)
    (hConvex : ConcretePresenceConvex h Concrete)
    (hTri : TimesTrichotomous T) :
    BeginningsHaveLastingGround h Concrete grounds := by
  sorry

open TruthCore.Causality.SustainingCausation.Control

/-- Omission, rival-reading and nonvacuity controls (`Control.Certificate`). -/
theorem controls : Control.Certificate := by
  sorry

end TruthCore.Results.Causality.SustainingCausation
