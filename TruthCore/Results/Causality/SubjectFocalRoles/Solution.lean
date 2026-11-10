module
public import TruthCore.Causality.SubjectFocalRoles
@[expose] public section
namespace TruthCore.Results.Causality.SubjectFocalRoles
open TruthCore.Causality.SubjectFocalRoles
open TruthCore.Latin.Aquinas.SummaTheologiae

theorem roleDiversity : RoleDiversity := by
  intro B E S I h
  have hd : ∀ x, Secondary S I x → ¬ S x := by
    rintro x ⟨s, _, hxs⟩
    exact (h.2.1 x s hxs).2.2.1
  refine ⟨hd, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := h.2.2.1
    exact ⟨s, hs, fun hx => hd s hx hs⟩
  · obtain ⟨x, hx⟩ := h.2.2.2
    exact ⟨x, hx, hd x hx⟩

/-- Immediate composition of explicit bridges; a transcription, not a new
independent derivation of efficient causality from focal semantics. -/
theorem orderedFromBridges {B : Type} (S : B → Prop) (I : B → B → Prop)
    (Creature : B → Prop) (CausesIn : B → B → Unit → Prop) (p : B)
    (hCreature : CreatureSubjectBridge S I Creature)
    (hCenter : CommonCenter S I p) (hCause : SubjectCauseBridge I CausesIn) :
    OrderedToPrimaryAsCauseReading (HasBeing S I) CausesIn Creature () p := by
  intro x hx _
  exact hCause x p (hCenter.2 x (hCreature x hx))

theorem controls : Controls := by
  unfold Controls
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp only [SubjectFocalReading, Account, Secondary, CommonCenter,
    CreatureSubjectBridge, SubjectCauseBridge, HasBeing, DegreeComparable, Calibration,
    ApproachToPrimaryReading, OrderedToPrimaryAsCauseReading,
    Control.existsAt, Control.substance, Control.common, Control.split, Control.creature,
    Control.noCause, Control.subjectCause, Control.splitCause, Control.partialNear, Control.totalNear,
    Control.totalMore, Control.noMore]
  all_goals decide
end TruthCore.Results.Causality.SubjectFocalRoles
