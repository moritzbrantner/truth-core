import TruthCore.Results.Modal.S4.Laws.Solution
namespace TruthCore.Results.Modal.S4.Countermodels
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite
open TruthCore.Modal.S4Research
open TruthCore.Modal.KResearch (PossibilityActuality)
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)
open TruthCore.Modern.Hume.Conceivability (Contingent)

theorem reflexive (paired : Bool) : Reflexive (pockets paired).frame := by
  intro w; cases w <;> rfl

theorem transitive (paired : Bool) : Transitive (pockets paired).frame := by
  intro w v z h₁ h₂
  cases paired <;> cases w <;> cases v <;> cases z <;>
    first | rfl | exact h₂ | exact h₁ | exact Bool.noConfusion h₁ | exact Bool.noConfusion h₂

theorem left_collapse (paired : Bool) (D : Domain World) :
    MC (pockets paired).frame D .left := by
  intro P _ hp v hv
  cases v with
  | root => cases hv
  | left => exact hp
  | right => cases hv
  | twin => cases hv

theorem root_not_language (paired : Bool) :
    ¬ MC (pockets paired).frame (language paired) .root := by
  intro h
  have hd : language paired (fun w => Holds (pockets paired).frame
      (pockets paired).valuation w (.neg (.atom false))) := ⟨.neg (.atom false), rfl⟩
  have hr : Holds (pockets paired).frame (pockets paired).valuation .root
      (.neg (.atom false)) := by intro hf; cases hf
  exact h _ hd hr .left rfl rfl

theorem root_not_full (paired : Bool) : ¬ MC (pockets paired).frame allPredicates .root := by
  intro h
  exact root_not_language paired (restrict _ allPredicates (language paired) .root
    (fun _ _ => trivial) h)

theorem p_expressible (paired : Bool) : language paired p := ⟨.atom false, rfl⟩

theorem root_contingent (paired : Bool) : Contingent (pockets paired).frame p .root := by
  exact ⟨⟨.left, rfl, rfl⟩, ⟨.root, rfl, by intro h; cases h⟩⟩

theorem not_actuality (paired : Bool) (D : Domain World) (hp : D p) :
    ¬ PossibilityActuality (pockets paired).frame D .root := by
  intro h
  exact Bool.noConfusion (h p hp ⟨.left, rfl, rfl⟩)

/-- Even an accessible world with necessary full collapse does not remove root branching. -/
theorem possible_necessary (paired : Bool) : Dia (pockets paired).frame
    (Box (pockets paired).frame (MC (pockets paired).frame allPredicates)) .root := by
  exact ⟨.left, rfl, Laws.necessary _ _ (left_collapse paired allPredicates)⟩

theorem checks : Countermodels := by
  intro paired
  refine ⟨⟨reflexive paired, transitive paired⟩, ?_, ?_,
    left_collapse paired allPredicates, left_collapse paired (language paired),
    ⟨.left, rfl, left_collapse paired allPredicates⟩,
    ⟨.left, rfl, left_collapse paired (language paired)⟩,
    root_not_full paired, root_not_language paired, ?_, ?_, root_contingent paired,
    not_actuality paired allPredicates trivial,
    not_actuality paired (language paired) (p_expressible paired)⟩
  · intro h; exact Bool.noConfusion (h .root .left rfl)
  · intro h; exact Bool.noConfusion (h .root .left .root rfl rfl)
  · intro h; exact root_not_full paired (h .root rfl)
  · intro h; exact root_not_language paired (h .root rfl)
end TruthCore.Results.Modal.S4.Countermodels
