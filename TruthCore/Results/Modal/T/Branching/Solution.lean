import TruthCore.Modal.TResearch
namespace TruthCore.Results.Modal.T.Branching
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite
open TruthCore.Modal.TResearch
open TruthCore.Modal.KResearch (PossibilityActuality)
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)

theorem reflexive : Reflexive branching.frame := by
  intro w; cases w <;> rfl

theorem endpoint (D : Domain Bool) : MC branching.frame D true := by
  intro P _ hp v hv
  cases v with
  | false => cases hv
  | true => exact hp

theorem language_extensional : PropositionalExtensionality branchingLanguage := by
  intro w v h
  have ha := h (fun x => Holds branching.frame branching.valuation x (.atom ()))
    ⟨.atom (), rfl⟩
  cases w <;> cases v
  · rfl
  · exact Bool.noConfusion (ha.mp rfl)
  · exact Bool.noConfusion (ha.mpr rfl)
  · rfl

theorem not_actuality (D : Domain Bool) (hp : D (fun w => ¬ branchingP w)) :
    ¬ PossibilityActuality branching.frame D false := by
  intro h
  have hn := h (fun w => ¬ branchingP w) hp ⟨true, rfl, by intro ht; cases ht⟩
  exact hn rfl

theorem checks : Branching := by
  refine ⟨reflexive, endpoint allPredicates, endpoint branchingLanguage,
    ⟨true, rfl, endpoint allPredicates⟩, ⟨true, rfl, endpoint branchingLanguage⟩,
    branching_full_not_collapse, branching_language_not_collapse, ?_, ?_, ?_,
    not_actuality allPredicates trivial, not_actuality branchingLanguage ?_,
    language_extensional, rfl, rfl, rfl, rfl, rfl⟩
  · intro h; exact branching_full_not_collapse (h false rfl)
  · intro h; exact branching_language_not_collapse (h false rfl)
  · exact ⟨⟨false, rfl, rfl⟩, ⟨true, rfl, by intro h; cases h⟩⟩
  · exact ⟨.neg (.atom ()), rfl⟩
end TruthCore.Results.Modal.T.Branching
