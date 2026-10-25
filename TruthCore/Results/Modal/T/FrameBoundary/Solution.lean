import TruthCore.Modal.TResearch
namespace TruthCore.Results.Modal.T.FrameBoundary
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite
open TruthCore.Modal.TResearch
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)

theorem endpoint (D : Domain ChainWorld) : MC chain.frame D .endpoint := by
  intro P _ hp v hv
  cases v with
  | root => cases hv
  | middle => cases hv
  | endpoint => exact hp

theorem middle_not_language : ¬ MC chain.frame chainLanguage .middle := by
  intro h
  have hp : Holds chain.frame chain.valuation .middle (.neg (.atom ())) := by
    intro ha; cases ha
  exact h _ ⟨.neg (.atom ()), rfl⟩ hp .endpoint rfl rfl

theorem root_not_language : ¬ MC chain.frame chainLanguage .root := by
  intro h
  have hp : Holds chain.frame chain.valuation .root (.neg (.diamond (.atom ()))) := by
    rintro ⟨v, hv, ha⟩
    cases v with
    | root => cases ha
    | middle => cases ha
    | endpoint => cases hv
  have hm := h _ ⟨.neg (.diamond (.atom ())), rfl⟩ hp .middle rfl
  exact hm ⟨.endpoint, rfl, rfl⟩

theorem not_full (w : ChainWorld) (hn : ¬ MC chain.frame chainLanguage w) :
    ¬ MC chain.frame allPredicates w := by
  intro h; exact hn (restrict _ allPredicates chainLanguage w (fun _ _ => trivial) h)

theorem not_possible_language : ¬ Dia chain.frame (MC chain.frame chainLanguage) .root := by
  rintro ⟨v, hv, hm⟩
  cases v with
  | root => exact root_not_language hm
  | middle => exact middle_not_language hm
  | endpoint => cases hv

theorem checks : FrameBoundary := by
  refine ⟨?_, ?_, ?_, endpoint allPredicates, endpoint chainLanguage,
    not_full .root root_not_language, root_not_language,
    not_full .middle middle_not_language, middle_not_language, ?_,
    not_possible_language, ⟨.middle, rfl, .endpoint, rfl, endpoint allPredicates⟩,
    ?_, ?_, rfl, rfl⟩
  · intro w; cases w <;> rfl
  · intro h; exact Bool.noConfusion (h .root .middle .endpoint rfl rfl)
  · intro h; exact Bool.noConfusion (h .root .middle rfl)
  · rintro ⟨v, hv, hm⟩
    exact not_possible_language ⟨v, hv, restrict _ allPredicates chainLanguage v
      (fun _ _ => trivial) hm⟩
  · intro h; exact not_full .root root_not_language (h .root rfl)
  · intro h; exact root_not_language (h .root rfl)
end TruthCore.Results.Modal.T.FrameBoundary
