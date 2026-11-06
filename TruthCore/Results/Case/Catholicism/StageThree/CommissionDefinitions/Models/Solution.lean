module

public import TruthCore.Case.Catholicism.StageThree.CommissionDefinitions

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageThree.CommissionDefinitions.Models

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism.StageThree.Commissions
open TruthCore.Case.Catholicism.StageThree.CommissionDefinitions

/-- Four nonvacuous bridge/criterion controls, not institutional history. -/
theorem criterionModels : CommissionCriterionModels := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨σ, A, E, hOld, hRival, hMandate, hFounded, hVisible, _, hMatthew⟩ :=
      messageRival_compatible_with_mt28
    refine ⟨σ, A, E, hOld, hRival, hMandate, hFounded, hVisible, hMatthew, ?_⟩
    intro hBroad
    obtain ⟨g, hm⟩ := hMandate
    have hTeach : E.Gave .teach := hMatthew .teach (.tail _ (.tail _ (.head _)))
    exact hRival g σ.catholicChurch hm
      ((hBroad g hm hFounded hVisible).1 .teach (Or.inr rfl) hTeach)
  · refine ⟨modelSig True, modelAgency True (fun p => p) True True True,
      fullCommissioning, (fun p => p.Governing = true ∨ p = .teach),
      (fun _ => Iff.rfl), ?_, ?_, ⟨true, trivial⟩, trivial, trivial, ?_⟩
    · intro _ _ _ _; exact ⟨fun _ _ _ => trivial, fun _ => trivial⟩
    · intro _ _; trivial
    · intro _ _ _ _; exact ⟨trivial, trivial⟩
  · refine ⟨modelSig True, modelAgency True (fun p => p) True True True,
      fullCommissioning, (fun p => p.Governing = true ∨ p = .baptize),
      ⟨?_, ?_⟩, ?_, ?_, ⟨true, trivial⟩, trivial, trivial, ?_⟩
    · intro hNarrow
      have h : false = true := (hNarrow .baptize).1 (Or.inr rfl)
      cases h
    · intro hTeaching
      cases (hTeaching .baptize).1 (Or.inr rfl) with
      | inl h => cases h
      | inr h => cases h
    · intro _ _ _ _; exact ⟨fun _ _ _ => trivial, fun _ => trivial⟩
    · intro _ _; trivial
    · intro _ _ _ _; exact ⟨trivial, trivial⟩
  · obtain ⟨σ, A, E, hOld, hRival, hMandate, hFounded, hVisible, _, hMatthew⟩ :=
      messageRival_compatible_with_mt28
    refine ⟨σ, A, E, (fun _ => False), ⟨?_, ?_⟩, ?_,
      hMatthew, hMandate, hFounded, hVisible, ?_⟩
    · intro hNarrow; exact (hNarrow .keys).2 rfl
    · intro hTeaching; exact (hTeaching .teach).2 (Or.inr rfl)
    · intro g hm hf hv
      exact ⟨fun _ hFalse _ => False.elim hFalse, (hOld g hm hf hv).2⟩
    · intro hScope
      obtain ⟨g, hm⟩ := hMandate
      exact hRival g σ.catholicChurch hm (hScope g hm hFounded hVisible).1

end TruthCore.Results.Case.Catholicism.StageThree.CommissionDefinitions.Models
