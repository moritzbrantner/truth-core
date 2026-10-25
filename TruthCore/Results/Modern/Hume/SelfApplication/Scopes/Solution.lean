import TruthCore.Modern.Hume.SelfApplication
namespace TruthCore.Results.Modern.Hume.SelfApplication.Scopes
open TruthCore.Modal
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Modern.Hume.Conceivability
open TruthCore.Modern.Hume.SelfApplication

private theorem oneStepBridge : StrongBridge oneStep oneStepConception false := by
  intro P h
  exact ⟨true, ⟨rfl, rfl⟩, h.2⟩

private theorem deadEndBridge : StrongBridge oneStep oneStepConception true := by
  intro P h
  cases h.1

theorem checks : ScopeCountermodels := by
  have old := TruthCore.Results.Modern.Hume.Conceivability.checks
  have hself := old.2.2.2.2.2.2.2.1
  refine ⟨⟨hself.1, hself.2, old.1 Bool universal selfC false hself.1 hself.2, ?_⟩,
    oneStepBridge, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rcases h with h | h
    · exact h.2 false True.intro hself.1
    · cases h
  · intro v hv
    exact hv.2.symm ▸ deadEndBridge
  · refine ⟨rfl, ?_⟩
    intro v hv
    cases hv.1
  · intro h
    exact h.2 deadEndBridge
  · intro h
    cases (h false).2
  · intro h
    obtain ⟨z, hz⟩ := h true ⟨rfl, rfl⟩
    cases hz.1
end TruthCore.Results.Modern.Hume.SelfApplication.Scopes
