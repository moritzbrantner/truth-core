module

public import TruthCore.Case.Catholicism.StageThree.MessageReportBoundary
public import TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary.Scope.Solution
public import TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary.Models.Solution

@[expose] public section
namespace TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism.StageThree.MessageReportBoundary

theorem messageScopeModels : MessageScopeModels := by
  constructor
  · refine ⟨modelSig True, modelAgency True (fun p => p) False False True,
      ?_, ?_, ?_⟩
    · intro _ _ hm; exact False.elim hm
    · intro _ hm; exact False.elim hm
    · intro ⟨_, hm, _, _⟩; exact hm
  · obtain ⟨⟨σ, A, _, hr, _, ha, _, _⟩, _⟩ := messageReportModels
    exact ⟨σ, A, hr, ha, actualMessageOnlyRejectsCatholicScope σ A hr ha⟩

end TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary
