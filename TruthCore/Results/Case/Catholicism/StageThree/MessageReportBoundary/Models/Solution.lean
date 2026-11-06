module

public import TruthCore.Case.Catholicism.StageThree.MessageReportBoundary
public import TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary.Link.Solution
public import TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary.Rival.Solution
public import TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary.Rejection.Solution

@[expose] public section
namespace TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism.StageThree.Commissions
open TruthCore.Case.Catholicism.StageThree.MessageReportBoundary

theorem messageReportModels : MessageReportModels := by
  constructor
  · refine ⟨modelSig True, modelAgency True (fun p => p) True False True,
      fullCommissioning, ?_, ?_, ⟨true, trivial, trivial, trivial⟩,
      ⟨true, trivial, trivial, trivial, ⟨.keys, rfl, trivial⟩, ?_⟩, ?_⟩
    · intro _ _ _ h; exact h
    · exact ⟨fun _ _ => trivial, Or.inl (fun _ _ => trivial)⟩
    · intro h; exact h
    · intro h; exact h true trivial trivial trivial ⟨.keys, rfl, trivial⟩
  · obtain ⟨σ, A, E, hl, hr, ⟨g, hm⟩, hf, hv, _, h28⟩ :=
      messageRival_compatible_with_mt28
    have ha : ActualMandatedCatholicFounding σ A := ⟨g, hm, hf, hv⟩
    have hn := messageOnlyRejectsGoverning σ A E hr
      (institutionLinkComponent σ A E hl) ha
    exact ⟨σ, A, E, hr, hl, ha, h28, hn,
      noGoverningRejectsHistoricalBundle E hn⟩

end TruthCore.Results.Case.Catholicism.StageThree.MessageReportBoundary
