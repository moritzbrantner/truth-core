import TruthCore.Results.Modern.Hume.SelfApplication.HigherOrder.Solution
namespace TruthCore.Results.Modern.Hume.SelfApplication.Reflexive
open TruthCore.Modern.Hume.Conceivability
open TruthCore.Modern.Hume.SelfApplication

theorem checks : ReflexiveConflictLaws := by
  intro W F C w hr hn
  have hH := hn w (hr w)
  have laws := TruthCore.Results.Modern.Hume.SelfApplication.HigherOrder.checks
  exact ⟨fun hc => laws.2.1 W F C w hH hc hn,
    laws.2.2.2.1 W F C w hr hH hn⟩
end TruthCore.Results.Modern.Hume.SelfApplication.Reflexive
