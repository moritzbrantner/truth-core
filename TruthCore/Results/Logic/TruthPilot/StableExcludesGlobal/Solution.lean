import TruthCore.Logic.TruthPilot
namespace TruthCore.Results.Logic.TruthPilot.StableExcludesGlobal
open TruthCore.Logic.TruthPilot
/-- A global variation witness for the logical sentence conflicts with its explicit all-profile stability premise. This is a conditional test, not a premise-free refutation of philosophical relativism. -/
theorem stableExcludesGlobal (Holds : Interpretation) (hStable : LogicalSentenceStable Holds) : NotGlobalProfileVariation Holds := by
  intro hGlobal
  obtain ⟨E, F, hTrue, hFalse⟩ := hGlobal Sentence.logical
  have hAtF := hStable F
  exact hFalse hAtF
end TruthCore.Results.Logic.TruthPilot.StableExcludesGlobal
