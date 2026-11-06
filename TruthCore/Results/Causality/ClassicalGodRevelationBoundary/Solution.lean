module

public import TruthCore.Causality.ClassicalGodRevelationBoundary
public import TruthCore.Results.Causality.NecessaryClassicalGodRootControl.Solution

@[expose] public section

namespace TruthCore.Results.Causality.ClassicalGodRevelationBoundary
open TruthCore.Causality.ClassicalGodRevelationBoundary
open TruthCore.Logic (ExcludedMiddle)

/-- Reuse the full old positive configuration on its exact signature and
certify the two distinct failures, without claiming all root premises hold. -/
theorem checks (hEM : ExcludedMiddle) : Control := by
  have positive := TruthCore.Results.Causality.NecessaryClassicalGodRootControl.checks hEM
  have source := positive.2.2.1
  rcases source with ⟨_, _, _, _, _, hGod, _, hAttributes⟩
  refine ⟨positive, ⟨.source, hGod⟩, ?_, ?_, ?_⟩
  · intro g hg
    change g = .source at hg
    subst g
    exact hAttributes
  · intro revelation
    exact revelation .source hGod
  · intro root
    obtain ⟨g, _, founded⟩ := root.1
    exact founded

end TruthCore.Results.Causality.ClassicalGodRevelationBoundary
