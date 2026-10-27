import TruthCore.Logic.PerformedDenial

namespace TruthCore.Results.Logic.PerformedDenial.EmptyControl
open TruthCore.Logic.PerformedDenial

/-- An actual token is not derivable from logic alone. -/
theorem emptyControl : EmptyEpisodeControl := by
  refine ⟨fun _ => False, fun _ => True, ?_, trivial, ?_⟩
  · intro ⟨_, h⟩
    exact h
  · intro h
    exact h

end TruthCore.Results.Logic.PerformedDenial.EmptyControl
