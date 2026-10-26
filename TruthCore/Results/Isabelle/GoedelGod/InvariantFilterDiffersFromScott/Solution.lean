import TruthCore.Results.Isabelle.GoedelGod.InvariantFilterMakesNecessaryExistenceUniversal.Solution
import TruthCore.Results.Isabelle.GoedelGod.NecessaryExistenceWorldIsolation.Solution

namespace TruthCore.Results.Isabelle.GoedelGod.InvariantFilterDiffersFromScott

open TruthCore.Modal
open TruthCore.Isabelle.AFP.GoedelGod

/-- On the two-world universal frame, the new invariant-filter result gives
filtered NE. The already verified Scott characterization rules out full NE:
`true` is accessible from `false` but they are not identical worlds. -/
theorem checks : InvariantFilterDiffersFromScott := by
  let F : Frame Bool := ⟨fun _ _ => True⟩
  refine ⟨F, InvariantFilterMakesNecessaryExistenceUniversal.checks F () false, ?_⟩
  intro hNE
  have hIsolated :=
    (NecessaryExistenceWorldIsolation.checks F () false).mp hNE
  have hImpossible : true = false := hIsolated true trivial
  cases hImpossible

end TruthCore.Results.Isabelle.GoedelGod.InvariantFilterDiffersFromScott
