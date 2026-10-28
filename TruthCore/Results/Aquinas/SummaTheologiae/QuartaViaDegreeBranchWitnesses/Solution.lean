import TruthCore.Models.QuartaViaDegreeFork

namespace TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaDegreeBranchWitnesses

/-- A finite strict-causal-top interpretation and a separate infinite
unbounded-degree interpretation each jointly satisfy the fork's entire
nonlogical background. The infinite interpretation has no causal edges, so
strict-degree extension supplies no causal regress. These are satisfiability
witnesses, not premise truth or metaphysical possibility; Unit respects are
fixture assignments, not source identities. -/
theorem branchWitnesses : TruthCore.Models.QuartaViaDegreeFork.BranchWitnesses := by
  exact TruthCore.Models.QuartaViaDegreeFork.branchWitnesses

end TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaDegreeBranchWitnesses
