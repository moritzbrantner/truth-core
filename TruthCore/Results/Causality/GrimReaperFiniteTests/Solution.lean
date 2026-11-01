import TruthCore.Causality.GrimReaperFiniteTests
import TruthCore.Results.Causality.GrimReaperImpossible.Solution

namespace TruthCore.Results.Causality.GrimReaperFiniteTests
open TruthCore.Causality.GrimReaperFiniteTests

/-- Finite sets of full-tail clauses are satisfiable on the SAME Nat carrier;
the complete existing GrimReaperLaw has no satisfying action assignment. -/
theorem checks : FiniteTestsWithoutGlobalSchedule := by
  refine ⟨?_, TruthCore.Results.Causality.GrimReaperImpossible.grimReaperImpossible⟩
  intro indices
  let k := indices.sup id + 1
  refine ⟨fun n => n = k, ?_⟩
  intro n hn
  have hnk : n < k := Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)
  constructor
  · intro h
    exact (Nat.ne_of_lt hnk h).elim
  · intro h
    exact (h k hnk rfl).elim

end TruthCore.Results.Causality.GrimReaperFiniteTests
