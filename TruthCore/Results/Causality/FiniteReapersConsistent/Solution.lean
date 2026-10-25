import TruthCore.Causality.GrimReaper

namespace TruthCore.Results.Causality.FiniteReapersConsistent
open TruthCore.Causality

/-- The first-deadline Reaper (index 2) acts; the others do not. -/
theorem finiteReapersConsistent : ConsistentFiniteThreeReapers := by
  refine ⟨fun n => n = 2, ?_⟩
  simp [FiniteGrimReaperLaw, Fin.forall_fin_succ, Fin.forall_fin_zero]

end TruthCore.Results.Causality.FiniteReapersConsistent
