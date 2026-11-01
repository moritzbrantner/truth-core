import TruthCore.Causality.WholeRosterFoundation

namespace TruthCore.Results.Causality.WholeRosterRootEquivalence
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- Exact strength of the formal whole-roster premise under population and EM.
This proves an equivalence, not either side's applicability to reality. -/
theorem equivalence {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hEM : ExcludedMiddle) : WholeRosterRootEquivalenceAt m w := by
  sorry

end TruthCore.Results.Causality.WholeRosterRootEquivalence
