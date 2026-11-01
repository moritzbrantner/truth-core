import TruthCore.Results.Causality.WholeRosterFoundation.Solution
import TruthCore.Results.Causality.ConcreteExistentialSupply.Solution

namespace TruthCore.Results.Causality.WholeRosterRootEquivalence
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.ConcreteExistentialSupply
open TruthCore.Causality.JointGroups
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- Reverse direction needs neither population nor EM as an extra premise:
the same actual root contradicts the whole roster's source-free Trap clause. -/
theorem wholeRosterOfRoot {W B : Type} (m : Profile W B) (w : W)
    (hRoot : ∃ n, ActualRoot m w n) : WholeRosterNotTrapped m w := by
  obtain ⟨n, hn⟩ := hRoot
  intro _ hTrap
  apply hTrap.1 ⟨n, hn.1⟩ (Set.mem_univ _)
  rintro ⟨candidate, hEdge⟩
  exact hn.2 candidate.val ⟨candidate.property.1, candidate.property.2, hEdge⟩

/-- Exact strength of the formal whole-roster premise under population and EM.
This proves an equivalence, not either side's applicability to reality. -/
theorem equivalence {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hEM : ExcludedMiddle) : WholeRosterRootEquivalenceAt m w := by
  exact ⟨fun hWhole =>
    TruthCore.Results.Causality.WholeRosterFoundation.actualRootExists m w hPop hWhole hEM,
    wholeRosterOfRoot m w⟩

/-- Reuse the existing Supply/root equivalence: existential Supply is another
presentation of the same foundation commitment on a populated actual roster. -/
theorem supplyEquivalence {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hEM : ExcludedMiddle) : WholeRosterNotTrapped m w ↔ ActualConcreteSupply m w := by
  exact (equivalence m w hPop hEM).trans
    (TruthCore.Results.Causality.ConcreteExistentialSupply.supplyRootEquivalence W B m w).symm

end TruthCore.Results.Causality.WholeRosterRootEquivalence
