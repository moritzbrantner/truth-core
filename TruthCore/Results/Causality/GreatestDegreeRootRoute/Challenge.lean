import TruthCore.Causality.GreatestDegreeRootRoute
import TruthCore.Causality.ActualCommonRoot
import TruthCore.Causality.NecessaryConcreteRouteBridge
import TruthCore.Causality.ExistenceActuality
import TruthCore.Causality.WholeRosterFoundation

namespace TruthCore.Results.Causality.GreatestDegreeRootRoute
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.WholeRosterFoundation (WholeRosterNotTrapped)
open TruthCore.Causality.ActualCommonRoot (ActualCommonRootAt)
open TruthCore.Causality.GreatestDegreeRootRoute (GreatestBeingDegreeAttained)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- Seven explicit inputs give the existing common actual root at the SAME
world and grounding relation. Greatest attainment and its causal principle
replace the old weak H/strong I pair; no bundle weakening is asserted. -/
theorem commonRoot {W B R Degree : Type} [Preorder Degree]
    (m : Profile W B) (w : W) (InAct : B → R → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) (value : B → Degree)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w) (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hAttained : GreatestBeingDegreeAttained InAct esse value)
    (hGenus : GreatestDegreeCausesAllInGenusReading InAct CausesIn esse value) :
    ActualCommonRootAt m w := by
  sorry

end TruthCore.Results.Causality.GreatestDegreeRootRoute
