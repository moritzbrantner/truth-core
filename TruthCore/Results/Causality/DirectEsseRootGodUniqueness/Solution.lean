import TruthCore.Results.Causality.WholeRosterFoundation.Solution
import TruthCore.Causality.DirectEsseRootRoute
import TruthCore.Causality.WholeRosterFoundation
import TruthCore.Case.Catholicism.StageTwo

namespace TruthCore.Results.Causality.DirectEsseRootGodUniqueness
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.DirectEsseRootRoute
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Latin.Aquinas.SummaTheologiae (MaximumInGenusCausesAllInGenusReading)
open TruthCore.Case.Catholicism

/-- The same selected actual root identifies every maximum, hence every God
candidate under the explicit converse. This proves at most one God, without
God existence, root necessity, contingent dependence or maximum existence. -/
theorem godIsOne {W B Respect : Type} (m : Profile W B) (w : W)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect) (IsGod : B → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w) (hEM : ExcludedMiddle)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hMaximal : GodIsMaximalInBeing IsGod InAct MoreIn esse) :
    GodIsOne IsGod := by
  obtain ⟨n, hr⟩ := TruthCore.Results.Causality.WholeRosterFoundation.actualRootExists
    m w hPop hWhole hEM
  have hIdent := maximumEqualsRoot m w InAct MoreIn CausesIn esse n hr
    hEM hGenus hExisting hEsse
  intro g hg g' hg'
  exact (hIdent g' (hMaximal g' hg')).trans (hIdent g (hMaximal g hg)).symm

end TruthCore.Results.Causality.DirectEsseRootGodUniqueness
