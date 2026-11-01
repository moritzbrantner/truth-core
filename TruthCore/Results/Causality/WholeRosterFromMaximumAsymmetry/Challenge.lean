import TruthCore.Causality.DirectEsseRootUniquenessAtBeing
namespace TruthCore.Results.Causality.WholeRosterFromMaximumAsymmetry
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
theorem wholeRoster {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hApproach : GradesToMaximumAtBeing InAct MoreIn esse)
    (hEM : ExcludedMiddle) (hAsym : ActualGroundingAsymmetric m w) :
    WholeRosterNotTrapped m w := by
  sorry
end TruthCore.Results.Causality.WholeRosterFromMaximumAsymmetry
