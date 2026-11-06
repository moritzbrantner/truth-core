module

public import TruthCore.Results.Causality.MaximalGroundingAsymmetry.WholeRoster.Solution
public import TruthCore.Results.Causality.DirectEsseRootUniquenessAtBeing.Solution
public import TruthCore.Causality.DirectEsseRootUniquenessAtBeing
public import TruthCore.Causality.DirectEsseRootRoute
public import TruthCore.Causality.NecessaryRootUniqueness
public import TruthCore.Causality.WholeRosterFoundation

@[expose] public section

namespace TruthCore.Results.Causality.MaximalGroundingAsymmetry.UniqueRoot
open TruthCore.Causality.MaximalGroundingAsymmetry
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.NecessaryRootUniqueness
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
/-- Retain the original selected-root endpoint and dictionaries: derive whole-roster
nontrapping from the seven-input maximal-target asymmetry result, then reuse uniqueRoot8.
Contingent grounding supplies necessity; no naming or attribute adapter occurs. -/
theorem uniqueRoot {W B Respect : Type} (m : Profile W B) (w : W)
    (InAct : B → Respect → Prop) (MoreIn : Respect → B → B → Prop)
    (CausesIn : B → B → Respect → Prop) (esse : Respect)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hExisting : ExistingInActAt m.ontic InAct esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w CausesIn esse)
    (hApproach : GradesToMaximumAtBeing InAct MoreIn esse)
    (hAsym : AtMaximalTarget m w InAct MoreIn esse) :
    UniqueNecessaryActualRootAt m w := by
  have hWhole : WholeRosterNotTrapped m w :=
    TruthCore.Results.Causality.MaximalGroundingAsymmetry.WholeRoster.wholeRoster
      m w InAct MoreIn CausesIn esse hPop hExisting hEsse hGenus hApproach hEM hAsym
  exact TruthCore.Results.Causality.DirectEsseRootUniquenessAtBeing.uniqueRoot
    m w InAct MoreIn CausesIn esse hPop hWhole hDep hEM hGenus hExisting hEsse hApproach

end TruthCore.Results.Causality.MaximalGroundingAsymmetry.UniqueRoot
