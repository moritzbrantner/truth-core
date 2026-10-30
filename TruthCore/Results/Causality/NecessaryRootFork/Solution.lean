import TruthCore.Causality.NecessaryRootFork

namespace TruthCore.Results.Causality.NecessaryRootFork

open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt EveryContingentGroundedAt)
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- An inhabited world with well-founded actual grounding has a necessary
concretum or a nonnecessary root of the selected relation. Coverage only. -/
theorem necessaryOrNonnecessaryRoot {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w) (hWF : ActualGroundingWF m w)
    (hEM : ExcludedMiddle) :
    NecessaryOrNonnecessaryRoot m w := by
  exact TruthCore.Causality.NecessaryRootFork.necessaryOrNonnecessaryRoot m w hPop hWF hEM

/-- An inhabited world has a necessary concretum; or well-founded actual grounding
with a nonnecessary root; or non-well-founded actual grounding. Coverage only. -/
theorem necessaryRootTrilemma {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w) (hEM : ExcludedMiddle) :
    NecessaryRootTrilemma m w := by
  exact TruthCore.Causality.NecessaryRootFork.necessaryRootTrilemma m w hPop hEM

/-- Adding that every actual contingent concretum is grounded closes the root horn. -/
theorem necessaryConcreteOfActualGrounded {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w) (hWF : ActualGroundingWF m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle) :
    NecessaryConcreteAt m w := by
  exact TruthCore.Causality.NecessaryRootFork.necessaryConcreteOfActualGrounded m w hPop hWF hDep hEM

/-- Branch witnesses, omission and overlap controls, and the strength of the root
principle relative to excluded middle. -/
theorem necessaryRootControls : NecessaryRootControls := by
  exact TruthCore.Causality.NecessaryRootFork.necessaryRootControls

end TruthCore.Results.Causality.NecessaryRootFork
