import TruthCore.Causality.RootPositiveIntellectWill
import TruthCore.Logic.ExcludedMiddle

namespace TruthCore.Results.Causality.PerfectRootPositiveIntellectWill
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.DirectEsseRootPerfectionGoodness
open TruthCore.Causality.RootPositiveIntellectWill
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic (ExcludedMiddle)

/-- Consume the supplied perfect root, retaining ONE witness throughout.
Uniqueness is only among selected actual roots, not all necessary individuals.
The source/cognitive/causal applicability of the supplied readings stays open. -/
theorem derive {W B P R : Type} (m : Profile W B) (w : W)
    (p : PrimaPars.Question3.Article4.Profile B P R)
    (GoodIn : B → R → Prop) (MoreIn : R → B → B → Prop)
    (PriorSimply ComponentOf : B → B → Prop)
    (Composite MatterForm HasIntellect HasWill : B → Prop)
    (hPerfect : NecessaryPerfectRootAt m w p.InAct MoreIn p.esse)
    (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading p.InAct MoreIn p.CausesIn p.esse)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading p.InAct p.esse)
    (hGoodness : GoodnessIsActualityReading GoodIn p.InAct)
    (hTransfer : UniversalCauseTransfersPerfections p.InAct p.CausesIn p.esse)
    (hUniting : CompositeHasAUnitingCauseReading Composite p.CausesIn p.esse)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite p.essenceOf p.esseOf)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hIntellect : ImmaterialIsIntellectualReading MatterForm HasIntellect ComponentOf)
    (hWill : WillFollowsIntellectReading HasIntellect HasWill) :
    NecessaryPositiveRootIntellectWillAt m w p GoodIn MoreIn PriorSimply ComponentOf
      Composite MatterForm HasIntellect HasWill := by
  sorry

end TruthCore.Results.Causality.PerfectRootPositiveIntellectWill
