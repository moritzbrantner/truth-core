import TruthCore.Causality.UnderivedEssenceEsse
namespace TruthCore.Results.Causality.UnderivedEssenceEsse
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.UnderivedNonComposite
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.UnderivedEssenceEsse
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

theorem from_union_direct {W B P A : Type} (m : Ontic W B)
    (R : W → B → B → Prop) (w : W) (p : Profile B P A)
    (hNecessary : NecessaryBeing m w) (hReflexive : ActualReflexive m w)
    (hNoContingent : NoContingentGroundOfNecessary m R w)
    (hUnionWF : WellFoundedUnionNecessarySupport m R w)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hInAct : ExistingInActAt m p.InAct p.esse w)
    (hPresent : UnitingCausesPresent m p.CausesIn p.esse w)
    (hTyped : ActualEsseCausesSupportAt m R p.CausesIn p.esse w)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p) :
    UnderivedEssenceIdentity m R w p := by sorry

theorem all_controls : ExtendedControls := by sorry
end TruthCore.Results.Causality.UnderivedEssenceEsse
