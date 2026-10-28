import TruthCore.Causality.ActualUnderivedEssenceEsse
namespace TruthCore.Results.Causality.ActualUnderivedEssenceEsse
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.ActualUnderivedEssenceEsse
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.UnderivedNonComposite
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
/-- The q3 core needs only actual absence of support. Explicit EM selects the
source and eliminates double-negated identity for that same source. -/
theorem checks {W B P A : Type} (m : Ontic W B)
    (R : W → B → B → Prop) (w : W) (p : Profile B P A)
    (hNecessary : NecessaryBeing m w)
    (hWF : ActualNecessaryWellFounded m R w)
    (hLocal : ActualNoContingent m R w)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hInAct : ExistingInActAt m p.InAct p.esse w)
    (hPresent : UnitingCausesPresent m p.CausesIn p.esse w)
    (hTyped : ActualEsseCausesSupportAt m R p.CausesIn p.esse w)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p) :
    ActualUnderivedEssenceIdentity m R w p := by
  sorry
end TruthCore.Results.Causality.ActualUnderivedEssenceEsse
