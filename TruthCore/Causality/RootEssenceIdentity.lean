import TruthCore.Causality.NecessaryConcreteRouteBridge
import TruthCore.Causality.ExistenceActuality
import TruthCore.Results.Aquinas.SummaTheologiae.EssenceEsseExternalCause.Solution

namespace TruthCore.Causality.RootEssenceIdentity
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
  (DistinctEsseCauseDichotomyReading EssentialPrinciplesCannotCauseDistinctEsseReading)
open TruthCore.Logic (ExcludedMiddle)

/-- Source-free non-corpus composition for the supplied root. Every causal and
actuality field comes from the SAME q3 profile. The source's causal dichotomy
and exclusion of essential efficient self-origination remain explicit premises;
neither a maximum nor all-world underivedness is required. -/
theorem identityOfActualRoot {W B P R : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (n : B) (hr : ActualRoot m w n) (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p) :
    p.esseOf n = p.essenceOf n := by
  rcases hEM (p.esseOf n = p.essenceOf n) with h | h
  · exact h
  · have hExternal :=
      TruthCore.Results.Aquinas.SummaTheologiae.EssenceEsseExternalCause.distinctEsseExternalFromExhaustion
        p hExhaustive hNoSelfCause
    obtain ⟨c, hc, _, hCause⟩ := hExternal n ⟨hExisting n hr.1.2, h⟩
    exact (hr.2 c (hEsse c n hc hr.1 hCause)).elim

/-- One SAME actual concrete selected root is necessary at accessible worlds and
has equal represented esse/essence values in the supplied q3 profile. Equality
is not a proof of intrinsic explanatory adequacy, other-world rootness, unique
subsistent being or God, and the profile has no world-indexed essence maps. -/
def NecessaryRootEssenceIdentityAt {W B P R : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R) : Prop :=
  ∃ n, ActualRoot m w n ∧ NecessaryAt m.ontic w n ∧ p.esseOf n = p.essenceOf n

end TruthCore.Causality.RootEssenceIdentity
