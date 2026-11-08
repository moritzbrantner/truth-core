import TruthCore.Causality.RootPurity

namespace TruthCore.Results.Causality.RootPurity
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
  (EsseCauseIsActualConcreteGround SimplyPriorIsActualConcreteGround)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.PureActRoot (ActualRootDeterminationsArePure)
open TruthCore.Causality.RootPurity
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
  (DistinctEsseCauseDichotomyReading EssentialPrinciplesCannotCauseDistinctEsseReading)
open TruthCore.Logic (ExcludedMiddle)

/-- Every actual root lacks all three represented limiting principles. The
witnessed-root argument of ROOT-WITHOUT-LIMITING-PRINCIPLE, run for each actual
root; no population, whole-roster, dependence or necessity premise is used. -/
theorem rootsWithoutLimitingPrinciple {W B P R : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop) (Composite : B → Prop)
    (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hPosterior : CompositePosteriorToComponentsReading ComponentOf PriorSimply)
    (hOther : CompositeHasComponentOtherThanItselfReading Composite ComponentOf) :
    ActualRootsWithoutLimitingPrinciple m w Composite PriorSimply p.essenceOf p.esseOf := by
  sorry

/-- Strict pure actuality at the actual roots from the same seven inputs, excluded
middle and the open bridge that unlimited beings have only pure determinations. -/
theorem rootPurityFromNoLimitation {W B P R D : Type} (m : Profile W B) (w : W)
    (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P R)
    (PriorSimply ComponentOf : B → B → Prop) (Composite : B → Prop)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hEM : ExcludedMiddle)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hPosterior : CompositePosteriorToComponentsReading ComponentOf PriorSimply)
    (hOther : CompositeHasComponentOtherThanItselfReading Composite ComponentOf)
    (hBridge : UnlimitedDeterminationsArePure Composite PriorSimply p.essenceOf p.esseOf Has Pure) :
    ActualRootDeterminationsArePure m w Has Pure := by
  sorry

/-- Strict pure actuality for first unmoved movers from the existing simplicity
reading, the first-mover-is-first-being bridge and the same open bridge. -/
theorem firstMoverPurityFromNoLimitation {B R P D : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop) (PriorSimply : B → B → Prop)
    (Body ComposedOfMatterAndForm Composite : B → Prop) (essenceOf esseOf : B → P)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hSimple : FirstUnmovedMoverIsSimpleReading Moved Moves Body ComposedOfMatterAndForm
      Composite essenceOf esseOf)
    (hFirst : TruthCore.Case.Catholicism.FirstUnmovedMoverIsFirstBeing Moved Moves PriorSimply)
    (hBridge : UnlimitedDeterminationsArePure Composite PriorSimply essenceOf esseOf Has Pure) :
    TruthCore.Causality.PureActThisness.FirstMoverDeterminationsArePure Moved Moves Has Pure := by
  sorry

theorem controls : TruthCore.Causality.RootPurity.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.RootPurity
