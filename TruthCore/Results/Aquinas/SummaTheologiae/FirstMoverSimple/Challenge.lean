import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.FirstMoverAttributes
import TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverPureAct.Solution
namespace TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverSimple
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- ST I q.3 a.1 (first proof), a.2, a.4 and a.7 for the *prima via*'s mover. The
first conjunct uses only the *prima via* conclusion's "moved by none"; the other
three use pure act, obtained from `FirstMoverPureAct.firstMoverPureAct`. -/
theorem firstMoverSimple {Being : Type} {Respect : Type} {Principle : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InPotency InAct : Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop)
    (Body ComposedOfMatterAndForm Composite : Being → Prop)
    (essenceOf esseOf : Being → Principle)
    (hNoBody : NoBodyMovesUnlessMovedReading MovedIn MovesIn Body)
    (hFirstBeing : FirstUnmovedMoverIsFirstBeingReading MovedIn MovesIn PriorSimply)
    (hPrior : ActSimplyPriorToPotencyReading InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hMatter : MatterIsInPotencyReading InPotency ComposedOfMatterAndForm)
    (hEsse : EsseOtherThanEssenceIsPotencyReading InPotency essenceOf esseOf)
    (hComposite : CompositeIsInPotencyReading InPotency Composite) :
    FirstUnmovedMoverIsSimpleReading MovedIn MovesIn
      Body ComposedOfMatterAndForm Composite essenceOf esseOf := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverSimple
