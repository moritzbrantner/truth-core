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
  intro f hF
  -- Pure act (result AQUINAS-ST-I-Q3-A1-FIRST-MOVER-PURE-ACT)
  have hPure : PureAct InPotency f :=
    FirstMoverPureAct.firstMoverPureAct MovedIn MovesIn InPotency InAct PriorSimply
      hFirstBeing hPrior hNotBoth f hF
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- INF-AQUINAS-ST-I-Q3-A1-FIRST-MOVER-NOT-A-BODY: a body that moves is moved
    intro hBody
    obtain ⟨r, hMoved⟩ := hNoBody f hBody hF.1
    exact hF.2 r hMoved
  · -- INF-AQUINAS-ST-I-Q3-SIMPLE-FROM-PURE-ACT (a.2): matter is potency
    intro hMF
    obtain ⟨r, hPot⟩ := hMatter f hMF
    exact hPure r hPot
  · -- (a.4): an esse other than the essence is its act, the essence its potency
    intro hDistinct
    obtain ⟨r, hPot⟩ := hEsse f hDistinct
    exact hPure r hPot
  · -- (a.7): every composite has potency and act
    intro hComp
    obtain ⟨r, hPot⟩ := hComposite f hComp
    exact hPure r hPot
end TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverSimple
