import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.FirstMoverAttributes
import TruthCore.Case.Catholicism.StageOneBridges
namespace TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverSimple
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (FirstUnmovedMoverIsFirstBeing)

/-- ST I q.3 a.1 (first proof) and q.3 a.7 (second and fifth proofs) for the
*prima via*'s mover. It is not a body, because a body that moves is moved. It is
not composite: a composite has a component other than itself, which is simply
prior to it, but nothing other than the first being is prior to the first being.
Matter-form composition (a.2) and an esse other than the essence (a.4) are kinds
of composition, so they are excluded too. -/
theorem firstMoverSimple {Being : Type} {Respect : Type} {Principle : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (PriorSimply ComponentOf : Being → Being → Prop)
    (Body ComposedOfMatterAndForm Composite : Being → Prop)
    (essenceOf esseOf : Being → Principle)
    (hNoBody : NoBodyMovesUnlessMovedReading MovedIn MovesIn Body)
    (hFirstBeing : FirstUnmovedMoverIsFirstBeing MovedIn MovesIn PriorSimply)
    (hPosterior : CompositePosteriorToComponentsReading ComponentOf PriorSimply)
    (hOther : CompositeHasComponentOtherThanItselfReading Composite ComponentOf)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading
      ComposedOfMatterAndForm Composite essenceOf esseOf) :
    FirstUnmovedMoverIsSimpleReading MovedIn MovesIn
      Body ComposedOfMatterAndForm Composite essenceOf esseOf := by
  intro f hF
  -- INF-AQUINAS-ST-I-Q3-A7-FIRST-BEING-NOT-COMPOSITE
  have hNotComposite : ¬ Composite f := by
    intro hComp
    obtain ⟨p, hComponent, hDistinct⟩ := hOther f hComp
    exact hDistinct (hFirstBeing f hF p (hPosterior p f hComponent))
  refine ⟨?_, ?_, ?_, hNotComposite⟩
  · -- INF-AQUINAS-ST-I-Q3-A1-FIRST-MOVER-NOT-A-BODY: a body that moves is moved
    intro hBody
    obtain ⟨r, hMoved⟩ := hNoBody f hBody hF.1
    exact hF.2 r hMoved
  · -- INF-AQUINAS-ST-I-Q3-SIMPLE-KINDS: matter-form composition is composition
    exact fun hMF => hNotComposite ((hKinds f).1 hMF)
  · -- an esse other than the essence is composition
    exact fun hDistinct => hNotComposite ((hKinds f).2 hDistinct)
end TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverSimple
