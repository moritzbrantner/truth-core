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
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverSimple
