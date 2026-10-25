import TruthCore.Results.Case.Catholicism.StageTwo.GodIsSimple.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article8
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.IntellectWill
namespace TruthCore.Results.Case.Catholicism.StageTwo.GodHasIntellect
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism

theorem godHasIntellect {Being : Type} {Respect : Type} {Principle : Type}
    (IsGod Composite ComposedOfMatterAndForm HasIntellect : Being → Prop)
    (ComponentOf PriorSimply : Being → Being → Prop)
    (essenceOf esseOf : Being → Principle)
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hMaximal : GodIsMaximalInBeing IsGod InAct MoreIn esse)
    (hUniting : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading ComposedOfMatterAndForm Composite
      essenceOf esseOf)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFirstBeing : MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply)
    (hImmaterial : ImmaterialIsIntellectualReading ComposedOfMatterAndForm HasIntellect
      ComponentOf) :
    GodHasIntellect IsGod HasIntellect := by
  -- CATHOLICISM-STAGE2-GOD-IS-SIMPLE (imported)
  have hSimple := TruthCore.Results.Case.Catholicism.StageTwo.GodIsSimple.godIsSimple IsGod
    Composite InAct MoreIn CausesIn esse hMaximal hUniting hCauseMore
  -- INF-STAGE2-GOD-IS-IMMATERIAL: not a matter-form composite (simple, q.3 a.7) and a
  -- component of nothing (first being, q.3 a.8)
  -- INF-STAGE2-GOD-HAS-INTELLECT: the immaterial is intellectual (q.14 a.1)
  intro g hg
  exact hImmaterial g (fun hMatter => hSimple g hg ((hKinds g).1 hMatter))
    (fun y hComponent => hNoComponent g y hComponent (hFirstBeing g (hMaximal g hg)))

end TruthCore.Results.Case.Catholicism.StageTwo.GodHasIntellect
