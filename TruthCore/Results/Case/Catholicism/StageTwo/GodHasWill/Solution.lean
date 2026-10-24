import TruthCore.Results.Case.Catholicism.StageTwo.GodHasIntellect.Solution
namespace TruthCore.Results.Case.Catholicism.StageTwo.GodHasWill
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism

theorem godHasWill {Being : Type} {Respect : Type} {Principle : Type}
    (IsGod Composite ComposedOfMatterAndForm HasIntellect HasWill : Being → Prop)
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
      ComponentOf)
    (hWillFollows : WillFollowsIntellectReading HasIntellect HasWill) :
    GodHasWill IsGod HasWill := by
  -- CATHOLICISM-STAGE2-GOD-HAS-INTELLECT (imported)
  have hIntellect := TruthCore.Results.Case.Catholicism.StageTwo.GodHasIntellect.godHasIntellect
    IsGod Composite ComposedOfMatterAndForm HasIntellect ComponentOf PriorSimply essenceOf esseOf
    InAct MoreIn CausesIn esse hMaximal hUniting hCauseMore hKinds hNoComponent hFirstBeing
    hImmaterial
  -- INF-STAGE2-GOD-HAS-WILL: will follows intellect (q.19 a.1)
  exact fun g hg => hWillFollows g (hIntellect g hg)

end TruthCore.Results.Case.Catholicism.StageTwo.GodHasWill
