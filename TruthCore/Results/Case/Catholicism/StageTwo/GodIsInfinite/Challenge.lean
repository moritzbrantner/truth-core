import TruthCore.Results.Case.Catholicism.StageTwo.GodIsSimple.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityEternity
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Case.Catholicism.StageTwo.GodIsInfinite
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism
theorem godIsInfinite {Being : Type} {Respect : Type} {Principle : Type}
    (IsGod Composite ComposedOfMatterAndForm Infinite : Being → Prop)
    (essenceOf esseOf : Being → Principle)
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hMaximal : GodIsMaximalInBeing IsGod InAct MoreIn esse)
    (hUniting : CompositeHasAUnitingCauseReading Composite CausesIn esse)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading ComposedOfMatterAndForm Composite
      essenceOf esseOf)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hInfinity : SubsistentBeingIsInfiniteReading essenceOf esseOf Infinite) :
    GodIsInfinite IsGod Infinite := by
  sorry
end TruthCore.Results.Case.Catholicism.StageTwo.GodIsInfinite
