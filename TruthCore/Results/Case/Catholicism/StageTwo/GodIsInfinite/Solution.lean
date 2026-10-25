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
  -- CATHOLICISM-STAGE2-GOD-IS-SIMPLE (imported)
  have hSimple := TruthCore.Results.Case.Catholicism.StageTwo.GodIsSimple.godIsSimple IsGod
    Composite InAct MoreIn CausesIn esse hMaximal hUniting hCauseMore
  -- INF-STAGE2-GOD-IS-HIS-OWN-ESSE: an esse other than the essence would be a composition
  intro g hg
  have hOwnEsse : esseOf g = essenceOf g := by
    cases hEM (esseOf g = essenceOf g) with
    | inl h => exact h
    | inr hOther => exact absurd ((hKinds g).2 hOther) (hSimple g hg)
  -- INF-STAGE2-GOD-IS-INFINITE (q.7 a.1: subsistent being is infinite)
  exact hInfinity g hOwnEsse

end TruthCore.Results.Case.Catholicism.StageTwo.GodIsInfinite
