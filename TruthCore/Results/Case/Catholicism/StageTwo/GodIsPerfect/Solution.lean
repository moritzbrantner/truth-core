import TruthCore.Case.Catholicism.StageTwo
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article2
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Case.Catholicism.StageTwo.GodIsPerfect
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

theorem godIsPerfect {Being : Type} {Respect : Type}
    (IsGod : Being → Prop) (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hMaximal : GodIsMaximalInBeing IsGod InAct MoreIn esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    GodIsPerfect IsGod InAct := by
  -- INF-STAGE2-GOD-IS-PERFECT: every other being in act in r has being, so God causes
  -- its being (genus principle at esse), and its perfection pre-exists in God (q.4 a.2)
  intro g hg x r hx
  cases hEM (x = g) with
  | inl hSame => exact hSame ▸ hx
  | inr hOther =>
    exact hPreexist g x r (hGenus esse g (hMaximal g hg) x hOther (hBeing x r hx)) hx

end TruthCore.Results.Case.Catholicism.StageTwo.GodIsPerfect
