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
  sorry
end TruthCore.Results.Case.Catholicism.StageTwo.GodIsPerfect
