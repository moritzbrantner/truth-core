import TruthCore.Case.Catholicism.StageTwo
import TruthCore.Results.Aquinas.SummaTheologiae.AtMostOneMaximeEns.Solution
namespace TruthCore.Results.Case.Catholicism.StageTwo.GodIsOne
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism
theorem godIsOne {Being : Type} {Respect : Type}
    (IsGod : Being → Prop) (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hMaximal : GodIsMaximalInBeing IsGod InAct MoreIn esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    GodIsOne IsGod := by
  sorry
end TruthCore.Results.Case.Catholicism.StageTwo.GodIsOne
