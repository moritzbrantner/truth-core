import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question5.Article1
namespace TruthCore.Results.Aquinas.SummaTheologiae.GoodnessFromDesirability
open TruthCore.Latin.Aquinas.SummaTheologiae
theorem goodnessIsActualityFromDesirability {Being Perfection : Type}
    (GoodIn DesirableIn PerfectIn Has : Being → Perfection → Prop)
    (hGood : GoodIsDesirableReading GoodIn DesirableIn)
    (hDesirable : DesirableInsofarAsPerfectReading DesirableIn PerfectIn)
    (hPerfect : PerfectInsofarAsInActReading PerfectIn Has) :
    GoodnessIsActualityReading GoodIn Has := by
  sorry
theorem premisesNeeded : GoodnessFromDesirabilityPremisesNeeded := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.GoodnessFromDesirability
