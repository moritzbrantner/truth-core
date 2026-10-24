import TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaSuccessionNeedsInfinitePast.Solution
import TruthCore.Refutations.TertiaVia
namespace TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaFinitePastExcludesSuccession
open TruthCore.Logic
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Refutations.TertiaVia
theorem finitePastExcludesSuccession {Being Time : Type}
    (IsAt : Being → Time → Prop) (Before : Time → Time → Prop) (now : Time)
    (hEM : ExcludedMiddle)
    (hFinite : PastIsFinite Before now)
    (hBegin : NothingBeginsExceptThroughWhatIsReading IsAt Before)
    (hNow : SomethingNowIsReading IsAt now) :
    SuccessionWithoutBeginningFails IsAt Before := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaFinitePastExcludesSuccession
