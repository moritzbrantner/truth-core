import TruthCore.Logic.ExcludedMiddle
import TruthCore.Refutations.TertiaVia
namespace TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaSuccessionNeedsInfinitePast
open TruthCore.Logic
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Refutations.TertiaVia
theorem successionNeedsInfinitePast {Being Time : Type}
    (IsAt : Being → Time → Prop) (Before : Time → Time → Prop) (now : Time)
    (hEM : ExcludedMiddle)
    (hBegin : NothingBeginsExceptThroughWhatIsReading IsAt Before)
    (hNow : SomethingNowIsReading IsAt now) :
    SuccessionRequiresInfinitePast IsAt Before now := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaSuccessionNeedsInfinitePast
