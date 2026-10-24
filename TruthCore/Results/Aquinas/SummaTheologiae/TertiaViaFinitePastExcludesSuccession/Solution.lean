import TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaSuccessionNeedsInfinitePast.Solution
import TruthCore.Refutations.TertiaVia
namespace TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaFinitePastExcludesSuccession
open TruthCore.Logic
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Refutations.TertiaVia

/-- On the finite-past horn the rival fails: succession without beginning would
make the past infinite (`TERTIA-VIA-SUCCESSION-REQUIRES-INFINITE-PAST`), but some
time up to now has no earlier time. -/
theorem finitePastExcludesSuccession {Being Time : Type}
    (IsAt : Being → Time → Prop) (Before : Time → Time → Prop) (now : Time)
    (hEM : ExcludedMiddle)
    (hFinite : PastIsFinite Before now)
    (hBegin : NothingBeginsExceptThroughWhatIsReading IsAt Before)
    (hNow : SomethingNowIsReading IsAt now) :
    SuccessionWithoutBeginningFails IsAt Before := by
  intro hSuccession
  -- INF-AQUINAS-SUCCESSION-REQUIRES-INFINITE-PAST-RESULT (result TERTIA-VIA-SUCCESSION-REQUIRES-INFINITE-PAST)
  have hInfinite : PastIsInfinite Before now :=
    TertiaViaSuccessionNeedsInfinitePast.successionNeedsInfinitePast IsAt Before now hEM
      hBegin hNow hSuccession
  -- INF-AQUINAS-FINITE-PAST-EXCLUDES-SUCCESSION
  obtain ⟨t, hUpToNow, hFirst⟩ := hFinite
  obtain ⟨t', hEarlier⟩ := hInfinite t hUpToNow
  exact hFirst t' hEarlier

end TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaFinitePastExcludesSuccession
