module

public import TruthCore.Results.Metaethics.GoodnessFormEndBoundary.Solution

@[expose] public section
namespace TruthCore.Results.Metaethics.GoodnessDueToUnrestricted
open TruthCore.Metaethics.GoodnessFormEnd
open TruthCore.Latin.Aquinas.SummaTheologiae

theorem dueToUnrestricted (f : Frame) (hThesis : DueActualityThesis f)
    (hActualDue : AllActualitiesDue f) : GoodnessIsActualityReading f.GoodIn f.Has :=
  (TruthCore.Results.Metaethics.GoodnessFormEndBoundary.routeBridge f hThesis).mpr hActualDue
end TruthCore.Results.Metaethics.GoodnessDueToUnrestricted
