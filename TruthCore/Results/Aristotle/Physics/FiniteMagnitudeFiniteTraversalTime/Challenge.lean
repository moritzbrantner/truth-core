import TruthCore.Greek.Aristotle.Physics.BookVI.Chapter7
namespace TruthCore.Results.Aristotle.Physics.FiniteMagnitudeFiniteTraversalTime
open TruthCore.Greek.Aristotle.Physics
theorem finiteMagnitudeFiniteTraversalTime
    (MagnitudeTraversalFinite HasFiniteSegmentMeasure
      AllMeasuringSegmentTimesFinite WholeTraversalTimeFinite : Prop)
    (hMeasure : FiniteMagnitudeHasFiniteSegmentMeasureReading
      MagnitudeTraversalFinite HasFiniteSegmentMeasure)
    (hSegmentTimes : EachMeasuringSegmentHasFiniteTraversalTimeReading
      HasFiniteSegmentMeasure AllMeasuringSegmentTimesFinite)
    (hCompose : FiniteSegmentTimesYieldFiniteWholeTimeReading
      HasFiniteSegmentMeasure AllMeasuringSegmentTimesFinite
      WholeTraversalTimeFinite) :
    FiniteMagnitudeTraversalHasFiniteTimeReading
      MagnitudeTraversalFinite WholeTraversalTimeFinite := by
  sorry
end TruthCore.Results.Aristotle.Physics.FiniteMagnitudeFiniteTraversalTime
