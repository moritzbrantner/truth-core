import TruthCore.Greek.Aristotle.Physics.BookI.Chapter5

namespace TruthCore.Results.Aristotle.Physics.NaturalBecomingFromContraries

open TruthCore.Greek.Aristotle.Physics

/--
If natural becoming is from a contrary or an intermediate, and the relevant intermediate is
derived from contraries, then it is from a contrary or from contraries.
-/
theorem naturalBecomingFromContraryOrContraries
    (FromContrary FromIntermediate FromContraries : Prop)
    (hAlternatives :
      BecomingFromContraryOrIntermediateReading FromContrary FromIntermediate)
    (hIntermediate :
      IntermediatesDerivedFromContrariesReading FromIntermediate FromContraries) :
    NaturalBecomingFromContraryOrContrariesReading FromContrary FromContraries := by
  sorry

end TruthCore.Results.Aristotle.Physics.NaturalBecomingFromContraries
