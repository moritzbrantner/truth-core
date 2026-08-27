import TruthCore.Greek.Aristotle.Physics.BookI.Chapter8
namespace TruthCore.Results.Aristotle.Physics.PredecessorNoGeneration
open TruthCore.Greek.Aristotle.Physics
theorem predecessorDeniesGeneration (GenerationOccurs FromBeing FromNotBeing : Prop)
    (hSources : PredecessorGenerationSourceDilemmaReading GenerationOccurs FromBeing FromNotBeing)
    (hNotBeing : PredecessorRejectsGenerationFromBeingReading FromBeing)
    (hNotNotBeing : PredecessorRejectsGenerationFromNotBeingReading FromNotBeing) :
    PredecessorDeniesGenerationReading GenerationOccurs := by
  sorry
end TruthCore.Results.Aristotle.Physics.PredecessorNoGeneration
