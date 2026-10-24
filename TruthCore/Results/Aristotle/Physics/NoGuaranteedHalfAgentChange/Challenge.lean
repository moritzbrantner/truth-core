import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter5

namespace TruthCore.Results.Aristotle.Physics.NoGuaranteedHalfAgentChange
open TruthCore.Greek.Aristotle.Physics

theorem noGuaranteedHalfAgentChange
    (HalfAltererProducesAnyAlteration HalfGrowerProducesAnyGrowth
      GuaranteedHalfAltererProportionalEffect
      GuaranteedHalfGrowerProportionalEffect : Prop)
    (hThreshold : HalfAltererGrowerMayProduceNoChangeReading
      HalfAltererProducesAnyAlteration HalfGrowerProducesAnyGrowth) :
    NoGuaranteedHalfAgentProportionalChangeReading
      HalfAltererProducesAnyAlteration HalfGrowerProducesAnyGrowth
      GuaranteedHalfAltererProportionalEffect
      GuaranteedHalfGrowerProportionalEffect := by
  sorry

end TruthCore.Results.Aristotle.Physics.NoGuaranteedHalfAgentChange
