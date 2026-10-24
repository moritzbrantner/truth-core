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
  intro hAlterationEffect hGrowthEffect
  exact
    ⟨fun hGuaranteed => hThreshold.1 (hAlterationEffect hGuaranteed),
      fun hGuaranteed => hThreshold.2 (hGrowthEffect hGuaranteed)⟩

end TruthCore.Results.Aristotle.Physics.NoGuaranteedHalfAgentChange
