import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter5

namespace TruthCore.Results.Aristotle.Physics.NoGuaranteedHalfAgentChange
open TruthCore.Greek.Aristotle.Physics

theorem noGuaranteedHalfAgentChange {Case : Type}
    (HalfAltererAltersIn HalfGrowerGrowsIn : Case → Prop)
    (hThreshold : HalfAltererGrowerMayProduceNoChangeReading HalfAltererAltersIn
      HalfGrowerGrowsIn) :
    NoGuaranteedHalfAgentProportionalChangeReading HalfAltererAltersIn HalfGrowerGrowsIn := by
  sorry

end TruthCore.Results.Aristotle.Physics.NoGuaranteedHalfAgentChange
