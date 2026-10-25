import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter5

namespace TruthCore.Results.Aristotle.Physics.NoGuaranteedHalfAgentChange
open TruthCore.Greek.Aristotle.Physics

/-- A case in which the halved agent fails refutes the guarantee that it
succeeds in every case. A transcription (invariant 16): the cases and effects are
opaque. -/
theorem noGuaranteedHalfAgentChange {Case : Type}
    (HalfAltererAltersIn HalfGrowerGrowsIn : Case → Prop)
    (hThreshold : HalfAltererGrowerMayProduceNoChangeReading HalfAltererAltersIn
      HalfGrowerGrowsIn) :
    NoGuaranteedHalfAgentProportionalChangeReading HalfAltererAltersIn HalfGrowerGrowsIn := by
  obtain ⟨⟨c, hNoAlteration⟩, ⟨c', hNoGrowth⟩⟩ := hThreshold
  exact ⟨fun hAll => hNoAlteration (hAll c), fun hAll => hNoGrowth (hAll c')⟩

end TruthCore.Results.Aristotle.Physics.NoGuaranteedHalfAgentChange
