import TruthCore.Greek.Aristotle.Physics.BookII.Chapter8

namespace TruthCore.Results.Aristotle.Physics.NaturalTeleology

open TruthCore.Greek.Aristotle.Physics

/-- Regular natural outcomes satisfy Aristotle's stated bridge to teleology. -/
theorem naturalThingsActForEnds
    (NaturalOutcomesAreAlwaysOrUsual NaturalRegularityIsChanceOrSpontaneous
      NaturalThingsActForEnds : Prop)
    (hRegular : NaturalOutcomesAlwaysOrUsualReading NaturalOutcomesAreAlwaysOrUsual)
    (hNotChance :
      ChanceSpontaneityDoNotExplainNaturalRegularityReading
        NaturalRegularityIsChanceOrSpontaneous)
    (hBridge :
      NaturalRegularityImpliesTeleologyReading
        NaturalOutcomesAreAlwaysOrUsual NaturalRegularityIsChanceOrSpontaneous
        NaturalThingsActForEnds) :
    NaturalThingsActForEndsReading NaturalThingsActForEnds := by
  sorry

end TruthCore.Results.Aristotle.Physics.NaturalTeleology
