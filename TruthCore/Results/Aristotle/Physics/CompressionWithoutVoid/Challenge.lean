import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter9

namespace TruthCore.Results.Aristotle.Physics.CompressionWithoutVoid

open TruthCore.Greek.Aristotle.Physics

/-- The same matter's potentiality for both magnitudes removes the need for added void. -/
theorem compressionWithoutVoid
    (SameMatterIsPotentiallyLargeAndSmall
      CompressionOrExpansionRequiresAddedVoid : Prop)
    (hMatter :
      SameMatterPotentiallyLargeAndSmallReading SameMatterIsPotentiallyLargeAndSmall)
    (hBridge :
      SameMatterPotentialityExcludesAddedVoidReading
        SameMatterIsPotentiallyLargeAndSmall
        CompressionOrExpansionRequiresAddedVoid) :
    CompressionAndExpansionDoNotRequireVoidReading
      CompressionOrExpansionRequiresAddedVoid := by
  sorry

end TruthCore.Results.Aristotle.Physics.CompressionWithoutVoid
