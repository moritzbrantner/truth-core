import TruthCore.Greek.Aristotle.Physics.BookII.Chapter8

namespace TruthCore.Results.Aristotle.Physics.NaturalErrorTeleology

open TruthCore.Greek.Aristotle.Physics

/-- Artistic failure establishes the compatibility of natural error with teleology. -/
theorem naturalErrorsCompatibleWithTeleology
    (ArtAimsAtEnds ArtCanFailToReachItsEnd NaturalErrorsCompatibleWithTeleology : Prop)
    (hArt : ArtCanFailWhileAimingAtEndReading ArtAimsAtEnds ArtCanFailToReachItsEnd)
    (hAnalogy :
      ArtNatureErrorAnalogyReading
        (ArtCanFailWhileAimingAtEndReading ArtAimsAtEnds ArtCanFailToReachItsEnd)
        NaturalErrorsCompatibleWithTeleology) :
    NaturalErrorsCompatibleWithTeleologyReading NaturalErrorsCompatibleWithTeleology := by
  sorry

end TruthCore.Results.Aristotle.Physics.NaturalErrorTeleology
