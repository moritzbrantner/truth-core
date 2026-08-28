import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter3

namespace TruthCore.Results.Aristotle.Physics.GenerationNotAlteration
open TruthCore.Greek.Aristotle.Physics

theorem generationNotAlteration
    (CompletedShapedProductDenominatedFromMatter
      AlteredMatterPredicatedByAffection GenerationIsAlteration : Prop)
    (hFormation : ShapedProductDenominatedFromMatterReading
      CompletedShapedProductDenominatedFromMatter)
    (hAffection : AlteredMatterPredicatedByAffectionReading
      AlteredMatterPredicatedByAffection)
    (hTransition :
      FormationPredicationContrastEntailsGenerationNotAlterationReading
        CompletedShapedProductDenominatedFromMatter
        AlteredMatterPredicatedByAffection GenerationIsAlteration) :
    GenerationIsNotAlterationReading GenerationIsAlteration := by
  exact hTransition ⟨hFormation, hAffection⟩

end TruthCore.Results.Aristotle.Physics.GenerationNotAlteration
