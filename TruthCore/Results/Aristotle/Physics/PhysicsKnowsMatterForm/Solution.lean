import TruthCore.Greek.Aristotle.Physics.BookII.Chapter2

namespace TruthCore.Results.Aristotle.Physics.PhysicsKnowsMatterForm

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's craft analogy assigns both matter and form to physical science. -/
theorem physicsKnowsMatterAndForm
    (ArtImitatesNature OneCraftKnowsFormAndMatterUpToPoint
      PhysicsKnowsMatterAndForm : Prop)
    (hImitation : ArtImitatesNatureReading ArtImitatesNature)
    (hCraft :
      CraftKnowsFormAndMatterUpToPointReading
        OneCraftKnowsFormAndMatterUpToPoint)
    (hTransfer :
      CraftAnalogyTransfersMatterFormKnowledgeReading
        ArtImitatesNature OneCraftKnowsFormAndMatterUpToPoint
        PhysicsKnowsMatterAndForm) :
    PhysicsKnowsMatterAndFormReading PhysicsKnowsMatterAndForm := by
  exact hTransfer ⟨hImitation, hCraft⟩

end TruthCore.Results.Aristotle.Physics.PhysicsKnowsMatterForm
