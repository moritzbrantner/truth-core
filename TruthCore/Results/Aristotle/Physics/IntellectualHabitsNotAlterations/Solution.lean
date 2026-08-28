import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter3

namespace TruthCore.Results.Aristotle.Physics.IntellectualHabitsNotAlterations
open TruthCore.Greek.Aristotle.Physics

theorem intellectualHabitsNotAlterations
    (IntellectualKnowledgeIsRelational
      PotentialKnowerActualizedWithoutSelfMotion UniversalKnownThroughParticular
      IntellectComesToKnowByResting NoGenerationIntoRest
      IntellectualHabitsAreAlterations IntellectualHabitsHaveGeneration : Prop)
    (hRelational : IntellectualKnowledgeIsRelationalReading
      IntellectualKnowledgeIsRelational)
    (hPotential : PotentialKnowerActualizedWithoutSelfMotionReading
      PotentialKnowerActualizedWithoutSelfMotion UniversalKnownThroughParticular)
    (hRest : IntellectualKnowingThroughRestReading
      IntellectComesToKnowByResting NoGenerationIntoRest)
    (hTransition : IntellectualAccountEntailsNoAlterationOrGenerationReading
      IntellectualKnowledgeIsRelational
      PotentialKnowerActualizedWithoutSelfMotion
      IntellectComesToKnowByResting NoGenerationIntoRest
      IntellectualHabitsAreAlterations IntellectualHabitsHaveGeneration) :
    IntellectualHabitsAreNotAlterationsOrGeneratedReading
      IntellectualHabitsAreAlterations IntellectualHabitsHaveGeneration := by
  exact hTransition ⟨hRelational, hPotential.1, hRest.1, hRest.2⟩

end TruthCore.Results.Aristotle.Physics.IntellectualHabitsNotAlterations
