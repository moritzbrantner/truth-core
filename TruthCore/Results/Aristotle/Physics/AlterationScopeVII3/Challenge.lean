import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter3

namespace TruthCore.Results.Aristotle.Physics.AlterationScopeVII3
open TruthCore.Greek.Aristotle.Physics

theorem alterationScopeVII3
    (EveryAlteredThingAlteredBySensibles
      AlterationOnlyInPerSeSensiblyAffectedSubjects
      MoralHabitsAriseWithSensitiveAlteration MoralHabitsAreAlterations
      IntellectualHabitsAreAlterations IntellectualHabitsHaveGeneration
      BodilyAlterationsAccompanyIntellectualSettling
      AlterationOccursInSensibles AlterationOccursInSensitivePartOfSoul
      AlterationOccursPerSeElsewhere : Prop)
    (hOpening : AlterationRestrictedToSensibleAffectionReading
      EveryAlteredThingAlteredBySensibles
      AlterationOnlyInPerSeSensiblyAffectedSubjects)
    (hMoral : MoralHabitsAriseWithAlterationButAreNotAlterationsReading
      MoralHabitsAriseWithSensitiveAlteration MoralHabitsAreAlterations)
    (hIntellectual : IntellectualHabitsAreNotAlterationsOrGeneratedReading
      IntellectualHabitsAreAlterations IntellectualHabitsHaveGeneration)
    (hBodily : BodilyAlterationsAccompanyIntellectualSettlingReading
      BodilyAlterationsAccompanyIntellectualSettling)
    (hTransition : ChapterThreeAccountEntailsAlterationScopeReading
      EveryAlteredThingAlteredBySensibles
      AlterationOnlyInPerSeSensiblyAffectedSubjects
      MoralHabitsAriseWithSensitiveAlteration
      IntellectualHabitsAreAlterations IntellectualHabitsHaveGeneration
      BodilyAlterationsAccompanyIntellectualSettling
      AlterationOccursInSensibles AlterationOccursInSensitivePartOfSoul
      AlterationOccursPerSeElsewhere) :
    AlterationPerSeOnlyInSensiblesAndSensitiveSoulReading
      AlterationOccursInSensibles AlterationOccursInSensitivePartOfSoul
      AlterationOccursPerSeElsewhere := by
  sorry

end TruthCore.Results.Aristotle.Physics.AlterationScopeVII3
