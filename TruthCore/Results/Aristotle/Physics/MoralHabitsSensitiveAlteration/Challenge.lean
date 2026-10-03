import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter3

namespace TruthCore.Results.Aristotle.Physics.MoralHabitsSensitiveAlteration
open TruthCore.Greek.Aristotle.Physics

theorem moralHabitsSensitiveAlteration
    (EthicalVirtueConcernsBodilyPleasureAndPain
      ActionMemoryExpectationPleasuresDependOnSensation
      BodilyPleasuresUnderDiscussionAriseFromSensibles
      PleasureAndPainAlterSensitivePart
      VirtueAndViceAriseWithPleasureAndPain
      MoralHabitsAriseWithSensitiveAlteration MoralHabitsAreAlterations : Prop)
    (hEthical : EthicalVirtueConcernsBodilyPleasurePainReading
      EthicalVirtueConcernsBodilyPleasureAndPain)
    (hModes : ActionMemoryExpectationPleasuresDependOnSensationReading
      ActionMemoryExpectationPleasuresDependOnSensation)
    (hSensibles : BodilyPleasuresUnderDiscussionAriseFromSensiblesReading
      BodilyPleasuresUnderDiscussionAriseFromSensibles)
    (hPleasureHabit : PleasurePainAlterSensitivePartAndHabitsAriseReading
      PleasureAndPainAlterSensitivePart VirtueAndViceAriseWithPleasureAndPain)
    (hTransition : SensoryAccountEntailsMoralHabitsWithAlterationReading
      EthicalVirtueConcernsBodilyPleasureAndPain
      ActionMemoryExpectationPleasuresDependOnSensation
      BodilyPleasuresUnderDiscussionAriseFromSensibles
      PleasureAndPainAlterSensitivePart
      VirtueAndViceAriseWithPleasureAndPain
      MoralHabitsAriseWithSensitiveAlteration MoralHabitsAreAlterations) :
    MoralHabitsAriseWithAlterationButAreNotAlterationsReading
      MoralHabitsAriseWithSensitiveAlteration MoralHabitsAreAlterations := by
  sorry

end TruthCore.Results.Aristotle.Physics.MoralHabitsSensitiveAlteration
