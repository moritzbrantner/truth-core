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
  exact hTransition
    ⟨hEthical, hModes, hSensibles, hPleasureHabit.1, hPleasureHabit.2⟩

end TruthCore.Results.Aristotle.Physics.MoralHabitsSensitiveAlteration
