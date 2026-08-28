import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter3

namespace TruthCore.Results.Aristotle.Physics.HabitsNotAlterations
open TruthCore.Greek.Aristotle.Physics

theorem habitsNotAlterations
    (HabitsClassifiedAsVirtuesOrVices VirtueIsPerfection
      ViceIsCorruptionAndDeparture
      BodilyVirtuesAndVicesAreRelationalDispositions
      RelativeStatesAdmitNoIntrinsicChange
      HabitsOrTheirAcquisitionOrLossAreAlterations : Prop)
    (hKinds : VirtueViceHabitsArePerfectionsOrDeparturesReading
      HabitsClassifiedAsVirtuesOrVices VirtueIsPerfection
      ViceIsCorruptionAndDeparture)
    (hRelational : BodilyVirtuesAreRelationalDispositionsReading
      BodilyVirtuesAndVicesAreRelationalDispositions)
    (hNoChange : RelativeStatesAdmitNoIntrinsicChangeReading
      RelativeStatesAdmitNoIntrinsicChange)
    (hTransition : RelationalHabitAccountEntailsNoHabitAlterationReading
      HabitsClassifiedAsVirtuesOrVices
      BodilyVirtuesAndVicesAreRelationalDispositions
      RelativeStatesAdmitNoIntrinsicChange
      HabitsOrTheirAcquisitionOrLossAreAlterations) :
    HabitsAndAcquisitionOrLossAreNotAlterationsReading
      HabitsOrTheirAcquisitionOrLossAreAlterations := by
  exact hTransition ⟨hKinds.1, hRelational, hNoChange⟩

end TruthCore.Results.Aristotle.Physics.HabitsNotAlterations
