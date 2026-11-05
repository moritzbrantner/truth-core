module

public import TruthCore.Alternatives.Intentionality943
public import TruthCore.Results.Comparison.MindPhysicalism.Solution
public import TruthCore.Models.FiniteSupport

@[expose] public section
namespace TruthCore.Models.Intentionality943
open TruthCore.Alternatives.MindPhysicalism
open TruthCore.Alternatives.Intentionality943
open TruthCore.Results.Comparison.MindPhysicalism

/-- Reuse the existing non-vacuous reductive causal interpretation. -/
def rivalFrame : Frame Point Bool := pointFrame True False True True True False

/-- `false`: no threat; `true`: threat. The candidate signal occurs without a
threat. Its content is threat-present. Its accurate self-report concerns its
occurrence, not the threat. This is an abstract false alarm, not ethological data. -/
def falseAlarm : Semantics Point Unit Bool where
  content := fun _ => ()
  Holds := fun _ w => w = true
  Occurs := fun e w => e = .candidate ∧ w = false
  Report := fun e w => e = .candidate ∧ w = false

/-- One selected response and one specific end. The stipulated success
condition is threat-presence. No evolutionary history, behavior or cognition
is proved to exist merely by filling these primitive fields. -/
def alarmConsumer : Consumer Point Unit Unit Bool where
  SelectedFor := fun e _ _ => e = .candidate
  SuccessCondition := fun _ _ w => w = true

theorem falseAlarmError : SomeError rivalFrame falseAlarm := by
  exact ⟨.candidate, false, trivial, ⟨rfl, rfl⟩, Bool.noConfusion⟩

theorem falseAlarmReport : AffectionReportCorrect rivalFrame falseAlarm := by
  intro _ _ _ ho
  exact ho

theorem falseAlarmConsumer : ConsumerContent rivalFrame falseAlarm alarmConsumer := by
  intro e he
  cases e with
  | candidate => exact ⟨(), (), rfl, fun _ => Iff.rfl⟩
  | base => exact he.elim
  | effect => exact he.elim


/-- Make the content an occurrence-report. Then the occurring candidate is
accurate, while every contrary situation still has false content. -/
def occurrenceContent : Semantics Point Unit Bool where
  content := fun _ => ()
  Holds := fun _ w => w = false
  Occurs := fun e w => e = .candidate ∧ w = false
  Report := fun _ w => w = false


/-- Alter only the proposed self-report: it is now false when the signal occurs.
This removes the restriction *as it is affected*, not the external error. -/
def mistakenReport : Semantics Point Unit Bool :=
  { falseAlarm with Report := fun _ w => w = true }


/-- Explicit finite carrier coverage for the reused three-point interpretation. -/
theorem enumeratePoint (x : Point) :
    x = .candidate ∨ x = .base ∨ x = .effect := by
  cases x with
  | candidate => exact Or.inl rfl
  | base => exact Or.inr (Or.inl rfl)
  | effect => exact Or.inr (Or.inr rfl)

theorem occurrenceReportCorrect : AffectionReportCorrect rivalFrame occurrenceContent :=
  fun _ _ _ ho => ho.2

theorem occurrenceIdentification : ContentOnlyAffectionReport rivalFrame occurrenceContent :=
  fun _ _ _ => Iff.rfl

theorem occurrenceNoError : ¬ SomeError rivalFrame occurrenceContent := by
  rintro ⟨_, _, _, ho, hn⟩
  exact hn ho.2

theorem mistakenError : SomeError rivalFrame mistakenReport := falseAlarmError

theorem mistakenIdentification : ContentOnlyAffectionReport rivalFrame mistakenReport :=
  fun _ _ _ => Iff.rfl

theorem mistakenReportIncorrect : ¬ AffectionReportCorrect rivalFrame mistakenReport := by
  intro h
  exact Bool.noConfusion (h .candidate false trivial ⟨rfl, rfl⟩)

end TruthCore.Models.Intentionality943
