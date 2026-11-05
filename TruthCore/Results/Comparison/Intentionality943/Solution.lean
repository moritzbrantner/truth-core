module

public import TruthCore.Alternatives.Intentionality943
public import TruthCore.Models.Intentionality943
public import TruthCore.Logic.Configuration
public import TruthCore.Results.Comparison.MindPhysicalism.Solution

@[expose] public section
namespace TruthCore.Results.Comparison.Intentionality943
open TruthCore.Alternatives.MindPhysicalism
open TruthCore.Alternatives.Intentionality943
open TruthCore.Logic
open TruthCore.Results.Comparison.MindPhysicalism
open TruthCore.Models.Intentionality943

/-- The qualified self-report restriction would make every occurring judgment
true. This is a stipulated error-preservation constraint, not a physicalism proof. -/
theorem selfOnlyAccuracy {Occurrence Kind Content Situation : Type}
    (f : Frame Occurrence Kind) (s : Semantics Occurrence Content Situation)
    (hReport : AffectionReportCorrect f s)
    (hOnly : ContentOnlyAffectionReport f s) : EveryOccurrenceAccurate f s := by
  intro e w he ho
  exact (hOnly e w he).mpr (hReport e w he ho)

/-- Three incompatible commitments. Error supplies a nonempty token and
situation; neither source fidelity nor empirical truth follows. -/
theorem errorCore {Occurrence Kind Content Situation : Type}
    (f : Frame Occurrence Kind) (s : Semantics Occurrence Content Situation)
    (hError : SomeError f s) (hReport : AffectionReportCorrect f s)
    (hOnly : ContentOnlyAffectionReport f s) : ConfigurationFalse := by
  obtain ⟨e, w, he, ho, hFalse⟩ := hError
  exact hFalse (selfOnlyAccuracy f s hReport hOnly e w he ho)

/-- Given an error and the qualified report, the report-only content restriction
fails. No conclusion about a bearer’s physicality is present in this type. -/
theorem rejectAffectionOnly {Occurrence Kind Content Situation : Type}
    (f : Frame Occurrence Kind) (s : Semantics Occurrence Content Situation)
    (hError : SomeError f s) (hReport : AffectionReportCorrect f s) :
    RejectContentOnlyAffection f s :=
  fun hOnly => errorCore f s hError hReport hOnly

/-- One joint reductive causal/consumer/error interpretation exists. -/
theorem physicalistErrorModel : PhysicalistErrorModelExists := by
  exact ⟨Point, Bool, Unit, Bool, Unit, Unit, rivalFrame, falseAlarm, alarmConsumer,
    reductiveBackground, ⟨⟨.candidate, trivial⟩, trivial⟩, falseAlarmConsumer,
    falseAlarmReport, falseAlarmError,
    rejectAffectionOnly rivalFrame falseAlarm falseAlarmError falseAlarmReport⟩

/-- Delete the content/report identification: a populated, causally efficacious
physicalist interpretation retains error and correct affection-reporting. -/
theorem contentIdentificationOmission :
    CausalBackground rivalFrame ∧ Reductive rivalFrame ∧
    ConsumerContent rivalFrame falseAlarm alarmConsumer ∧
    SomeError rivalFrame falseAlarm ∧ AffectionReportCorrect rivalFrame falseAlarm ∧
    ¬ ContentOnlyAffectionReport rivalFrame falseAlarm := by
  exact ⟨reductiveBackground, ⟨⟨.candidate, trivial⟩, trivial⟩,
    falseAlarmConsumer, falseAlarmError, falseAlarmReport,
    rejectAffectionOnly rivalFrame falseAlarm falseAlarmError falseAlarmReport⟩

/-- Delete error. The other two commitments hold with an existing mental token;
this is not a control obtained by removing all occurrences. -/
theorem errorOmission :
    CausalBackground rivalFrame ∧ Reductive rivalFrame ∧
    AffectionReportCorrect rivalFrame occurrenceContent ∧
    ContentOnlyAffectionReport rivalFrame occurrenceContent ∧
    ¬ SomeError rivalFrame occurrenceContent ∧
    (∃ e w, rivalFrame.Mental e ∧ occurrenceContent.Occurs e w) := by
  refine ⟨reductiveBackground, ⟨⟨.candidate, trivial⟩, trivial⟩,
    fun _ _ _ ho => ho.2, fun _ _ _ => Iff.rfl, ?_,
    ⟨.candidate, false, trivial, rfl, rfl⟩⟩
  rintro ⟨_, _, _, ho, hn⟩
  exact hn ho.2

/-- Delete correctness of the qualified report. Error and the content/report
identification can coexist when the report is itself mistaken. -/
theorem reportCorrectnessOmission :
    CausalBackground rivalFrame ∧ Reductive rivalFrame ∧
    SomeError rivalFrame mistakenReport ∧
    ContentOnlyAffectionReport rivalFrame mistakenReport ∧
    ¬ AffectionReportCorrect rivalFrame mistakenReport := by
  refine ⟨reductiveBackground, ⟨⟨.candidate, trivial⟩, trivial⟩,
    falseAlarmError, fun _ _ _ => Iff.rfl, ?_⟩
  intro h
  exact Bool.noConfusion (h .candidate false trivial ⟨rfl, rfl⟩)

/-- The same finite causal/semantic interpretation also supports the old q.75
per-se-operation shape when the physical-basis/body-sharing bridge is omitted.
Content and error therefore do not supply that bridge. The q.75 operation here
is a stipulated formal witness, not an identification with actual human thought. -/
theorem bodySharingBridgeOmission :
    CausalBackground rivalFrame ∧ Reductive rivalFrame ∧
    ConsumerContent rivalFrame falseAlarm alarmConsumer ∧
    AffectionReportCorrect rivalFrame falseAlarm ∧ SomeError rivalFrame falseAlarm ∧
    ExerciseTokened rivalFrame (pointAttribution False) () candidateToken ∧
    ¬ PhysicalBasisIsBodySharing rivalFrame (pointAttribution False) () candidateToken ∧
    TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect.PerSeIntellectualOperation
      (pointAttribution False) () := by
  refine ⟨reductiveBackground, ⟨⟨.candidate, trivial⟩, trivial⟩,
    falseAlarmConsumer, falseAlarmReport, falseAlarmError,
    pointTokened _ _ _ _ _, ?_, pointPerSe⟩
  intro h
  exact h () .candidate trivial trivial trivial (Or.inl ⟨true, trivial, trivial⟩)

/-- Named certificate for the registered false-alarm interpretation. -/
theorem falseAlarmNotOnly : ¬ ContentOnlyAffectionReport rivalFrame falseAlarm :=
  rejectAffectionOnly rivalFrame falseAlarm falseAlarmError falseAlarmReport

end TruthCore.Results.Comparison.Intentionality943
