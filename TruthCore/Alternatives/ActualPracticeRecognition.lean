module

public import TruthCore.Alternatives.RevelationRecognition

/-! Stipulative RECOGNIZABLE_REVELATION_2: recognition and grammatical
correctness of the same move in the distinguished actual practice. This does
not assert external truth, Godhood, capability, admissibility or shared reason.
The recognition and correctness predicates retain their existing primitive
interpretations; neither is inferred from the other. -/

@[expose] public section

namespace TruthCore.Alternatives.RevelationRecognition

open TruthCore.Case.Catholicism
open TruthCore.Alternatives.Fideism

/-- Recognition of the selected being and correctness of the selected actual
move. No restriction to God candidates or to admitted situations is added. -/
def ActualPracticeRecognition (σ : Signature) (R : RecognitionProfile σ)
    (g : σ.Being) (m : (R.practice R.actual).Move) : Prop :=
  R.RecognizesAsDivine R.actual g m ∧ (R.practice R.actual).Correct m

/-- Moving actual uptake into the admitted domain needs the explicit bridge. -/
theorem actualRecognitionPossible (σ : Signature) (R : RecognitionProfile σ)
    (g : σ.Being) (m : (R.practice R.actual).Move)
    (h : ActualPracticeRecognition σ R g m) (ha : ActualAdmissible σ R) :
    PossibleCorrectRecognition σ R g :=
  ⟨R.actual, ha, m, h⟩

/-- A shared actual recognition move conflicts with actual cut-off only when
correctness is retained. Private correct uptake is not thereby excluded. -/
theorem actualRecognitionNotShared (σ : Signature) (R : RecognitionProfile σ)
    (g : σ.Being) (m : (R.practice R.actual).Move)
    (h : ActualPracticeRecognition σ R g m)
    (hc : CutOffReading (R.practice R.actual)) :
    ¬ (R.practice R.actual).AnswersToSharedReason m :=
  fun hs => hc m hs h.2

/-- Parameterized control over the original, unrestricted Being carrier.
The Boolean index only supplies two test situations, not an intended modal
exhaustion. The two flags vary recognition and correctness independently. -/
def uptakeControl (σ : Signature) (recognition correctness : Bool) : RecognitionProfile σ where
  Situation := Bool
  admissible := fun _ => True
  actual := false
  practice := fun s => {
    Move := Unit
    Correct := fun _ => s = true ∨ correctness = true
    OwnStandard := fun _ => False
    Defined := fun _ => False
    AffirmsNaturalKnowability := fun _ => False
    AnswersToSharedReason := fun _ => False }
  RecognizesAsDivine := fun s _ _ => s = true ∨ recognition = true

/-- Merely possible uptake, recognition without correctness, correctness
without recognition, and absent actual uptake all fail actual recognition.
Both flags together give a nonvacuous actual witness. -/
theorem actualUptakeControls (σ : Signature) (g : σ.Being) :
    PossibleCorrectRecognition σ (uptakeControl σ false false) g ∧
    ¬ ActualPracticeRecognition σ (uptakeControl σ false false) g () ∧
    ¬ ActualPracticeRecognition σ (uptakeControl σ true false) g () ∧
    ¬ ActualPracticeRecognition σ (uptakeControl σ false true) g () ∧
    ActualPracticeRecognition σ (uptakeControl σ true true) g () := by
  refine ⟨⟨true, True.intro, (), Or.inl rfl, Or.inl rfl⟩, ?_, ?_, ?_, ?_⟩
  all_goals simp [ActualPracticeRecognition, uptakeControl]

end TruthCore.Alternatives.RevelationRecognition
