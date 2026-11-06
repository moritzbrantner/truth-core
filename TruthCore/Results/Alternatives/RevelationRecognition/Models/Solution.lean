module

public import TruthCore.Alternatives.RevelationRecognition
public import TruthCore.Case.Catholicism.StageThree.DivineFounding

@[expose] public section

namespace TruthCore.Results.Alternatives.RevelationRecognition.Models

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.RevelationRecognition
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding

/-- Selected predicates vary across the two candidate situations; no claim
that these formal situations exhaust actual possibility. -/
def profile (σ : Signature) (correct shared admitted : Bool → Prop) : RecognitionProfile σ where
  Situation := Bool
  admissible := admitted
  practice s :=
    { Move := Unit, Correct := fun _ => correct s, OwnStandard := fun _ => False,
      Defined := fun _ => False, AffirmsNaturalKnowability := fun _ => False,
      AnswersToSharedReason := fun _ => shared s }
  actual := false
  RecognizesAsDivine := fun _ _ _ => True

/-- Six exact scope controls, with no historical or modal-exhaustion claim. -/
theorem recognitionModels : RecognitionModels := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨modelSig True, profile (modelSig True) (fun s => s = true)
        (fun _ => True) (fun _ => True),
      ⟨true, rfl⟩, (fun _ _ => trivial), ?_, trivial, ?_, ?_, ?_, ?_⟩
    · intro _ _ hCorrect
      cases hCorrect
    · intro _ _ _
      exact ⟨true, trivial, (), trivial, rfl⟩
    · intro _ _ _ _ _ _ _; trivial
    · intro hAll
      exact hAll true trivial () trivial rfl
    · intro hPersistence
      have hActual : CutOffReading
          ((profile (modelSig True) (fun s => s = true) (fun _ => True)
            (fun _ => True)).practice false) := by
        intro _ _ hCorrect; cases hCorrect
      exact hPersistence hActual true trivial () trivial rfl
  · refine ⟨modelSig True, profile (modelSig True) (fun _ => False)
        (fun _ => True) (fun _ => True),
      ⟨true, rfl⟩, (fun _ _ => trivial), ?_, ?_, ?_⟩
    · intro _ _ _ _ hCorrect; exact hCorrect
    · intro _ _ _ _ _ _ _; trivial
    · intro hRealized
      obtain ⟨_, _, _, _, hCorrect⟩ := hRealized true rfl trivial
      exact hCorrect
  · refine ⟨modelSig True, profile (modelSig True) (fun _ => True)
        (fun _ => False) (fun _ => True),
      ⟨true, rfl⟩, (fun _ _ => trivial), ?_, ?_, ?_⟩
    · intro _ _ _ hShared; exact False.elim hShared
    · intro _ _ _; exact ⟨false, trivial, (), trivial, trivial⟩
    · intro hShared
      exact hShared false true () trivial rfl trivial trivial
  · let noGod : Signature := { modelSig True with IsGod := fun _ => False }
    refine ⟨noGod, profile noGod (fun _ => False) (fun _ => True) (fun _ => True),
      ?_, ?_, ?_, ?_, ?_⟩
    · intro hExists; obtain ⟨_, hGod⟩ := hExists; exact hGod
    · intro _ hGod; exact False.elim hGod
    · intro _ _ _ _ hCorrect; exact hCorrect
    · intro _ hGod; exact False.elim hGod
    · intro _ _ _ _ hGod; exact False.elim hGod
  · let noCapacity : Signature :=
      { modelSig True with RevealsRecognizably := fun _ => False }
    refine ⟨noCapacity, profile noCapacity (fun _ => True) (fun _ => True)
      (fun _ => True), ⟨true, rfl⟩, ?_, ?_⟩
    · intro _ _ hCapacity; exact False.elim hCapacity
    · intro hDefinition
      exact (hDefinition true rfl).2 ⟨false, trivial, (), trivial, trivial⟩
  · refine ⟨modelSig True, profile (modelSig True) (fun _ => True)
        (fun _ => True) (fun _ => False),
      ⟨true, rfl⟩, (fun _ _ => trivial), ?_, ?_, ?_, ?_⟩
    · intro _ _ _; exact ⟨false, (), trivial, trivial⟩
    · refine ⟨true, rfl, trivial, false, (fun h => h), (), trivial, trivial, ?_⟩
      intro hPossible; obtain ⟨_, hAdmitted, _⟩ := hPossible; exact hAdmitted
    · intro hCoverage
      obtain ⟨_, hAdmitted, _⟩ :=
        hCoverage true rfl trivial ⟨false, (), trivial, trivial⟩
      exact hAdmitted
    · intro hRealized
      obtain ⟨_, hAdmitted, _⟩ := hRealized true rfl trivial
      exact hAdmitted

end TruthCore.Results.Alternatives.RevelationRecognition.Models
