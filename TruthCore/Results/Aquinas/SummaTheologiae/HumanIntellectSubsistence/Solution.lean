import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question75.Subsistence
import TruthCore.Results.Aquinas.SummaTheologiae.HumanIntellectIncorporeal.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.HumanIntellectNonorganic.Solution

namespace TruthCore.Results.Aquinas.SummaTheologiae.HumanIntellectSubsistence
open TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect

/-- Transcription (instantiation) of the remaining q.75 a.2 inference,
composing the two earlier reductios. The two extra philosophical premises
remain open. The conclusion excludes material/accidental inherence only;
it asserts neither a complete human person nor immortality. -/
theorem intellectSubsistsInWeakSense {Principle Nature Operation : Type}
    (m : Model Principle Nature) (through : Principle → Principle → Prop)
    (a : OperationAttribution Principle Operation) (intellect : Principle)
    (hScope : UniversalBodilyCognition m intellect)
    (hBodies : BodilyDeterminacy m)
    (hIntrinsic : NaturalBodilyInterference m intellect)
    (hOrgan : OrganBodilyInterference m through intellect)
    (hAttribution : NonorganicOperationAttribution m through a intellect)
    (hExistence : PerSeOperationRequiresSubsistence a) :
    SubsistsInWeakSense a intellect := by
  have hNotBody := HumanIntellectIncorporeal.intellectIsNotBody
    m intellect hScope hBodies hIntrinsic
  have hNoOrgan := HumanIntellectNonorganic.intellectUsesNoBodilyOrgan
    m through intellect hScope hBodies hOrgan
  exact hExistence intellect (hAttribution hNotBody hNoOrgan)

/-- Finite formal-schema control, not a possible-world or physicalist model. -/
theorem attributionOmission :
    ∃ (m : Model Unit Unit) (through : Unit → Unit → Prop)
      (a : OperationAttribution Unit Unit),
      UniversalBodilyCognition m () ∧ BodilyDeterminacy m ∧
      NaturalBodilyInterference m () ∧ OrganBodilyInterference m through () ∧
      PerSeOperationRequiresSubsistence a ∧
      ¬ NonorganicOperationAttribution m through a () ∧
      ¬ SubsistsInWeakSense a () := by
  let m : Model Unit Unit := ⟨(fun _ => False), (fun _ => True),
    (fun _ _ => False), (fun _ _ => True)⟩
  let through : Unit → Unit → Prop := fun _ _ => False
  let a : OperationAttribution Unit Unit := ⟨(fun _ _ => False),
    (fun _ => False), (fun _ => True), (fun _ => False)⟩
  refine ⟨m, through, a, (fun _ _ => trivial), (fun _ h => h.elim),
    (fun _ _ h => h.elim), (fun _ _ h => h.elim), ?_, ?_, ?_⟩
  · intro p h
    obtain ⟨_, hExercise, _⟩ := h
    exact hExercise.elim
  · intro h
    obtain ⟨_, hExercise, _⟩ := h (fun h => h.elim)
      (fun ⟨_, hBody, _⟩ => hBody.elim)
    exact hExercise
  · exact fun h => h trivial

/-- Finite formal-schema control, not a possible-world or physicalist model. -/
theorem existenceCorrespondenceOmission :
    ∃ (m : Model Unit Unit) (through : Unit → Unit → Prop)
      (a : OperationAttribution Unit Unit),
      UniversalBodilyCognition m () ∧ BodilyDeterminacy m ∧
      NaturalBodilyInterference m () ∧ OrganBodilyInterference m through () ∧
      NonorganicOperationAttribution m through a () ∧
      ¬ PerSeOperationRequiresSubsistence a ∧ ¬ SubsistsInWeakSense a () := by
  let m : Model Unit Unit := ⟨(fun _ => False), (fun _ => True),
    (fun _ _ => False), (fun _ _ => True)⟩
  let through : Unit → Unit → Prop := fun _ _ => False
  let a : OperationAttribution Unit Unit := ⟨(fun _ _ => True),
    (fun _ => False), (fun _ => True), (fun _ => False)⟩
  refine ⟨m, through, a, (fun _ _ => trivial), (fun _ h => h.elim),
    (fun _ _ h => h.elim), (fun _ _ h => h.elim),
    (fun _ _ => ⟨(), trivial, (fun h => h.elim)⟩), ?_, ?_⟩
  · exact fun h => h () ⟨(), trivial, (fun h => h.elim)⟩ trivial
  · exact fun h => h trivial

/-- Finite formal-schema control, not a possible-world or physicalist model. -/
theorem weakSubsistenceDoesNotRequireCompleteness :
    ∃ a : OperationAttribution Unit Unit,
      PerSeIntellectualOperation a () ∧ PerSeOperationRequiresSubsistence a ∧
      SubsistsInWeakSense a () ∧ ¬ SubsistsAsComplete a () := by
  let a : OperationAttribution Unit Unit := ⟨(fun _ _ => True),
    (fun _ => False), (fun _ => False), (fun _ => False)⟩
  exact ⟨a, ⟨(), trivial, (fun h => h.elim)⟩,
    (fun _ _ h => h.elim), (fun h => h.elim), (fun h => h.2)⟩

end TruthCore.Results.Aquinas.SummaTheologiae.HumanIntellectSubsistence
