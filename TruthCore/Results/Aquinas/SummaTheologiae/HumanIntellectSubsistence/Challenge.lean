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
  sorry

theorem attributionOmission :
    ∃ (m : Model Unit Unit) (through : Unit → Unit → Prop)
      (a : OperationAttribution Unit Unit),
      UniversalBodilyCognition m () ∧ BodilyDeterminacy m ∧
      NaturalBodilyInterference m () ∧ OrganBodilyInterference m through () ∧
      PerSeOperationRequiresSubsistence a ∧
      ¬ NonorganicOperationAttribution m through a () ∧
      ¬ SubsistsInWeakSense a () := by
  sorry

theorem existenceCorrespondenceOmission :
    ∃ (m : Model Unit Unit) (through : Unit → Unit → Prop)
      (a : OperationAttribution Unit Unit),
      UniversalBodilyCognition m () ∧ BodilyDeterminacy m ∧
      NaturalBodilyInterference m () ∧ OrganBodilyInterference m through () ∧
      NonorganicOperationAttribution m through a () ∧
      ¬ PerSeOperationRequiresSubsistence a ∧ ¬ SubsistsInWeakSense a () := by
  sorry

theorem weakSubsistenceDoesNotRequireCompleteness :
    ∃ a : OperationAttribution Unit Unit,
      PerSeIntellectualOperation a () ∧ PerSeOperationRequiresSubsistence a ∧
      SubsistsInWeakSense a () ∧ ¬ SubsistsAsComplete a () := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.HumanIntellectSubsistence
