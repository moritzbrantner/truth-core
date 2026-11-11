module
public import TruthCore.Science.FineTuningEvidence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
@[expose] public section
namespace TruthCore.Results.Science.FineTuningEvidence
open TruthCore.Science.FineTuningSelection TruthCore.Science.FineTuningEvidence

theorem factorization : Factorization := by
  intro d n
  have hd := ne_of_gt d.observers_pos
  have hn := ne_of_gt n.observers_pos
  have he := ne_of_gt n.evidence_pos
  have hf : factor d n = raw d n / observer d n := by
    unfold factor likelihood raw observer
    field_simp
  have ho : 0 < observer d n := div_pos d.observers_pos n.observers_pos
  refine ⟨hf, ?_, ?_, ?_⟩
  · rw [hf, lt_div_iff₀ ho]; simp
  · rw [hf, div_eq_one_iff_eq (ne_of_gt ho)]
  · intro h₁ h₂
    simp [factor, likelihood, h₁, h₂, ne_of_gt d.evidence_pos, he]

theorem controls : Controls := by
  norm_num [Controls, raw, observer, factor, likelihood, design, natural,
    selectedNatural, screenedDesign, screenedNatural]

theorem invariance : PushforwardInvariance := by
  intro X Y _ _ f d n e o
  have h (μ : MeasureTheory.Measure X) (s : Set X) :
      (μ.map f) (f '' s) = μ s := by
    rw [f.map_apply, Set.preimage_image_eq _ f.injective]
  refine ⟨h d e, h n e, ?_, ?_⟩
  · simp only [eventFactor, h]
  · unfold conditionalFactor
    rw [← Set.image_inter f.injective, h, h, h, h]
end TruthCore.Results.Science.FineTuningEvidence
