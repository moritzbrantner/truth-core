module
public import TruthCore.Alternatives.ReligiousExperienceRecognition
@[expose] public section
namespace TruthCore.Results.Alternatives.ReligiousExperienceRecognition
open TruthCore.Case.Catholicism
open TruthCore.Alternatives.RevelationRecognition
open TruthCore.Alternatives.ReligiousExperienceRecognition
theorem recognition (σ : Signature) (R : RecognitionProfile σ) (E : Experience σ R)
    (ho : Occurrence E) (hc : Calibrated E) (hi : Identified E) : RecognizedGod σ R := by
  obtain ⟨e, he, hd⟩ := ho
  obtain ⟨hg, ha, hr, hm⟩ := hi e (hc e he hd)
  exact ⟨E.candidate e, hg, E.situation e, ha, E.move e, hr, hm⟩
theorem permission (σ : Signature) (R : RecognitionProfile σ) (E : Experience σ R)
    (ho : Occurrence E) (hp : Permission E) : WarrantedToken E := by
  obtain ⟨e, he, hd⟩ := ho
  exact ⟨e, hp e he hd⟩
theorem root (σ : Signature) (R : RecognitionProfile σ) (E : Experience σ R)
    (hc : Calibrated E) (hi : Identified E) (hv : CoversGods E)
    (hb : CapacityBridge σ R) : RevelationPossibleAndRecognizable σ := by
  intro g hg
  obtain ⟨e, he, hd, eq⟩ := hv g hg
  obtain ⟨_, ha, hr, hm⟩ := hi e (hc e he hd)
  apply hb g hg
  rw [eq] at hr
  exact ⟨E.situation e, ha, E.move e, hr, hm⟩
theorem controls : Controls := by
  simp [Controls, Occurrence, Calibrated, Identified, CoversGods, CapacityBridge,
    RecognizedGod, Permission, WarrantedToken, Veridical, PossibleCorrectRecognition,
    RevelationPossibleAndRecognizable, mixedExperience, modelExperience, modelProfile,
    modelSignature, TruthCore.Case.Catholicism.StageThree.DivineFounding.modelSig]
end TruthCore.Results.Alternatives.ReligiousExperienceRecognition
