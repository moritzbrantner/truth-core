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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨true, ⟨rfl, rfl⟩, (fun h => h)⟩, ?_, ?_, ?_, ?_⟩
    · intro e _ _; rfl
    · intro e _; exact ⟨rfl, trivial, rfl, rfl⟩
    · intro g hg; exact ⟨true, ⟨rfl, rfl⟩, (fun h => h), hg.symm⟩
    · intro g _ _; rfl
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro e ho _; cases ho.1
    · intro e hv; cases hv
    · intro g _ hr
      obtain ⟨s, _, m, _, hm⟩ := hr
      cases hm
    · intro h
      obtain ⟨g, _, s, _, m, _, hm⟩ := h
      cases hm
  · refine ⟨⟨true, ⟨rfl, rfl⟩, (fun h => h)⟩, ?_, ?_, ⟨true, trivial⟩, ?_⟩
    · intro e hv; cases hv
    · intro e _ _; trivial
    · intro h
      obtain ⟨g, _, s, _, m, _, hm⟩ := h
      cases hm
  · refine ⟨⟨true, ⟨rfl, rfl⟩, (fun h => h)⟩, ?_, ?_⟩
    · intro e _ _; rfl
    · intro h
      obtain ⟨g, _, s, _, m, _, hm⟩ := h
      cases hm
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro e _ _; rfl
    · intro e _; exact ⟨rfl, trivial, rfl, rfl⟩
    · intro g hg; exact ⟨true, ⟨rfl, rfl⟩, (fun h => h), hg.symm⟩
    · intro h; cases h true rfl
  · refine ⟨trivial, trivial, ?_, rfl, ?_, ?_⟩
    · intro h; cases h
    · intro e _ hd
      cases e
      · exact False.elim (hd rfl)
      · rfl
    · intro e hv
      cases e
      · cases hv
      · exact ⟨rfl, trivial, rfl, rfl⟩
end TruthCore.Results.Alternatives.ReligiousExperienceRecognition
