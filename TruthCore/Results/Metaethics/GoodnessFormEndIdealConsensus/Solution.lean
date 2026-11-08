module
public import TruthCore.Metaethics.GoodnessFormEndIdealConsensus
@[expose] public section
namespace TruthCore.Results.Metaethics.GoodnessFormEndIdealConsensus
open TruthCore.Metaethics.GoodnessFormEnd
open TruthCore.Metaethics.GoodnessFormEndIdealConsensus

theorem consensusToDue (f : Frame) (a : Assessment f)
    (hR : Reduction f a) (hA : Acceptance f a) (hS : SoundWitness f a) :
    DueActualityThesis f := by
  intro x p
  constructor
  · intro h
    obtain ⟨i, hi⟩ := hS x p
    exact hi ((hR x p).mp h i)
  · intro h
    exact (hR x p).mpr (hA x p h)

theorem controls : Controls := by
  have exactR : Reduction artifact exactAssessment := by
    intro x p; exact ⟨fun h _ => h, fun h => h ()⟩
  have exactA : Acceptance artifact exactAssessment := by
    intro x p h _; exact h
  have exactS : SoundWitness artifact exactAssessment := by
    intro x p; exact ⟨(), fun h => h⟩
  have permR : Reduction surplusArtifact permissive := by
    intro x p; exact ⟨fun h _ => h, fun h => h ()⟩
  have permA : Acceptance surplusArtifact permissive := by
    intro x p h _; exact h.2
  have permNS : ¬ SoundWitness surplusArtifact permissive := by
    intro h; obtain ⟨i, hi⟩ := h .knife .mass
    exact (hi True.intro).1
  have surplusN : ¬ DueActualityThesis surplusArtifact := by
    intro h; exact ((h .knife .mass).mp True.intro).1
  have rejectR : Reduction omissionArtifact rejecting := by
    intro x p; exact ⟨fun h _ => h, fun h => h ()⟩
  have rejectS : SoundWitness omissionArtifact rejecting := by
    intro x p; exact ⟨(), fun h => h.2⟩
  have rejectNA : ¬ Acceptance omissionArtifact rejecting := by
    intro h; have bad := h .knife .existence ⟨True.intro, True.intro⟩ ()
    cases bad.1
  have omissionN : ¬ DueActualityThesis omissionArtifact := by
    intro h; have bad := (h .knife .existence).mpr ⟨True.intro, True.intro⟩
    cases bad.1
  refine ⟨⟨exactR, exactA, exactS, ?_⟩,
    ⟨permR, permA, permNS, surplusN⟩,
    ⟨rejectR, rejectS, rejectNA, omissionN⟩,
    ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x p; exact Iff.rfl
  · intro x p h i; cases i
  · intro h; obtain ⟨i, _⟩ := h .knife .mass; cases i
  · intro i; cases i
  · let a : Assessment surplusArtifact :=
      ⟨Unit, fun _ x p => DueActuality surplusArtifact x p⟩
    refine ⟨a, ?_, ?_, ?_, surplusN⟩
    · intro x p h _; exact h
    · intro x p; exact ⟨(), fun h => h⟩
    · intro h; exact ((h .knife .mass).mp True.intro ()).1
end TruthCore.Results.Metaethics.GoodnessFormEndIdealConsensus
