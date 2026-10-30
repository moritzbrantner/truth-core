import TruthCore.Modal.ActualReasonWitness
namespace TruthCore.Results.Modal.ActualReasonWitness
open TruthCore.Modal.ActualReasonWitness
theorem checks : Certificate := by
  exact ⟨fun _ _ m d x => anchorOverlap_implies_actualStable m d x,
    fun _ _ m d x => actualStable_implies_stable m d x,
    ⟨TruthCore.Modal.WorldwiseExplanation.alternatingSound,
      alternating_actual_local, alternating_not_actualStable⟩,
    ⟨overlap_sound, overlap_anchor,
      anchorOverlap_implies_actualStable _ _ _ overlap_anchor,
      overlap_not_invariant⟩⟩
end TruthCore.Results.Modal.ActualReasonWitness
