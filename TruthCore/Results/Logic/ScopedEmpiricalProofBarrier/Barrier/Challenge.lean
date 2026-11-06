import TruthCore.Logic.ScopedEmpiricalProofBarrier
namespace TruthCore.Results.Logic.ScopedEmpiricalProofBarrier.Barrier
open TruthCore.Logic.Verificationism
open TruthCore.Logic.ScopedEmpiricalProofBarrier
theorem barrier {L : Language} (F : Frame L) (s : L.Sentence)
    (h : ObservationBarrier F s) : ¬ ConclusivelyVerifiable F s := by
  sorry
end TruthCore.Results.Logic.ScopedEmpiricalProofBarrier.Barrier
