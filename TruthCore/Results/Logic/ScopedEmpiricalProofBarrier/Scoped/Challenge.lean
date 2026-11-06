import TruthCore.Logic.ScopedEmpiricalProofBarrier
import TruthCore.Results.Logic.ScopedEmpiricalProofBarrier.Barrier.Solution
namespace TruthCore.Results.Logic.ScopedEmpiricalProofBarrier.Scoped
open TruthCore.Logic.Verificationism
open TruthCore.Logic.ScopedEmpiricalProofBarrier
theorem restrictedFromBarrier {L : Language} (F : Frame L) (q : Inquiries L) (T : q.Inquiry → Prop)
    (h : ScopedObservationBarrier F q T) : RestrictedNoEmpiricalProof F q T := by
  sorry
end TruthCore.Results.Logic.ScopedEmpiricalProofBarrier.Scoped
