module

public import TruthCore.Logic.ScopedEmpiricalProofBarrier
public import TruthCore.Results.Logic.ScopedEmpiricalProofBarrier.Barrier.Solution

@[expose] public section
namespace TruthCore.Results.Logic.ScopedEmpiricalProofBarrier.Scoped
open TruthCore.Logic.Verificationism
open TruthCore.Logic.ScopedEmpiricalProofBarrier
theorem restrictedFromBarrier {L : Language} (F : Frame L) (q : Inquiries L) (T : q.Inquiry → Prop)
    (h : ScopedObservationBarrier F q T) : RestrictedNoEmpiricalProof F q T := by
  intro t ht
  exact Barrier.barrier F (q.target t) (h t ht)
end TruthCore.Results.Logic.ScopedEmpiricalProofBarrier.Scoped
