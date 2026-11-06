module

public import TruthCore.Logic.ScopedEmpiricalProofBarrier

@[expose] public section
namespace TruthCore.Results.Logic.ScopedEmpiricalProofBarrier.Strength
open TruthCore.Logic.Verificationism
open TruthCore.Logic.ScopedEmpiricalProofBarrier
theorem strength {L : Language} (F : Frame L) (q : Inquiries L) (T : q.Inquiry → Prop)
    (h : GlobalNoEmpiricalProof F q) : RestrictedNoEmpiricalProof F q T := by
  intro t ht
  exact h t
end TruthCore.Results.Logic.ScopedEmpiricalProofBarrier.Strength
