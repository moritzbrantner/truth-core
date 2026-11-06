module

public import TruthCore.Logic.ScopedEmpiricalProofBarrier

@[expose] public section
namespace TruthCore.Results.Logic.ScopedEmpiricalProofBarrier.Barrier
open TruthCore.Logic.Verificationism
open TruthCore.Logic.ScopedEmpiricalProofBarrier
theorem barrier {L : Language} (F : Frame L) (s : L.Sentence)
    (h : ObservationBarrier F s) : ¬ ConclusivelyVerifiable F s := by
  intro ⟨os, hObs, ⟨w, hw⟩, hEntails⟩
  obtain ⟨v, hSame, hFalse⟩ := h w (hEntails w hw)
  exact hFalse (hEntails v (fun o ho => (hSame o (hObs o ho)).mp (hw o ho)))
end TruthCore.Results.Logic.ScopedEmpiricalProofBarrier.Barrier
