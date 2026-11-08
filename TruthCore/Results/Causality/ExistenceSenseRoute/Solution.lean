module
public import TruthCore.Causality.ExistenceSenseRoute
public import TruthCore.Results.Causality.NecessarySenseFork.Solution

@[expose] public section
namespace TruthCore.Results.Causality.ExistenceSenseRoute
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Causality.ExistenceSenseRoute
open TruthCore.Case.Catholicism (Signature)
open TruthCore.Causality.BruteFoundationBoundary (Profile)

theorem boxKToActualistK {W : Type} (σ : Signature) (m : Profile W σ.Being)
    (w : W) (CN : σ.Being → σ.Being → Prop)
    (h : NecessaryRootBoxK σ m w CN) : NecessaryRootActualistK σ m w CN := by
  obtain ⟨n, hn, hf⟩ := h
  exact ⟨n, ⟨hf.1.1.2, hn⟩, hf⟩

theorem controls : Controls := by
  have h := TruthCore.Results.Causality.NecessarySenseFork.nonvacuity.1
  refine ⟨(h .boxK).1, (h .actualistK).1, ⟨(), ?_⟩, ?_⟩
  · intro v hv
    exact False.elim hv
  · rintro ⟨x, hx⟩
    exact hx
end TruthCore.Results.Causality.ExistenceSenseRoute
