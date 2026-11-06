module

public import TruthCore.Logic.ScopedEmpiricalProofBarrier
public import TruthCore.Results.Logic.Verificationism.StrongVerificationLaws.Solution

@[expose] public section
namespace TruthCore.Results.Logic.ScopedEmpiricalProofBarrier.Finitary
open TruthCore.Logic.Verificationism
open TruthCore.Logic.ScopedEmpiricalProofBarrier
open TruthCore.Logic.ScopedEmpiricalProofBarrier.Control
open TruthCore.Results.Logic.Verificationism.VerdictSilent
theorem finitary : Control.FinitaryControl := by
  have hNoFinite := (TruthCore.Results.Logic.Verificationism.StrongVerificationLaws.strongVerificationExcludesLaws
    Model.lawLanguage Model.lawFrame Model.ravens Model.ravensSetting).1
  have hNoBarrier : ¬ ObservationBarrier Model.lawFrame Model.ravens.law := by
    intro h
    obtain ⟨v, hSame, hNotLaw⟩ := h (fun _ => (true, true)) (fun _ _ => rfl)
    apply hNotLaw
    intro n hR
    exact (hSame (.b n) True.intro).mp rfl
  refine ⟨hNoBarrier, hNoFinite, ⟨(), True.intro, hNoBarrier, hNoFinite⟩, ?_⟩
  intro hCoverage
  exact hNoBarrier (hCoverage () True.intro hNoFinite)
end TruthCore.Results.Logic.ScopedEmpiricalProofBarrier.Finitary
