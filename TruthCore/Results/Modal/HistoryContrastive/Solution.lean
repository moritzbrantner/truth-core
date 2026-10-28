import TruthCore.Modal.HistoryContrastive

namespace TruthCore.Results.Modal.HistoryContrastive
open TruthCore.Modal.HistoryContrastive

/-- Same infinite local chains admit a contingent internal discriminator or
an everywhere-true nondiscriminator. Empty discovery does not remove the former. -/
theorem controls : TruthCore.Modal.HistoryContrastive.Controls := by
  refine ⟨causal_coverage, coverage false, sound false, coverage true, sound true,
    distinct_histories, internal_discriminates, constant_not_discriminating,
    ?_, internal_bearer.1, internal_bearer.2, ?_, ⟨false, internal_discriminates⟩⟩
  · intro w v _
    trivial
  · rintro ⟨r, hr, _⟩
    exact hr

end TruthCore.Results.Modal.HistoryContrastive
