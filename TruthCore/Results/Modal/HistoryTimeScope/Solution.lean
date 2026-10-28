import TruthCore.Models.HistoryTimeScope
namespace TruthCore.Results.Modal.HistoryTimeScope
open TruthCore.Modal.TemporalHistory TruthCore.Models.HistoryTimeScope
/-- Shared-time formal controls; no metaphysical necessity or eternity assertion. -/
theorem controls : Controls := by
  refine ⟨?_, ?_, ?_⟩
  · intro W B T h x
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨h.now, fun w => a w h.now⟩
    · rintro ⟨t, a⟩ w
      exact ⟨t, a w⟩
    · constructor
      · intro a
        exact ⟨fun w => ⟨h.now, a w h.now⟩, fun w _ t _ => a w t⟩
      · rintro ⟨a, u⟩ w t
        obtain ⟨s, hs⟩ := a w
        exact u w s t hs
  · refine ⟨fun w => ⟨w, rfl⟩, ?_, ?_⟩
    · rintro ⟨t, a⟩
      have hf : false = t := a false
      have ht : true = t := a true
      exact Bool.noConfusion (hf.trans ht.symm)
    · intro w a
      cases w with
      | false => exact Bool.noConfusion (a true)
      | true => exact Bool.noConfusion (a false)
  · refine ⟨⟨false, fun _ => rfl⟩, ?_, ?_⟩
    · intro a
      exact Bool.noConfusion (a false true)
    · intro w a
      exact Bool.noConfusion (a true)
end TruthCore.Results.Modal.HistoryTimeScope
