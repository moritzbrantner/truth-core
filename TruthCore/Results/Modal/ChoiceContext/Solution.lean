import TruthCore.Modal.ChoiceContext
import TruthCore.Results.Modal.SelectedEffectBridge.Solution
namespace TruthCore.Results.Modal.ChoiceContext
open TruthCore.Modal.ChoiceContext

theorem sameContextSameAction (h k : History) (hSame : SameContext h k) :
    action h = action k := by
  unfold action
  rw [hSame.1, hSame.2]

theorem controls : Controls := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W B A L C p w a law condition r hFixed hLaw
    apply TruthCore.Results.Modal.SelectedEffectBridge.fixedConditionsStable
      p w a (fun v => (law v, condition v)) r
    · intro v hv
      exact Prod.ext (hFixed v hv).1 (hFixed v hv).2
    · exact hLaw
  · intro h ⟨k, hSame, hDifferent⟩
    exact hDifferent (sameContextSameAction h k hSame)
  · exact ⟨rfl, rfl⟩
  · refine ⟨rfl, ?_, ?_⟩
    · intro h
      have bad : true = false := congrArg Prod.fst h
      cases bad
    · intro h
      cases h
  · refine ⟨rfl, ?_, ?_⟩ <;> intro h <;> cases h
  · exact ⟨fun h => Bool.noConfusion h, rfl⟩
  · exact ⟨fun h => Bool.noConfusion h, fun _ => rfl, Bool.noConfusion⟩
  · intro c a hImposed hLaw
    exact hLaw hImposed
end TruthCore.Results.Modal.ChoiceContext
