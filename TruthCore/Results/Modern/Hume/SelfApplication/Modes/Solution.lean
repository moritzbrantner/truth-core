import TruthCore.Modern.Hume.SelfApplication
namespace TruthCore.Results.Modern.Hume.SelfApplication.Modes
open TruthCore.Modal
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Modern.Hume.Conceivability
open TruthCore.Modern.Hume.SelfApplication

private theorem describedFalse : Verbal universal (fun _ => False) false := by
  refine ⟨.both .atom (.neg .atom), ?_⟩
  intro v
  exact ⟨fun h => h.2 h.1, fun h => h.elim⟩

theorem checks : ConceptionModeChecks := by
  have old := TruthCore.Results.Modern.Hume.Conceivability.checks
  refine ⟨?_, ?_, ⟨describedFalse, ?_⟩, ?_, ?_⟩
  · intro W F w P h
    exact h
  · intro h
    obtain ⟨v, hv, hp⟩ := h (fun w => w = true) ⟨true, rfl⟩
    exact Bool.false_ne_true (hv.trans hp)
  · intro h
    obtain ⟨v, _, hf⟩ := h (fun _ => False) describedFalse
    exact hf
  · exact ⟨⟨.collapse, fun _ => Iff.rfl⟩, fun h => h⟩
  · have hnarrow := old.2.2.2.2.2.2.2.2.2.2.1
    exact ⟨hnarrow.1, hnarrow.2, old.2.2.2.2.2.2.1⟩
end TruthCore.Results.Modern.Hume.SelfApplication.Modes
