module
public import TruthCore.Mereology.FormMate1397
@[expose] public section
namespace TruthCore.Results.Mereology.FormMate1397
open TruthCore.Mereology.FormMate1397

theorem stableToUnique {T S B : Type} (r : T → S → B → Prop)
    (h : StableMate r) : UniqueAt r := by
  intro t s b c hb hc
  exact h t t s b c hb hc

theorem certificate : Certificate := by
  refine ⟨?_, (fun _ => trivial), (fun _ => ⟨rfl, rfl⟩), ?_, ?_, ?_, ?_⟩
  · intro p t s b c hb hc
    cases t <;> cases s
    · exact hb.trans hc.symm
    · exact False.elim hb
    · exact hb.trans hc.symm
  · intro _ _ h
    exact h
  · intro h
    have bad := h .before .returned .designated .original .other rfl rfl
    cases bad
  · intro t u s b c hb hc
    cases t <;> cases u <;> cases s
    all_goals first | exact hb.trans hc.symm | exact False.elim hb | exact False.elim hc
  · intro h
    cases h
end TruthCore.Results.Mereology.FormMate1397
