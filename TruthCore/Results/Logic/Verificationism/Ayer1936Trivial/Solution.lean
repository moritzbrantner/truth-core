module

public import TruthCore.Logic.Verificationism

@[expose] public section

namespace TruthCore.Results.Logic.Verificationism.Ayer1936Trivial
open TruthCore.Logic.Verificationism

theorem mem_singleton {α : Type} {a b : α} (h : a ∈ [b]) : a = b := by
  cases h with
  | head => rfl
  | tail _ h => cases h

/-- Ayer's 1936 test admits every sentence whose negation does not entail a given observation statement o: with the further premise ¬s ∨ o, the sentence entails o. -/
theorem ayer1936CriterionTrivial : Ayer1936CriterionTrivial := by
  intro L F o s ho hno
  refine ⟨[L.disj (L.neg s) o], o, ho, ?_, ?_⟩
  · intro w hw
    have hs := hw s (List.Mem.head _)
    have hd := hw _ (List.Mem.tail _ (List.Mem.head _))
    rcases (L.holds_disj w _ _).mp hd with hn | ho'
    · exact absurd hs ((L.holds_neg w s).mp hn)
    · exact ho'
  · intro hent; apply hno; intro w hw
    have hn := hw _ (List.Mem.head _)
    exact hent w (fun g hg => by
      cases mem_singleton hg; exact (L.holds_disj w _ _).mpr (Or.inl hn))
end TruthCore.Results.Logic.Verificationism.Ayer1936Trivial
