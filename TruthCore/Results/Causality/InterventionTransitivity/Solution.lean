module
public import TruthCore.Causality.InterventionTransitivity
@[expose] public section
namespace TruthCore.Results.Causality.InterventionTransitivity
open TruthCore.Causality.InterventionTransitivity

private theorem binary_change (a b : Bool) (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all

private theorem compensate : CompensationSchema := by
  intro m hxy hyz hxz
  have hf : m.f (!m.actualX) = !(m.f m.actualX) :=
    binary_change _ _ hxy.changed
  have ht : m.g (!m.actualX) (m.f (!m.actualX)) = m.g m.actualX (m.f m.actualX) := by
    by_contra h
    exact hxz ⟨by decide, h⟩
  change m.g m.actualX (m.f (!m.actualX)) ≠ _
  rw [hf] at ht ⊢
  intro he
  exact hyz.changed (he.trans ht)

private theorem exclude : LocalExclusionSchema := by
  intro m hxy hyz he
  by_contra hn
  exact compensate m hxy hyz hn he

private theorem pure_chain : ChainSchema := by
  intro x f g hxy hyz
  exact exclude _ hxy hyz rfl

theorem certificate : Certificate := by
  refine ⟨?_, pure_chain, compensate, exclude, ?_, ?_, ?_, ?_⟩
  · constructor <;> try rfl
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · intro h; exact h.changed rfl
  · constructor
    · exact ⟨⟨by decide, by decide⟩, fun h => h.changed rfl⟩
    · exact ⟨⟨by decide, by decide⟩, fun h => h.changed rfl⟩
  · exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
  · exact Relation.TransGen.trans (Relation.TransGen.single (Or.inl ⟨rfl, rfl⟩))
      (Relation.TransGen.single (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  · intro a b c hab hbc
    exact hab.trans hbc
end TruthCore.Results.Causality.InterventionTransitivity
