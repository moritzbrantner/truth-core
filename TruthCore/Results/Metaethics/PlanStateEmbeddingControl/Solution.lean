import TruthCore.Metaethics.PlanStateEmbedding
namespace TruthCore.Results.Metaethics.PlanStateEmbeddingControl
open TruthCore.Metaethics.PlanStateEmbedding

/-- The stipulated plan-state semantics validates MP nonvacuously and rejects
its converse; this is an analyst reconstruction, not historical attribution. -/
theorem planStateEmbeddingControl : PlanStateEmbeddingControl := by
  refine ⟨?_, ?_, ?_⟩
  · intro Fact Action state p q hp hc w hw
    rcases hc hw with hnot | hq
    · exact False.elim (hnot (hp hw))
    · exact hq
  · let w : Point Unit ExampleAction :=
      ⟨fun _ => false, fun a => match a with
        | .direct => false | .induced => false | .abstain => true⟩
    refine ⟨{w}, ⟨w, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      cases hx
      exact ⟨.abstain, rfl⟩
    · intro x hx
      cases hx
      rfl
    · intro x hx
      cases hx
      exact Or.inr rfl
    · intro x hx
      cases hx
      rfl
    · intro h
      cases h
  · let w : Point Unit ExampleAction :=
      ⟨fun _ => false, fun a => match a with
        | .direct => true | .induced => false | .abstain => true⟩
    refine ⟨{w}, ⟨w, rfl⟩, ?_, ?_, ?_, ?_⟩
    · intro x hx
      cases hx
      exact ⟨.abstain, rfl⟩
    · intro x hx
      cases hx
      rfl
    · intro x hx
      cases hx
      exact Or.inr rfl
    · intro hp
      have impossible : true = false :=
        hp (show w ∈ ({w} : Set (Point Unit ExampleAction)) from rfl)
      cases impossible
end TruthCore.Results.Metaethics.PlanStateEmbeddingControl
