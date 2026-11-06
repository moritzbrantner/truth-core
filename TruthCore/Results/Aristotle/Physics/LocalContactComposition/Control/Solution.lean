module

public import TruthCore.Greek.Aristotle.Physics.LocalContactComposition

@[expose] public section
namespace TruthCore.Results.Aristotle.Physics.LocalContactComposition.Control
open TruthCore.Greek.Aristotle.Physics.Typed
open TruthCore.Greek.Aristotle.Physics.LocalContactComposition

/-- Analyst local-scope consequence; original source reading and frozen result unchanged. -/
theorem populatedStrictness : PopulatedStrictness := by
  have hLocalInj : Function.Injective Control.localChain := by
    intro a b h
    exact congrArg Prod.fst h
  have hOtherInj : Function.Injective Control.otherChain := by
    intro a b h
    exact congrArg Prod.fst h
  have hOtherNoWhole : ¬ ∃ w, Control.composed w Control.otherChain := by
    rintro ⟨w, hw⟩
    have h := hw 0
    cases h
  refine ⟨?_, hLocalInj, ?_, (fun _ => rfl), hOtherInj, (fun _ => trivial),
    hOtherNoWhole, ?_⟩
  · intro c _ hChain _
    refine ⟨(0,false), ?_⟩
    intro n
    obtain ⟨r, _, hMoves⟩ := (hChain n).2.2.1
    exact hMoves.2.2
  · intro n
    refine ⟨?_, rfl, ⟨(), trivial, rfl, rfl, rfl⟩, ⟨(), trivial, rfl⟩⟩
    intro h
    exact Nat.succ_ne_self n (congrArg Prod.fst h)
  · intro h
    exact hOtherNoWhole (h Control.otherChain hOtherInj (fun _ => trivial))

end TruthCore.Results.Aristotle.Physics.LocalContactComposition.Control
