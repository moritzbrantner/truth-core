module

public import TruthCore.Alternatives.NaturalReasonAuthority

@[expose] public section
namespace TruthCore.Results.Alternatives.NaturalReasonAuthority
open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.NaturalReasonAuthority

/-- Only the forward direction is needed for sufficiency, on the same scope. -/
theorem determinationSuffices (P : Practice) (scope : P.Move → Prop)
    (h : InternalDetermination P scope) : InternalSufficiency P scope := by
  intro m hm hOwn
  exact (h m hm).mp hOwn

/-- Explicit finite dictionaries for shared answerability and external exclusion; verdict agreement is not modeled. -/
def practice (own correct shared natural : Bool → Prop) : Practice where
  Move := Bool
  Correct := correct
  OwnStandard := own
  Defined := fun _ => False
  AffirmsNaturalKnowability := natural
  AnswersToSharedReason := shared

/-- An internal standard always has jurisdiction; the external one's
jurisdiction varies independently of every Practice predicate. -/
def authorities (P : Practice) (external : Bool) : AuthorityProfile P where
  Standard := Bool
  Internal s := s = true
  HasAuthority s _ := s = true ∨ external = true

/-- Inhabited shared-answerability/external-exclusion combinations and omitted-strength controls. -/
theorem forkControls : ForkControls := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro shared external
    let P := practice (fun _ => True) (fun _ => True)
      (fun _ => shared = true) (fun _ => True)
    refine ⟨P, authorities P external, true, trivial, trivial, trivial,
      (fun _ _ => ⟨fun _ => trivial, fun _ => trivial⟩), Iff.rfl, ?_⟩
    cases external with
    | false =>
      constructor
      · intro _; rfl
      · intro _ s _ _ hn ha
        cases ha with
        | inl hi => exact hn hi
        | inr he => cases he
    | true =>
      constructor
      · intro h
        exact False.elim (h false true trivial (by intro hf; cases hf) (Or.inr rfl))
      · intro he; cases he
  · let P := practice (fun _ => False) (fun _ => True)
      (fun _ => True) (fun _ => True)
    refine ⟨P, true, trivial, (fun _ _ ho => False.elim ho), ?_⟩
    intro h
    exact (h true trivial).mpr trivial
  · let P := practice (fun _ => True) (fun m => m = true)
      (fun _ => True) (fun m => m = true)
    refine ⟨P, true, rfl, (fun _ hn _ => hn), ?_⟩
    intro h
    have hf := h false trivial trivial
    cases hf
  · let P := practice (fun _ => True) (fun _ => False)
      (fun _ => True) (fun _ => True)
    refine ⟨P, authorities P false, true, trivial, trivial, (fun h => h), ?_, ?_⟩
    · intro s _ _ hn ha
      cases ha with
      | inl hi => exact hn hi
      | inr he => cases he
    · intro h
      exact h true trivial trivial
  · intro P broad narrow hScope
    exact ⟨fun h m hn => h m (hScope m hn),
      fun h m hn => h m (hScope m hn),
      fun A h s m hn => h s m (hScope m hn)⟩

end TruthCore.Results.Alternatives.NaturalReasonAuthority
