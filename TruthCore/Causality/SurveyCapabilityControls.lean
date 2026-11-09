module

/-!
Conditional controls for the A2 domain-narrowing gap. `canCause` is an explicit
primitive capability relation on an arbitrary carrier, NOT a completed meaning
of either original source sense. No accessibility, endpoint existence, actual
exercise, rigidity, distinctness or structural law is imposed. Application to
source concrete coverage and to the actualGraph necessary-being route is OPEN.
These controls do not bind either original sense or discharge any premise.
-/

@[expose] public section

namespace TruthCore.Causality.SurveyCapabilityControls

/-- For the SAME relation and carrier, outgoing capability is included in
outgoing-or-incoming capability. No converse or strictness for every relation. -/
theorem outgoingIncluded {B : Type} (canCause : B → B → Prop) (x : B) :
    (∃ y, canCause x y) → ((∃ y, canCause x y) ∨ (∃ y, canCause y x)) :=
  Or.inl

/-- A nonempty capability relation witnesses both domains. Its effect is in
only the broader domain; its cause is in the narrower domain. Bool is solely a
separating control, not a restriction on the general carrier above. -/
theorem incomingOnlySeparator :
    let R := fun x y : Bool => x = true ∧ y = false
    (∃ y, R true y) ∧
    ((∃ y, R false y) ∨ (∃ y, R y false)) ∧ ¬ (∃ y, R false y) := by
  refine ⟨⟨false, rfl, rfl⟩, Or.inr ⟨true, rfl, rfl⟩, ?_⟩
  rintro ⟨y, h, _⟩
  cases h

/-- A coverage predicate may cover every outgoing-capable candidate while
failing to cover an incoming-only candidate. Thus broad-domain denial cannot
be transferred to narrow-domain denial just by domain inclusion. This tests
quantifier direction only; it supplies no interpretation of source chains. -/
theorem coverageDenialDoesNotTransfer :
    let R := fun x y : Bool => x = true ∧ y = false
    let covered := fun x : Bool => x = true
    (∀ x, (∃ y, R x y) → covered x) ∧
    ¬ (∀ x, ((∃ y, R x y) ∨ (∃ y, R y x)) → covered x) := by
  constructor
  · rintro x ⟨y, h, _⟩
    exact h
  · intro h
    have bad := h false (Or.inr ⟨true, rfl, rfl⟩)
    cases bad

/-- A primitive capability relation may be inhabited while a separately
supplied exercise relation is empty. Equating them needs an explicit bridge. -/
theorem capabilityWithoutExercise :
    let canCause := fun x y : Bool => x = true ∧ y = false
    let exercises := fun _ _ : Bool => False
    (∃ y, canCause true y) ∧ ¬ (∃ y, exercises true y) := by
  exact ⟨⟨false, rfl, rfl⟩, fun ⟨_, h⟩ => h⟩

end TruthCore.Causality.SurveyCapabilityControls
