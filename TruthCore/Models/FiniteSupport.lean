/-! Constructive finite quantification used only by explicit model certificates. -/
namespace TruthCore.Models.FiniteSupport

instance unitForall {p : Unit → Prop} [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p ())
    ⟨fun h x => by cases x; exact h, fun h => h ()⟩

instance unitExists {p : Unit → Prop} [DecidablePred p] : Decidable (∃ x, p x) :=
  decidable_of_iff (p ())
    ⟨fun h => ⟨(), h⟩, fun ⟨x, h⟩ => by cases x; exact h⟩

instance boolForall {p : Bool → Prop} [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p false ∧ p true)
    ⟨fun h x => by cases x; exact h.1; exact h.2, fun h => ⟨h false, h true⟩⟩

instance boolExists {p : Bool → Prop} [DecidablePred p] : Decidable (∃ x, p x) :=
  decidable_of_iff (p false ∨ p true)
    ⟨fun h => h.elim (fun h => ⟨false, h⟩) (fun h => ⟨true, h⟩),
     fun ⟨x, h⟩ => by cases x; exact Or.inl h; exact Or.inr h⟩

theorem enumerateUnit : ∀ x : Unit, x = Unit.unit := by intro x; cases x; rfl

theorem enumerateBool : ∀ x : Bool, x = false ∨ x = true := by
  intro x; cases x; exact Or.inl rfl; exact Or.inr rfl

end TruthCore.Models.FiniteSupport
