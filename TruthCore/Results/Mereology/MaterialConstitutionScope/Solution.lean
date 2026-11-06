module

public import TruthCore.Mereology.MaterialConstitutionScope
public import TruthCore.Results.Mereology.ProcessTurnover.Solution

@[expose] public section

namespace TruthCore.Results.Mereology.MaterialConstitutionScope
open TruthCore.Mereology.MaterialConstitutionScope

/-- A coincidence-to-identity principle conflicts with different later
existence for the very same two bearer labels. It does not select which
philosophical premise should be abandoned. -/
theorem incompatible {T B M : Type} (e : T → B → Prop) (c : T → B → M → Prop)
    (initial later : T) (x y : B) (same : Coincident c initial x y)
    (different : Divergent e later x y) : ¬ SliceIdentity c := by
  intro identity
  have equal := identity initial x y same
  exact different.1 (equal ▸ different.2)

/-- Extensionality ranges over all occurrences of both histories. -/
theorem global_extensionality (x y : Whole)
    (h : ∀ t m, wholeMaterial t x m ↔ wholeMaterial t y m) : x = y := by
  apply Subtype.ext
  apply Set.ext
  intro o
  exact h o.1 o.2

theorem correspondence : Correspondence := by
  constructor
  · intro t b
    constructor
    · intro h
      exact ⟨(), h⟩
    · intro h
      exact h.choose_spec
  · intro t b m
    rfl

theorem enduring_control :
    Coincident enduringMaterial false false true ∧
    Divergent enduringExists true false true ∧ false ≠ true ∧
    ¬ SliceIdentity enduringMaterial := by
  have coincident : Coincident enduringMaterial false false true :=
    ⟨fun _ => ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩, ⟨(), Or.inl rfl⟩⟩
  have divergent : Divergent enduringExists true false true :=
    ⟨(by intro h; rcases h with h | h <;> cases h), Or.inr rfl⟩
  exact ⟨coincident, divergent, Bool.false_ne_true,
    incompatible enduringExists enduringMaterial false true false true coincident divergent⟩

theorem temporal_control :
    Coincident wholeMaterial false (history false) (history true) ∧
    Divergent wholeExists true (history false) (history true) ∧
    history false ≠ history true ∧
    TruthCore.Mereology.UniversalFusionBoundary.Overlap (history false) (history true) ∧
    ¬ (∀ p : Whole, p ≤ history false ↔ p ≤ history true) := by
  have absent : ¬ wholeExists true (history false) := by
    rintro ⟨_, h | h⟩ <;> cases h
  have present : wholeExists true (history true) := ⟨(), Or.inr rfl⟩
  have distinct : history false ≠ history true := by
    intro h
    exact absent (h ▸ present)
  refine ⟨?_, ⟨absent, present⟩, distinct, ?_, ?_⟩
  · exact ⟨fun _ => ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩,
      ⟨(), Or.inl rfl⟩⟩
  · refine ⟨⟨{(false, ())}, ⟨(false, ()), rfl⟩⟩, ?_, ?_⟩
    · intro o ho
      have : o = (false, ()) := ho
      exact this ▸ Or.inl rfl
    · intro o ho
      have : o = (false, ()) := ho
      exact this ▸ Or.inl rfl
  · intro allparts
    have included : history true ≤ history false := (allparts (history true)).mpr le_rfl
    exact absent ⟨(), included (Or.inr rfl)⟩

theorem certificate : Certificate := by
  refine ⟨?_, enduring_control, temporal_control, correspondence,
    global_extensionality, TruthCore.Results.Mereology.ProcessTurnover.certificate, ?_⟩
  · intro T B M e c initial later x y same different
    exact incompatible e c initial later x y same different
  · intro B b e n adjacent
    rw [TruthCore.Mereology.TheseusIdentity.chain_identity b n adjacent]

end TruthCore.Results.Mereology.MaterialConstitutionScope
