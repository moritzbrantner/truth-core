module

public import TruthCore.Ontology.NaturalismLaws
public import TruthCore.Results.Modern.Hume.Regularity.Solution

@[expose] public section

namespace TruthCore.Results.Ontology.NaturalismLaws
open TruthCore.Ontology.NaturalismLaws
open TruthCore.Ontology.Spatiotemporal
open TruthCore.Ontology.Naturalism
open TruthCore.Modern.Hume.Regularity

def inhabited : Representation Unit Bool Regularity where
  Region := Unit
  bearerPresent := fun _ b => b = true
  lawPresent := fun _ l => l = .pattern
  bearerAt := fun _ _ => True
  instantiates := fun l b => l = .pattern ∧ b = true
  whole := true

def description : Representation Unit Bool Regularity :=
  { inhabited with lawPresent := fun _ _ => False
                   instantiates := fun _ _ => False }

def unsupported : Representation Unit Bool Regularity :=
  { inhabited with instantiates := fun _ _ => False }

private theorem inhabitedN1 :
    ExistenceNaturalism (ontic inhabited)
      (Located (frame inhabited (immanentAt inhabited ()))) () := by
  intro x hx
  cases x with
  | inl b => exact ⟨(), True.intro⟩
  | inr l => exact ⟨(), true, rfl, ⟨hx, rfl⟩, True.intro⟩

private theorem descriptionN1 :
    ExistenceNaturalism (ontic description)
      (Located (frame description (immanentAt description ()))) () := by
  intro x hx
  cases x with
  | inl b => exact ⟨(), True.intro⟩
  | inr l => exact False.elim hx

theorem controls : Controls := by
  refine ⟨?_, ⟨inhabited, inhabitedN1, rfl, ⟨true, rfl, rfl, rfl⟩, ?_⟩,
    ⟨description, descriptionN1, ?_, ⟨true, rfl⟩, ?_⟩,
    ⟨unsupported, (fun _ _ => True), ?_, ?_, ?_, rfl, ?_, ?_, true, rfl, (), True.intro⟩⟩
  · exact TruthCore.Results.Modern.Hume.Regularity.checks.2.2.2.2.2.2.1
  · intro h; cases h
  · intro l h; exact h
  · intro ⟨_, _, h⟩; exact h
  · intro x hx; cases x <;> exact ⟨(), True.intro⟩
  · intro _ _ _ _ h; exact False.elim h
  · intro h
    obtain ⟨_, _, hi, _⟩ := h .pattern () True.intro
    exact hi
  · intro ⟨_, _, hi⟩; exact hi
  · intro ⟨_, _, _, hi, _⟩; exact hi

end TruthCore.Results.Ontology.NaturalismLaws
