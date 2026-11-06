module

public import TruthCore.Ontology.NaturalismSets
public import TruthCore.Results.Ontology.NaturalismSets.Unlocation.Solution

@[expose] public section

namespace TruthCore.Results.Ontology.NaturalismSets
open TruthCore.Ontology.NaturalismSets TruthCore.Ontology.Naturalism
open TruthCore.Ontology.Spatiotemporal
open TruthCore.German.Kant.CosmologicalInference (Ontic)

def nominalOntic : Ontic Unit (Unit ⊕ Bool) where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ x => match x with
    | .inl _ => True
    | .inr _ => False
  Causes := fun _ _ _ => False

def nominalFrame : Frame (Unit ⊕ Bool) where
  Region := Unit
  locatedAt := fun x _ => match x with
    | .inl _ => True
    | .inr _ => False
  related := fun _ _ => False
  partOf := fun _ _ => False
  whole := .inl ()

def allOntic : Ontic Unit (Unit ⊕ Bool) :=
  { nominalOntic with ExistsAt := fun _ _ => True }

def allFrame : Frame (Unit ⊕ Bool) :=
  { nominalFrame with locatedAt := fun _ _ => True }

private theorem nominalSupport : SetLocationHasMemberSupport sampleDecode nominalFrame := by
  intro s ⟨_, h⟩
  exact False.elim h

theorem controls : Controls := by
  refine ⟨?_, ?_, ⟨nominalOntic, nominalFrame, ?_, nominalSupport,
    True.intro, ⟨(), True.intro⟩, ?_, unlocated sampleDecode nominalFrame nominalSupport⟩,
    ⟨allOntic, allFrame, ?_, ?_, ?_, True.intro, ⟨(), True.intro⟩,
      True.intro, ⟨(), True.intro⟩, True.intro, ⟨(), True.intro⟩⟩⟩
  · exact ZFSet.mem_singleton.mpr rfl
  · intro t; exact ZFSet.notMem_empty _
  · intro x hx
    cases x with
    | inl b => exact ⟨(), True.intro⟩
    | inr s => exact False.elim hx
  · intro s h; exact h
  · intro x _; exact ⟨(), True.intro⟩
  · intro _ _ _ _ _; exact True.intro
  · intro h
    obtain ⟨t, hm, _⟩ := h false ⟨(), True.intro⟩
    exact ZFSet.notMem_empty (sampleDecode t) hm

end TruthCore.Results.Ontology.NaturalismSets
