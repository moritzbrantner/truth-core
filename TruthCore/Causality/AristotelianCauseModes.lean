module

public import TruthCore.Greek.Aristotle.Physics

@[expose] public section

namespace TruthCore.Causality.AristotelianCauseModes

universe u v

/-- CAUSE_3: a relational interpretation of Aristotle's four-mode classification.
`Cause` and `Effect` are carriers, not classes of intrinsically tagged objects.
Each field is a primitive relation with an intended role: material is what an
 effect is made from; formal is its form/account; source-of-change is where its
 change originates; final is that for the sake of which it occurs. Their
 applicability is supplied, not derived from their names. `exhaustive` retains
 precisely Physics.FourCauseExhaustiveReading, without a converse or disjointness.

This is a type of conditional interpretations, not a definition of the four
primitive relations or evidence that a real-world interpretation inhabits it.
It is distinct from TermSenseForks.CauseFrame and does not extend CauseSense. -/
structure FourCauseModes (Cause : Type u) (Effect : Type v) where
  IsCause : Cause → Effect → Prop
  Material : Cause → Effect → Prop
  Formal : Cause → Effect → Prop
  SourceOfChange : Cause → Effect → Prop
  Final : Cause → Effect → Prop
  exhaustive : TruthCore.Greek.Aristotle.Physics.FourCauseExhaustiveReading
    IsCause Material Formal SourceOfChange Final

/- Semantic controls, not registered research results: the classification can
fail; the modes may overlap; and its implication has no implicit converse. -/
example : ¬ TruthCore.Greek.Aristotle.Physics.FourCauseExhaustiveReading
    (fun _ _ : Unit => True) (fun _ _ => False) (fun _ _ => False)
    (fun _ _ => False) (fun _ _ => False) := by
  intro h
  rcases h () () True.intro with h | h | h | h <;> exact h

/-- A nonempty interpretation with overlapping material and formal roles. -/
def overlapping : FourCauseModes Unit Unit where
  IsCause := fun _ _ => True
  Material := fun _ _ => True
  Formal := fun _ _ => True
  SourceOfChange := fun _ _ => False
  Final := fun _ _ => False
  exhaustive := fun _ _ _ => Or.inl True.intro

/-- Mode membership need not imply IsCause in the existing one-way reading. -/
def withoutConverse : FourCauseModes Unit Unit where
  IsCause := fun _ _ => False
  Material := fun _ _ => True
  Formal := fun _ _ => False
  SourceOfChange := fun _ _ => False
  Final := fun _ _ => False
  exhaustive := fun _ _ h => False.elim h

example : overlapping.Material () () ∧ overlapping.Formal () () :=
  ⟨True.intro, True.intro⟩

example : withoutConverse.Material () () ∧ ¬ withoutConverse.IsCause () () :=
  ⟨True.intro, fun h => h⟩

end TruthCore.Causality.AristotelianCauseModes
