module

public import TruthCore.Ontology.QuotientGeneration

/-! Conditional mathematical consequences and finite interpretation controls.
No result completes the constitutive abstraction sense or defends a premise. -/

@[expose] public section
namespace TruthCore.Results.Ontology.QuotientGeneration
open TruthCore.Ontology.QuotientGeneration
open TruthCore.Ontology.ConcreteAbstract
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Causality.CausalPowerConcreteness

theorem kernel {A B : Type} (g : Presentation A B) : KernelLaw g := by
  intro a b
  exact ⟨fun h => Quotient.exact (g.faithful h), fun h => congrArg g.embed (Quotient.sound h)⟩

theorem range {A B : Type} (g : Presentation A B) : RangeLaw g := by
  intro b
  constructor
  · rintro ⟨q, h⟩
    induction q using Quotient.inductionOn with
    | h a => exact ⟨a, h⟩
  · rintro ⟨a, h⟩
    exact ⟨Quotient.mk g.relation a, h⟩

theorem unrestricted : UnrestrictedGeneration := by
  intro B b
  let s : Setoid Unit := ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩
  let g : Presentation Unit B := {
    relation := s
    embed := fun _ => b
    faithful := by
      intro q r _
      induction q using Quotient.inductionOn with
      | h a =>
        induction r using Quotient.inductionOn with
        | h a' => exact Quotient.sound trivial }
  exact ⟨g, Quotient.mk s (), rfl⟩

theorem classify {A B R : Type} (g : Presentation A B)
    (InAct : B → R → Prop) (esse : R) (b : B)
    (h : ValuesNoEsse g InAct esse) (hb : QuotientGenerated g b) :
    EsseAbstract InAct esse b := by
  rcases hb with ⟨q, rfl⟩
  exact h q

theorem inert {A B R W : Type} (g : Presentation A B)
    (InAct : B → R → Prop) (esse : R) (o : Ontic W B)
    (power : W → B → Prop) (w : W)
    (h : ValuesNoEsse g InAct esse)
    (ho : OwnerCommitmentAt o (HasEsseInRe InAct esse) power w) :
    ValuesInert g o power w := by
  intro b hb
  have hn := classify g InAct esse b h hb
  exact ⟨fun hp => hn (ho.1 b hp), fun y hc => hn (ho.2 b y hc)⟩

theorem controls : Control.Certificate := by
  have selected : QuotientGenerated Control.presentation Control.selected :=
    ⟨Quotient.mk Control.sameFirst (true, false), rfl⟩
  have noEsse : ValuesNoEsse Control.presentation (Control.InAct false) () := by
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
      cases a with
      | mk x y =>
        cases x <;> simp [EsseAbstract, Control.InAct, Control.presentation,
          Control.first, Control.reasoner, Control.selected]
  have notInert : ∀ active,
      active = true → ¬ ValuesInert Control.presentation (Control.ontic active) (Control.power active) () := by
    intro active ha hi
    exact (hi Control.selected selected).1 ⟨ha, rfl⟩
  refine ⟨rfl, by decide, by decide, ?_, ?_, selected, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨q, h⟩
    change Sum.inl (Control.first q) = Sum.inr true at h
    cases h
  · rintro ⟨q, h⟩
    change Sum.inl (Control.first q) = Sum.inr false at h
    cases h
  · simp [Control.Anchored, HasEsseInRe, EsseAbstract, Control.InAct,
      Control.reasoner, Control.outside]
  · simp [Control.Anchored, HasEsseInRe, EsseAbstract, Control.InAct,
      Control.reasoner, Control.outside, Control.selected]
  · exact ⟨Or.inr ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩
  · simp [EsseAbstract, Control.InAct, Control.power, Control.ontic,
      Control.selected, Control.reasoner]
  · refine ⟨?_, ?_, notInert true rfl⟩
    · constructor
      · intro b hp
        exact Or.inr ⟨rfl, hp.2⟩
      · intro b y hc
        exact Or.inr ⟨rfl, hc.2.1⟩
    · intro hn
      exact classify Control.presentation (Control.InAct true) () Control.selected hn selected
        (Or.inr ⟨rfl, rfl⟩)
  · refine ⟨noEsse, ?_, notInert true rfl⟩
    intro ho
    have h := ho.1 Control.selected ⟨rfl, rfl⟩
    simp [HasEsseInRe, Control.InAct, Control.selected, Control.reasoner] at h
  · refine ⟨noEsse, ?_⟩
    constructor
    · intro b hp
      cases hp.1
    · intro b y hc
      cases hc.1
end TruthCore.Results.Ontology.QuotientGeneration
