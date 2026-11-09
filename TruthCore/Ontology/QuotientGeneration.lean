module

public import Mathlib.Data.Set.Basic
public import TruthCore.Causality.CausalPowerConcreteness

/-!
# Extensional quotient generation, an analyst candidate

A presentation embeds the quotient of a supplied equivalence into a candidate
carrier. Its values have a representative-independent mathematical construction;
this says nothing about constitutive essence, esse, powers or causation.
The original abstraction sense remains unfinished. The new sense is relative
to a fixed presentation: existentially varying presentations loses all contrast.
-/

@[expose] public section
namespace TruthCore.Ontology.QuotientGeneration
open TruthCore.Ontology.ConcreteAbstract
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Causality.CausalPowerConcreteness

structure Presentation (A B : Type) where
  relation : Setoid A
  embed : Quotient relation → B
  faithful : Function.Injective embed

def Presentation.value {A B : Type} (g : Presentation A B) (a : A) : B :=
  g.embed (Quotient.mk g.relation a)

/-- CONCRETE_AND_ABSTRACT_9: value of this fixed faithful quotient presentation.
No esse or causal predicate occurs in its body. -/
def QuotientGenerated {A B : Type} (g : Presentation A B) (b : B) : Prop :=
  b ∈ Set.range g.embed

def KernelLaw {A B : Type} (g : Presentation A B) : Prop :=
  ∀ a a', g.value a = g.value a' ↔ g.relation a a'

def RangeLaw {A B : Type} (g : Presentation A B) : Prop :=
  ∀ b, QuotientGenerated g b ↔ ∃ a, g.value a = b

/-- OPEN same-bearer classification bridge, restricted to this presentation's
values; no claim about other candidates or the original essential sense. -/
def ValuesNoEsse {A B R : Type} (g : Presentation A B)
    (InAct : B → R → Prop) (esse : R) : Prop :=
  ∀ q, EsseAbstract InAct esse (g.embed q)

def ValuesInert {A B W : Type} (g : Presentation A B) (o : Ontic W B)
    (power : W → B → Prop) (w : W) : Prop :=
  ∀ b, QuotientGenerated g b → ¬ power w b ∧ ∀ y, ¬ o.Causes w b y

/-- Existential presentation choice is too permissive even on Unit. -/
def UnrestrictedGeneration : Prop :=
  ∀ (B : Type) (b : B), ∃ g : Presentation Unit B, QuotientGenerated g b

namespace Control
abbrev Input := Bool × Bool
abbrev Bearer := Bool ⊕ Bool

def sameFirst : Setoid Input where
  r a b := a.1 = b.1
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

def first : Quotient sameFirst → Bool :=
  Quotient.lift Prod.fst (fun _ _ h => h)

def presentation : Presentation Input Bearer where
  relation := sameFirst
  embed q := Sum.inl (first q)
  faithful := by
    intro q q' h
    induction q using Quotient.inductionOn with
    | h a =>
      induction q' using Quotient.inductionOn with
      | h b => exact Quotient.sound (Sum.inl.inj h)

def reasoner : Bearer := Sum.inr false
def selected : Bearer := Sum.inl true
def outside : Bearer := Sum.inr true

/-- Two interpretations keep the reasoner/abstract anchor fixed and change
only the selected generated value's independently supplied esse assignment. -/
def InAct (includeSelected : Bool) (b : Bearer) (_ : Unit) : Prop :=
  b = reasoner ∨ (includeSelected = true ∧ b = selected)

def power (active : Bool) (_ : Unit) (b : Bearer) : Prop :=
  active = true ∧ b = selected

def ontic (active : Bool) : Ontic Unit Bearer where
  frame := ⟨fun _ _ => True⟩
  ExistsAt _ b := b = reasoner ∨ b = selected
  Causes _ b c := active = true ∧ b = selected ∧ c = reasoner

def Anchored (includeSelected : Bool) : Prop :=
  HasEsseInRe (InAct includeSelected) () reasoner ∧
    EsseAbstract (InAct includeSelected) () outside

/-- This finite certificate includes a genuine collision, distinct quotient
values and a point outside the range. The same fixed presentation supports
both a concrete active selected value and an abstract inert selected value.
Omissions separately remove classification or the owner's causal commitment. -/
def Certificate : Prop :=
  presentation.value (false, false) = presentation.value (false, true) ∧
  (false, false) ≠ (false, true) ∧
  presentation.value (false, false) ≠ presentation.value (true, false) ∧
  ¬ QuotientGenerated presentation outside ∧
  ¬ QuotientGenerated presentation reasoner ∧
  QuotientGenerated presentation selected ∧
  Anchored false ∧ Anchored true ∧
  (HasEsseInRe (InAct true) () selected ∧ power true () selected ∧
    (ontic true).Causes () selected reasoner) ∧
  (EsseAbstract (InAct false) () selected ∧ ¬ power false () selected ∧
    ∀ y, ¬ (ontic false).Causes () selected y) ∧
  (OwnerCommitmentAt (ontic true) (HasEsseInRe (InAct true) ()) (power true) () ∧
    ¬ ValuesNoEsse presentation (InAct true) () ∧
    ¬ ValuesInert presentation (ontic true) (power true) ()) ∧
  (ValuesNoEsse presentation (InAct false) () ∧
    ¬ OwnerCommitmentAt (ontic true) (HasEsseInRe (InAct false) ()) (power true) () ∧
    ¬ ValuesInert presentation (ontic true) (power true) ()) ∧
  (ValuesNoEsse presentation (InAct false) () ∧
    OwnerCommitmentAt (ontic false) (HasEsseInRe (InAct false) ()) (power false) ())
end Control
end TruthCore.Ontology.QuotientGeneration
