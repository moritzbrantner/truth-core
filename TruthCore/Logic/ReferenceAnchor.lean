module

public import Mathlib.ModelTheory.Semantics
public import TruthCore.Results.Modern.Russell.Description.Solution

/-!
Analyst formulation for #1073 / #1010; attribution deferred. Literal reference
means the value of a constant on one fixed carrier, not an isomorphism class.
Mathlib already supplies first-order syntax (equality, connectives, quantifiers)
and isomorphism invariance. Existing Verificationism syntax has no interpreted
names; CorrectionCriterion classifies data fibers, and Fideism.Practice concerns
correct moves, neither supplies reference. We reuse Russell's exact description
analysis for the independently fixed anchor, not a new notion of uniqueness.
-/

@[expose] public section
namespace TruthCore.Logic.ReferenceAnchor
open FirstOrder
open TruthCore.Modern.Russell.Existence

inductive FunctionSymbol : Nat → Type where
  | name : FunctionSymbol 0
inductive PredicateSymbol : Nat → Type where
  | marked : PredicateSymbol 1

/-- One name and one unary predicate; the logical syntax is Mathlib's. -/
def language : Language := ⟨FunctionSymbol, PredicateSymbol⟩

/-- Stipulated two-individual interpretation. `false` and `true` are carrier
labels, not truth values here; the predicate picks exactly the named label. -/
@[instance_reducible] def original : language.Structure Bool where
  funMap := fun f _ => match f with | .name => false
  RelMap := fun r xs => match r with | .marked => xs 0 = false

/-- Swap both individuals. This is a carrier bijection, not a sentence rename. -/
def swap : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

/-- Transport *all* nonlogical interpretation with the bijection. In particular,
the marked predicate is not independently fixed across interpretations. -/
@[instance_reducible] def transported : language.Structure Bool :=
  @Equiv.inducedStructure language Bool Bool original swap

/-- Literal name value in a supplied interpretation on the fixed carrier. -/
def referent (S : language.Structure Bool) : Bool :=
  @Language.Structure.funMap language Bool S 0 .name (fun i => Fin.elim0 i)

/-- Same truth for every first-order sentence of this language. This includes
all encoded implications; it does not include arbitrary outside predicates. -/
def SameSentences : Prop :=
  ∀ φ : language.Sentence,
    @Language.Sentence.Realize language Bool original φ ↔
    @Language.Sentence.Realize language Bool transported φ

/-- Inference behavior for every list of premises at the selected interpretation.
This is truth preservation there, not global logical validity. -/
def ConsequenceAt (S : language.Structure Bool) (Γ : List language.Sentence)
    (φ : language.Sentence) : Prop :=
  (∀ ψ ∈ Γ, @Language.Sentence.Realize language Bool S ψ) →
    @Language.Sentence.Realize language Bool S φ

/-- Fixed external anchor: the original individual. Transporting it instead
would preserve structure but would abandon the cross-interpretation anchor. -/
def anchor (x : Bool) : Prop := x = false

/-- Explicit anchor recovery condition: both referents satisfy one predicate
with a Russell definite description. Independent applicability remains OPEN.
No epistemic access or causal history is encoded by satisfaction alone. -/
def AnchorRecovery : Prop :=
  ∀ (E : Type) (F : E → Prop) (a b : E),
    DescriptionExists F → F a → F b → a = b

/-- Joint boundary: all sentences and interpretation-relative inferences agree,
yet literal name values differ. The fixed singleton anchor distinguishes them;
keeping a common uniquely satisfied anchor would force referent agreement.
A structuralist who identifies permuted interpretations is not refuted. -/
def ReferenceBoundary : Prop :=
  SameSentences ∧
  (∀ Γ φ, ConsequenceAt original Γ φ ↔ ConsequenceAt transported Γ φ) ∧
  referent original ≠ referent transported ∧
  DescriptionExists anchor ∧ anchor (referent original) ∧
  ¬ anchor (referent transported) ∧ AnchorRecovery

end TruthCore.Logic.ReferenceAnchor
