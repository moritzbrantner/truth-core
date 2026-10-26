import TruthCore.Logic.SelfApplication

/-!
Relativism about truth as an instance of the self-application schema (#397).

The global thesis "no content (in scope) is absolutely true" is a `Norm` whose
standard nothing meets and whose acceptance predicate is absolute truth. Its
own formulation, if in scope and disquoting, is not absolutely true, so it
cannot be asserted in the absolute sense without contradiction (horn 1).
Asserted relative to its speaker it is consistent, but its relative truth for
the speaker settles nothing for anyone else (horn 2, a model). Exempting the
thesis from its own scope is consistent too; Aristotle's cost of that move
(*Metaphysics* IV.8, 1012b18-22) is the exemption regress proved below.
Local relativism is the restriction of the norm to a demarcated domain.

Vocabulary is stipulated test semantics (`DEF-ABSOLUTE-TRUTH`,
`DEF-RELATIVE-TRUTH`), not a translation of every relativist's idiom.
-/

namespace TruthCore.Logic.Relativism

open TruthCore.Logic.SelfApplication

variable {Agent Content : Type}

/-- The no-absolute-truth norm: within its scope nothing meets the standard
(`False`); its acceptance predicate is absolute truth. -/
def noAbsoluteTruthNorm (scope : Content → Prop) : Norm Content :=
  ⟨scope, fun _ => False⟩

/-- No content in scope is absolutely true (`STMT-NO-ABSOLUTE-TRUTH-SCOPED`).
With every content in scope this is global relativism about absolute truth;
it is silent about relative truth. -/
def NoAbsoluteTruth (T : TruthSemantics Agent Content) (scope : Content → Prop) : Prop :=
  (noAbsoluteTruthNorm scope).Holds T.trueAbs

/-- Global form: no content is absolutely true (`STMT-GLOBAL-NO-ABSOLUTE-TRUTH`). -/
def GlobalNoAbsoluteTruth (T : TruthSemantics Agent Content) : Prop :=
  ∀ p, ¬ T.trueAbs p

/-- Some content is absolutely true (`STMT-SOME-ABSOLUTE-TRUTH`). -/
def SomeAbsoluteTruth (T : TruthSemantics Agent Content) : Prop :=
  ∃ p, T.trueAbs p

/-- Scope premise: the thesis's own formulation lies in its scope
(`STMT-NO-ABSOLUTE-TRUTH-THESIS-IN-OWN-SCOPE`). -/
def ThesisInOwnScope (scope : Content → Prop) (thesis : Content) : Prop :=
  scope thesis

/-- Content premise: if the thesis content is absolutely true, no content in
scope is absolutely true (`STMT-NO-ABSOLUTE-TRUTH-THESIS-DISQUOTES`). -/
def ThesisDisquotes (T : TruthSemantics Agent Content) (scope : Content → Prop)
    (thesis : Content) : Prop :=
  Disquotes T.trueAbs thesis (NoAbsoluteTruth T scope)

/-- The thesis is not absolutely true; so asserting it in the absolute sense
commits its speaker to a contradiction
(`STMT-NO-ABSOLUTE-TRUTH-THESIS-NOT-ABSOLUTELY-TRUE`). -/
def ThesisNotAbsolutelyTrue (T : TruthSemantics Agent Content) (thesis : Content) : Prop :=
  ¬ T.trueAbs thesis

/-- Horn 2 is consistent: the scoped, disquoting thesis holds and its speaker's
relative assertion commitment is met, while the thesis is not true for the
other agent. -/
def RelativeHornConsistent : Prop :=
  ∃ (T : TruthSemantics Bool Bool) (scope : Bool → Prop) (thesis a : Bool),
    NoAbsoluteTruth T scope ∧ ThesisInOwnScope scope thesis ∧ ThesisDisquotes T scope thesis ∧
      AssertionCommitment T (TruthSense.relativeTo a) thesis ∧ ¬ T.trueFor (!a) thesis

/-- Dropping the scope premise (exempting the thesis) is consistent with an
absolute assertion of the thesis. -/
def ExemptionConsistent : Prop :=
  ∃ (T : TruthSemantics Bool Bool) (scope : Bool → Prop) (thesis : Bool),
    NoAbsoluteTruth T scope ∧ ¬ ThesisInOwnScope scope thesis ∧ ThesisDisquotes T scope thesis ∧
      AssertionCommitment T TruthSense.absolute thesis

/-- Both models (`STMT-NO-ABSOLUTE-TRUTH-MODELS`). -/
def NoAbsoluteTruthModels : Prop :=
  RelativeHornConsistent ∧ ExemptionConsistent

/-- Truth ascent: if a content is absolutely true, so is the content saying
that it is true (`STMT-TRUTH-ASCENT`; Aristotle, *Metaphysics* IV.8, 1012b21-22). -/
def TruthAscent (T : TruthSemantics Agent Content) (trueOf : Content → Content) : Prop :=
  ∀ p, T.trueAbs p → T.trueAbs (trueOf p)

/-- The exempted thesis is asserted, and is, absolutely true
(`STMT-EXEMPTED-THESIS-ABSOLUTELY-TRUE`). -/
def ExemptedThesisAbsolutelyTrue (T : TruthSemantics Agent Content) (thesis : Content) : Prop :=
  T.trueAbs thesis

/-- Every truth-ascent iterate of the thesis must also be exempted from the
scope (`STMT-EXEMPTION-REGRESS`). -/
def ExemptionRegress (scope : Content → Prop) (trueOf : Content → Content)
    (thesis : Content) : Prop :=
  ∀ n : Nat, ¬ scope (Nat.repeat trueOf n thesis)

/-- Local relativism: the no-absolute-truth norm restricted to a demarcated
domain (`STMT-LOCAL-NO-ABSOLUTE-TRUTH`). -/
def LocalNoAbsoluteTruth (T : TruthSemantics Agent Content) (D : Norm.Demarcation Content) :
    Prop :=
  ((noAbsoluteTruthNorm (fun _ => True)).restrict D).Holds T.trueAbs

/-- Second-order test for local relativism (`STMT-LOCAL-RELATIVISM-SECOND-ORDER`):
a local thesis `w` inside its own domain cannot be absolutely true if it holds;
outside its domain, if absolutely true, it concedes an absolute truth and
global relativism fails. -/
def LocalRelativismSecondOrder : Prop :=
  ∀ (Agent Content : Type) (T : TruthSemantics Agent Content) (D : Norm.Demarcation Content)
    (w : Content),
    (D.inDomain w → LocalNoAbsoluteTruth T D → ¬ T.trueAbs w) ∧
      (¬ D.inDomain w → T.trueAbs w → SomeAbsoluteTruth T ∧ ¬ GlobalNoAbsoluteTruth T)

end TruthCore.Logic.Relativism
