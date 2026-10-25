import TruthCore.Comparison.Metaethics
import TruthCore.Metaethics.Questions
import TruthCore.Metaethics.AnswerMap
import TruthCore.Modal.Kripke
import TruthCore.English.Railton.MoralRealism
import TruthCore.English.Boyd.MoralRealism

/-! Shared finite tests for #249, extending the existing metaethics signature.
These are interpretations of the recorded fragments, not complete historical
worldviews. An invariant natural criterion does not make every belief correct,
and descriptive identification alone does not entail categorical reasons.
The signatures deliberately distinguish welfare, rightness, practical goodness,
truth, belief, and an agent's reason to act. -/
namespace TruthCore.Metaethics.NaturalisticRealism

structure Sig where
  base : TruthCore.Comparison.Metaethics.Sig
  GoodFor : base.Agent → base.Act → Prop
  SatisfiesObjectiveInterest : base.Agent → base.Act → Prop
  Right : base.Act → Prop
  ImpartialCriterion : base.Act → Prop
  FostersGoods : base.Act → Prop
  SustainsMechanisms : base.Act → Prop
  /-- A judgment ascribes the relevant theory's evaluative property to an act. -/
  Ascribes : base.Sentence → base.Act → Prop
  /-- A reason for this agent, not mere motivation or a command. -/
  Reason : base.Agent → base.Act → Prop

/-- Sincere ascriptions describe an evaluative fact; no acceptance predicate
occurs in their truth conditions. Source readings apply this separately to
Railton's rightness and Boyd's goodness; they are not identified. -/
def DescriptiveTruth {Sentence Act : Type}
    (Ascribes : Sentence → Act → Prop) (Holds : Sentence → Prop)
    (Evaluative : Act → Prop) : Prop :=
  ∀ φ a, Ascribes φ a → (Holds φ ↔ Evaluative a)

/-- Existence of ordinary cognitive moral error, reusing the shared definition. -/
def ErrorOccurs (s : Sig) : Prop :=
  SomeMoralError s.base.Accepts s.base.Moral s.base.TruthApt s.base.Holds

/-- A single right act need not serve every agent's ends. This is an encoded
possibility, not the assertion of an actual historical amoralist. -/
def RightWithoutUniversalReasons (s : Sig) : Prop :=
  ∃ x a, s.Right a ∧ ¬ s.Reason x a

/-- The analogous distinction for Boyd's positive moral goodness. -/
def GoodWithoutUniversalReasons (s : Sig) : Prop :=
  ∃ x a, s.base.GoodAct a ∧ ¬ s.Reason x a

/-- A true moral ascription, preventing an all-false interpretation. -/
def TrueMoralAscriptionOccurs (s : Sig) : Prop :=
  ∃ φ, s.base.Moral φ ∧ s.base.Holds φ

/-- One truth-functional interpretation validates moral modus ponens for
any natural predicate on acts. Reuses the existing formula interpreter;
no modal principle or excluded-middle axiom is needed. -/
def NaturalPredicateModusPonens : Prop :=
  ∀ (Act : Type) (Natural : Act → Prop) (p q : TruthCore.Modal.Formula Act),
    let frame : TruthCore.Modal.Frame Unit := ⟨fun _ _ => False⟩
    let holds := TruthCore.Modal.Holds frame (fun _ => Natural) ()
    holds (.imp p q) → holds p → holds q

/-- Epistemic openness of an identity question is not, by itself, property
nonidentity: two labels can denote literally the same property even when an
agent does not recognize their identity. This small semantic countermodel
refutes only that inference, not Moore's full philosophical objection. -/
def UnrecognizedIdentityPossible : Prop :=
  ∃ (Name Act : Type) (moral natural : Name) (denotes : Name → Act → Prop)
    (RecognizesIdentity : Name → Name → Prop),
    moral ≠ natural ∧ denotes moral = denotes natural ∧
      ¬ RecognizesIdentity moral natural ∧
      (∃ a, denotes moral a) ∧ (∃ a, ¬ denotes moral a)

end TruthCore.Metaethics.NaturalisticRealism
