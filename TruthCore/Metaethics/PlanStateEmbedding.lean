import Mathlib.Data.Set.Basic

/-!
An analyst's propositional planning-language reconstruction for #185.
The pinned secondary account SEP-MORAL-COGNITIVISM §2.5 motivates keeping
factual possibilities separate from complete permission plans, and representing
partial commitment by compatible pairs. The syntax and material-conditional
clause below are stipulations, not an attribution to Gibbard or Blackburn.
The primary GIBBARD-REPLY-2022-535-544 witness distinguishes permission from
picking (pp. 541–542), but denies full truth values to false-antecedent indicative
conditionals (pp. 536–538). Our support clause is not that indicative semantics.
The semantic result establishes consequence inside this model only. It does
not establish its psychological interpretation, ordinary-language adequacy,
or either the truth or falsity of substantive moral realism.
-/
namespace TruthCore.Metaethics.PlanStateEmbedding

/-- A descriptive valuation and a complete permission plan are separate fields.
`permitted a` records a planning option, not a fact that a is morally permitted.
A plan need not permit exactly one action: this is permission, not choice. -/
structure Point (Fact Action : Type) where
  factual : Fact → Bool
  permitted : Action → Bool

/-- An explicit fragment of a planning language. A forbidden-action atom
expresses exclusion of an action from a plan; it is not a descriptive atom. -/
inductive Sentence (Fact Action : Type) where
  | factual : Fact → Sentence Fact Action
  | forbidden : Action → Sentence Fact Action
  | conditional : Sentence Fact Action → Sentence Fact Action → Sentence Fact Action

/-- Stipulated compositional support. The conditional excludes precisely a
point supporting its antecedent but failing to support its consequent.
This material clause is an added semantic commitment, not an assumed MP rule. -/
def support {Fact Action : Type} : Sentence Fact Action → Set (Point Fact Action)
  | .factual f => {w | w.factual f = true}
  | .forbidden a => {w | w.permitted a = false}
  | .conditional p q => {w | w ∉ support p ∨ w ∈ support q}

/-- Ideal semantic acceptance: every point still compatible with a state
supports the sentence. This is not a claim about actual agents' explicit
beliefs or awareness of consequences. Empty states accept everything; the
separate controls below use inhabited states. -/
def Accepts {Fact Action : Type} (state : Set (Point Fact Action))
    (sentence : Sentence Fact Action) : Prop := state ⊆ support sentence

/-- Every compatible state preserves acceptance under modus ponens, including
mixed factual/planning formulas and nested conditionals. -/
def SemanticModusPonens : Prop :=
  ∀ (Fact Action : Type) (state : Set (Point Fact Action)) (p q : Sentence Fact Action),
    Accepts state p → Accepts state (.conditional p q) → Accepts state q

/-- Three available actions for the finite controls: the two disapproved
actions and an alternative that remains permitted. This is an analyst example. -/
inductive ExampleAction where
  | direct | induced | abstain

/-- A nonempty compatible state accepts two distinct forbidden-action atoms
and their conditional, while each point leaves an action permitted. No atom or conditional is identified with `True`. -/
def InhabitedDistinctControl : Prop :=
  ∃ state : Set (Point Unit ExampleAction), state.Nonempty ∧
    (∀ w ∈ state, ∃ a, w.permitted a = true) ∧
    Accepts state (.forbidden .direct) ∧
    Accepts state (.conditional (.forbidden .direct) (.forbidden .induced)) ∧
    Accepts state (.forbidden .induced) ∧
    (Sentence.forbidden .direct : Sentence Unit ExampleAction) ≠ .forbidden .induced

/-- The same semantic clauses do not validate affirming the consequent:
there is a nonempty state with an available action accepting q and if p then q while failing to accept p. -/
def ConverseCounterexample : Prop :=
  ∃ state : Set (Point Unit ExampleAction), state.Nonempty ∧
    (∀ w ∈ state, ∃ a, w.permitted a = true) ∧
    Accepts state (.forbidden .induced) ∧
    Accepts state (.conditional (.forbidden .direct) (.forbidden .induced)) ∧
    ¬ Accepts state (.forbidden .direct)

/-- The precise reconstruction result: acceptance-preserving MP, an inhabited
control with distinct atoms, and failure of the converse. No primitive validity
predicate, source-fidelity premise, or substantive moral fact occurs here. -/
def PlanStateEmbeddingControl : Prop :=
  SemanticModusPonens ∧ InhabitedDistinctControl ∧ ConverseCounterexample

end TruthCore.Metaethics.PlanStateEmbedding
