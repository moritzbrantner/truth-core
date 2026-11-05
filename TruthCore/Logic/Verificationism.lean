module

/-!
Verificationist meaning criteria, typed so that their logical consequences can
be derived (#1008, the logical-positivism showcase).

**Languages.** A `Language` has sentences, worlds and a truth relation, with
negation, conjunction and disjunction obeying their classical truth conditions.
`Language.Entails Γ s` is truth preservation at every world: logical
entailment for the language. Sentences are not identified with their truth
sets, so a sentence type of formulas fits; the standard propositional language
is the instance whose worlds are valuations. Nothing else is assumed: no
particular atoms, no finiteness, no decidability of entailment.

**Frames.** A `Frame` adds the empiricist's two classifications: which
sentences are observation statements and which are analytic. They are
parameters. The criteria below are defined from them and from entailment
alone, so every consequence is a theorem about the criterion as defined, not a
reading of it.

**Criteria.**

* `ConclusivelyVerifiable`: strong verification (variant V1): some jointly
  satisfiable finite set of observation statements entails the sentence.
* `WeaklyVerifiable1936`: Ayer's first-edition test (variant V2): with some
  further premises the sentence entails an observation statement that the
  further premises alone do not entail.
* `DirectlyVerifiable`, `IndirectlyVerifiable`, `EmpiricallyVerifiable`,
  `LiterallyMeaningful1946`: Ayer's revised criterion of the 1946
  introduction (variant V3). Indirect verifiability is the least predicate
  closed under its clause, so the recursion "capable of being independently
  established as indirectly verifiable" is an inductive definition.

**Church's sentence.** `churchSentence o₁ o₂ o₃ s` is `(¬o₁ ∧ o₂) ∨ (o₃ ∧ ¬s)`,
the auxiliary premise of Church's 1949 review of the second edition.
`ChurchObservations` asks only what the construction uses: three observation
statements with `o₁ ⊭ o₃` and `o₃ ⊭ o₂`. Church's own hypothesis, that "no
one of the three taken alone entails any of the others" (as quoted in IEP,
"Religious Language", §2a), contains both.

Everything is constructive; no axiom is used. The theorems are in
`TruthCore.Results.Logic.Verificationism.*`.
-/
@[expose] public section

namespace TruthCore.Logic.Verificationism

/-- A truth-conditional language: sentences true or false at worlds, with
negation, conjunction and disjunction obeying their classical truth
conditions. -/
structure Language where
  Sentence : Type
  World : Type
  holds : World → Sentence → Prop
  neg : Sentence → Sentence
  conj : Sentence → Sentence → Sentence
  disj : Sentence → Sentence → Sentence
  holds_neg : ∀ w s, holds w (neg s) ↔ ¬ holds w s
  holds_conj : ∀ w s t, holds w (conj s t) ↔ (holds w s ∧ holds w t)
  holds_disj : ∀ w s t, holds w (disj s t) ↔ (holds w s ∨ holds w t)

namespace Language

variable (L : Language)

/-- Logical entailment: `s` holds at every world at which every premise in `Γ`
holds. -/
def Entails (Γ : List L.Sentence) (s : L.Sentence) : Prop :=
  ∀ w, (∀ g, g ∈ Γ → L.holds w g) → L.holds w s

/-- The premises hold together at some world. -/
def Satisfiable (Γ : List L.Sentence) : Prop :=
  ∃ w, ∀ g, g ∈ Γ → L.holds w g

end Language

/-- The empiricist's classifications of a language's sentences: observation
statements and analytic statements. -/
structure Frame (L : Language) where
  observation : L.Sentence → Prop
  analytic : L.Sentence → Prop

variable {L : Language}

/-! ### V1: strong (conclusive) verification -/

/-- Strong verification: some jointly satisfiable finite set of observation
statements entails the sentence. -/
def ConclusivelyVerifiable (F : Frame L) (s : L.Sentence) : Prop :=
  ∃ os : List L.Sentence, (∀ o, o ∈ os → F.observation o) ∧ L.Satisfiable os ∧
    L.Entails os s

/-- A universal law over individuals in a language: atomic sentences `R a`
("a is a raven") and `B a` ("a is black"), and a sentence `law` that holds at a
world exactly when every `R` there is `B`. -/
structure UniversalLaw (L : Language) where
  Individual : Type
  R : Individual → L.Sentence
  B : Individual → L.Sentence
  law : L.Sentence
  holds_law : ∀ w, L.holds w law ↔ ∀ a, L.holds w (R a) → L.holds w (B a)

/-- The empirical setting in which a law is tested by observation:

* `mentions o a` says which individuals an observation statement is about;
  each observation statement is about finitely many;
* there are infinitely many individuals: no finite list contains them all;
* individuals vary independently: at any world, any individual can be made
  an `R` that is not `B` without changing the truth value of any observation
  statement not about it. -/
structure LawSetting (F : Frame L) (U : UniversalLaw L) where
  mentions : L.Sentence → U.Individual → Prop
  finite_mentions : ∀ o, F.observation o → ∃ l : List U.Individual, ∀ a, mentions o a → a ∈ l
  infinite : ∀ l : List U.Individual, ∃ a, ¬ a ∈ l
  vary : ∀ w a, ∃ w', L.holds w' (U.R a) ∧ ¬ L.holds w' (U.B a) ∧
    ∀ o, F.observation o → ¬ mentions o a → (L.holds w' o ↔ L.holds w o)

/-- V1 excludes universal laws (`STMT-STRONG-VERIFICATION-EXCLUDES-LAWS`): in
every such setting the law is not conclusively verifiable, while its negation
is conclusively verifiable whenever an observed counterinstance is possible
(observation statements `R a` and `notB a`, the latter true exactly where
`B a` is false, holding together somewhere). -/
def StrongVerificationExcludesLaws : Prop :=
  ∀ (L : Language) (F : Frame L) (U : UniversalLaw L), LawSetting F U →
    ¬ ConclusivelyVerifiable F U.law ∧
      ∀ (a : U.Individual) (notB : L.Sentence),
        F.observation (U.R a) → F.observation notB →
        (∀ w, L.holds w notB ↔ ¬ L.holds w (U.B a)) →
        L.Satisfiable [U.R a, notB] →
        ConclusivelyVerifiable F (L.neg U.law)

/-! ### V2: Ayer's first-edition criterion (1936) -/

/-- Ayer's 1936 test: with some further premises the sentence entails an
observation statement that the further premises alone do not entail. -/
def WeaklyVerifiable1936 (F : Frame L) (s : L.Sentence) : Prop :=
  ∃ (ps : List L.Sentence) (e : L.Sentence), F.observation e ∧
    L.Entails (s :: ps) e ∧ ¬ L.Entails ps e

/-- The 1936 test admits every sentence whose negation does not entail a given
observation statement (`STMT-AYER-1936-CRITERION-TRIVIAL`): with the further
premise `¬s ∨ o`, the sentence entails `o`. -/
def Ayer1936CriterionTrivial : Prop :=
  ∀ (L : Language) (F : Frame L) (o s : L.Sentence), F.observation o →
    ¬ L.Entails [L.neg s] o → WeaklyVerifiable1936 F s

/-- The V2 exclusion thesis (`STMT-AYER-1936-EXCLUDES-METAPHYSICS`): some
sentence fails the 1936 test although its negation does not entail some
observation statement. A metaphysical sentence in Ayer's sense has no
observational consequences, and neither does its negation. -/
def Ayer1936ExcludesMetaphysics (F : Frame L) : Prop :=
  ∃ m o : L.Sentence, F.observation o ∧ ¬ L.Entails [L.neg m] o ∧ ¬ WeaklyVerifiable1936 F m

/-- No 1936 frame excludes such a sentence (`STMT-AYER-1936-EXCLUSION-FAILS`). -/
def Ayer1936ExclusionFails : Prop :=
  ∀ (L : Language) (F : Frame L), ¬ Ayer1936ExcludesMetaphysics F

/-! ### V3: Ayer's revised criterion (1946) -/

/-- Direct verifiability (1946): an observation statement, or a sentence that
with one or more observation statements entails an observation statement not
entailed by those observation statements alone. -/
def DirectlyVerifiable (F : Frame L) (s : L.Sentence) : Prop :=
  F.observation s ∨
    ∃ (os : List L.Sentence) (e : L.Sentence), os ≠ [] ∧ (∀ o, o ∈ os → F.observation o) ∧
      F.observation e ∧ L.Entails (s :: os) e ∧ ¬ L.Entails os e

mutual

/-- Indirect verifiability (1946): with certain further premises the sentence
entails a directly verifiable statement not entailed by those premises alone,
and each further premise is an admissible auxiliary premise. -/
inductive IndirectlyVerifiable (F : Frame L) : L.Sentence → Prop
  | intro {s : L.Sentence} (ps : List L.Sentence) (d : L.Sentence)
      (hps : ps ≠ [])
      (hd : DirectlyVerifiable F d)
      (hEnt : L.Entails (s :: ps) d)
      (hNot : ¬ L.Entails ps d)
      (hAux : ∀ p, p ∈ ps → AdmissiblePremise F p) :
      IndirectlyVerifiable F s

/-- An admissible further premise of the 1946 indirect clause: analytic,
directly verifiable, or independently established as indirectly verifiable. -/
inductive AdmissiblePremise (F : Frame L) : L.Sentence → Prop
  | analytic {p : L.Sentence} : F.analytic p → AdmissiblePremise F p
  | direct {p : L.Sentence} : DirectlyVerifiable F p → AdmissiblePremise F p
  | indirect {p : L.Sentence} : IndirectlyVerifiable F p → AdmissiblePremise F p

end

/-- Empirical verifiability (1946): directly or indirectly verifiable. -/
def EmpiricallyVerifiable (F : Frame L) (s : L.Sentence) : Prop :=
  DirectlyVerifiable F s ∨ IndirectlyVerifiable F s

/-- Literal meaningfulness by the 1946 criterion: analytic or empirically
verifiable. -/
def LiterallyMeaningful1946 (F : Frame L) (s : L.Sentence) : Prop :=
  F.analytic s ∨ EmpiricallyVerifiable F s

/-- Church's auxiliary sentence `(¬o₁ ∧ o₂) ∨ (o₃ ∧ ¬s)`. -/
def churchSentence (L : Language) (o₁ o₂ o₃ s : L.Sentence) : L.Sentence :=
  L.disj (L.conj (L.neg o₁) o₂) (L.conj o₃ (L.neg s))

/-- What Church's construction uses: three observation statements with
`o₁ ⊭ o₃` and `o₃ ⊭ o₂`. -/
def ChurchObservations (F : Frame L) (o₁ o₂ o₃ : L.Sentence) : Prop :=
  F.observation o₁ ∧ F.observation o₂ ∧ F.observation o₃ ∧
    ¬ L.Entails [o₁] o₃ ∧ ¬ L.Entails [o₃] o₂

/-- Church's trivialization (`STMT-CHURCH-1949-TRIVIALIZATION`): given such
observation statements, every sentence whose negation is not directly
verifiable is indirectly verifiable. -/
def ChurchTrivialization : Prop :=
  ∀ (L : Language) (F : Frame L) (o₁ o₂ o₃ : L.Sentence), ChurchObservations F o₁ o₂ o₃ →
    ∀ s, ¬ DirectlyVerifiable F (L.neg s) → IndirectlyVerifiable F s

/-- The V3 exclusion thesis (`STMT-AYER-1946-EXCLUDES-SENTENCE-AND-NEGATION`):
the language has observation statements as Church's construction uses them,
and some sentence and its negation are both not literally meaningful by the
1946 criterion, as Ayer holds of "there is a god" and "there is no god". -/
def Ayer1946ExcludesSentenceAndNegation (F : Frame L) : Prop :=
  (∃ o₁ o₂ o₃, ChurchObservations F o₁ o₂ o₃) ∧
    ∃ m, ¬ LiterallyMeaningful1946 F m ∧ ¬ LiterallyMeaningful1946 F (L.neg m)

/-- No 1946 frame excludes a sentence together with its negation
(`STMT-AYER-1946-EXCLUSION-FAILS`). -/
def Ayer1946ExclusionFails : Prop :=
  ∀ (L : Language) (F : Frame L), ¬ Ayer1946ExcludesSentenceAndNegation F

/-- Meaningfulness is closed under negation: if the negation of a sentence is
literally meaningful, so is the sentence. -/
def NegationClosed1946 (F : Frame L) : Prop :=
  ∀ s, LiterallyMeaningful1946 F (L.neg s) → LiterallyMeaningful1946 F s

/-- With closure under negation the 1946 criterion excludes nothing
(`STMT-AYER-1946-NEGATION-CLOSED-EXCLUDES-NOTHING`): no sentence fails to be
literally meaningful. -/
def Ayer1946NegationClosedExcludesNothing : Prop :=
  ∀ (L : Language) (F : Frame L) (o₁ o₂ o₃ : L.Sentence), ChurchObservations F o₁ o₂ o₃ →
    NegationClosed1946 F → ∀ s, ¬ ¬ LiterallyMeaningful1946 F s

/-! ### Self-application (V1–V3) -/

/-- The verification principle with explicit scope, for a variant's
verifiability predicate (`STMT-VERIFICATION-PRINCIPLE`): every meaningful
sentence in scope is analytic or verifiable. `meaningful` is the predicate the
criterion is offered as an account of (literal, cognitive significance). It is
a parameter, not defined from the criterion, so the principle can fail. -/
def VerificationPrinciple (F : Frame L) (meaningful scope verifiable : L.Sentence → Prop) :
    Prop :=
  ∀ s, scope s → meaningful s → F.analytic s ∨ verifiable s

/-- The formulation `v` of the principle lies in its own scope
(`STMT-VERIFICATION-PRINCIPLE-IN-OWN-SCOPE`). -/
def PrincipleInOwnScope (scope : L.Sentence → Prop) (v : L.Sentence) : Prop :=
  scope v

/-- The formulation is not analytic (`STMT-VERIFICATION-PRINCIPLE-NOT-ANALYTIC`). -/
def PrincipleNotAnalytic (F : Frame L) (v : L.Sentence) : Prop :=
  ¬ F.analytic v

/-- The formulation is not verifiable in the variant's sense
(`STMT-VERIFICATION-PRINCIPLE-NOT-VERIFIABLE`). -/
def PrincipleNotVerifiable (verifiable : L.Sentence → Prop) (v : L.Sentence) : Prop :=
  ¬ verifiable v

/-- The verificationist self-application dilemma
(`STMT-VERIFICATIONIST-DILEMMA`): if the principle holds its formulation is not
meaningful, and if the formulation is meaningful the principle fails. -/
def VerificationistDilemma (F : Frame L) (meaningful scope verifiable : L.Sentence → Prop)
    (v : L.Sentence) : Prop :=
  (VerificationPrinciple F meaningful scope verifiable → ¬ meaningful v) ∧
    (meaningful v → ¬ VerificationPrinciple F meaningful scope verifiable)

/-! ### V4: the criterion as a proposal -/

/-- A criterion's verdict settles nothing about truth
(`STMT-CRITERION-VERDICT-SILENT-ON-TRUTH`): in some language with an
observation statement, some sentence that is neither analytic nor conclusively
verifiable is true at a world. Adopting a criterion as a recommendation
classifies sentences; failing it does not make a sentence untrue or deprive it
of truth conditions. -/
def CriterionVerdictSilentOnTruth : Prop :=
  ∃ (L : Language) (F : Frame L) (s : L.Sentence) (w : L.World),
    (∃ o, F.observation o) ∧ ¬ F.analytic s ∧ ¬ ConclusivelyVerifiable F s ∧ L.holds w s

end TruthCore.Logic.Verificationism
