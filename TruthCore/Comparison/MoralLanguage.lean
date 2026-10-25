import TruthCore.English.VanRoojen.MoralCognitivism

/-!
The moral-language comparison (#182, part of the emotivism refutation #181):
the shared signature of the Frege–Geach question, the shared data every theory
of moral language must answer for, and the theory variants.

Question `Q-MORAL-LANGUAGE-VALIDITY`: why is Geach's moral modus ponens valid?

* Naive emotivism (`NaiveEmotivism`, the occasion reading of "meaning is the
  expressed attitude"): it cannot say. With the shared data it makes the
  argument equivocate, so it is refuted
  (`FREGE-GEACH-REFUTES-NAIVE-EMOTIVIST-MEANING`).
* Constant-meaning expressivism (`ConstantMeaningExpressivism`; Blackburn,
  Gibbard): the minor premise means the same free-standing and embedded, so the
  Frege point is met. It is consistent with the shared data
  (`EXPRESSIVISM-CONSISTENT-WITH-GEACH-VALIDITY`). What it still owes, a logic
  of attitudes that explains why the argument is valid rather than merely
  coherent, is recorded as open attacks, not refuted.
* Catholic natural law answers through truth-apt moral propositions; its answer
  map is #185's task, so it has no definition here.

Only theories and consistency claims live in this namespace: `bind-check`
treats every `TruthCore.Comparison.*` definition as a theory bundle.
-/

namespace TruthCore.Comparison.MoralLanguage

open TruthCore.English.VanRoojen

/-- The shared signature of the Frege–Geach question. `p` is "tormenting the
cat is bad" and `q` is "getting your little brother to torment the cat is
bad". -/
structure Sig where
  Sentence : Type
  Ctx : Type
  Meaning : Type
  Attitude : Type
  /-- A free-standing assertoric occurrence. -/
  free : Ctx
  /-- An occurrence as the antecedent of a conditional. -/
  antecedent : Ctx
  meaning : Sentence → Ctx → Meaning
  Expresses : Sentence → Ctx → Attitude → Prop
  Moral : Sentence → Prop
  ValidMP : Sentence → Sentence → Prop
  p : Sentence
  q : Sentence

/-- The shared data of the question, as one flat conjunction so that
`bind-check` binds each conjunct to its statement: a free-standing moral
assertion expresses an attitude; the antecedent occurrence of `p` does not
express the attitude it expresses free-standing; validity requires constant meaning (the Frege point); Geach's modus
ponens is valid; its minor premise is moral. -/
def SharedData (s : Sig) : Prop :=
  FreeMoralAssertionExpressesAttitudeReading s.Moral s.Expresses s.free ∧
    AntecedentLacksFreeStandingAttitudeReading s.Expresses s.free s.antecedent s.p ∧
    ValidityRequiresConstantMeaningReading s.ValidMP s.meaning s.free s.antecedent ∧
    GeachModusPonensValidReading s.ValidMP s.p s.q ∧
    GeachMinorPremiseIsMoralReading s.Moral s.p

/-- Naive emotivism: the meaning of a moral sentence in an occurrence is
accounted for by the attitude it expresses there. -/
def NaiveEmotivism (s : Sig) : Prop :=
  EmotivistMeaningIsExpressedAttitudeReading s.Moral s.meaning s.Expresses

/-- Constant-meaning expressivism: a moral sentence means the same in every
kind of occurrence. -/
def ConstantMeaningExpressivism (s : Sig) : Prop :=
  ExpressivistMoralMeaningInvariantReading s.Moral s.meaning

/-- Constant-meaning expressivism survives the equivocation charge: it and the
shared data are jointly satisfiable. -/
def ExpressivismConsistentWithGeachValidity : Prop :=
  ∃ s : Sig, ConstantMeaningExpressivism s ∧ SharedData s

end TruthCore.Comparison.MoralLanguage
