/-!
Readings of the positions that Mark van Roojen's *Stanford Encyclopedia of
Philosophy* entry "Moral Cognitivism vs. Non-Cognitivism" (Spring 2026
edition) reports on the Frege–Geach embedding problem (#182). The entry is a
secondary witness: each reading attributes a position the entry reports
(emotivism, Geach, the expressivists), not a thesis of the entry's author.

Shared vocabulary, all of it parameters rather than definitions:

* `Sentence` — declarative sentences, moral ones included.
* `Ctx` — the kinds of occurrence a sentence can have. `free` is a
  free-standing (unembedded) assertoric use; `antecedent` is an occurrence as
  the antecedent of a conditional.
* `meaning φ c` — what `φ` means in an occurrence of kind `c`, in a type
  `Meaning` the readings leave abstract.
* `Expresses φ c a` — uttering `φ` in an occurrence of kind `c` expresses the
  attitude `a` (approval, disapproval, …).
* `Moral φ` — `φ` is a moral sentence.
* `ValidMP φ ψ` — the modus ponens with minor premise `φ`, major premise
  "if `φ`, then `ψ`", and conclusion `ψ` is valid.

The vocabulary says nothing about what meanings or attitudes are. In
particular it does not assume that meanings are propositions.
-/

namespace TruthCore.English.VanRoojen

universe u v w x

/-- Emotivism, occasion reading: the entire meaning of a moral sentence in an
occurrence is accounted for by the attitude it expresses there. So two
occurrences with the same meaning express the same attitudes: whatever one
occurrence expresses, the other expresses too.

This is the "simplest story" Geach targets: moral terms are "devices for
expressing pro and con attitudes", so that if the entire meaning of "tormenting
the cat is bad" is "well explained by saying that it is suited for use in
expressing disapproval", that meaning "cannot be the same" in the antecedent of
a conditional. Only the direction the argument needs is formalized: same
meaning implies same expressed attitudes, not the converse. A second reading,
on which meaning is the attitude the sentence is suited to express whatever
the occurrence, is `ExpressivistMoralMeaningInvariantReading`.

Source: Mark van Roojen, "Moral Cognitivism vs. Non-Cognitivism", *Stanford
Encyclopedia of Philosophy* (Spring 2026), §4.1.
-/
def EmotivistMeaningIsExpressedAttitudeReading {Sentence : Sort u} {Ctx : Sort v}
    {Meaning : Sort w} {Attitude : Sort x}
    (Moral : Sentence → Prop) (meaning : Sentence → Ctx → Meaning)
    (Expresses : Sentence → Ctx → Attitude → Prop) : Prop :=
  ∀ φ, Moral φ → ∀ c c', meaning φ c = meaning φ c' →
    ∀ a, Expresses φ c a → Expresses φ c' a

/-- A free-standing moral assertion expresses an attitude: "to call a person
virtuous is to express an attitude of approval", and sentences with "wrong" or
"bad" "signal negative non-cognitive attitudes".

The emotivists hold this, but it is not peculiar to them: a descriptivist "can
agree" that the free-standing premise of Geach's argument is used emotively
(§4.1). Only the existence of some expressed attitude is formalized.

Source: Mark van Roojen, "Moral Cognitivism vs. Non-Cognitivism", *Stanford
Encyclopedia of Philosophy* (Spring 2026), §2.1.
-/
def FreeMoralAssertionExpressesAttitudeReading {Sentence : Sort u} {Ctx : Sort v}
    {Attitude : Sort x}
    (Moral : Sentence → Prop) (Expresses : Sentence → Ctx → Attitude → Prop)
    (free : Ctx) : Prop :=
  ∀ φ, Moral φ → ∃ a, Expresses φ free a

/-- In the antecedent of a conditional, the sentence `φ` does not express the
attitude it expresses free-standing: when the words of a moral sentence "occur in the antecedent of a
conditional ... they are typically not being used to express such disapproval";
Geach's major premise is one "one might accept even if one approves of
tormenting cats".

The entry says "typically", so the reading is stated for one sentence, the
minor premise of Geach's argument, not for every moral sentence. Only the
attitude the free-standing occurrence expresses ("such disapproval") is denied of
the antecedent, not every attitude (Codex P1 on #187).

Source: Mark van Roojen, "Moral Cognitivism vs. Non-Cognitivism", *Stanford
Encyclopedia of Philosophy* (Spring 2026), §4.1.
-/
def AntecedentLacksFreeStandingAttitudeReading {Sentence : Sort u} {Ctx : Sort v}
    {Attitude : Sort x}
    (Expresses : Sentence → Ctx → Attitude → Prop) (free antecedent : Ctx)
    (φ : Sentence) : Prop :=
  ∀ a, Expresses φ free a → ¬ Expresses φ antecedent a

/-- The Frege point as a constraint on validity: a modus ponens is valid only if
its minor premise means the same free-standing as it means in the antecedent
of the major premise. "The status of an argument as valid depends, at least in
part, on the words not shifting in meaning as we move from premise to premise";
if content did not remain constant across embedded and unembedded occurrences,
"we would routinely commit a fallacy of equivocation".

Only the necessary condition is formalized ("at least in part"), not that
constant meaning suffices for validity.

Source: Mark van Roojen, "Moral Cognitivism vs. Non-Cognitivism", *Stanford
Encyclopedia of Philosophy* (Spring 2026), §4.1 (reporting Geach 1965, 449
and 463).
-/
def ValidityRequiresConstantMeaningReading {Sentence : Sort u} {Ctx : Sort v}
    {Meaning : Sort w}
    (ValidMP : Sentence → Sentence → Prop) (meaning : Sentence → Ctx → Meaning)
    (free antecedent : Ctx) : Prop :=
  ∀ φ ψ, ValidMP φ ψ → meaning φ free = meaning φ antecedent

/-- Geach's moral modus ponens is valid: from "if tormenting the cat is bad,
getting your little brother to do it is bad" and "tormenting the cat is bad"
to "getting your little brother to torment the cat is bad". "The argument is
valid."

`p` is "tormenting the cat is bad" and `q` is "getting your little brother to
torment the cat is bad".

Source: Mark van Roojen, "Moral Cognitivism vs. Non-Cognitivism", *Stanford
Encyclopedia of Philosophy* (Spring 2026), §4.1 (Geach 1965, 463).
-/
def GeachModusPonensValidReading {Sentence : Sort u}
    (ValidMP : Sentence → Sentence → Prop) (p q : Sentence) : Prop :=
  ValidMP p q

/-- The minor premise of Geach's argument, "tormenting the cat is bad", is a
moral sentence: it applies a general predicate of negative moral evaluation
("bad").

Source: Mark van Roojen, "Moral Cognitivism vs. Non-Cognitivism", *Stanford
Encyclopedia of Philosophy* (Spring 2026), §4.1.
-/
def GeachMinorPremiseIsMoralReading {Sentence : Sort u}
    (Moral : Sentence → Prop) (p : Sentence) : Prop :=
  Moral p

/-- Expressivism: a moral sentence means the same in every kind of occurrence.
Expressivists in the narrower sense "construct a systematic semantics for moral
sentences by pairing them with the states of mind that the sentences are said
to express", and hold that their meanings "are determined by the mental states
that they serve to express". The state a sentence serves to express belongs to
the sentence, not to an occasion of use, so its meaning does not shift when it
is embedded.

This is a second reading of "meaning is the expression of an attitude", beside
`EmotivistMeaningIsExpressedAttitudeReading`; Gibbard's norm- and
plan-expressivism (§2.5) and Blackburn's higher-order attitudes (§4.1.1) are
recorded as claims of it. Only constancy of meaning is formalized, not what the
meaning is or how complex sentences get theirs.

Source: Mark van Roojen, "Moral Cognitivism vs. Non-Cognitivism", *Stanford
Encyclopedia of Philosophy* (Spring 2026), §2.4.
-/
def ExpressivistMoralMeaningInvariantReading {Sentence : Sort u} {Ctx : Sort v}
    {Meaning : Sort w}
    (Moral : Sentence → Prop) (meaning : Sentence → Ctx → Meaning) : Prop :=
  ∀ φ, Moral φ → ∀ c c', meaning φ c = meaning φ c'

/-- Quasi-realism's minimal truth: moral sentences can be true or false in a
deflationary sense, but not in a robust one. Most current non-cognitivists
"deny that their contents are true or false in any robust sense but not that
they can be true or false in a deflationary sense according to which there is
no substantial property separating true and false sentences".

`TruthApt φ` is having a truth value in the thin sense the shared questions
use; `RobustlyTruthApt φ` is having a robust (substantial) truth value. The
reading says nothing about how the two are related beyond this.

Source: Mark van Roojen, "Moral Cognitivism vs. Non-Cognitivism", *Stanford
Encyclopedia of Philosophy* (Spring 2026), §1.1.
-/
def QuasiRealistMinimalTruthAptReading {Sentence : Sort u}
    (Moral TruthApt RobustlyTruthApt : Sentence → Prop) : Prop :=
  ∀ φ, Moral φ → TruthApt φ ∧ ¬ RobustlyTruthApt φ

/-- Realism's robust truth: "moral realists are cognitivists insofar as they
think moral statements are apt for robust truth and falsity and that many of
them are in fact true".

Only robust truth-aptness is formalized, not that many moral statements are
true. `RobustlyTruthApt` is the predicate of `QuasiRealistMinimalTruthAptReading`.

Source: Mark van Roojen, "Moral Cognitivism vs. Non-Cognitivism", *Stanford
Encyclopedia of Philosophy* (Spring 2026), preamble.
-/
def RealistRobustTruthAptReading {Sentence : Sort u}
    (Moral RobustlyTruthApt : Sentence → Prop) : Prop :=
  ∀ φ, Moral φ → RobustlyTruthApt φ

/-- Stevenson's descriptive meaning: even the most general moral terms have,
besides their emotive meaning, a descriptive meaning. "Some theorists who view
themselves as emotivists suggest that even the most general terms of moral
evaluation have a descriptive meaning rather than just an emotive or
non-cognitive meaning (Stevenson 1944, 22 ...)".

`HasDescriptiveMeaning φ` says that `φ` has some descriptive meaning; what
that meaning is is not formalized.

Source: Mark van Roojen, "Moral Cognitivism vs. Non-Cognitivism", *Stanford
Encyclopedia of Philosophy* (Spring 2026), §2.1.
-/
def MoralSentencesHaveDescriptiveMeaningReading {Sentence : Sort u}
    (Moral HasDescriptiveMeaning : Sentence → Prop) : Prop :=
  ∀ φ, Moral φ → HasDescriptiveMeaning φ

/-- Stevenson's disagreement in attitude: when one person accepts a moral
sentence and another rejects it, their attitudes clash. Stevenson distinguishes
disagreement in belief from "disagreements in attitude", which involve
conative clash, and holds that moral disagreements involve both.

Only the attitude half is formalized; that moral disagreements also involve
disagreement in belief is not.

Source: Mark van Roojen, "Moral Cognitivism vs. Non-Cognitivism", *Stanford
Encyclopedia of Philosophy* (Spring 2026), §3.5.
-/
def MoralDisagreementInvolvesAttitudeClashReading {Agent : Sort u} {Sentence : Sort v}
    (Moral : Sentence → Prop) (Accepts Rejects : Agent → Sentence → Prop)
    (ClashInAttitude : Agent → Agent → Sentence → Prop) : Prop :=
  ∀ x y φ, Moral φ → Accepts x φ → Rejects y φ → ClashInAttitude x y φ

end TruthCore.English.VanRoojen
