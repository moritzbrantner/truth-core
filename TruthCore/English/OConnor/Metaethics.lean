/-!
Source-derived readings of Alex O'Connor's recorded statements of his own
metaethics (media-span witnesses pinned to youtube-corpus transcript segments).

Shared vocabulary, all of it parameters rather than definitions:

* `Sentence` — declarative sentences, moral ones included.
* `Moral φ` — `φ` is a moral statement.
* `SaysSomethingBad φ` — `φ` says of something that it is bad.
* `TruthApt φ` — `φ` has a truth value: it is the kind of sentence that can be
  true or false.
* `Holds φ` — `φ` is true.
* `ObjectiveTruth φ` — `φ` is an objective truth: true independently of anyone's
  attitudes or conventions.

The readings say nothing about which sentences are moral beyond what each
passage states. In particular they do not identify a moral sentence's content
with any non-moral fact.
-/

namespace TruthCore.English.OConnor

universe u

/-- Ethical emotivism: moral statements do not have truth value at all
("moral statements don't actually have truth value at all").

O'Connor presents this as his own view ("myself I ... essentially conform to a
view called ethical emotivism"), adding that moral sentences also carry a
prescriptive element ("don't murder"), which "equally ... doesn't have truth
value". The reading captures only the denial of truth value, not the positive
expressive or prescriptive account.

Source: Alex O'Connor, "Destiny's Ethics Tested by CosmicSkeptic"
(Alex O'Connor, 2023-05-22), 17:35–18:25.
-/
def MoralStatementsLackTruthValueReading {Sentence : Sort u}
    (Moral TruthApt : Sentence → Prop) : Prop :=
  ∀ φ, Moral φ → ¬ TruthApt φ

/-- A sentence without truth value is not true: it is "not the kind of sentence
that can be true or false".

This is O'Connor's own gloss on "truth value" in the same breath. Only the
half the gloss needs is formalized: lacking a truth value excludes being true.
It is stated in the weak form `¬ TruthApt φ → ¬ Holds φ`, not as
`Holds φ → TruthApt φ`, which would need classical logic to recover from it.

Source: Alex O'Connor, "Destiny's Ethics Tested by CosmicSkeptic"
(Alex O'Connor, 2023-05-22), 17:35–18:25.
-/
def LackingTruthValueExcludesTruthReading {Sentence : Sort u}
    (TruthApt Holds : Sentence → Prop) : Prop :=
  ∀ φ, ¬ TruthApt φ → ¬ Holds φ

/-- There are no objective moral truths ("you're assuming that objective moral
truths exist which if you ask me they don't and they can't").

Only the non-existence claim is formalized, not the stronger "they can't". The
2016 video defends this by a subjectivist account ("morals are entirely
subjective"), not yet by emotivism; the reading is neutral between the two.

Source: Alex O'Connor, "Frank Turek thinks that Evil proves God's existence"
(Alex O'Connor, 2016-08-23), 01:31–01:39.
-/
def NoObjectiveMoralTruthsReading {Sentence : Sort u}
    (Moral ObjectiveTruth : Sentence → Prop) : Prop :=
  ∀ φ, Moral φ → ¬ ObjectiveTruth φ

/-- The evil invoked by the problem of evil is not objective: Turek assumes "that
the evil that people refer to when they try to criticize the idea of an omni
benevolent God is objective whereas I would argue that it's absolutely not".

`evilPremise` is the sentence the critic asserts, that there is evil in the
world. The reading denies only that it is an objective truth.

Source: Alex O'Connor, "Frank Turek thinks that Evil proves God's existence"
(Alex O'Connor, 2016-08-23), 01:56–02:06.
-/
def EvilPremiseNotObjectiveReading {Sentence : Sort u}
    (ObjectiveTruth : Sentence → Prop) (evilPremise : Sentence) : Prop :=
  ¬ ObjectiveTruth evilPremise

/-- Saying that something is bad is a moral statement: O'Connor's example of
the sentences emotivism is about ("saying ... that something is bad or
expressing a moral discontempt with it, it's a bit like saying murder, boo").

`SaysSomethingBad φ` holds when `φ` says of something that it is bad. The
reading classifies such sentences as moral; it does not say which sentences
say that something is bad. Whether the problem of evil's premise is one of them
is a separate bridge, not part of this reading.

Source: Alex O'Connor, "Destiny's Ethics Tested by CosmicSkeptic"
(Alex O'Connor, 2023-05-22), 17:35–18:25.
-/
def BadnessAscriptionsAreMoralReading {Sentence : Sort u}
    (SaysSomethingBad Moral : Sentence → Prop) : Prop :=
  ∀ φ, SaysSomethingBad φ → Moral φ

end TruthCore.English.OConnor
