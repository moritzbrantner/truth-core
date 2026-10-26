import TruthCore.English.OConnor.Metaethics
import TruthCore.English.VanRoojen.MoralCognitivism
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question5.Article1
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question48.Articles2and3
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaSecundae.Question94.Article2
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaSecundae.Question94.Article4

/-!
Emotivism, expressivism and Catholic natural law as complete rival theories
(#185, part of #181; owner principles on #143 and #149: a theory is a set of
propositions and arguments with an answer map, results are counts plus prose,
no score).

Only theories and consistency claims live in this namespace: `bind-check`
treats every `TruthCore.Comparison.*` definition as a theory bundle.

## Theories

* **O'Connor's emotivism** (`OConnorEmotivism`): his four recorded metaethical
  readings (#157/#160). One of them, "there are no objective moral truths", is
  recorded from his 2016 subjectivism, not his 2023 emotivism
  (`DISAMB-MORAL-ANTIREALISM`), so the bundle is his recorded metaethics, not
  emotivism alone. The prescriptive element he adds is not formalized yet,
  because his spans cannot be re-read without the youtube-corpus export (#184).
* **Stevenson's emotivism** (`StevensonEmotivism`): emotive meaning
  (free-standing moral assertions express attitudes), descriptive meaning, and
  disagreement in attitude (SEP §2.1, §3.5).
* **Quasi-realism** (Blackburn, Gibbard): its bundles are in
  `TruthCore.Comparison.MoralError` and `TruthCore.Comparison.MoralLanguage`,
  and its deviation map is in `TruthCore.Refutations.QuasiRealism`.
* **Ayer's emotivism** (*Language, Truth and Logic*, 1936): not modeled. No
  pinnable witness exists, since the book is in copyright, so it is the
  candidate `AYER-LTL-EMOTIVISM`.
* **Catholic natural law** (`CatholicNaturalLaw`): goodness is actuality and
  evil privation (ST I q.5 a.1, q.48), moral judgments have truth (I-II q.94
  a.4), the Germans' error (a.4), and the first precept (a.2). The first
  precept's self-evidence is the candidate
  `AQUINAS-FIRST-PRECEPT-SELF-EVIDENT`.

Each modeled theory is shown consistent together with the existence of a moral
sentence: `OCONNOR-EMOTIVISM-CONSISTENT`, `STEVENSON-EMOTIVISM-CONSISTENT`,
`CATHOLIC-NATURAL-LAW-CONSISTENT`, and, for quasi-realism,
`QUASI-REALISM-ADMITS-MORAL-ERROR` and
`EXPRESSIVISM-CONSISTENT-WITH-GEACH-VALIDITY`.

## Answer map over the shared questions

Each cell takes one of four values:

* **V**: answered, and the answer is a verified result;
* **S**: answered by a sourced claim, without a result;
* **U**: unexplained (no answer in the theory as recorded);
* **C**: the theory contradicts the shared datum.

The questions:

1. **Q-MORAL-GROUNDING**: what makes something objectively good or evil? (#150)
2. **Q-MORAL-LANGUAGE-VALIDITY**: why is Geach's moral modus ponens valid? (#182)
3. **Q-MORAL-ERROR**: can one err about a moral matter? (#183)
4. **Q-MORAL-DISAGREEMENT**: is a moral disagreement a contradiction? (#183)
5. **Q-MORAL-PROGRESS**: is a change of moral view sometimes a correction? (#183)
6. **Q-ROBUST-TRUTH**: is moral truth more than minimal? (#185)
7. **Q-NORMATIVE-REASONS**: why is the good to be pursued?
8. **Q-EVIL-PREMISE**: is "there is evil" true, as the problem of evil asserts? (#160)

| Question | O'Connor | Stevenson | Quasi-realism | Catholic natural law |
|---|---|---|---|---|
| 1. Grounding | S: no objective moral truths | U | U: explanatory order (§5.2) and supervenience (§3.4) are recorded, but neither answers what makes a moral judgment true | S: actuality and privation (q.5, q.48) |
| 2. Validity | U | U | U: consistency with validity is verified, but no explanation of validity is derived | U (not formalized) |
| 3. Error | V: none (`EMOTIVISM-EXCLUDES-MORAL-ERROR`) | U | V: minimal error (model) | V: the Germans erred (`AQUINAS-ST-I-II-Q94-A4-GERMANS-ERRED`) |
| 4. Disagreement | V: no contradiction (`EMOTIVISM-EXCLUDES-GENUINE-MORAL-CONTRADICTION`) | S: opposed interests and mutual redirection (Stevenson 1937, pp. 27–29) | S: minimal contradiction | S: contradiction, since moral judgments are truth-apt (a.4) |
| 5. Progress | U (on the cognitive reading of correction) | U | S: minimal correction (§4.3) | S: correction of corruption (q.94 a.5 ad 1) |
| 6. Robust truth | S: no truth value at all | U | V: not robust, a deviation (`QUASI-REALISM-DEVIATES-ON-ROBUST-TRUTH`); sustained on the anti-realist order of explanation (`ANTIREALIST-ORDER-SUSTAINS-ROBUST-TRUTH-DEVIATION`), collapsed by the collapse premise (`MINIMALISM-COLLAPSES-ROBUST-TRUTH-DEVIATION`), open | S: practical truth, the same for all (a.4) |
| 7. Normative reasons | U | U | U | S: the first precept (a.2) |
| 8. Evil premise | C: not true (`POE-EXTERNAL-PREMISE-VS-EMOTIVISM`) | U | U | U: not derived from `CatholicNaturalLaw`; the separate problem-of-evil theory entails it (see below) |

**Counts**, in the order V / S / U / C:

| Theory | V | S | U | C |
|---|---|---|---|---|
| O'Connor | 2 | 2 | 3 | 1 |
| Stevenson | 0 | 1 | 7 | 0 |
| Quasi-realism | 2 | 2 | 4 | 0 |
| Catholic natural law | 1 | 5 | 2 | 0 |

Prose:

* **Emotivism, in O'Connor's form,** answers the error and disagreement
  questions only by denial. It contradicts the shared evil premise, which is
  what #160 needs against the external problem of evil, and it leaves
  validity, progress (on the cognitive reading) and normative reasons
  unexplained.
* **Stevenson's form** now has a primary-source refinement: opposed interests
  and mutual attempts to redirect them can persist under factual agreement.
  `STEVENSON-FACTUAL-AGREEMENT` verifies an enriched model with an actual
  clash and a nonempty factual domain. It is a consistency result, so this
  does not promote the sourced answer to an entailed-coverage result. The
  other seven questions remain unexplained in this bundle. See
  `docs/stevenson-disagreement.md` for reasons, embedding and remaining gaps.
* **Quasi-realism** matches realism wherever minimal truth suffices. It
  deviates on robust truth and on explanatory order (#190, #191); its answer
  to the grounding question is not in the pinned witness. Validity remains
  unexplained: `EXPRESSIVISM-CONSISTENT-WITH-GEACH-VALIDITY` supplies validity
  as shared data in a joint model, rather than deriving it from constant
  meaning. That consistency result remains a separate achievement.
* **The Catholic natural-law theory** leaves validity and the evil premise
  unexplained in this bundle. Most of its answers are sourced, not yet verified.

The evil premise has a separate verified answer:
`POE-CATHOLIC-ENTAILS-EVIL-PREMISE` follows from
`TruthCore.Comparison.ProblemOfEvil.Background` and
`TruthCore.Comparison.ProblemOfEvil.Catholic`. Its proof uses both that
something lacks a due good (`SomethingFallsShortOfDueGoodReading`) and that
existence of evil makes the evil-premise sentence true
(`EvilIsAsPropositionalTruthReading`). Neither commitment is included in
`CatholicNaturalLaw`. The result remains verified for the separate
problem-of-evil theory; it is not counted as an answer derived from this
natural-law bundle.

A count is not a score (#149).

Issue #249 adds objective naturalistic realism (Railton and Boyd), the shared
mind-independence/epistemology questions, and an equally scoped compositional
validity test for all three realist accounts. See
`docs/naturalistic-moral-realism.md`; the older counts above retain their
original eight-question scope.
-/

namespace TruthCore.Comparison.Metaethics

open TruthCore.English.OConnor
open TruthCore.English.VanRoojen
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- The shared signature of the metaethics comparison. -/
structure Sig where
  Agent : Type
  Sentence : Type
  Ctx : Type
  Attitude : Type
  Being : Type
  Perfection : Type
  Act : Type
  Moral : Sentence → Prop
  TruthApt : Sentence → Prop
  Holds : Sentence → Prop
  ObjectiveTruth : Sentence → Prop
  SaysSomethingBad : Sentence → Prop
  HasDescriptiveMeaning : Sentence → Prop
  Accepts : Agent → Sentence → Prop
  Rejects : Agent → Sentence → Prop
  ClashInAttitude : Agent → Agent → Sentence → Prop
  Expresses : Sentence → Ctx → Attitude → Prop
  /-- A free-standing assertoric occurrence. -/
  free : Ctx
  Has : Being → Perfection → Prop
  Due : Being → Perfection → Prop
  GoodIn : Being → Perfection → Prop
  Evil : Being → Prop
  GoodAct : Act → Prop
  EvilAct : Act → Prop
  ToBePursued : Act → Prop
  ToBeAvoided : Act → Prop
  /-- "Tormenting the cat is bad" (#182). -/
  p : Sentence
  germans : Agent
  /-- "Robbery is not unjust" (ST I-II q.94 a.4). -/
  robberyNotUnjust : Sentence

/-- There is a moral sentence: Geach's "tormenting the cat is bad" (#182). It
keeps the consistency claims from holding only vacuously. -/
def ThereIsAMoralSentence (s : Sig) : Prop :=
  GeachMinorPremiseIsMoralReading s.Moral s.p

/-- O'Connor's emotivism: his four recorded metaethical readings. The third,
no objective moral truths, is recorded from his 2016 subjectivism. -/
def OConnorEmotivism (s : Sig) : Prop :=
  MoralStatementsLackTruthValueReading s.Moral s.TruthApt ∧
    LackingTruthValueExcludesTruthReading s.TruthApt s.Holds ∧
    NoObjectiveMoralTruthsReading s.Moral s.ObjectiveTruth ∧
    BadnessAscriptionsAreMoralReading s.SaysSomethingBad s.Moral

/-- Stevenson's emotivism: emotive meaning, descriptive meaning, and
disagreement in attitude. -/
def StevensonEmotivism (s : Sig) : Prop :=
  FreeMoralAssertionExpressesAttitudeReading s.Moral s.Expresses s.free ∧
    MoralSentencesHaveDescriptiveMeaningReading s.Moral s.HasDescriptiveMeaning ∧
    MoralDisagreementInvolvesAttitudeClashReading s.Moral s.Accepts s.Rejects s.ClashInAttitude

/-- Catholic natural law in this question set. -/
def CatholicNaturalLaw (s : Sig) : Prop :=
  GoodnessIsActualityReading s.GoodIn s.Has ∧
    EvilIsPrivationReading s.Evil s.Due s.Has ∧
    MoralJudgmentsAreTruthAptReading s.Moral s.TruthApt ∧
    GermansHeldRobberyNotUnjustReading s.Accepts s.Moral s.Holds s.germans s.robberyNotUnjust ∧
    FirstPreceptOfNaturalLawReading s.GoodAct s.EvilAct s.ToBePursued s.ToBeAvoided

/-- O'Connor's emotivism and the existence of a moral sentence are jointly
satisfiable. -/
def OConnorEmotivismConsistent : Prop :=
  ∃ s : Sig, OConnorEmotivism s ∧ ThereIsAMoralSentence s

/-- Stevenson's emotivism and the existence of a moral sentence are jointly
satisfiable. -/
def StevensonEmotivismConsistent : Prop :=
  ∃ s : Sig, StevensonEmotivism s ∧ ThereIsAMoralSentence s

/-- Catholic natural law, as formalized here, is satisfiable. -/
def CatholicNaturalLawConsistent : Prop :=
  ∃ s : Sig, CatholicNaturalLaw s

end TruthCore.Comparison.Metaethics
