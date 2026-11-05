# Showcase: logical positivism, systematically defeated (#1008)

This page is a worked example of the defeat-by-consequence method of #1007. It
takes one rival worldview at full strength, states each of its variants in its
proponents' own words, derives the consequences in Lean, and says exactly which
defeats count and what survives.

- **Counted defeats:** a defeat counts only if it rests on established premises
  (#999). Two of the defeats rest on no premise at all, so they count.
- **Status of the rest:** the others are proved consequences whose bite needs
  an open premise, and they are labelled that way.
- **No route impact:** no premise on a root route lists verificationism as a
  rival, so none of this changes a route cost. It is a demonstration of the
  method, not frontier progress.

All Lean results are in `TruthCore/Results/Logic/Verificationism/`, over the
vocabulary module `TruthCore/Logic/Verificationism.lean`.

- **Axioms:** none. Every result is zero-axiom, and all are constructive.
- **Premises:** each result is premise-free unless stated otherwise.

## 1. The worldview at full strength

The movement's core thesis is that a sentence has literal (cognitive) meaning
only if it is analytic or empirically verifiable. Metaphysics, theology and
ethics then come out not false but meaningless. The variants differ in what
"verifiable" means.

| Variant | Proponent's wording (pinned claim) | Typed as |
|---|---|---|
| Programme | The right method is "to say nothing except what can be said, i.e. the propositions of natural science" and to show the metaphysician "that he had given no meaning to certain signs" (Tractatus 6.53, `WITTGENSTEIN-TLP-6-53-RIGHT-METHOD`). | (no criterion; the programme) |
| **V1** Schlick | "The meaning of a proposition is the method of its verification" (`SCHLICK-MV-342-METHOD`). "Verifiability, which is the sufficient and necessary condition of meaning, is a possibility of the logical order" (`SCHLICK-MV-351-LOGICAL-POSSIBILITY`). Ayer reports that "some positivists" proposed *conclusive* verifiability, citing Schlick 1931 (`AYER-LTL-PELICAN-I-18-CONCLUSIVE-PROPOSED`). | `ConclusivelyVerifiable`: a jointly satisfiable finite set of observation statements entails the sentence |
| **V2** Ayer 1936 | A genuine factual proposition is one from which "some experiential propositions can be deduced … in conjunction with certain other premises without being deducible from those other premises alone" (`AYER-LTL-PELICAN-I-20-CRITERION`). | `WeaklyVerifiable1936` |
| **V3** Ayer 1946 | Direct and indirect verifiability, quoted verbatim from the 1946 Introduction p. 13 (`IEP-REL-LANG-2A-AYER-1946-CRITERION`). | `DirectlyVerifiable`, `IndirectlyVerifiable` (inductive), `LiterallyMeaningful1946` |
| **V4** Carnap | Metaphysical "sentences" are pseudo-sentences: word sequences that form no sentence "innerhalb einer bestimmten, vorgegebenen Sprache" (`CARNAP-UEBERWINDUNG-1-SCHEINSATZ`). The choice of a framework is "not a theoretical question … but rather a practical question" (`CARNAP-ESO-II-EXTERNAL-PRACTICAL`). | the criterion as a proposal for a language, not an assertion |
| Popper (cousin) | Ayer cites Popper's *Logik der Forschung* for a falsifiability criterion of significance (ch. I, p. 19, note 7). Popper himself offered falsifiability as a demarcation of science, not as a criterion of meaning, but that claim has no admissible witness here (see §6). | not modelled; kept apart so it is not conflated |

**Fidelity notes.**

- **Schlick and "conclusive" (V1).** Schlick 1936 does not say *conclusive*.
  - His criterion is the logical possibility of verification, fixed by rules (`SCHLICK-MV-351-LOGICAL-POSSIBILITY`).
  - The conclusive reading of V1 rests on Ayer's report about Schlick 1931.
  - Issue #1008's wording, "conclusively verifiable in principle", is therefore Ayer's version of Schlick, not Schlick 1936's. The claims keep the two apart.
- **Ayer on his own 1936 test (V2).** Ayer's own note on the 1936 formulation calls it "an over-simplified statement, which is not literally correct". That is why V3 exists.

### Answers to the shared questions

The answer kinds are:

- **S**: a sourced answer.
- **V**: a verified consequence in Lean.
- **U**: unexplained.
- **R**: the variant's answer is refuted under the stated semantics.

| Question | V1 | V2 | V3 | V4 |
|---|---|---|---|---|
| Is "God exists" meaningful? | U: not addressed by the pinned V1 claims | S, by pattern only: the criterion condemns transcendent theses (`AYER-LTL-PELICAN-I-21-CONDEMNED`); **R** for the exclusion thesis (defeat 3′) | S: no, the notion of God is "not an intelligible notion" (`IEP-REL-LANG-2A-AYER-GOD`); **R** for the pair "God exists" / "there is no God" (defeat 3) | S: not a sentence of the empiricist language; V (general): failing a criterion does not entail untruth (defeat 4) |
| Are laws of science meaningful? | S: "important nonsense" (`AYER-LTL-PELICAN-I-18-IMPORTANT-NONSENSE`); V: laws are excluded and their negations admitted; **R** with the weak closure floor item (defeat 2) | S: yes, the criterion was designed to admit them | S: yes | S: yes, inside the framework |
| What is the status of the criterion itself? | U (V: the dilemma, if it is in scope) | U (V: the dilemma) | S: a definition (Ayer 1946; no admissible witness); V: the dilemma | S: a practical proposal, not an assertion |
| Does the criterion exclude anything? | V: yes, too much (laws) | **R**: it excludes only sentences whose negation entails every observation statement | **R**: never a sentence together with its negation | V: only relative to the adopted language |
| Ethics | S: emotivism (Ayer ch. VI, `AYER-LTL-EMOTIVISM`, no witness) | same | same | U |

## 2. Defeat 3 (centrepiece): Church's trivialization of V3

**Source.** IEP, "Religious Language" §2a, quotes Church's 1949 review (JSL 14,
p. 53) verbatim (claim `IEP-REL-LANG-2A-CHURCH`). Church writes:

> For let O1, O2, O3 be three "observation-statements" … such that no one of
> the three taken alone entails any of the others. … Then (under Ayer's
> definition) –O1O2 v O3–S is directly verifiable, because with O1 it entails
> O3. Moreover S and –O1O2 v O3–S together entail O2. Therefore (under Ayer's
> definition) S is indirectly verifiable – unless it happens that –O1O2 v O3–S
> alone entails O2, in which case –S and O3 together entail O2, so that –S is
> directly verifiable.

**The construction in Lean** (`CHURCH-1949-TRIVIALIZATION`, theorem
`…Church.churchTrivialization`), step by step:

1. **Setting.** A truth-conditional language: sentences, worlds, and classical
   ¬, ∧, ∨. Entailment is truth preservation at every world. Take observation
   statements o₁, o₂, o₃ with o₁ ⊭ o₃ and o₃ ⊭ o₂. These are two of Church's
   non-entailments, so the hypothesis is weaker than his and the theorem is
   stronger.
2. **Church's sentence is directly verifiable.** A = (¬o₁ ∧ o₂) ∨ (o₃ ∧ ¬S)
   together with o₁ entails o₃, and o₁ alone does not (`churchSentence_direct`).
3. **S with A entails o₂.**
4. **Case split.**
   - If A alone entails o₂, then ¬S with o₃ entails o₂, which o₃ alone does
     not, so ¬S is directly verifiable (`neg_direct_of_entails`).
   - Otherwise S is indirectly verifiable, with A as its admissible further
     premise.
5. **Constructive form.** Proved as: *if ¬S is not directly verifiable, S is
   indirectly verifiable*. Classically this is Church's "either it or its
   negation is verifiable". The constructive form needs no excluded middle.
6. **Non-vacuity.** `churchObservationsInhabited` shows the hypotheses hold
   in the raven language (`TruthCore/Logic/Verificationism/Model.lean`).

**What it defeats.** V3's own commitment is that some sentence and its
negation (for example "there is a god" and "there is no god") are both not
literally meaningful. This is `STMT-AYER-1946-EXCLUDES-SENTENCE-AND-NEGATION`,
supported by `IEP-REL-LANG-2A-AYER-GOD` and `AYER-LTL-PELICAN-I-21-CONDEMNED`,
with their gaps recorded. `AYER-1946-EXCLUSION-FAILS` refutes it from no
premises.

- **Status:** the refutation counts (`corpus.py frontier --json` shows it as
  `counted: true`). **Established.**
- **With closure under negation:** if meaningfulness is closed under negation
  for *every* sentence, then no sentence fails to be meaningful
  (`AYER-1946-NEGATION-CLOSED-EXCLUDES-NOTHING`). That universal closure is an
  additional assumption, not attributed to Ayer: his verdict that one
  theistic sentence and its negation are both nonsensical does not supply it.
- **Counted with the floor (owner decision, 2026-11-05).** The owner approved
  closure of meaningfulness under negation as a floor item, in two sibling
  versions (§3a). `AYER-1946-EXCLUDES-A-NEGATION-FAILS` uses the **strong**
  version: if a sentence is meaningful, so is its negation. Its argument:
  1. Suppose ¬y is not meaningful, where meaningfulness is the 1946 criterion.
  2. Then ¬y is not directly verifiable.
  3. By Church, y is indirectly verifiable, so y is meaningful.
  4. By closure, ¬y is meaningful, a contradiction.

  So under V3 no negated sentence fails to be meaningful; "there is no god"
  is included. This refutes `STMT-AYER-1946-EXCLUDES-A-NEGATION`, and the
  refutation counts. The strong version is the weakest one this refutation
  needs, because the rival leaves open which negation it excludes. It does
  not show that every sentence is meaningful: closure runs only from a
  sentence to its negation.

**V2 falls the same way, more simply.** `AYER-1936-CRITERION-TRIVIAL` uses the
further premise ¬S ∨ o: S passes the 1936 test unless ¬S entails o.
`AYER-1936-EXCLUSION-FAILS` refutes `STMT-AYER-1936-EXCLUDES-METAPHYSICS`.
This is also counted and **established**.

## 3. Defeat 2: strong verification excludes universal laws (V1)

**Result.** `STRONG-VERIFICATION-EXCLUDES-LAWS`:

- **Setting:** infinitely many individuals, each observation statement about
  finitely many of them, and individuals that vary independently.
- **The law fails:** "every R is B" is not conclusively verifiable.
- **Its negation passes:** the negation is conclusively verifiable whenever an
  observed counterinstance is possible.
- **Non-vacuity:** `lawSettingInhabited`.

**Sources.**

- Ayer states the argument himself: general propositions of law "cannot, even
  in principle, be verified conclusively" (`AYER-LTL-PELICAN-I-18-LAWS`).
- SEP reports Hempel's version with the negation half
  (`SEP-HEMPEL-2-3-UNIVERSALS`).
- Both are linked to the statement as `supports`, with their gaps noted.

**The proponent's answer.** Some positivists bite the bullet: laws are
"important nonsense" (`AYER-LTL-PELICAN-I-18-IMPORTANT-NONSENSE`).

**Status: established, via the weak floor item.**
`STRONG-VERIFICATIONISM-WITH-LAWS-FAILS` refutes the V1 package
`STMT-STRONG-VERIFICATIONISM-WITH-LAWS`. The package has three parts:
analytic sentences are valid; a sentence is meaningful iff it is analytic or
conclusively verifiable; and the language has a testable universal law. The
refutation goes:

1. The negation of the law is conclusively verifiable, so it is meaningful.
2. By closure, the law's double negation is meaningful.
3. So the double negation is analytic or conclusively verifiable.
4. It is not analytic: analytic sentences are valid, and the double negation
   fails where the possible counterinstance holds.
5. It is not conclusively verifiable: the argument is the same as for the law.

This also defeats the "important nonsense" reply: V1 cannot admit the
negation of a law while excluding its double negation. The refutation counts.

- **Weakest version needed.** It uses only the **weak** version: closure for
  negated sentences.
- **F3/F4 still do not help.** The observation items are singular and
  consistent with V1. The defeat runs through the closure floor item instead.

### 3a. The floor item: closure under negation, strong and weak

The owner approved it on 2026-11-05
(https://github.com/moritzbrantner/truth-core/issues/1008#issuecomment-6662364121).
It is recorded as two sibling statements for #1017.

| Sibling | Statement | Used by |
|---|---|---|
| `STMT-MEANINGFULNESS-CLOSED-UNDER-NEGATION-STRONG` | for every S, if S is meaningful, so is ¬S | `AYER-1946-EXCLUDES-A-NEGATION-FAILS` |
| `STMT-MEANINGFULNESS-CLOSED-UNDER-NEGATION-WEAK` | for every S, if ¬S is meaningful, so is ¬¬S | `STRONG-VERIFICATIONISM-WITH-LAWS-FAILS` |

`MEANING-NEGATION-CLOSURE-STRONG-ENTAILS-WEAK` proves strong ⊢ weak.

How each sibling is marked:

- **Marking.** Each is marked `self_evident` on the `common_ground` basis,
  with `owner_approval`.
- **Justification.** Hempel's adequacy condition, which SEP §2.3 reports as
  "S is meaningful iff its negation is". Claims `SEP-HEMPEL-2-3-NEGATION-CLOSURE`
  and `…-WEAK`.
- **Recorded rivals.** These are unattributed; they are what V1 is committed
  to: `STMT-SOME-MEANINGFUL-NEGATION-NOT-MEANINGFUL` (strong) and
  `STMT-SOME-MEANINGFUL-NEGATION-DOUBLE-NEGATION-NOT-MEANINGFUL` (weak).
- **Basis criterion.** It is not mechanically met. Both items are established
  relative to the owner's approval.

## 4. Defeat 1: self-application (V1–V3)

**Result.** `VERIFICATIONISM-SELF-APPLICATION-DILEMMA` instantiates the
existing schema `LOGIC-SELF-APPLICATION-DILEMMA`. For any variant's
verifiability predicate: if the principle's formulation is in its own scope
and is neither analytic nor verifiable, then if the principle holds, its
formulation is not meaningful; and if the formulation is meaningful, the
principle fails.

**"Meaningful" is kept apart from the criterion.** It is a separate parameter
(`DISAMB-VERIFICATIONIST-MEANINGFUL`). Otherwise the principle would hold by
definition.

**The movement's own admission.** Tractatus 6.54: "he who understands me
finally recognizes them as senseless … He must so to speak throw away the
ladder" (`WITTGENSTEIN-TLP-6-54-LADDER`). It is linked as `supports` to the
scope premise, with the gap noted: the Tractatus states no verification
principle.

**Status: conditional, not counted.** All three premises are open:
`STMT-VERIFICATION-PRINCIPLE-IN-OWN-SCOPE`, `…-NOT-ANALYTIC` and
`…-NOT-VERIFIABLE`.

- **Not analytic?** Ayer's 1946 reply that the principle is a "definition"
  contests non-analyticity. That reply has no admissible witness.
- **Not verifiable, for V3?** Here the third premise is in tension with
  Church: given Church's observation statements, it can hold only if the
  principle's *negation* is directly verifiable. So for V3, defeat 3 does the
  work that self-application cannot.
- **Proposal reading.** The distinction between adopting a rule and asserting
  a sentence (`docs/ayer-verification-boundary.md`) is what V4 builds on.

## 5. Defeat 4: the proposal reading (V4) is not defeated here, and is toothless

**Objects to self-application.** Carnap's reply is that adopting an empiricist
language is "a matter of a practical decision", and "there is no such belief
or assertion or assumption" (`CARNAP-ESO-II-EXTERNAL-PRACTICAL`). It is
recorded as an `attacks` objection to the scope premise, not as its failure:
`PrincipleInOwnScope scope v` says only that the formulation is in scope, and
nonassertive adoption does not by itself take a formulation out of scope.
The missing bridge, from "the criterion is adopted, not asserted" to "its
formulation is not a sentence in the scope it governs", is open
(`docs/ayer-verification-boundary.md`). `LOGIC-SELF-APPLICATION-SCOPE-NEEDED`
shows only that if the scope premise is dropped, nothing follows.

**Settles no truth.** `CRITERION-VERDICT-SILENT-ON-TRUTH` is a countermodel:

- A language whose frame has an observation statement contains a sentence
  that is neither analytic nor conclusively verifiable, and yet is true at a
  world.
- So failing an adopted criterion does not make a sentence untrue, and does
  not deprive it of truth conditions.

**No defeat applies, and no verdict on theology follows from the model.**
None of defeats 1–3 binds V4 as recorded here, but V4 itself is not encoded
as a configuration, so its consistency as a complete position is not
certified. The countermodel shows only that the general inference from
"fails the adopted criterion" to "untrue" fails; it says nothing specifically
about theological sentences. Read as a recommendation rather than a truth, V4
gives no ground for the claim that theology is meaningless beyond "not a
sentence of the recommended language".

**Search for a bridge against V4.** At the owner's request
(`ATTEMPT-CARNAP-V4-BRIDGE-1008`, outcome: blocked), I tried three routes:

- **The pragmatic-justification regress.** On what grounds is the proposal
  adopted? Carnap answers that the grounds are factual questions of
  efficiency, "a matter of fact, based upon the content of our experiences",
  asked inside an accepted language (`CARNAP-ESO-II-EFFICIENCY-FACT`). No
  further criterion is needed, so no regress arises.
- **Quine 1951.** As SEP reports him, Quine rejects the internal/external
  distinction because it rests on the analytic/synthetic distinction
  (`SEP-CARNAP-7-QUINE`). This is recorded as `attacks`. It bites only if
  analyticity is rejected, which is not an established floor item, and SEP
  reports the mainstream reply that Quine partly misunderstood Carnap.
- **Self-application to Carnap's metatheses.** This is the analyst's
  reasoning, unsourced. Carnap could treat his metatheses as analytic in a
  constructed metalanguage, which would meet the analytic disjunct of the
  standard.

No honest bridge was found. V4 stays open.

**Status (D-I, #1007).** It neither defends nor attacks any route premise.
That it is undefeated here is recorded, and it has no cost effect.

## 6. Defeat 5: the movement's own retrospective (optional)

**Hempel's verdict.** In 1950 Hempel conceded that it was "useless to continue
to search for an adequate criterion of testability in terms of deductive
relationships to observation sentences" (`SEP-VIENNA-CIRCLE-3-1-HEMPEL`, a
verbatim quotation in SEP).

**Status.** This is testimony, not a proof. The Lean results above are the
proofs.

## 7. Status summary

| Defeat | Target | Status |
|---|---|---|
| 3 Church | V3 exclusion of a sentence and its negation | **established**: premise-free refutation, counted |
| 3′ 1936 triviality | V2 exclusion | **established**: premise-free refutation, counted |
| 2 universal laws | V1 package with testable laws | **established**: counted refutation from the owner-approved weak closure floor item |
| 3″ 1946 with closure | V3 exclusion of a negated sentence | **established**: counted refutation from the owner-approved strong closure floor item |
| 1 self-application | V1–V3 | conditional on three open premises; for V3 superseded by Church |
| 4 proposal | V4 | **V4 not defeated** (bridge search blocked, `ATTEMPT-CARNAP-V4-BRIDGE-1008`): the scope objection needs an open bridge; the countermodel blocks only the inference from failing the criterion to untruth; V4's consistency is not certified (D-I: no route effect) |
| 5 Hempel | the programme | sourced testimony (SEP) |

**Frontier.** Every step left the frontier unchanged (`frontier-diff`), so
the cost effect is 0. Neither closure floor item is a premise on any route,
and no route leaf has a verificationist `alternative_to`.

- **Showcase PRs:** open premises reaching the root stayed 91 → 91.
- **Closure follow-up:** the count stayed 90 → 90. The base is 90 because the
  F4 marking (#1009) had already been merged.
- **Cheapest route:** stays at cost 31 throughout.

## 8. Witnesses and gaps

**Pinned** (all `web_snapshot`; none has a Wayback fallback yet):

| Work | Witness | Status |
|---|---|---|
| Tractatus, Ogden 1922 | Project Gutenberg #5740 PDF | public domain (US) |
| Schlick 1936 | MSGA I/6 PDF, Universität Rostock | public domain; no renewal found for the *Philosophical Review* |
| Ayer, *LTL* ch. I | LSE PH201 course PDF, Penguin pp. 18–21, OCR | in copyright |
| Ayer 1946 (Introduction p. 13; ch. VI p. 144) | IEP "Religious Language" §2a | secondary, verbatim quotation |
| Church 1949 | IEP "Religious Language" §2a | secondary, verbatim quotation |
| Hempel 1950 | SEP "Hempel" §2.3; SEP "Vienna Circle" §3.1 | secondary |
| Carnap 1950 (ESO) | CMU Carnap Project transcriptions | in copyright |
| Quine 1951 (as reported) | SEP "Carnap" §7 | secondary |
| Carnap 1931/32 (*Überwindung*) | CMU Carnap Project transcriptions | in copyright |

**Not pinned:**

- **Ayer ch. VI**, "the atheist's assertion … is equally nonsensical": no
  admissible witness. `AYER-LTL-EMOTIVISM` stays a candidate.
- **Ayer's 1946 "definition" reply**: no admissible witness.
- **Popper's statement that falsifiability is not a criterion of meaning**:
  no admissible witness. SEP's Popper entries do not say it in those words.
- **Church's review and Hempel 1950 themselves**: copyrighted and unhosted, so
  only the verbatim secondary quotations are pinned.
