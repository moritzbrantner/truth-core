# Resurrection pilot: the shared question set

Issue #223 implements `QSET-RESURRECTION-PILOT` with the existing proposition,
argument and `AnswerMap` model. The six systems face the same fifteen
questions. A system can leave a question unexplained; the name of a
resurrection hypothesis supplies no metaphysics automatically. No modern
proponent is attributed one of these bundles.

The implementation is in `TruthCore/History/Resurrection.lean`,
`TruthCore/Comparison/Resurrection.lean` and
`TruthCore/History/ResurrectionCoverage.lean`. The Catholic account reuses
`TruthCore.Case.Catholicism.Signature` and its God, claimed-authority and
resurrection predicates. It does not identify those predicates with the
separate Creed atoms or establish the skeleton's stage 4.

## Source reports and historical premises

All the following witnesses were pinned, materialized and read before their
claims were finalized. Claim records contain the exact locator and reading;
passage manifests retain chapter or book context. The Greek NT is
Westcott–Hort's text in canonical-greekLit; First Clement is Lake's Greek
edition in First1KGreek; Josephus is the Greek Antiquities witness in
canonical-greekLit; Tacitus is Fisher's Latin Annals witness in
canonical-latinLit. Each file has its own immutable revision and Git blob SHA.
The repositories' CC BY-SA 4.0 terms are recorded in the manifests. No primary
text or translation is copied into the corpus records.

| Finding | Source support | What remains open |
| --- | --- | --- |
| E0: crucifixion | Mark 15.24–25,37,44–45 | Accepting narrated crucifixion as history; death is separate. Tacitus Ann.15.44 reports execution under Pilate, without specifying crucifixion. |
| E1: appearance proclamation before the Corinthian letter | 1 Cor 15.3–8 | Accepting the received/transmitted chronology as historical. No absolute date, interval from Easter, or pre-Pauline formula boundary is encoded. |
| E2: empty-tomb tradition with a reported opposing theft story | Matt 28.5–8,11–15, with 27.57–66 context | Matthew's hostile acknowledgement is a Christian narration of an opposing story. It is not independently preserved enemy testimony. Actual tomb emptiness and payment to guards are separate historical claims. |
| E3: sincere interpreted experiences by Cephas and another disciple | 1 Cor 15.5; John 20.19–25; 1 Clement 42.3; endurance context at 5.2–7 | Identifying participants across reports, narrated perception and attributed conviction do not alone establish inner sincerity, actual experience, external veridicality, or a common mechanism for all reported groups. |
| E4: Paul's transition from nonbelief to belief | Gal 1.13–24; appearance context at 1 Cor 15.8–10 | Persecution and preaching are reported activities. Reading them as inner belief states is explicit; the supernatural cause is separately proposed. |
| E5: James's transition from nonbelief to belief | John 7.3–5; Acts 1.13–14; Gal 1.18–19; appearance context at 1 Cor 15.7 | Identifying this James within the brother groups, distributing the earlier group nonbelief to him, and reading later prayer as belief are open interpretive bridges. |

Josephus Ant.20.200 (20.9.1), read with 20.197–203, reports the stoning of
James, brother of Jesus called Christ, in an account of Ananus's irregular
judicial action. It supplies neither conversion nor refusal to recant an
appearance claim. First Clement's endurance language does not supply those
missing premises either.

`STMT-PILOT-REPORT-*` statements concern what a text reports. The six
`STMT-PILOT-E*` findings are independent open premises, connected to that
support by `supports` relations. The five `STMT-PILOT-BRIDGE-*` statements
make the historical reading steps explicit. They are not new source claims,
axioms, or proofs of findings. E2 is already a tradition finding and requires
no event-truth bridge. The report/finding distinction is recorded in
`DISAMB-RESURRECTION-PILOT-EVIDENCE` and in the linked definitions.

## Alternative readings of the findings

The competing accounts concern the reports as well as the events. Matthew's
story can be read as preserving an actual hostile response or as apologetic
narration of one; its mere presence establishes neither alternative's
historical truth. The explicit E2 finding preserves the tradition while the
actual-tomb account is asked separately. John 20 and Clement's assurance can
be read as reflecting sincere experience, or as an author's portrayal which
requires further historical defense. Paul's transition in activity supports a
belief transition without logically forcing inner sincerity.

James is especially underdetermined: a collective comment about brothers
need not individually describe this James, prayer does not itself narrate a
conversion, and the appearance list does not identify its James as the
previously unbelieving brother or say that the appearance caused conversion.
The accepted E5 premise states that additional reading openly. Its denial is
not refuted here. Josephus's lawbreaking accusation is compatible with several
motives and cannot fill that gap. These are alternatives to investigate
through evidence and argument, not uncertainty percentages.

The swoon account contests actual death while accepting crucifixion. It
therefore faces Mark's narrated death and centurion confirmation, the received
death/burial proclamation, and Tacitus's execution report. Its consistency
model is possible because the common E0 states crucifixion alone; the model
is no historical vindication of survival. Legend here concerns development
of the bodily-resurrection narrative from sincere experiences. A claim that
*all* appearance proclamation began only after the Corinthian letter would
instead conflict with accepted E1 and is not substituted for this variant.

## The whole answer map

The cells below name propositions, not probabilities. `E0`–`E5` abbreviate the
six independent finding statements. `C`, `L`, `V`, `G`, `T` and `S` abbreviate
`CatholicAccount`, `LegendAccount`, `VisionAccount`, `GroupAccount`,
`TheftAccount` and `SwoonAccount`; their exact conjunctions are in Lean.
**Unexplained** is represented by `available = false`, with no inferred answer
from the unused `says` value.

| Shared question | Catholic | Legend | Individual hallucination | Group variant | Stolen body | Swoon |
| --- | --- | --- | --- | --- | --- | --- |
| Does God exist? | Existing skeleton GodExists | Unexplained | Unexplained | Unexplained | Unexplained | Unexplained |
| What causes the world? | DivineCause, an open God-as-cause commitment | Unexplained | Unexplained | Unexplained | Unexplained | Unexplained |
| Did Jesus claim divine authority? | JesusClaims | Unexplained | Unexplained | Unexplained | Unexplained | Unexplained |
| Was that authority vindicated? | AuthorityVindicated | Unexplained | Unexplained | Unexplained | Unexplained | Unexplained |
| Did Jesus rise from death? | Rose | Denial with L | Denial with V | Denial with G | Denial with T | Denial with S |
| E0: crucifixion | E0 | E0 | E0 | E0 | E0 | E0 |
| E1: prior appearance proclamation | E1 | E1 | E1 | E1 | E1 | E1 |
| E2: tomb/hostile-story tradition | E2 | E2 | E2 | E2 | E2 | E2 |
| E3: sincere experiences | E3 | E3 | E3 | E3 | E3 | E3 |
| E4: Paul's conversion | E4 | E4 | E4 | E4 | E4 | E4 |
| E5: James's conversion | E5 | E5 | E5 | E5 | E5 | E5 |
| Account of actual tomb emptiness | C: rising with empty tomb | Unexplained | Unexplained | Unexplained | T: body removal | S: recovery/departure |
| Account of appearance experiences | C: risen encounter | L: narrative elaboration from experience | V: individual visions | G: group suggestion | T: separate visionary account | S: survivor encounter |
| Cause of Paul's changed belief | C: encounter caused belief | Unexplained | Unexplained | Unexplained | Unexplained | Unexplained |
| Cause of James's changed belief | C: encounter caused belief | Unexplained | Unexplained | Unexplained | Unexplained | Unexplained |

Catholic source support for existence and divine causation reuses the
materialized Greek Creed's first article through support relations. Jesus's
authority claims have separate Mark 14.61–64 and Matt 28.18 report claims.
Neither source support nor the Catholic name turns the open causal or
vindication commitments into established conclusions.

The individual and group visionary accounts are kept separate because a
shared report need not imply identical private experiences. The theft variant
requires both removal and an account of sincere experiences; removal alone
would not explain E3. The swoon variant requires survival/recovery and
encounters interpreted as resurrection. Those additional accounts are open
commitments, with no claim of medical or psychological sufficiency. Each
naturalist label is asked the existence and causation questions; each is
recorded as unexplained because no particular metaphysical supplement has
been supplied. This preserves the full shared comparison instead of winning
by subtracting the Catholic questions.

## Counts and their limits

| Bundle | Consistency witness | Entailed cells / 15 | Unexplained | Auxiliary commitments |
| --- | --- | --- | --- | --- |
| Catholic | Finite model | 15 | 0 | 1 |
| Legend | Finite model | 8 | 7 | 1 |
| Individual hallucination | Finite model | 8 | 7 | 1 |
| Group variant | Finite model | 8 | 7 | 1 |
| Stolen body | Finite model | 9 | 6 | 2 |
| Swoon | Finite model | 9 | 6 | 1 |

The six E-item cells in every row follow by accepting the findings as common
open premises. They are not six independent explanations. The remaining
available cells project the account and theological commitments expressly
posited by that bundle. Per the adopted rule, any derivation counts, so this
is conditional coverage, not an explanatory-quality ranking.

Auxiliaries count the named supplementary account commitments: the composite
Catholic encounter account, legend's elaboration, individual vision, group
suggestion, theft **plus** a separate visionary account, and survival/recovery.
Conjunctions are grouped explicitly; the numbers are not counts of logical
atoms or claims of simplicity. No aggregate or epistemic-certainty score is
computed.

The six `RESURRECTION-*-CONSISTENT` results exhibit models and bind every
bundle commitment to its statement. The models check precisely these pilot
bundles, not all Catholic dogma or all claims of a complete naturalist system.
`RESURRECTION-ANSWER-MAPS-CORRECT` checks all available cells and computes this
count table. Its coverage component is a **transcription** of commitments;
it closes no historical or case-root frontier node. The causal adequacy of
each proposed mechanism and the truth of the historical premises remain for
the premise program. The issue delivers a comparison pilot, not a proof of
resurrection or a selection of the winning worldview.

## Reproducibility

The resolved shared convention source revision is
`c104800c7aaeaea12d56f9093e71bdef6a2ce6fa`. Source verification uses the exact
revisions and blob identities in the new passage manifests. Existing chapter
selectors retain sufficient NT context, so no new verse selector or source
kind is needed. Tacitus uses TEI P4 milestone chapters and two named
punctuation entities: materialization retains the full verified text and
locally resolves only `dagger` and `mdash` to their Unicode characters. It
fetches no external DTD; arbitrary undeclared entities still fail.
