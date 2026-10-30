# Founding: mission, authorization and the scope of the Church

Research for #357, targeting `STMT-BRIDGE-CHRISTS-CHURCH-FOUNDED-BY-GOD`.
The first section below (2026-10-27) records the derivation that replaced the
bare bridge by four typed premises. The later sections are the earlier source
scan (PR #421), kept as the record of verified witnesses and rejected
shortcuts. The exact universal bridge, its Challenge types on the root routes
and the root's `Founded` semantics are unchanged.

## The case, its rivals and the decisive fork (derivation, 2026-10-27)

**End-to-end case.** Given a God with the classical attributes who can reveal
recognizably, Jesus' claim to divine authority, his resurrection, and a
visible authoritative society `c` Jesus founded:

1. *Attestation* (`STMT-RESURRECTION-CONFIRMS-JESUS-MANDATE`): by the
   resurrection God confirms that Jesus holds a mandate from him. Read from
   Acts 17.31, with added content noted in the claim (claim `NT-ACTS-17-31-RESURRECTION-AS-ASSURANCE`: God "gave
   assurance to all" of the man he appointed "by raising him").
2. *Veracity* (`STMT-GOD-CONFIRMS-ONLY-TRUTH`): what God confirms by a sign is
   true, so Jesus holds the mandate. Supported by *Dei Filius* ch. 3 para. 1.
3. *Scope* (`STMT-MANDATE-COVERS-JESUS-FOUNDING-WITH-TEACHING`): Jesus founded
   `c` in the exercise of that mandate and commissioned it to teach. Supported
   by Matthew 28.18–20 ("all authority has been given to me; go therefore ...
   teaching them").
4. *Envoy founding* (`STMT-ENVOY-FOUNDING-IS-GODS-FOUNDING`): what Jesus
   founds in a God's mandate with a teaching commission, that God founded as
   a teaching authority. It is restricted to Jesus, so other envoys' societies
   are not added to God's founding. Supported by John 13.20 (who receives the one I send
   receives me and the one who sent me).

Result `CATHOLICISM-BRIDGE-DIVINE-FOUNDING-FROM-ATTESTED-MANDATE`
(`bridge_from_attested_mandate`) proves the bridge from these four over the
typed vocabulary `TruthCore.Case.Catholicism.StageThree.DivineFounding.Agency`
(`DEF-FOUNDED-BY-GOD-THROUGH-ENVOY`). `omissionModels` shows each premise is
needed; `jointModel` shows the four premises and every stage antecedent are
jointly satisfiable. These are schema models, not possible worlds of history.

This is a decomposition, not a derivation of the bridge's universal reach over
societies: that is carried by premise 3. `HoldsMandate` has no object; unlike
the old `AuthorityVindicated` field, the vocabulary is constrained by the four
premises, and premise 3 is what gives the mandate its founding content.

**Rivals, each located at the premise it denies.**

| Rival | Denies | Status |
| --- | --- | --- |
| Jesus preached the kingdom; a church came later (no founding by Christ) | stage 5 `STMT-CHRIST-FOUNDED-VISIBLE-CHURCH`, not the bridge (the bridge is conditional on `Founded`) | belongs to #383 |
| The resurrection, if it occurred, vindicates the person or is an anomaly, not God's confirmation of Jesus' claim | 1 | open; Acts 17.31 is a source commitment, not a defence |
| God may confirm by signs what is false (or signs are not testimony) | 2 | rejected by classical theism; open as a premise |
| God ratified the message, not an institution: the mandate does not cover founding a society with teaching authority | 3 | **decisive fork**; open |
| The eleven were commissioned, but the society in the antecedent is not that commissioned body (founding by disciples, local churches) | 3 (universal scope) | open; Lumen gentium §23 particular/universal distinction applies |
| An authorized envoy's act is his own; only immediate divine institution is God's founding | 4 | `DISAMB-FOUNDED-BY-GOD`: a modelling choice (*per Filium* fits both senses; the Signature does not identify Jesus with God); the immediate-only sense makes 4 false |

**Decisive fork.** Premise 3. Premises 1 and 2 concern only Jesus'
mandate, and premise 4 only what follows once a founding is done in a
mandate; none of them separates an institutional from a purely
message-centred reading of Jesus' mission; the dividing question is
whether the attested mandate covers founding a visible society with a
teaching commission, and whether every society in the bridge's antecedent is
the commissioned one. Matthew 28.18–20 grounds the commission in the given
authority, but its universal reach over societies is not in the source.

**Premise effect.** The bare bridge leaves the frontier (reaching-root: 10
bare → 9 bare; 44 → 48 sourced-undefended). Route costs rise by 3 (cheapest
28 → 31): one bare premise is replaced by four smaller sourced ones. Nothing
is discharged.

## The scope premise split: which society, and institution or message (2026-10-27, second PR)

The scope premise `STMT-MANDATE-COVERS-JESUS-FOUNDING-WITH-TEACHING` carried
both forks of the table above. They are now separated.

**Which society.** Result `CATHOLICISM-MANDATE-SCOPE-FROM-CATHOLIC-CHURCH-FOUNDING`
(`mandate_scope_from_catholic_church_founding`, module
`TruthCore.Case.Catholicism.StageThree.FoundingScope`) derives the scope
premise from two premises: its instance at the Catholic Church,
`STMT-MANDATE-COVERS-JESUS-FOUNDING-OF-CATHOLIC-CHURCH` (if Jesus holds a
mandate from g and founded the Catholic Church as a visible society with
authority, he founded it in that mandate and commissioned it to teach), and
stage 6, `STMT-CHRISTS-CHURCH-IS-THE-CATHOLIC-CHURCH`. The step is substitution
of the stage-6 identity. The narrow premise is strictly weaker than the old one
(`scope_implies_catholic_church_scope`); `omissionModels` shows both premises
needed (a second founded society, or a Catholic Church not founded in the
mandate) and `jointModel` shows them satisfiable with every stage antecedent.
Stage 6 is already a premise of every root route, so the rival "the society in
the antecedent is not the commissioned body" (local churches, bodies founded by
disciples) is now exactly the stage-6 rival, with no extra commitment. The
Lumen gentium §23 particular/universal distinction bears on stage 6, as the
earlier section below already noted for any generic mediated-founding rule.

**Institution or message.** The narrow premise still carries this fork.
*Lumen gentium* III §§18-20, already pinned and now read in full, supports it
(claim `VATICAN-II-LG-19-CHURCH-FOUNDED-IN-APOSTLES-SENT-WITH-CHRISTS-POWER`):
the Lord founded the universal Church *in Apostolis*, sending them as he was
sent by the Father and as sharers of his power (*suae participes potestatis*)
to make disciples of all peoples, sanctify and govern them; their successors
are *doctrinae magistri*. Its reading of the Church as `catholicChurch` is
stage 6's content, and the council is a doctrinal witness, not historical
corroboration.

The rival is recorded from a pinned source: Harnack, *History of Dogma* I,
ch. II §2, II.7 (Buchanan's translation, Gutenberg 19612, passage
`HARNACK-HOD-I-II-2`): Jesus "did not found a new religious community, but
gathered round him a circle of disciples, and chose Apostles whom he commanded
to preach the Gospel". In the same section Harnack grants that Jesus knew
himself to be the Messiah called by God, so the rival accepts a mandate and
denies only its institutional content. Statement
`STMT-JESUS-MANDATE-COVERS-ONLY-MESSAGE` (`MandateCoversOnlyMessage`: no
society is founded in the exercise of the mandate) records that part; Harnack's
further denial that Jesus founded any community is the stage-5 rival and is not
attributed to this statement. `messageRival_excludes_scope` locates the
disagreement: with Jesus' mandate and the founding of the Catholic Church, the
rival and the narrow premise are incompatible. The rival is not refuted. It is
consistent with the premises other than the narrow one (it is the scope
omission model of `DivineFounding.omissionModels`), and the dispute is
historical: whether the commissions whose content goes beyond preaching
(Matthew 28.18-20 "teaching them to keep all I commanded", John 20.21-23
forgiving and retaining, and the unpinned Matthew 16.18-19, 18.17-18, John
21.15-17) go back to Jesus. Harnack's position requires treating those reports
as later, so the next obligation is a sourced report-to-event premise for them.

**Attestation.** Acts 2 is newly pinned (`NT-ACTS-2`). Claim
`NT-ACTS-2-22-36-RESURRECTION-MAKES-KNOWN-LORD-AND-CHRIST` supports
`STMT-RESURRECTION-CONFIRMS-JESUS-MANDATE` more closely than Acts 17.31: God
attested Jesus by signs and raised him, so that all Israel may know assuredly
(*asphalōs*) that God made him Lord and Christ. Its limit: the office is said
to be conferred with the exaltation, so the verse does not date the mandate to
Jesus' ministry.

**Rejected alternatives.** (i) Deriving the scope premise from Matthew 28
alone: the commission names the eleven, not a society. (ii) A new
commissioned-body constant plus an identity premise "every society Jesus
founded is the commissioned body": it would duplicate stage 6 as a new open
premise. (iii) *Dei Filius* ch. 3 para. 5 as a premise: it asserts the root
component itself.

**Premise effect.** Reaching the root, `STMT-MANDATE-COVERS-JESUS-FOUNDING-WITH-TEACHING`
leaves the open frontier and the strictly weaker
`STMT-MANDATE-COVERS-JESUS-FOUNDING-OF-CATHOLIC-CHURCH` takes its place (57
open premises, 9 bare, 48 sourced-undefended, unchanged); stage 6 was already
on every route. Per-route costs are unchanged (cheapest 31). Nothing is
discharged.

## Institution or message: the reported commissions (2026-10-27, third PR)

The narrow premise `STMT-MANDATE-COVERS-JESUS-FOUNDING-OF-CATHOLIC-CHURCH` is
now derived (result `CATHOLICISM-NARROW-SCOPE-FROM-COMMISSION-REPORTS`,
`narrow_scope_from_commissions`, module
`TruthCore.Case.Catholicism.StageThree.Commissions`) from two premises:

1. *Report-to-event* (`STMT-COMMISSION-REPORTS-GO-BACK-TO-JESUS`): the
   commission of Matthew 28.18-20 goes back to Jesus, and so does at least one
   of the four commissions with governing content, Matthew 16.18-19, 18.17-18,
   John 20.21-23 and 21.15-17. Supported by *Dei Verbum* §19 (newly pinned,
   `VATICAN-II-DEI-VERBUM-V`): the four Gospels faithfully hand on what Jesus
   *reapse fecit et docuit*. The council asserts more (all four Gospels); the
   premise needs only two of the five commissions.
2. *Founding in the commissioned apostles*
   (`STMT-CHURCH-FOUNDED-IN-COMMISSIONED-APOSTLES`): if Jesus holds a mandate
   from `g` and founded the Catholic Church, his giving a governing power makes
   that founding one in the mandate, and his giving the power to teach is a
   commission of that Church to teach. Supported by *Lumen gentium* §19 (the
   Church founded *in Apostolis*, sent *ut suae participes potestatis*; citing
   Matthew 28, John 20, 21, Matthew 16.18) and §22 (Peter as rock and
   key-bearer and pastor of the whole flock; binding and loosing given to the
   college, Matthew 18.18). The council asserts one conferral of all these
   powers on the twelve under Peter; that a single governing power or a
   promise suffices, for any recipient disciple and any mandator, is open
   content of the premise, not attributed to it.

What each report says is the sourced definition `CommissionReport.powers`
(`DEF-COMMISSION-REPORT-POWERS`, from five report claims); which powers are
governing is the stipulation `Power.Governing`
(`DEF-COMMISSION-EVENT-AND-GOVERNING-POWER`): keys, binding and loosing, the
church's judging, forgiving and retaining, shepherding. Preaching, making
disciples, baptizing and teaching are not governing, so the rival's concession
of a teaching commission does not already count as an institution.

**What the derivation shows.** It depends on content: it goes through because
the reports name a governing power and the power to teach. In a preaching-only
model (the commission Harnack names; that he denies every other power is not
attributed to him), premise 2 holds and premise 1 fails
(`preachingOnly_fails_reports`; this rests on the stipulated distinction of
teaching from preaching); without premise 2, every commission may be
historical and the narrow premise still fail (`omissionModels`). Premise 2 is
strictly weaker than the narrow premise (`narrow_implies_link`, strict by the
first omission model), but it carries the institutional content. The fork is
therefore split between the two premises, not moved onto premise 1: a rival
may deny premise 2 (the second omission model satisfies the message rival with
every commission historical), or, granting premise 2, Jesus' mandate and his
founding of the Catholic Church as a visible society with authority, must deny
**each** of the four governing commissions
(`messageRival_denies_governing_reports`); it may keep Matthew 28.18-20
(`messageRival_compatible_with_mt28`). Premise 2 has the conclusion's two parts
as consequents and the case analysis only supplies its antecedents, so the
result is recorded as a transcription (invariant 16, `single_application`;
Codex review on #581): it closes nothing and derives no institutional
content.

**Findings from the text** (Matthew 16, 18, 28 and John 20, 21 read in full):

| Report | Powers | Recipient | Limit |
| --- | --- | --- | --- |
| Matthew 16.18-19 | keys; binding and loosing | Peter | a promise (*oikodomēsō*, *dōsō*), not a narrated conferral; authenticity is the classic dispute |
| Matthew 18.17-18 | the *ekklēsia* judges and excludes; binding and loosing | "the disciples" (18.1), plural | *ekklēsia* may be the local assembly |
| Matthew 28.18-20 | make disciples, baptize, teach | the eleven | the only report that names teaching |
| John 20.21-23 | forgive and retain sins | the disciples present; Thomas absent (20.24) | sending grounded in the Father's sending |
| John 21.15-17 | shepherd Jesus' lambs and sheep | Peter | the flock is not identified with a society; 21.24 is the Gospel's own claim to true testimony |

Matthew 16.18 and 18.17 are the only Gospel uses of *ekklēsia*. Only Matthew
28.18 and John 20.21 ground the commission in Jesus' own received authority or
sending; that the others were also given in the mandate stays inside premise 2,
since no recorded rival separates it (decomposition gate).

**Rejected.** (i) A premise that all five commissions go back to Jesus: stronger
than needed. (ii) Teaching or baptizing as governing: it would beg the question
against the rival. (iii) A separate "given in the mandate" premise: no rival
separates it. (iv) Report statements as premises: their content is the sourced
definition, and only the report-to-event step is a premise.

**Open** (at #581; see the fourth-PR section for the pinned denial). Neither side's historical argument was pinned. The pinned Harnack
section does not discuss the governing sayings, so no source yet stated their
historical denial; *Dei Verbum*'s own redaction clause (*statui ecclesiarum
attendendo explanantes*) is where such readings place Matthew 16.18-19 and
18.17-18. Next: pin a critical denial (for example on Matthew 16.18) and a
historical argument for one governing commission (the double attestation of
binding and loosing and forgiving, Matthew 16.19, 18.18 and John 20.23; Paul on
Cephas, Galatians 1.18 and 2.9).

**Premise effect.** Because the result is a transcription with open premises,
the narrow premise stays on the open frontier ("open although proved"), and the
two new premises are listed beside it (on main at merge: 61 → 63 open premises;
12 bare unchanged, 49 → 51 sourced-undefended). Per-route costs are unchanged
(cheapest 31). Nothing is discharged.

## Institution or message: multiple attestation against the critical denial (2026-10-27, fourth PR)

Module `TruthCore.Case.Catholicism.StageThree.CommissionAttestation`, result
`CATHOLICISM-MESSAGE-RIVAL-EXCLUDED-BY-ATTESTATION`
(`message_rival_excluded_by_attestation`). It tests the message rival, once it
grants the link premise, against the strongest historical argument for a
governing commission and against a pinned critical denial.

**The pinned denial.** Harnack, *History of Dogma* I, ch. II §3, note 76
(`HARNACK-HOD-I-II-3-FN-76`, same Gutenberg snapshot as §2): "The words of the
Lord, Matt. XVI. 18; XVIII. 17, belong to a later period." Claim
`HARNACK-HOD-I-II-3-N76-CHURCH-SAYINGS-LATER` reads it at the event level for
18.17 (`STMT-MATT-18-17-JUDGING-SAYING-LATER`: Jesus did not give the
*ekklēsia* its judging power), because Harnack's §2 denies that Jesus founded a
community; a wording-only reading was rejected for that reason. The note gives
no argument and names only the two *ekklēsia* sayings. Matthew 16.18 names no
power given to a disciple and bears on stage 5, not here. In Lean the denial
refutes only that Matthew 18.17-18 goes back to Jesus
(`judgingSayingLater_refutes_mt18`); it is compatible with
`STMT-COMMISSION-REPORTS-GO-BACK-TO-JESUS` and with both attestation premises
below (`judgingSayingLater_compatible`). **Matthew 16.19, 18.18, John 20.23
and 21.15-17 are untouched by any pinned denial.**

**The attested family.** Matthew 16.19 and 18.18 (binding and loosing) and John
20.23 (forgiving and retaining) share one form: the disciples' act on earth is
ratified before God (`HeavenRatified`, `DEF-HEAVEN-RATIFIED-POWER`; a stipulated
grouping, since John 20.23 has no "in heaven" and the divine-passive reading is
the definition's). The family, not one saying, is reported in both the
Matthean and the Johannine strand (`heavenRatified_in_both_strands`;
`DISAMB-ATTESTATION-OF-POWER-AND-FAMILY`), and every power in it is governing.

**The argument.** From the link premise, `STMT-JOHN-COMMISSION-INDEPENDENT-OF-MATTHEW`
(John 20.21-23's saying is literarily independent of Matthew 18.17-18's or
16.18-19's) and `STMT-HEAVEN-RATIFIED-ATTESTATION-CRITERION` (two distinct,
independent reports of the family ⇒ Jesus gave or promised some power of it), it follows that wherever
Jesus holds a mandate and founded the Catholic Church as a visible society with
authority, the message rival is false. It is not a transcription: the proof
meets each premise's antecedent only through the reported content and the
stipulated classifications; that checked content is thin, and the two
attestation premises are tailored to this family. `omissionModels` shows each premise needed; `jointModel` shows
them jointly satisfiable with stage 6 and every stage antecedent.

**The fork, sharpened.** A message rival that grants the link premise, Jesus'
mandate and his founding of the Catholic Church must now deny one of:

1. John's independence for this saying, from both Matthew 18.17-18 and
   16.18-19 (John 20.23 derives from Matthew's saying or shares a written
   source with it); or
2. the criterion for this family (both strands share the early community's
   practice of binding and forgiving, or an oral tradition formed by it, not a
   gift of Jesus). Note that John
   20.23 is set after the resurrection: a gift by the risen Jesus counts as
   Jesus' giving (`DISAMB-COMMISSION-REPORT-AND-EVENT`); "post-Easter" in the
   critical sense means formed by the community.

Otherwise it denies the link premise, the mandate or the founding (stage 5,
Harnack's own route in §2). Harnack's note 76 supports none of these denials
beyond the Matthew 18 commission.

**What it does not do.** The two attestation premises yield only *some*
heaven-ratified power, not a whole governing report, so they do not give
`STMT-COMMISSION-REPORTS-GO-BACK-TO-JESUS` (`attestation_not_reports`). With
Matthew 28's report-to-event content they would give the narrow premise
(`narrow_from_attestation`), but that route is not recorded as an argument: it
would replace one sourced premise with two unsourced ones.

**Paul on Cephas** (`NT-GAL-2`, claim `NT-GAL-2-7-9-CEPHAS-PILLAR`; 1.18 in
`NT-GAL-1`). Within Paul's lifetime Cephas is one of three reputed pillars and
holds an apostolate to the circumcised. This is a datum both sides explain: by
a commission (Matthew 16.18-19, John 21.15-17), or by the first appearance
(1 Corinthians 15.5) and his role among the disciples. It does not discriminate
and is not a premise; Paul names James first and opposes Cephas at Antioch.

**Open.** Pinnable sources for the criterion and for John's independence (or
dependence) were not found: archive.org was unreachable and the standard
modern treatments are copyrighted and were not read
(`ATTEMPT-GOVERNING-COMMISSION-ATTESTATION`).

**Premise effect.** No change. The conclusion is used by no argument reaching
the root, so `frontier --reaching-root` and `--routes` are unchanged.

## Verified witnesses and findings

The complete ranges below were materialized and read, not inferred from the
citations in another work. The Latin conciliar witnesses are doctrinal
assertions; the Gospel witnesses are textual reports. Neither status by itself
establishes an occurrence or the truth of a theological commitment.

| Witness | Precise locator | Finding relevant to the bridge | Limit |
| --- | --- | --- | --- |
| `VATICAN-I-DEI-FILIUS-CH3` | paragraph 2, external signs and the following examples | Miracles and prophecies are asserted to be certain signs of revelation; Christ and apostolic preaching are among the examples. | This paragraph does not identify the resurrection as God's ratification of each institutional act or supply a rule for transmitting a teaching mandate. |
| `VATICAN-I-DEI-FILIUS-CH3` | paragraph 5, institution through the Son and recognition as teacher | The council expressly asserts God's institution of the Church through the Son and its recognizability as custodian and teacher. | Reusing this assertion as a premise for deriving that same root component would not independently establish the component. Existing claim `VATICAN-I-DEI-FILIUS-CH3-CHURCH-GOD-FOUNDED-TEACHER` already records it. |
| `NT-MATT-28` | 28.16–20, especially 18–20 | Jesus is reported to claim received universal authority and to commission the eleven to disciple all nations, baptize, and teach observance of everything he commanded. | The authority speech is a report, not an established grant; the commission does not name every society satisfying the root's predicates. The narrative's resurrection setting does not by itself encode a ratification-to-institution inference. |
| `NT-JOHN-20` | 20.19–23, especially 21 | In the reported encounter, Jesus connects the Father's sending of him with his own sending of the gathered disciples. The gift of the Spirit and the forgiveness/retention commission follow. | This is a specific sending comparison, not a general transitivity theorem about authorization, nor a universal rule identifying every founded society. The disciples gathered here are not silently identified with every later office-holder; 20.24 explicitly notes Thomas's absence. |
| `VATICAN-II-LUMEN-GENTIUM-I` | §3, opening three sentences; §5, both paragraphs | The Son is sent by the Father and inaugurates the kingdom to fulfil the Father's will. The post-resurrection Church receives a mission to announce and establish Christ's and God's kingdom among all nations. | Mission content is richer than a bare authority label, but these assertions do not derive the generic founding bridge from its existing antecedents. |
| `VATICAN-II-LUMEN-GENTIUM-I` | §8, first two paragraphs | The source describes the one complex Church, its visible constitution and its entrustment to Peter and the other apostles. | Its singular/unique Church language is not a statement that every possible visible authoritative society is numerically that Church. |
| `VATICAN-II-LUMEN-GENTIUM-III` | §18, second paragraph; §19; §20, first paragraph | The council explicitly connects Christ's building of the Church to sending the apostles as the Father sent him, their sharing in his authority, and a continuing divine mission. | This is a substantive conciliar account of mediated mission. It is not independent historical corroboration or an unrestricted agency-composition law. |
| `NT-MATT-16`, `NT-MATT-18`, `NT-JOHN-21` | Matthew 16.18-19; 18.17-18; John 21.15-17 (chapters read in full) | The governing commissions: keys and binding to Peter (promised), the church's judging and binding to the disciples, shepherding to Peter. | Textual reports; recipients differ; Matthew 16 is a promise. |
| `VATICAN-II-DEI-VERBUM-V` | §19, first sentence; §§18-19 | The Gospels faithfully hand on what Jesus really did and taught; the evangelists selected, synthesised and explained, always communicating what is true of Jesus. | A doctrinal assertion about the Church's own texts, not historical corroboration; its redaction clause leaves the critical dispute open. |
| `VATICAN-II-LUMEN-GENTIUM-III` | §§23, 26–28; compare §§21, 24–25 | The text distinguishes particular Churches from the universal Church, describes apostolic/successor establishment and limited pastoral jurisdictions, and specifies teaching, sanctifying and governing ministries. | These are not interchangeable numerical society identities or unrestricted delegations. The conditions on communion, office and mission must survive any typed refinement. |

The new chapter-III passage reuses the existing Latin snapshot, including its
byte hash, with a new selector and text hash. The complete chapter (§§18–29)
was read so that the sending passages are not isolated from the later
jurisdiction, teaching and communion conditions. No chapter-III wording is
copied into the repository beyond the short witness incipit.

## Existing semantics and the proposed agency shortcut

`DEF-CHURCH-VISIBLE-AUTHORITATIVE-SOCIETY` already selects the community of
§8 for the stage-5 reading. Its note expressly does **not** interpret every
possible society in `Signature`. `DEF-SKELETON-OPEN-PREDICATES` likewise
records the intended Church reading without making the historical predicates
true. Thus the new reading is not a counterexample to the root's intended
Church or a finding that existing source claims are contradictory.

The separate issue is a proposed **generic** mediated-founding rule. If such
a rule enlarged `Founded jesus c` to include every local body established by
an apostle or successor, it would need to be reconciled with
`STMT-CHRISTS-CHURCH-IS-THE-CATHOLIC-CHURCH`, whose Lean type concludes
`c = catholicChurch` for every society in its antecedent. Chapter III's
particular/universal distinction is not that numerical equality. The source
must not be made to assert equality merely because the same word *Church*
is used. A future rule may instead preserve the intended universal-body
scope, but that restriction and its source justification must be explicit.
(PR #421:) This section made no change to either predicate or statement; the 2026-10-27 section and `DISAMB-FOUNDED-BY-GOD` now fix the envoy reading of `FoundedAsTeachingAuthority`.

## Rejected shortcuts and the next obligation

- The existing pilot `AuthorityVindicated` field does not encode a sending,
  institutional mandate or scope of authority. Renaming it authorization adds
  none of these constraints.
- A report of a commission is not an actual commission without an explicit
  historical reading premise. Conciliar repetition of that account also does
  not establish the historical premise by formal logic.
- Two sending relations do not compose into every kind of authorized act
  merely because both are called sending. The object of the mandate and the
  permission to entrust it onward need content.
- A divine mission, a teaching ministry, and founding a society as a teaching
  authority are related source notions, not definitions of each other.
- The direct God-founded-Church assertion in *Dei Filius* cannot serve as an
  independent derivation of that same assertion. Nor does starting with the
  already-complete stage-6 identity establish how divine founding follows.

The next formal obligation is a source-faithful account of the **particular
mission and its permitted mediation**, keeping its recipient/body and its
teaching scope explicit. The verified John 20.21 and *Lumen gentium*
§§18–21, 24 and 28 give concrete starting passages. Before transporting its
consequence into the existing bridge, a worker must also justify the map
from each society in that bridge's antecedent to the commissioned universal
body, without silently adding local Churches to or removing them from the
existing `Founded` relation. Genuine divine attestation of this mission
remains a separate obligation; recognizable-revelation capacity alone is
not that attestation.

`TruthCore.Results.Case.Catholicism.FoundingIndependence.independent` already
verifies non-entailment from the declared local pilot inputs. No new finite
model is supplied here to repeat it, and that theorem is not a refutation of
Christian history or of the full root theory. (PR #421:) The advance of that batch was verified
source context and a more precise constraint on a proposed inference; there
is no newly advertised mechanically verified consequence or frontier closure.

Resolved convention source revision:
`c104800c7aaeaea12d56f9093e71bdef6a2ce6fa`.
