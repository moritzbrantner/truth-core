# Mark 14: answer to the high priest

This bounded reading for #381 refines the pilot's existing Mark 14 report.
It does not add independent attestation or establish a historical claim.
Issue #381 remains open for historical defense, rival comparison and the
remaining texts. The binding whole-system comparison guidance in
[catholic-case.md](catholic-case.md) excludes certainty numbers and hidden
trilemma assumptions.

## Verified witness and context

The existing `NT-MARK-14` and `NT-MARK-15` witnesses were materialized and
read in full. Their Westcott–Hort Greek text is pinned to canonical-greekLit
revision `0189b9c8d8d1f148133f2f0af309b4ee90ea4332`, blob
`2664594193aa224378e58ab565b493b1c0bdbcb3`, edition
`urn:cts:greekLit:tlg0031.tlg002.perseus-grc2`. The pin fixes consulted bytes,
not authorship, date, eyewitness access or the exact underlying print edition;
the existing pilot note retains the edition-header uncertainty.

Mark 14 moves from the plot and betrayal through the meal, prayer and arrest
to the hearing and Peter's denial. At 14.55–59 the narrator labels the
witnesses false and reports their disagreement; their temple saying is not
silently promoted to Jesus's own admission. Jesus initially remains silent
(14.60–61). The high priest then asks whether he is the Messiah, the Son of
the Blessed; Jesus answers affirmatively and adds the future seeing saying
(14.61–62). The high priest tears his clothing and charges blasphemy; the
assembled group condemns Jesus as deserving death (14.63–64). The narrative
continues with abuse, denial, transfer to Pilate and the king-of-the-Jews
question (15.1–5). These scenes distinguish narrator judgments, quoted
speeches and character reactions. Their juxtaposition is not independent
hostile corroboration of the hearing.

## Prose beside the types

The local `HighPriestAnswer.Narrative` retains the Mark 2 `Narrative`, hence
the existing pilot `State.core`. Its additional speech relation has the same
textual-attribution boundary. It does not modify the case signature.

| Statement | Exact proposition body for `n : Narrative` | Reading |
| --- | --- | --- |
| `STMT-REPORTED-MARK-AFFIRMATIVE-ANSWER` | `n.attributes .jesus (.affirmsSelfAs .messiah) = true ∧ n.attributes .jesus (.affirmsSelfAs .sonOfBlessed) = true` | The answer accepts both titles in the immediately preceding question. |
| `STMT-REPORTED-MARK-SON-OF-MAN-PREDICTION` | `n.attributes .jesus (.predictsHearersWillSee .sonOfMan .seatedAtRightOfPower) = true ∧ n.attributes .jesus (.predictsHearersWillSee .sonOfMan .comingWithHeavensClouds) = true` | Jesus is reported predicting future seeing by the addressed hearers, retaining both images. |
| `STMT-REPORTED-MARK-BLASPHEMY-REACTION` | `n.attributes .highPriest .chargesPrecedingSpeechAsBlasphemy = true` | The high priest charges blasphemy; the proposition does not endorse his judgment. |

These declarations express content for attribution; none asserts that its
content occurred or is true. The affirmative answer is tied to the question,
not encoded as an isolated divine-name formula. Son of the Blessed is kept
as its filial title rather than converted to consubstantiality. The Son of
Man token reuses Mark 2's spoken title without a referential equation with
Jesus, God, or the holder intended in the other passage. The prediction
retains futurity and its addressed audience without specifying a date,
actual fulfillment, a mode of seeing, or the referent of Power as a formal
equality. Its imagery supports an exaltation reading; the verse does not
explicitly predicate judging, so judgment remains interpretation rather
than a new sourced assertion hidden in the type.

## Distinct affirmative accounts

A stronger divine-prerogative reading takes the affirmative answer, exalted
right-hand position, heavenly coming and blasphemy reaction together as a
narrative portrayal of Jesus occupying an exceptional divine role. A judicial
reversal reading can understand the condemned speaker as announcing future
vindication before his judges. To infer identity with God or an explicit
universal judgeship requires an account of the imagery and title references
beyond the bare wording; the hostile charge does not establish that account.
This preserves the strongest affirmative theological reading as a research
commitment without attributing its entire conclusion to this sentence.

A delegated messianic/apocalyptic account affirmatively explains the same
sequence as the earthly rejection of God's anointed son followed by God's
exaltation and vindication of him. The right-hand distinction permits a
commissioned agent interpretation, while heavenly coming gives that agent
an exceptional eschatological role. The high priest can regard the claim as
presumptuous or offensive without interpreting it as numerical identity with
God. This account does not reduce the speech to an ordinary ethical teacher
or mere announcement of another's status. Delegation itself is not explicitly
stated in 14.62; it too needs interpretive defense. No rival is refuted by
its compatibility with this narrow textual report.

A narrative-development account explains the exchange as the author's
presentation of Jesus's status and vindication in the passion story. It can
accept all three textual attributions while withholding historical speech,
the reaction's occurrence and the predicted event. Establishing development,
its dating or its mechanism requires transmission and source evidence beyond
this witness; the account is a substantive possibility to investigate, not
a sourced attribution to a modern scholar or a complete rival worldview.

These accounts are preserved separately here rather than multiplying claims
that falsely attribute each larger interpretation to the same wording.
Intertextual arguments concerning the right hand and clouds need their own
materialized witnesses and explicit interpretive steps; no unread parallel
is used as a premise here. An eventual whole-system comparison must ask each
account the pilot's shared questions, including its positive replacement
account, rather than count denial as explanation.

Rejected shortcuts: reported speech is not a historical utterance; neither
claimed authority nor hostile condemnation establishes actual authority;
Messiah, divine sonship, exaltation, delegated judgment and divine identity
are not synonymous. A mad/bad/God inference additionally assumes that the
report is historically reliable, self-referential in the required sense,
and excludes sincere delegated agency and narrative development. Those
premises are neither supplied nor smuggled into this reading.

## Reuse and remaining obligations

The existing `MarkAuthority` declaration and
`STMT-PILOT-REPORT-MARK-AUTHORITY` remain intact. The new statements refine
its speech contents without equating distinct statement identities. The new
`supports` relation to `STMT-PILOT-JESUS-CLAIMS` is evidential only and is not
an inference application or independent witness. Transport still requires
historical attribution of the utterance, the relevant title reference and
classification of this particular saying as the signature's divine-authority
claim. Actual divine authority and vindication are further questions. This
chapter alone supplies no multiple independent attestation or absolute early
dating; embarrassment is an assessment requiring defended premises.

The existing theorem
`TruthCore.Results.Bridges.StageFourFromResurrectionPilot.jesusClaimedDivineAuthorityAndRoseOfPilot`
continues to combine the existing open pilot cells. No conclusion is restated
as a new premise. No argument, result or transcription is added here.
Intended root-route change: none. All existing historical/interpretive open
premises remain open. The dossiers for the broad report, pilot claim and
stage-four conjunction were inspected; the attempt record preserves this
successful source reading without asserting closure.

Shared conventions source revision:
`c104800c7aaeaea12d56f9093e71bdef6a2ce6fa`.
