# Mark 2: forgiveness authority

This bounded first reading for #381 records one source attribution, not an
argument establishing a historical event. #381 remains open for Mark 14,
Matthew 11, John 8 and 10, Philippians 2, 1 Corinthians 8, historical attribution
and the comparison of rival accounts. Binding whole-worldview guidance in
`catholic-case.md` governs this work; the issue's older probabilistic wording
does not introduce certainty numbers or Bayesian machinery.

## Witness and contextual reading

`NT-MARK-2` materializes the entire second chapter from the existing pinned
Westcott–Hort Greek witness: canonical-greekLit revision
`0189b9c8d8d1f148133f2f0af309b4ee90ea4332`, blob
`2664594193aa224378e58ab565b493b1c0bdbcb3`, edition
`urn:cts:greekLit:tlg0031.tlg002.perseus-grc2`. The complete chapter was read,
including the subsequent meal with sinners, fasting and Sabbath disputes.
The digital witness does not resolve the underlying print edition more
precisely than the existing pilot note. No book title supplies authorship or
a composition date.

Within 2.1–12, Jesus pronounces the paralytic's sins forgiven (2.5). The
passive formulation alone does not name the agent of pardon. Some scribes
inwardly object with a blasphemy charge and a God-alone question (2.6–7).
Jesus responds to their reasoning, contrasts two sayings (2.8–9), and frames
the command to rise as enabling knowledge of the Son of Man's authority to
forgive sins on earth (2.10–11). The narrator reports the man's rising and
the crowd's amazement and glorification of God (2.12).

The one formalized claim, `NT-MARK-2-FORGIVENESS-AUTHORITY`, binds the
assertion in 2.10. Its Lean type is
`ReportedForgivenessAuthority (n : Narrative) :=
n.attributes .jesus ⟨.sonOfMan, .forgiveSins, .onEarth⟩ = true`.
It records speaker, titled holder, action and earthly scope, retaining the
narrative attribution without asserting its content as history. The title's
referent is not an equality in this type. The surrounding healing supplies
the narrative's proposed demonstration; this batch does not establish that
a healing occurred or that it verifies an actual pardon.

## Interpretive alternatives and rejected shortcuts

The following are affirmative accounts to investigate, not sourced claims
attributed to modern scholars or fully developed rival worldviews:

- A divine-prerogative reading takes Jesus's pronouncement, response to the
  objection and demonstrative action together as a narrative portrayal of
  exercising God's forgiving prerogative. Its strongest account explains why
  a blasphemy objection and a demonstration of authority are paired. Going on
  to divine identity needs an account of why delegated authority cannot
  explain the same scene; the objection itself supplies no such proof.
- A delegated-agent reading takes the Son of Man as authorized by God to
  forgive on earth, with the narrated healing confirming that commission.
  It affirmatively explains the authority claim and glorification of God
  without reducing the assertion to merely announcing a pardon. The passage
  does not explicitly say the authority was delegated, so that origin is an
  additional interpretation rather than the bound textual assertion.
- A narrative-development account takes the scene as an author's theological
  presentation of forgiveness through Jesus, with the controversy and
  healing expressing that message. It accounts for the text's existence
  without accepting a historical utterance or miracle. Actual development,
  dating and transmission require evidence beyond this chapter; naming this
  account neither establishes nor refutes it.

All three can accept the narrow textual attribution while disagreeing about
its implication or origin. They are therefore preserved as distinct possible
explanations in this linked note, rather than made into competing claims
that the chapter itself explicitly asserts them. No alternative is refuted.
A title taken generically or as referring beyond Jesus would also require
an account of how the speech and immediate demonstrative action relate;
no identity is forced by the encoding.

Rejected shortcuts: the scribes' God-alone objection is not silently promoted
to an unqualified narrator assertion; claimed authority is not actual
possession; authority to forgive is not identity with God; narrated healing
is not an independently established event; the title Son of Man is not a
formal identity equation; earthly authority is not silently expanded to all
heaven and earth. A mad/bad/God trilemma excludes neither sincere delegated
agency nor narrative development, and is not used.

## Reuse and premise comparison

The local typed report extends the existing resurrection `State` through
`Narrative.pilot`; no shared signature or existing report constructor changes.
There is an evidential `supports` relation to `STMT-PILOT-JESUS-CLAIMS`, with
no inference application. Any future transport needs explicit premises for
historical utterance, the title's referent and classification of this
particular forgiveness claim as divine authority. Historical attribution
needs its own transmission/source assessment; multiple attestation, early
dating or embarrassment are not manufactured from this one witness.

The existing composition theorem
`TruthCore.Results.Bridges.StageFourFromResurrectionPilot.jesusClaimedDivineAuthorityAndRoseOfPilot`
remains the route from the existing pilot claim and resurrection predicates
to `STMT-JESUS-CLAIMED-DIVINE-AUTHORITY-AND-ROSE`. It is neither restated as a
premise nor reproved here. The resurrection conjunct is untouched. This is
source-reading work with no new result, transcription or discharge. Intended
and actual root-path premise change: none; all existing historical and
interpretive open premises remain open, and no route gains or loses a leaf.

Shared conventions resolved at source revision
`c104800c7aaeaea12d56f9093e71bdef6a2ce6fa`.
