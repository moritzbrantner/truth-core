# Proclus: received unity and the One (#359)

## Witness and scope

Before formalization, the complete range `PROCLUS-ET-1-13-TAYLOR` was
materialized with `python3 scripts/source_evidence.py materialize
PROCLUS-ET-1-13-TAYLOR` and read, including the opening of proposition 14.
The witness is Thomas Taylor's 1816 English translation, vol. II, printed
pp. 300–310, physical PDF pages 806–816. Its exact bytes and text extraction
are pinned in `corpus/passages/proclus-elements-theology-taylor.json`.
The proposition-2 wording was also checked against the image of printed
p. 301 (physical PDF page 807), rather than relying on OCR alone.
This is a translation reading, not a verified reading of the Greek original.
The work identifier is local, not an invented CTS identity. Intake is #460;
this investigation reuses its identical witness records.

This small batch records one substantive reading of proposition 2, not a
completed defense of either proposition 1 or proposition 2. The candidate
for propositions 1–13 must remain queued. The first unresolved work remains
proposition 1; proposition 2 also needs independent premises. No additional
per-proposition candidate or schema instance is registered.

## Source-order findings

**Proposition 1, pp. 300–301.** The conclusion says every multitude participates
in unity in some respect. The reductio denies unity of both the whole and each
constituent, repeats the decomposition without limit, and rejects an actual
infinite composed of infinites. It also rejects composition out of nothing.
The distinction between actual and potential infinity occurs in Taylor's
brackets and is not silently promoted to verified Greek wording.

A modern cardinality proof is rejected. The text's comparison of a whole with
its parts is not simply strict inequality of infinite cardinalities: an
infinite set can be equinumerous with a proper subset. Neither declaring a
multitude finite nor replacing its composition by a finite set would recover
the unrestricted source conclusion. An `Acc` or well-founded parthood premise
would likewise be an additional reconstruction until its relation and strength
are defended. The exact unmet work is to specify whole/constituent composition,
what counts as being one, why absence of participation removes unity from both
whole and constituents, and why the resulting actual infinitely iterated
composition is impossible. No such independent premises or proof are supplied
here. Nothing in this batch proves that every composite has a uniting cause.

**Proposition 2, p. 301.** Taylor distinguishes receiving unity through
participation from being the One itself. The text argues that a participant
is something besides the One; something that is nothing besides it would be
the One itself rather than its participant. Its closing contrast assigns
non-one to the excess and one to the reception. The bounded claim
`PROCLUS-ET-2-PARTICIPANT-UNITY-CONTRAST` records received unity and numerical
nonidentity. It does not claim that identity/nonidentity exhausts the stronger
language about being non-one of itself. The two senses are linked through
`DISAMB-PROCLUS-ONE`.

**Propositions 3–6, pp. 301–304.** The context continues to distinguish becoming
one, participation, the united and the One. Proposition 3 adds a transition
and conjunction/communication account; proposition 4 reuses proposition 2 and
rejects a regress; proposition 5 argues priority of the One over multitude;
proposition 6 distinguishes united things from unities. These further steps
have not been extracted as claims in this batch. Taylor flags supplied
conclusions in propositions 3 and 4 as missing in his original. They are not
used as independent unmarked premises here. In particular becoming-one is not
identified with timeless predication, and priority is not identified with
temporal precedence.

**Propositions 7–13, pp. 304–310.** The productive-cause superiority argument
precedes the Good/self-sufficiency discussion and the first-cause argument.
Proposition 11 appeals to causal ordering, the rejection of cycles and an
infinite ascent, and scientific knowledge; its uniqueness step appeals back
to the priority of unity. Proposition 13 connects the Good with preservation,
connection and unity. Reading this context does not establish any of those
premises or identify the One with the Thomistic first being. They remain
future contiguous-range work, including the root-target comparisons in #359.

## What the Lean declaration says

`TruthCore.Greek.Proclus.ElementsTheology.ParticipantUnityContrast` is:

```lean
∀ x, s.Participates x one → s.Exemplifies x unity ∧ x ≠ one
```

The `one` entity and `unity` quality are distinct parameters. Entities occupy
one common domain, so participant nonidentity is not obtained by giving the
One and its participants disjoint types. The existing `Forms.Vocabulary`
provides only the entity and relation/predication interface. Its bearer-to-Form
participation gloss is not used for the One: `DEF-PROCLUS-UNITY-PARTICIPATION`
and `DISAMB-PROCLUS-UNITY-PARTICIPATION` explicitly record that distinction. Its
`Nonidentity`, `FormOf`, `OneOverMany`, explanatory and causal commitments are
not imported as hypotheses or asserted for Proclus. Reusing an interface is
not a historical identification of the One with a Platonic Form.

This is a proposition declaration and an attributed source reading. There is
no Challenge/Solution pair, result or verification claim for this proposition.
The conjunction is not a proof of the source argument. Asserting the same
nonidentity as a premise and projecting it would only transcribe the argument.

## Rejected stronger reconstruction and remaining burden

One considered reconstruction assigned each participant an essential quality
other than unity and restricted every essential quality of the One to unity.
An assumed identity would then transport the distinguishing quality to the
One and contradict that restriction. This formal consequence would be easy,
but Taylor's something-besides language does not establish that inventory of
essential determinations. In particular it does not quantify over every
essential quality of the One. That strengthening is rejected as a source
attribution; no statement, claim or theorem asserting it was added. Omission
models of those invented premises would test only an analyst's adapter and
would not defend Proclus's argument.

A deeper defense must state an independently motivated account of the
participant's excess or otherness and of received unity, then show why it
excludes being the One without building that very nonidentity into a renamed
premise. It must also retain the of-itself/through-participation distinction
more fully if that distinction becomes load-bearing. The present identity
projection is deliberately narrower. Further investigation stays in the
existing propositions-1–13 source-range candidate, with these gaps recorded
in the linked attempt and this note; the campaign is not exhausted.

## Premise comparison and reproducibility

Intended and actual root-premise change: **none**. No root result is connected,
no open premise is discharged, and no bare root premise is relocated to a new
one. The new Proclus statement is an open attributed commitment outside the
current root routes. In particular this batch discharges none of the composition,
producer-superiority or causal-regress obligations of #359; it is source clarification,
not progress measured by frontier closure.

At baseline `bf106c2f`, route costs were:

| Root argument | Before | After this batch |
| --- | ---: | ---: |
| CATHOLICISM-SKELETON | 28 | 28 |
| CATHOLICISM-FROM-QUARTA-VIA-WITH-CLASSICAL-ATTRIBUTES | 29 | 29 |
| CATHOLICISM-FROM-PRIMA-VIA | 33 | 33 |
| CATHOLICISM-FROM-PRIMA-VIA-VIA-FULL-DESCRIPTION | 35 | 35 |
| CATHOLICISM-FROM-PRIMA-VIA-VIA-MAXIME-ENS | 36 | 36 |
| CATHOLICISM-FROM-PRIMA-VIA-WITH-CLASSICAL-ATTRIBUTES | 36 | 36 |
| CATHOLICISM-FROM-EFFICIENT-REGRESS-WITH-CLASSICAL-ATTRIBUTES | 37 | 37 |
| CATHOLICISM-FROM-PRIMA-VIA-WITH-Q11-UNIQUENESS | 38 | 38 |

The complete root-route sets are unchanged, not only their counts. Corpus
attempt `ATTEMPT-PROCLUS-ET-1-2-UNITY-READING` preserves the blocked derivation
and rejected readings without creating philosophical claims to log activity.

Shared conventions were resolved with source revision
`c104800c7aaeaea12d56f9093e71bdef6a2ce6fa`. Source integrity, scholarly fidelity
and formal consequence remain separate verification boundaries.
