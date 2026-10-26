# Expressivist embedding: primary-witness boundary

This investigation concerns the strongest Blackburn/Gibbard response to the
Frege–Geach objection in #185, #182 and #181. It records a primary-source reading
and a separately checked analyst control. It reaches no verdict against
expressivism. The existing candidate
`EXPRESSIVIST-LOGIC-OF-ATTITUDES-COST` remains queued. A separate analyst semantic
control is formalized below, alongside two historical source readings. No
answer-map upgrade or root-path discharge follows.

## What the existing result establishes

The certified theorem
`TruthCore.Results.Comparison.MoralLanguage.ExpressivismConsistentWithGeachValidity.expressivismConsistentWithGeachValidity`
(`EXPRESSIVISM-CONSISTENT-WITH-GEACH-VALIDITY`) constructs a model of
`ConstantMeaningExpressivism s ∧ SharedData s`. Its signature makes `ValidMP`
primitive. The concrete model sets it to `True`, uses `Unit` sentences, and
therefore has `p = q`. These choices are appropriate for the advertised
satisfiability claim; they do not derive validity from a semantics of embedded
conditionals or demonstrate a nontrivial inference between distinct sentences.
Reproving this consistency theorem would duplicate the existing control.

`STMT-BLACKBURN-VALIDITY-AS-ATTITUDE-CLASH` and
`STMT-EXPRESSIVISM-NEEDS-B-TYPE-INCONSISTENCY` remain secondary-witness readings.
The latter concerns an attitude-type architecture; it does not establish that
all expressivist models require that architecture. The existing result does
not refute either the later Blackburn reply or Gibbard's reply. The dossiers of
these two statements and `STMT-EXPRESSIVISM-CONSISTENT-WITH-GEACH-VALIDITY` were
inspected before this search; none contained an earlier primary-source attempt.

## Primary witness and conditional mismatch

A later search found Gibbard’s own “Reply to Commentators” in the open-access
2022 volume *Meaning, Decision, and Norms* (Michigan Publishing). The publisher
PDF is pinned and the complete physical pp. 564–573 (printed pp. 535–544) were
materialized as `GIBBARD-REPLY-2022-535-544` and read, including the responses
to McPherson/Perl and Yalcin and their surrounding context.

Two independent historical statements preserve its relevant commitments:
`STMT-GIBBARD-PERMISSION-NOT-PICKING` (pp. 541–542) distinguishes settling what
to permit oneself from picking among eligible alternatives, and
`STMT-GIBBARD-INDICATIVE-NOT-MATERIAL-TRUTH` (pp. 536–538) records the crucial
qualification: false-antecedent indicative conditionals lack truth values in
his expanded full-truth sense, though lighter truth-like statuses and proper
assertion are left possible. His reply to Yalcin (p. 540) also describes an
indicative conditional in terms of conditional credence. The material support
clause below is therefore **not Gibbard’s indicative-conditional semantics**.
The model does not settle Frege–Geach for his historical theory.

His primary clarification motivates permission rather than single-action
choice, but it supplies no proof that the analyst acceptance relation captures
his independently characterized practical psychology. In particular, the
reconstruction does not represent hyperplans on subjective predicaments or
the third-personal correlations discussed on p. 543. No new historical reading
is bound to a Lean declaration; the checked theorem is a different proposition.

## Earlier acquisition attempts on 2026-10-26

The following are precise acquisition leads and observed retrieval outcomes,
not verified passage witnesses. No source interpretation is attributed on the
basis of a search snippet. These failed routes are preserved even though the
2022 primary response was subsequently acquired.

| Lead | Outcome and limit |
| --- | --- |
| Blackburn, “Attitudes and Contents,” *Ethics* 98 (1988), 501–517; https://www.journals.uchicago.edu/doi/pdf/10.1086/292968 | Publisher retrieval returned HTTP 403 with a browser challenge. Metadata alone does not expose the argument. The later reply must be inspected rather than identified with the 1984 higher-order-attitude account. |
| Gibbard, “An Expressivistic Theory of Normative Discourse,” *Ethics* 96 (1986), 472–485; https://www.journals.uchicago.edu/doi/pdf/10.1086/292770 | Publisher search exposes metadata and an access boundary, not inspected full text. |
| Gibbard, *Wise Choices, Apt Feelings* (1990), chapter 5, “Normative Logic,” 83–102; https://doi.org/10.1093/oso/9780198249856.003.0005 | Publisher abstract describes the chapter's project, but the full chapter requires access. The abstract is insufficient for its conditional clauses. |
| Gibbard, “Normative and Recognitional Concepts,” *Philosophy and Phenomenological Research* 64 (2002), 151–167; https://hdl.handle.net/2027.42/73386 | PhilPapers supplies this institutional repository lead. https://deepblue.lib.umich.edu/handle/2027.42/73386 returned HTTP 403. A guessed bitstream path was also blocked; its filename is not verified. |
| https://citeseerx.ist.psu.edu/document?doi=6978b27f0d09e07550d88d9ef0bb3204603de588&repid=rep1&type=pdf | An indexed copy of the 2002 article, but retrieval failed. No bytes or source-hosting provenance were verified. |
| Gibbard, “Thinking How to Live with Each Other,” https://tannerlectures.org/wp-content/uploads/sites/105/2024/06/Gibbard_2007.pdf | The indexed official lecture URL returned HTTP 404 through both browsing and curl. |
| Gibbard, *Reconciling Our Aims* (OUP, 2008), legal preview: https://api.pageplace.de/preview/DT0400.9780199708208_A23607980/preview-9780199708208_A23607980.pdf | Retrieval succeeded: 23 physical pages, ending at printed page 14, before the needed planning semantics. The complete preview was inspected for scope. The planning/acceptance discussion is in Stroud’s Introduction, especially printed pp. 4–6; Gibbard’s own contribution in this preview occupies pp. 11–14 and does not state the needed conditional semantics. This is not a witness for the conditional treatment. |

The retrieved preview's byte SHA-256 was
`51386cd502b89aca684a459b694ae6445a87d67ec3e98ff249ff9d7557c28345`.
This hash identifies an inspected acquisition lead only. No passage manifest
was created and no repository materialization was performed for it, since it
does not supply the target source range. No copyrighted text is committed.
The author page https://websites.umich.edu/~gibbard/ supplies bibliographic and
teaching context; it supplies no inspected text of the target semantics.

Unattributed full-book uploads and unattributed article transcriptions were
excluded because this search did not establish legitimate hosting or edition
integrity. Secondary accounts can locate a candidate reply; they do not turn
that reply into a primary-source reading. No access control was bypassed.

## Analyst semantic control

`PLAN-STATE-EMBEDDING-CONTROL` implements a separate, explicitly stipulated
planning-language fragment in `TruthCore/Metaethics/PlanStateEmbedding.lean`.
It reuses the existing distinction between a normative planning component and
a descriptive component, motivated by materializing and reading the pinned
secondary witness `SEP-MORAL-COGNITIVISM-2-5` and its context
`SEP-MORAL-COGNITIVISM-4-1`. Those passages remain secondary. The separately acquired 2022 response
adds primary motivation for permission/picking and the explicit conditional
mismatch, not a primary derivation of the reconstruction’s semantic clauses.

The model makes
sentences and their conditional construction explicit, distinguishes descriptive
possibilities from permission plans, and defines ideal acceptance of a sentence
by containment in its compositional support. The theorem derives the
inference from acceptance of `p` and `if p then q` to acceptance of `q` using
compositional clauses, without assuming that inference as a primitive
`ValidMP` fact or a bridge whose consequent already is the conclusion.

The added stipulations are: a complete Boolean permission plan; a Boolean
descriptive valuation kept separate from it; factual, forbidden-action and
conditional sentence constructors; the conditional support clause “antecedent
unsupported or consequent supported”; and ideal acceptance as containment of
compatible points in support. This exact material-conditional clause is not
attributed to either historical author. The result derives MP for all formulas
(including nested and mixed factual/planning conditionals) and all compatible
states, then exhibits a nonempty state accepting distinct forbidden-action atoms
and their conditional, with a third action left permitted. A second nonempty
state also leaves an action permitted, accepts the consequent and
conditional but fails to accept the antecedent, so the converse inference fails.
No descriptive atom is used to encode a moral fact. These are semantic
consequences of independently declared clauses, not a psychological account.

The still-open work is to obtain a faithful semantics for the selected
historical embedded conditional (rather than identify our material support
clause with the different indicative treatment in the acquired response),
distinguish compatibility from an agent's actual psychological acceptance,
and explain why the encoded incompatibility is logical rather than merely an
undesirable clash of attitudes. The exhibited states guard
against empty-state vacuity and conflating the two normative atoms. Empty states
still accept everything by definition; the universal MP property does not itself
require nonemptiness.

A semantic satisfaction value or a predicate of accepted plans is not by itself
a mind-independent moral fact. Conversely, replacing the label “truth” with
“acceptance” does not establish an expressivist explanation. Any future result
must identify separately (a) the compositional semantic commitments, (b) the
non-cognitive interpretation of the planning state, and (c) substantive moral
realism. A theorem about (a) cannot establish either (b) or the negation of (c)
without further premises. The descriptive-world component must not silently
contain the very moral facts whose necessity is under examination.

## Handoff and premise comparison

Retain the original rival theories and their current answer maps. No premise
is added or removed from an existing rival or root route, no answer changes
from unexplained to entailed, and no root-route open-premise count changes.
The analyst control has no proposition hypotheses: its result follows from
the new stipulative definitions listed above. This is a new connection within
a selected semantics, not a discharge of the historical or psychological
adequacy obligation. It does not connect to the original primitive `ValidMP`
without a defended bridge. Obtain an
admissible text-bearing primary range for the selected reply, pin it as a
`web_snapshot` (or an already admitted immutable witness), materialize it, and
read its complete context before selecting declarations or changing an answer.
The analyst derivation succeeds; the historical conditional and its
psychological/metasemantic bridge remain separate source and modeling gaps.
Keep #185 open for this gap and the other outstanding theory questions.
