# Wittgenstein and Wittgensteinian positions, classified against the case

Issue #1010. Wittgenstein's positions and the positions developed from his work
are recorded as readings, then classified as **rival**, **support** or
**neutral** relative to the root routes' premises (their open leaves, `corpus.py
frontier --routes`) and the floor items of #1007 (approved: F1, F3, F4, F6;
F5 a candidate). A classification is a research judgment about bearing, not a
defeat: defeats and support count only by #999, #1007, D-I and D-L.

Exegesis caution. Wittgenstein's texts are contested. Readings are recorded as
readings, and a view developed by followers is not attributed to him.

## Classification table

| Position | Variant and source | Class | Against which premise or floor item | Status |
|---|---|---|---|---|
| Wittgensteinian fideism, sharp form | WF-N: the critics' four theses (Nielsen 1967), `SEP-FIDEISM` §2.2.4 | rival | `STMT-REVELATION-POSSIBLE-AND-RECOGNIZABLE` (all 12 routes) | conditionally defeated as a description of Catholic practice (`WF-FAILS-AS-DESCRIPTION-OF-CATHOLIC-PRACTICE`); open premises, so not counted (#999) |
| Early Phillips | WF-P1: praise of God refers to no object (1976), `SEP-RELIGIOUS-LANGUAGE` §4.1; the stronger thesis that "God" names no being is an unattributed reconstruction it supports | rival (the reconstruction) | `STMT-GOD-NAMES-THE-FULLY-DESCRIBED-PRINCIPLE`, `STMT-GOD-NAMES-THE-UNIQUE-MAXIME-ENS`, `STMT-UNIQUE-PURE-ACT-FIRST-MOVER-IS-GOD` (the nominal identification on every route) | recorded, not refuted |
| Late Phillips, religious minimalism | WF-P2: reference and truth constituted inside the game; outside evidence admissible, `SEP-RELIGIOUS-LANGUAGE` §§4.1-4.2; `SEP-FIDEISM` §2.2.4 | rival off-route (face value theory); neutral to route leaves | `STMT-FACE-VALUE-THEORY-RELIGIOUS-LANGUAGE` (no route premise) | recorded |
| Nielsen's critique | insulation of every form of life, `SEP-RELIGIOUS-LANGUAGE` §4.2 | objection to WF-N | attacks `STMT-WF-RELIGION-CUT-OFF-FROM-SHARED-REASON` | recorded; not a defeat (#1007: "not preferable" is not falsity) |
| Lectures on religious belief (1938, student notes) | religious beliefs not hypotheses, `SEP-RELIGIOUS-LANGUAGE` §4.2 | rival in spirit to recognizability by signs; not attached to a leaf | none (the notes are not Wittgenstein's text; no claim attributes WF-N to him) | recorded as a reported reading |

The Tractatus, the *Investigations* (rule-following, private language) and *On
Certainty* follow in later PRs of #1010.

## Wittgensteinian fideism

### The worldview at full strength

The label is Kai Nielsen's (*Philosophy* 42, 1967). The SEP entry *Fideism*
(§2.2.4) reports that the view is "variously characterized" as entailing that
(1) religion is logically cut off from other aspects of life, (2) religious
discourse is self-referential and does not let us talk about reality, (3)
religious beliefs can be understood only by believers, and (4) religion cannot
be criticized. It also reports that Nielsen aimed at Wittgensteinians (Malcolm,
Winch), not Wittgenstein; that Wittgenstein likely endorsed none of the four;
and that Phillips called the charge a caricature (1981, 89-90): he denied only
his critics' *conception* of the connection between religion and life and of
criticism (`STMT-PHILLIPS-DENIES-ONLY-CRITICS-CONCEPTION`).

Three variants are kept apart (`DEF-WITTGENSTEINIAN-FIDEISM`):

- **WF-N**, the sharp form: internal grammar (`STMT-WF-RELIGION-INTERNAL-GRAMMAR`)
  and cut-off (`STMT-WF-RELIGION-CUT-OFF-FROM-SHARED-REASON`).
- **WF-P1**, early Phillips: religious belief expresses a moral vision, and praise
  of God "does not refer to some object called God"
  (`STMT-PHILLIPS-GOD-TALK-NOT-REFERENCE-TO-AN-OBJECT`). This is a remark about
  the activity of praise. The stronger thesis that the name "God" applies to no
  being (`STMT-GOD-NAMES-NO-BEING-WF-P1`) is an unattributed reconstruction that
  the remark only supports.
- **WF-P2**, late Phillips and minimalism: "God" may be said to refer, but what
  reference, object and existence amount to must be shown in the religious
  context, and "true" has several senses
  (`STMT-PHILLIPS-REALISM-CONCEPTS-RELIGION-INTERNAL`). Religious beliefs depend
  on non-religious features of life but are "not generally" conclusions from
  them (`STMT-PHILLIPS-RELIGION-NOT-GENERALLY-CONCLUSION`). Minimalists allow
  outside evidence into religious justification
  (`STMT-MINIMALISM-ALLOWS-EXTERNAL-EVIDENCE`).

Its answers to the shared question set are in the answer map of
`TruthCore/Comparison/Fideism.lean`. Each answer there is labelled *reported*
(the SEP entries report it) or *reconstruction* (the comparison's own,
unattributed). Reported: what "God exists" says is fixed inside the practice
(WF-P2). Religious belief expresses a moral vision (WF-P1). Criticism from
outside is denied (WF-N) or reconceived (Phillips). No witness reports a
fideist answer to the cosmological or first-mover questions, so they are
**unexplained**, and the reconstructions there are labelled as such.

Sources. Phillips, Winch and Nielsen are in copyright, and no legitimately
hosted copy was found. They have bibliographic source identities only
(`PHILLIPS-RELIGION-WITHOUT-EXPLANATION`, `NIELSEN-WITTGENSTEINIAN-FIDEISM-1967`,
`WINCH-UNDERSTANDING-A-PRIMITIVE-SOCIETY`,
`NIELSEN-PHILLIPS-WITTGENSTEINIAN-FIDEISM-2005`). Every claim is read from the
pinned SEP entries, and each says it reports the position.

### Defeat by consequence: the practice's own rule

Fideism's thesis is descriptive: it says how the religious game is played.
The Catholic practice describes its own game in the opposite way. *Dei Filius*
ch. 2 teaches that God "can be known with certainty from created things by
the natural light of human reason", and canon II.1 condemns the denial
(`STMT-DEI-FILIUS-DEFINES-NATURAL-KNOWABILITY-OF-GOD`).

`TruthCore.Results.Alternatives.FideismCatholicPractice.fideismFailsAsDescription`:

```
CouncilDefinesNaturalKnowabilityReading P → DefinitionIsOwnStandardReading P →
  NaturalReasonIsSharedReading P → ¬ (InternalGrammarReading P ∧ CutOffReading P)
```

By the fideist's own internality, the defined move is correct. By the cut-off
thesis it is not. Each premise is needed (countermodels in the same Comparator
config), and the fideist bundle alone is consistent (`WF-CONSISTENT`). So the
defeat comes from the community's rule, not from incoherence.

What it shows, and what it does not:

- It refutes WF-N **as a description of Catholic practice**. It says nothing
  about other practices, or about every possible fideistic proposal.
- It does not touch Phillips's "not generally" thesis: that thesis allows
  God's knowability by natural reason. Nor does it touch minimalism, which admits
  outside evidence.
- It is conditional. The canon is stated. The bridge that conciliar definitions
  belong to the practice's grammar (`STMT-CONCILIAR-DEFINITION-IS-PRACTICE-OWN-STANDARD`,
  supported by ch. 3) and the reading that natural reason is shared reason
  (`STMT-NATURAL-REASON-IS-SHARED-REASON`, supported by ch. 2's contrast with the
  "supernatural way", `DISAMB-NATURAL-REASON`) are open. Under #999 no refutes
  relation is recorded.
- The fideist's escapes are exactly the denials of the two bridges.
  - Treat the council as theology *about* the practice rather than its grammar
    (`needsDefinitionIsOwnStandard`). It may connect with Phillips's remark
    that his approach rescues belief and atheism "from philosophical
    distortion" (2005, 75, as quoted), but no witness says he read conciliar
    teaching so. The reconstruction is unattributed.
  - Re-read "natural reason" as a practice-internal standard
    (`needsNaturalReasonIsShared`).

  A further objection is recorded as unresolved and is not a consequence of
  either escape: that a fideist who takes an escape imports a standard from
  outside the game, against the internal-grammar thesis. The countermodels show
  only that each bridge is needed. The objection would need two bridges, neither
  recorded:

  1. that rejecting conciliar definitions as part of the grammar appeals to a
     standard not internal to the practice. It could instead appeal to
     distinctions within the practice, and the second escape is itself an
     internal re-reading of "natural reason";
  2. that the internal-grammar thesis forbids external standards.
     `InternalGrammarReading` formalizes only that internal endorsement implies
     correctness.

  It is not counted. Blocker: a typed account of who fixes a practice's
  grammar.

Self-application: an unresolved objection, not a result. One might argue
that the fideist thesis is a claim about the grammar of religion made in
philosophy, outside the religious game, and so cannot be correct by its own
lights. That does not follow from the reported theses.

- Thesis (3) restricts who can *understand* religious beliefs, not who can
  correctly make philosophical claims about religion. A believer doing
  philosophy is compatible with it.
- The generic schema `STMT-SELF-APPLICATION-DILEMMA` (`DEF-SELF-APPLICATION-NORM`)
  applies only if the fideist claim falls within the norm's scope and fails its
  standard. Placing the claim outside the game establishes neither.

The objection would need three explicit bridges, none recorded:

1. a norm whose scope includes claims *about* a practice's grammar;
2. a bridge from understanding to correctness;
3. the premise that the fideist claim fails that norm's standard.

Until then it stays an objection for the whole-worldview comparison, with no
Lean and no counted defeat.

Nielsen's critique (`STMT-NIELSEN-WF-INSULATES-FORMS-OF-LIFE`) is recorded as an
`attacks` relation on the cut-off thesis. It judges a consequence (no form of
life can be criticized or defended) unacceptable. Under #1007 that is
whole-worldview comparison, not falsity.

### Rival entries on route leaves

- `STMT-REVELATION-POSSIBLE-AND-RECOGNIZABLE` (12 of 12 routes): rival
  `STMT-WF-RELIGION-CUT-OFF-FROM-SHARED-REASON`. Recognizability by external
  signs answers to shared reason. Conditionally defeated, as above.
- `STMT-GOD-NAMES-THE-FULLY-DESCRIBED-PRINCIPLE` (9 routes),
  `STMT-GOD-NAMES-THE-UNIQUE-MAXIME-ENS` (1), `STMT-UNIQUE-PURE-ACT-FIRST-MOVER-IS-GOD`
  (3): rival `STMT-GOD-NAMES-NO-BEING-WF-P1`, the unattributed reconstruction of
  WF-P1, which Phillips's reported remark only supports. Unrefuted.
  The parallel argument from *Dei Filius* ch. 1 and canons I.1-3 (God a
  substance really distinct from the world) needs a typed reference relation.

No route cost changes: the leaves were already open, and none had a floor
marking.
