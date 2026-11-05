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
| On Certainty: doubt rests on what stands fast | §§115, 341 (German, `WITTGENSTEIN-UEBER-GEWISSHEIT`) | support (against global doubt only) | the global sceptical rival of any observation floor item; no specific item (F3, F4) | `WITTGENSTEIN-UNIVERSAL-DOUBT-FAILS`, conditional on the stated §341 premise |
| On Certainty: hinges stand fast but are not known | §151, §§204-205 (conditional), §§94-97; readings via `SEP-FIDEISM` §4 (Pritchard, Moyal-Sharrock, Read/Crary) | rival reading of the *basis* of F3/F4 (not of their truth) | 'established' for F3/F4 (observation basis) | recorded; floor-basis proposal for the owner below |
| On Certainty: "there are physical objects" is nonsense | §§35-36 | rival to the statementhood of a candidate F2 phrased with "physical object" | candidate F2 ('something exists'), not approved | recorded |
| PI: rule-following regress | §§198, 201-202; Kripke via `SEP-PRIVATE-LANGUAGE` §4 | neutral to the routes | none | `WITTGENSTEIN-INTERPRETATION-REGRESS` (regress plus three-way fork) |
| PI: private-language argument | §§243, 258, 293, 304, 308; readings via `SEP-PRIVATE-LANGUAGE` §§1.1-1.2 | neutral to F5 as an occurrence premise; rival only to a private-introspection basis for it | candidate F5 (`STMT-COGITO-THOUGHT-OCCURS`) | recorded |
| Lectures on religious belief (1938, student notes) | religious beliefs not hypotheses, `SEP-RELIGIOUS-LANGUAGE` §4.2 | rival in spirit to recognizability by signs; not attached to a leaf | none (the notes are not Wittgenstein's text; no claim attributes WF-N to him) | recorded as a reported reading |

The Tractatus and the Lecture on Ethics follow in a later PR of #1010.

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

  A possible further objection, unresolved: the first escape seems to need a
  criterion of the practice's grammar that can override the practice's own
  authoritative self-description, and such a criterion may not fit the
  internal-grammar thesis. The second escape is an interpretive dispute about
  the council's text, settled by reading, not by this objection. The
  objection is a judgment with no vocabulary yet and is not counted. Blocker: a
  typed account of who fixes a practice's grammar.

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

## On Certainty

The witness is the German text, public domain in the EU, pinned as the raw
wikitext of one revision of the Ludwig Wittgenstein Project page. The Paul and
Anscombe translation is in copyright and is not used.

### Doubt rests on what stands fast (support, narrowly)

§341: "unsre *Zweifel* beruhen darauf, daß gewisse Sätze vom Zweifel ausgenommen
sind". §115: "Wer an allem zweifeln wollte, der würde auch nicht bis zum Zweifel
kommen."

`TruthCore.Results.Wittgenstein.DoubtPresupposesCertainty.universalDoubtFails`
derives the failure of universal doubt from §341. The premise is needed.

`anyGivenSentenceDoubtable` bounds what the result gives: §341 is consistent
with doubting any one chosen sentence. So the result can serve against a
*global* sceptical rival of an observation floor item. It supports no
particular item. It does not establish 'something changes' (F3) or 'something
is moved' (F4). It does not touch Pyrrhonian suspension, which neither
asserts nor doubts in this sense.

### What the hinges are: the reading that decides "established"

Four senses are recorded in `DISAMB-HINGE-STATUS`:

1. **Known truth** (Moore's own claim). Only on this reading would a hinge
   count as an established floor item with an observation basis.
2. **A-rational commitment** (Pritchard's quasi-fideism).
3. **Non-propositional animal certainty** (Moyal-Sharrock).
4. **Nonsense** (Read, Crary).

Wittgenstein's own text leans against sense 1:

- §151: "Moore *weiß* nicht, was er zu wissen behauptet, aber es steht für ihn
  fest".
- §204: justification ends not in seeing that something is true but in our
  acting.
- §205, recorded as a conditional only: *if* the true is what is grounded, the
  ground is neither true nor false.

So the "neither true nor false" reading bears on 'established' as follows.
F3 and F4 would *stand fast* without being *established* in the corpus's
sense. They would not be denied, but they would not be known truths that
refute their rivals either.

The bearing is on the floor **basis**, not on the items. No reading of *On
Certainty* says that nothing changes or that nothing is moved. A hinge
reading is therefore not an `alternative_to` F3/F4, and none is recorded.
Recording one would reopen the approved markings.

### "There are physical objects" (F2)

§§35-36: "»Es gibt physikalische Gegenstände« Unsinn", since "physical object"
is a logical concept. This bears on how a candidate F2 ('something exists') is
phrased, not on its truth. Phrased as an existential over a formal concept, it
falls under the same remark. Phrased with a material predicate ("here is a
hand", §1), it is a Moore-type hinge, and the reading question above decides it.

### Proposed floor-basis changes (for the owner; none applied)

- **P-OC-1.** Add the On Certainty hinge readings to the F3 and F4
  `disagreement` records, as claims that deny that the items are known
  (`WITTGENSTEIN-OC-151-STAND-FAST-NOT-KNOWN`, `SEP-FIDEISM-4-HINGES-NONSENSE-A`,
  `SEP-FIDEISM-4-HINGES-NON-PROPOSITIONAL-A`). Under #1007 this is
  bookkeeping: the approval stays, and the disagreement becomes visible.
  Recommended.
- **P-OC-2.** Use `WITTGENSTEIN-UNIVERSAL-DOUBT-FAILS` as the refutation of a
  recorded *global* doubt rival, should one ever be listed under
  `sceptical_rival_ids` for an observation marking. It cannot count until
  §341 is established, so it has no effect today. Recommended only as a
  pointer.
- **P-OC-3.** Do not adopt a "hinge" basis for F2-F4. It would make the items
  stand fast without being true, which is weaker than the case needs.

## Philosophical Investigations

The witness is the German *Philosophische Untersuchungen*, Part I, public
domain in the EU, pinned like *Über Gewißheit*.

### Rule-following (§§198, 201-202): the shape of the regress

`TruthCore.Results.Wittgenstein.InterpretationRegress.interpretationRegress` is
the logical point. Suppose an item is determined only through a determined
interpretation of it, and there is no endless chain of interpretations
("Deutung hinter Deutung"). Then nothing is determined. The proof is
well-founded induction.

`regressFork` adds that these two premises and "some application is
determined" cannot all hold. The readings choose differently:

- §201 itself keeps determination and gives up the interpretation premise:
  "eine Auffassung einer Regel ..., die *nicht* eine *Deutung* ist".
- Kripke's sceptic keeps the paradox and denies factual determination. Kripke
  does not identify this figure with Wittgenstein.
- An endless regress gives up finiteness.

The result settles no reading (`DISAMB-RULE-FOLLOWING-PARADOX`). Neutral to the
routes.

### Private language and F5

§258 denies a criterion of correctness for a sign fixed by private ostension.
§304 says that the sensation "ist kein Etwas, aber auch nicht ein Nichts".
§308: "Und wollen sie [die geistigen Vorgänge] doch natürlich nicht leugnen!"

On either reading of the sections (reductio or nonsense,
`DISAMB-PLA-FALSE-OR-NONSENSE`), the argument targets the private
*identification* of an inner object, not the occurrence of thought. So it is
**neutral** to candidate F5 (`STMT-COGITO-THOUGHT-OCCURS`) as an occurrence
premise. It is a rival only to a Cartesian private-introspection *basis* for
F5. The retorsion basis proposed on #1007 ("a denial is a thought") uses a
public speech act and is unaffected.
