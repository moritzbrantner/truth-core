# De ente: does a really distinct esse need a source other than the thing? (#1629)

**Status:** conditional formal results plus a provisional judgment, revised
after an independent semantic challenge. Source: Thomas Aquinas, *De ente et
essentia*, pinned Corpus Thomisticum witness `AQUINAS-DE-ENTE-C3-4` (passage
`7070ccdd`), anchor [69874]. That witness uses the Baur/Koch numbering, where
the passage is **c.3**; it is **c.4** in the Leonine numbering the issue cites.
The materialized text of capp. 3–4 was read in full before the claims below
were made.

Formal home: `TruthCore/Latin/Aquinas/DeEnte/ExtrinsicSource.lean`, results in
`TruthCore/Results/Aquinas/DeEnte/ExtrinsicSource/`, spec
`specs/de-ente-extrinsic-source-1629.toml`, attempt `fbc68d10`.

## The passage and its steps

> Omne autem quod convenit alicui vel est causatum ex principiis naturae suae,
> sicut risibile in homine, vel advenit ab aliquo principio extrinseco, sicut
> lumen in aere ex influentia solis. Non autem potest esse quod ipsum esse sit
> causatum ab ipsa forma vel quiditate rei (dico sicut a causa efficiente) quia
> sic aliqua res esset sui ipsius causa et aliqua res seipsam in esse
> produceret, quod est impossibile. Ergo oportet quod omnis talis res, cuius
> esse est aliud quam natura sua habeat esse ab alio.

1. A disjunction over everything that belongs to a thing: from the principles
   of its nature, or from an extrinsic principle (claim `676bdaeb`, statement
   `75919560`).
2. A conditional: if esse were caused by the thing's quiddity *as by an
   efficient cause*, the thing would be its own cause and produce itself in
   being (claim `ce55e563`, statement `a2800f45`).
3. That this is impossible (claim `85857e47` on the existing
   `STMT-NOTHING-CAUSES-ITS-OWN-BEING`, `b62a64ab`). The impossibility is said
   under the efficient supposition; the statement's generic scope (no cause
   of its own being in any mode) rests on "sui ipsius causa", as the claim
   records.

The conclusion, "habeat esse ab alio", is the existing q.3 a.4 statement
`STMT-DISTINCT-ESSE-REQUIRES-EXTERNAL-CAUSE` (`33ad148b`). The q.3 a.4 profile
is reused, so the witness, the `CausesIn` relation and the represented
essence/esse are the same. **What its type certifies:** for every actual x with
`esseOf x ≠ essenceOf x`, some c with `c ≠ x`, in act as to being, causes x's
esse (`CausesIn`, DEF-CAUSE-OF-PERFECTION, mode of causation not fixed). The
words "efficient" and "extrinsic" in the q.3 a.4 statement are its prose
reading; the type adds no efficiency condition, and `c ≠ x` does not exclude a
constituent counted as a being.

## The gap: "not self-produced" is not "produced by another"

**Exact extra premise.** Given no self-causation, "caused by another" needs
only `DistinctEsseHasSomeCause` (`d1f3ffcc`): every actual distinct-esse x has
*some* cause of being. This is the vocabulary-free answer to the issue's
question; it is OPEN. Brute esse rejects it, and so does a non-causal intrinsic
or structural account unless its explainer counts as a being that causes x's
esse.

**De ente's decomposition of it.** Step 2 rejects only *efficient* causation
by the quiddity ("dico sicut a causa efficiente"); step 1's nature disjunct is
not restricted to efficient causation. Two senses are therefore kept apart
(`DISAMB` `87ac7ae0`, term `NATURE_SOURCE`):

| Sense | Lean | Meaning |
|---|---|---|
| `NATURE_SOURCE_1` | `NatureSource.fromNature` | caused from the principles of x's nature, mode unspecified (literal disjunct) |
| `NATURE_SOURCE_2` | `NatureSource.quiddityEfficientlyCauses` | x's own quiddity is an efficient cause (the sense of the rejection) |

In De ente's vocabulary the extra premise comes from
`DistinctEsseNatureOrOtherCause` (`8592601e`: every actual distinct esse is
efficiently caused by its quiddity or caused by another, esse only) plus the
self-causation reading. The literal disjunction gives `8592601e` only through
the OPEN sense bridge `NatureSourcedDistinctEsseIsEfficient` (`600f91cb`). Why
the bridge is not definitional: the qualifier in step 2 suggests that a
non-efficient causation of esse is in view, and the standard Thomist gloss
counts a form as a formal, non-efficient principle of being. That gloss is the
analyst's: the passage's own "forma dat esse materiae" concerns form and
matter, not a nature and its own subject's esse.

## Formal results (all zero-axiom; Comparator and NanoDa checked locally)

| Result | Theorem | Content |
|---|---|---|
| `9f071740` | `distinctEsseExternalFromCaused` | some cause + no self-causation + causes of being are in act + definitional cause-sense bridge → `33ad148b` |
| `44eef980` | `distinctEsseCausedFromDeEnte` | weak exhaustiveness + self-causation reading → some cause |
| `42a89226` | `distinctEsseExhaustionFromDeEnte` | literal disjunction + efficiency bridge → weak exhaustiveness |
| `901d94c9` | `otherActualCauseOfBeingIsExternalEsseCause` | premise-free, by definition: a distinct cause of being in act witnesses `HasExternalEsseCause` (adds only distinctness and actuality) |
| `08275113` | `extrinsicSourceControls` | six finite interpretations on `Bool` |

The controls are interpretations in which `false` actually exists with esse
distinct from its essence:

- **Brute esse**: nothing causes anything, nothing is from its nature. The
  literal disjunction, the weak exhaustiveness and some-cause fail; the other
  inputs hold; no other cause.
- **Formal nature**: `false`'s esse is from its nature (sense 1) without its
  quiddity efficiently causing it; nothing causes anything. The literal
  disjunction, the self-causation reading, no self-causation and the actuality
  of causes of being all hold, and there is no other cause. "Formal" is a
  label: `fromNature` is an unconstrained primitive, so this is a structural
  surrogate. It shows that the two nature senses are independent, so the
  source's three steps read literally do not yield the conclusion without the
  efficiency bridge; it does not model formal causation.
- **Self-cause**, **unrealized quiddity**, **nonactual cause**: drop
  no-self-causation, the self-causation reading (with some-cause downstream)
  and the actuality of causes of being respectively; the conclusion fails.
- **Nonvacuity**: every input holds and an actual `true` causes `false`'s esse.

These show logical underdetermination under the encoded predicates only. They
are not evidence that brute or formally sourced esse is possible or plausible.

## Existing routes to the same conclusion

`33ad148b` already had the q.3 a.4 transcription `af503cd7` from the stated
dichotomy `be639b3f` and the stated no-sufficient-self-cause premise
`61bd42e5`. That direct, source-attributed option stays. The new route is a
sibling option with a different decomposition: it isolates the extra premise
(`d1f3ffcc`) and shows where De ente needs the efficient reading. Both routes
share one underlying commitment, causal coverage of distinct esse, so they are
not independent corroboration of it. The participation route (`732302a1`)
reaches a distinct esse-cause from `Participates x`, a different antecedent;
nothing here relates participation to real essence–esse distinction.

`33ad148b` reaches the root through `4876dc46` (participated beings have an
external esse cause) on the designated efficient-regress route `3b0f4fa5`.
Computed `truth frontier-diff --base origin/main` (excerpt): "distinct
verified support alternatives: 469 -> 473"; "bare premises added: 1 ...
[600f91cb]"; "added (stated): 2 ... [75919560], [a2800f45]"; "moved (stated ->
closed): 1 ... [33ad148b]" ("closed" in that report means no longer an open
leaf, here because it is proved from open premises). The dossier status of `33ad148b` is "proved;
established: false": proved from open premises, not established. The cheapest
expanded route is unchanged (cost 16).

## Rivals on the same actual being and explanandum

Each row names its target, mechanism and the independent justification
offered, per the Substantive Objection Standard.

| Account | Target | Mechanism and justification | Price under its own commitments |
|---|---|---|---|
| Thomistic received esse | — (the route) | A distinct esse has some cause (`d1f3ffcc`); in De ente's terms, a nature that is not its esse supplies it, if at all, only as an efficient agent (bridge `600f91cb`), and an agent quiddity would make the thing its own cause (steps 2–3). So the cause is another being, and in act as to being (`4ccb319f`). | Needs causal coverage of distinct esse and, for the De ente decomposition, the efficiency bridge; the conclusion is tenseless, so it says nothing about present sustaining (#1604/#1616). |
| Brute esse (#312/#746) | `d1f3ffcc` / the disjunction | x's esse has no cause and no nature source. Justification offered in the corpus: explanation must stop somewhere, and unrestricted PSR has recorded costs (#312/#746). | Consistent (brute control). By the brute hypothesis, it stops at an actual composite whose nature is not its esse and which has no account of its actuality, and it must give a stopping criterion that selects this composite rather than a source. That is the open #746 stopping-criterion question; no view-internal contradiction is shown here. |
| Non-efficient intrinsic nature account | efficiency bridge `600f91cb` (and `d1f3ffcc`) | A nature may be a formal, non-efficient principle of its own subject's esse, so a distinct esse may be from the nature without efficient self-causation. Justification: the standard Thomist gloss of form as formal principle of being; step 2's qualifier motivates it. | It must say whether the nature *accounts for* x's actuality or only *specifies* an actuality it presupposes. If it only specifies, the actuality is still unaccounted for (brute row) or from another. If it accounts for it without being an agent, a principle that is not x's esse supplies x's actuality, which is #1621's intrinsic-adequacy question applied to distinct esse. Not refuted here. Also note: a form encoded as a distinct being that causes x's esse would satisfy the conclusion as typed. |
| Constitutive or global structural explanation (#311/#750) | `d1f3ffcc` (the cause-of-being reading of "from another") | x exists because of its place in an actual structure that does not cause its esse. Justification: non-causal structural and grounding explanation in science and metaphysics. | If the structure is an actual being distinct from x that causes x's esse, it satisfies the conclusion (a candidate source, not a rival to the bridge). If it only characterizes x, it must show explanatory direction and joint sufficiency for the actual obtaining of this bearer (#311 EXP-LOCAL-TO-GLOBAL, #750). Unpaid, not refuted. |
| Modal necessity | none separately | A necessary existent with really distinct esse faces the same question; this passage says separate substances receive esse (it does not assert their necessity). Necessity from the nature falls under the intrinsic row; brute necessity under the brute row. No separate mechanism identified. | — |
| Merely conceptual distinction | the antecedent `DistinctEsseAt` | If essence and esse differ only in concept, `esseOf x = essenceOf x` and the bridge is silent. The De ente argument for a real distinction (understanding a nature without knowing whether it exists) is not formalized here; a conceptual difference does not by itself prove a real one. | Rejects the antecedent, not the inference. |

**Existential inertia.** It targets present sustaining, not this route: the
conclusion's `CausesIn c x esse` is tenseless and holds of an originating
source. Inertia bears on "a source once" only if x also has no origin; that
combination is the brute-esse row. No separate objection identified.

## Overall provisional judgment (2026-11-14, this revision)

**Claim.** For an actual x whose esse is really distinct from its essence,
x's esse is caused by another being in act.

**Judgment.** The inference is valid exactly with one further premise, causal
coverage of distinct esse (`d1f3ffcc`); the De ente text supplies that
premise only when its nature disjunct is read efficiently (formal-nature
control). The claim is therefore provisionally supported to the degree that
causal coverage of distinct esse is: it is not established. Against brute
esse, the received-esse account has an explanatory-scope advantage (it
accounts for the actuality where brute esse accounts for none). That is a
comparison of explanatory performance, not a substantive test that brute esse
failed; both are consistent under the encoded predicates, and the stopping
criterion burden is shared with #746. No further comparative advantage is
shown here. The **strongest standing rival to the De ente inference** is the
non-efficient intrinsic nature account; its price is to show that a principle
that is not x's esse can account for x's actuality without being an agent,
#1621's adequacy question restricted to distinct esse. The **strongest rival
overall** is brute esse, at the price stated in its row.

**Would revise.** Downward: a worked account in which a non-efficient
principle accounts for (not merely specifies) the actuality of a distinct
esse, or a principled stopping criterion selecting brute composites. Upward:
a checked derivation of the efficiency bridge or of causal coverage from a
specify-versus-actualize principle (below).

**Boundaries.** No premise is established; no conservation, uniqueness,
concreteness at a world, efficiency of the cause, or God identification
follows; the real distinction is an input, not proved.

## Next discriminating test and connection plan

1. **Efficiency bridge from a specify-versus-actualize principle.** Split
   sense 1 into "specifies the actuality x has" and "accounts for x's being
   actual", and test whether `600f91cb` follows from: an accounting principle
   either is an agent or is identical with the act it accounts for. Under real
   distinction, identity is excluded, leaving agency, which steps 2–3 exclude
   for the thing itself. A finite model of a non-agent, non-identical
   accounting principle would show the extra principle is needed.
2. **#319 connection.** The root-essence identity compositions
   (`RootEssenceIdentity.identityOfActualRoot` and its consumers) take the
   q.3 a.4 pair `be639b3f`/`61bd42e5` directly. A sibling consuming `33ad148b`
   would let this route feed #319's necessary-root chain; blocker: those
   arguments are frozen, so it needs new sibling arguments, not edits.
3. **#1496 connection.** Composing `33ad148b` with `cb1cdea9` gives an actual
   concrete ground for actual distinct-esse concreta at w, given the existing
   presence/actuality bridge. Reaching `c71c068c` (contingent concreta) still
   needs a contingency-to-real-distinction bridge, which is not available.

## Semantic challenge

An independent reviewer challenged the first draft (staged diff, this
branch). Accepted and repaired: the conclusion's "efficient" and "extrinsic"
are prose, not type conditions (stated above and in the records); "forma dat
esse materiae" was overread as the passage granting a formal source of a
nature's own esse (now the analyst's gloss); the generic scope of
no-self-causation is noted on its claim; the weakest premise is the
vocabulary-free `d1f3ffcc`, now certified as the step's only extra premise;
the formal-nature control is labelled a structural surrogate; nonvacuity was
removed as a comparative reason, and "gains relative standing" was withdrawn
in favour of an explanatory-scope comparison. No disagreement was left
unresolved.
