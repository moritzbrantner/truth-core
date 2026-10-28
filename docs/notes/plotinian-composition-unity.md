# Plotinian composition, dependence and the first

Bounded #361 investigation connected to #319/#320 and the comparison of
Platonism, Aristotelianism, mereological rivals and Catholic metaphysics. The
six source readings are prose commitments, not new Lean results or a proof
that their philosophical premises are true. No root premise is discharged.

## Witness and contextual reading

`PLOTINUS-ENN-V-4` materializes the complete Greek *Enneads* V.4, chapters 1–2,
from Volkmann's Teubner edition (1883–1884), First1KGreek revision
`ed91552c52530c8f5a3ddf2dd767e899372a804c`, blob
`7b5a33eade9341bfabd4a2ac6a3a7551756f3128`. The whole materialized treatise was
read before these claims. The bounded claim range is V.4.1; V.4.2 supplies
context rather than an additional formal claim. No English translation is
used as the witness. The first reading preserves the source’s requirement that
such a first exist; recording that requirement does not establish existence. VI.9.1–6 remains a successor reading, not evidence read
for this batch.

The opening sets a conditional explanatory order: anything **subsequent** to
the first derives from it directly or through intermediaries. It then requires there to be
a first that stands on its own, prior to all, distinct from its derivatives,
not mixed with them but present in another way. The text's genuine unity is
outside combination and composition. It even qualifies predication of “one”
about this first, so it must not be modeled without argument as an ordinary
object whose cardinal number happens to be one.

The explicit reason relevant to composition follows: what is nonfirst needs
what precedes it, and what is nonsimple needs the simples within it to be
constituted from them. This is a positive parts-to-composite dependence account,
not merely an unexplained assertion that a first is simple. It nevertheless
contains a substantive direction-of-dependence commitment: the internal
constituents are explanatory prerequisites. A whole-first rival denies that
direction rather than denying that the whole has parts.

The following uniqueness argument says another such first would leave the two
not one. This records an argument in the text, not a certified inference from
individual noncomposition. The distinction between a pair's plurality and each
individual's simplicity remains crucial. The text also invokes global
firstness and a distinctive genuine-unity ontology, so its full first-principle
claim is stronger than the mere absence of an upstream node in one selected
causal relation.

V.4.1 excludes bodies because they are nonsimple and come to be, whereas the
first is ungenerated. This does not date a beginning of time or identify a
modern physical ontology with the source's body. The text then presents
productive perfection as an account of derivatives: fire, snow and other
agents communicate what they can; a perfect first cannot be sterile through
weakness or envy. That productivity argument is preserved here as contextual
reasoning, not silently converted into a theorem of necessary production in
all Kripke worlds or an account of deliberative creation.

The end of V.4.1 distinguishes the first from Intellect: intellection turns
toward the intelligible and is determined or completed by it; Intellect is both
thinking and intelligible, so already two and many in the relevant sense.
V.4.2 elaborates activity of essence versus activity from essence, using fire
again, and puts the first beyond *ousia*. Neither passage warrants identifying
the Plotinian first with the Catholic account of subsistent esse and divine
knowledge without separate interpretation. Nor does it refute every account
of divine cognition by defining all cognition as Plotinian Intellect.

## Argument map and exact reuse

The dependence argument has the following distinct commitments:

1. An ultimate first must not need a distinct explanatory prerequisite.
2. A nonsimple is constituted from internal simples and needs them.
3. Those internal relata count as distinct prerequisites in the relation
   excluded by the proposed first.
4. Therefore that first cannot be nonsimple in the pertinent sense.

This is the recognizable conditional pattern already implemented by
`TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverSimple.firstMoverSimple`.
Its exact premises include `FirstUnmovedMoverIsFirstBeing`,
`CompositePosteriorToComponentsReading` and
`CompositeHasComponentOtherThanItselfReading`; the first-being predicate
`IsFirstBeing PriorSimply f` means every y prior to f equals f. The proof uses a
distinct component prior to f to reach a contradiction. It does **not** show
that Plotinus's constitutive need is `PriorSimply`, that a source of exercised
power is that first being, or that every modern fusion belongs to the relevant
composition predicate. Adding another theorem with renamed parameters would
repeat the certificate and leave precisely these interpretation questions open.

The alternative existing
`TruthCore.Results.Case.Catholicism.StageTwo.GodIsSimple.godIsSimple` uses
maximality, `CompositeHasAUnitingCauseReading` and the cause-more-such premise.
It is not the same premise vector: the Plotinian need for internal simples does
not by itself supply a numerically distinct efficient cause of continued esse
or causal superiority. The same-witness connection in
[PR #655](https://github.com/moritzbrantner/truth-core/pull/655) retains its
explicit actual-presence and causal-correspondence interfaces; this source
reading neither discharges nor deletes them. The six mappings in
[PR #661](https://github.com/moritzbrantner/truth-core/pull/661) remain relevant.

For uniqueness,
`TruthCore.Results.Causality.SourceForest.atMostOne_of_confluent` requires weak
connectivity and upstream confluence of a **chosen graph**;
`rooted_of_confluent` additionally requires well-founded edges and population.
No V.4.1 term is silently substituted for that graph. Individual simplicity,
sourcehood and global explanatory coverage are different commitments. The
existing `OneFirstMover.oneFirstMover` instead uses every-perfection,
differentiation in act and an identity/distinctness split. None of those three
is supplied merely by the sentence that a pair would not be one.

The #320 audit (`ATTEMPT-ULTIMATE-GROUND-UNIQUENESS-BRIDGE-AUDIT`) already keeps
nature/individuation, perfection and reciprocal potential-causal scope routes
separate. The current reading adds a sourced positive argument and locates its
burden; it does not manufacture an opaque “simplicity implies uniqueness”
bridge, a new model of all Plotinian commitments, or a duplicate graph proof.

## Strongest rivals under shared questions

| Question | Plotinian answer in this range | Rival reply and remaining burden |
| --- | --- | --- |
| Q-COMPOSITION | Nonsimple reality is constituted from internal simples. | Universal fusions and substantial wholes need not share one sense of composition; the domain interface remains open. |
| Q-UNITY | Genuine first-principle unity excludes combination; derivative Intellect can be one-and-many. | A unity criterion needs defense against immanent organization and whole-first priority; numerical singularity alone is not that criterion. |
| Q-LIFE-SOUL | No argument about an individual soul is delivered here. | Do not derive human immortality or a cosmic mind from the first-principle claim. |
| Q-IDENTITY | First differs from derivatives; another alleged first is rejected by the unity argument. | Plural simples may each be individually one; a global unity or individuation principle is needed to exclude them. |
| Q-GROUNDING | Internal simples are needed by a nonsimple; derivatives reduce to the first directly or through intermediaries. | Schaffer's basic composite cosmos reverses the first dependence direction in its material domain. It is not refuted by parthood syntax. |
| Q-EXPLANATION | The first stands on its own and explains derivative reality through ordered procession. | Standing alone is not yet a noncircular sufficient reason for its actuality; the #312 PSR challenge applies symmetrically. |
| Q-ULTIMATE | A unique genuinely one first is beyond Intellect and ousia. | Existence, uniqueness, scope over all beings, necessity and any Catholic identification remain separately open. |

The priority-monist reply is affirmative: the basic material whole grounds its
real parts, under independently defended priority and tiling commitments
(`STMT-SCHAFFER-BASIC-COMPOSITE-WHOLE`). Plotinus instead gives internal simples
explanatory priority. This is a substantive disagreement about dependence,
not a formal contradiction until a common relation and domain are supplied.
The material restriction of Schaffer's comparison cannot be promoted to a
closed ontology excluding nonmaterial causes.

A plural-simples rival can affirm that composites need constituents while
leaving several independent simples. This is not a newly verified full model
of Plotinus's background. It identifies the missing uniqueness bridge; no
simplicity or sourcehood theorem alone licenses rejecting that rival.
An immanent-form account may explain why organized matter is one without
positing a further uniter of proximate form and matter; its moving/generative
cause question remains distinct. The H.6 comparison in
[PR #662](https://github.com/moritzbrantner/truth-core/pull/662) must not be
converted into a denial of every kind of dependence. The NIHILIST arrangement
certificate likewise reproduces specified intervention histories without
establishing that its primitive individuals lack every metaphysical kind of
composition.

## Premise comparison and next decisive test

Intended and actual root-premise change: **none**. The six prose source readings
add no Lean theorem, inference application, result or root-route edge. Existing
premises are retained; none is treated as established by source attribution.
No route cost is reduced and no rival worldview is refuted by this batch.

The next consequential task is to defend a common-domain interpretation of
constitutive need against whole-first and immanent-form accounts, and to locate
an independently defensible unity/individuation argument against plural
simples. V.4.1's global firstness cannot be installed merely as a convenient
uniqueness definition. VI.9.1–6 is the bounded primary-source successor for the
unity argument; V.4.2's productive-activity account remains read context rather
than a formalized modal principle. The candidate and dossier-linked attempt
preserve these gaps without creating a transcription as supposed progress.
