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
read before these claims. Five readings concern V.4.1; the Intellect reading concerns V.4.2.
The remaining text of V.4.2 supplies context. No English translation is
used as the witness. The first reading preserves the source’s requirement that
such a first exist; recording that requirement does not establish existence. VI.9.1–6 was not evidence for the initial V.4 batch; its subsequent complete
reading and separate witnesses are recorded below.

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

The opening of V.4.2 distinguishes the first from Intellect: intellection turns
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
uniqueness definition. The bounded VI.9.1–6 successor reading is now complete, as recorded below;
V.4.2's productive-activity account remains read context rather than a formalized
modal principle. The dossier-linked attempt preserves the remaining gaps; the
exhausted source candidate has been removed.


## Completed successor reading: Enneads VI.9.1–6 (2026-10-31)

The earlier V.4 batch above did not read this range. The six complete chapters
of VI.9.1–6 have now been pinned, materialized and read in sequence as Greek
primary text, without using an English translation as evidence. New passage IDs
are **PLOTINUS-ENN-VI-9-1**, **PLOTINUS-ENN-VI-9-2**,
**PLOTINUS-ENN-VI-9-3**, **PLOTINUS-ENN-VI-9-4**,
**PLOTINUS-ENN-VI-9-5**, and **PLOTINUS-ENN-VI-9-6** in
`corpus/passages/plotinus-enneads-vi-9-1-6.json`. They reuse the existing source
**PLOTINUS-ENNEADS**, Volkmann/Teubner1883–1884,
`urn:cts:greekLit:tlg2000.tlg001.1st1K-grc1`, First1KGreek revision
`ed91552c52530c8f5a3ddf2dd767e899372a804c`, path
`data/tlg2000/tlg001/tlg2000.tlg001.1st1K-grc1.xml`, blob
`7b5a33eade9341bfabd4a2ac6a3a7551756f3128`. Each CTS selector is book6,
chapter9, section1 through6 respectively. No source-derived claim or Lean
statement was added for this reading; this argument map preserves findings for
review before formalization.

### Sequential reading and positive argument

| Complete chapter / precise internal locator | Positive source reasoning | Exact inference boundary |
| --- | --- | --- |
| VI.9.1, opening through army/chorus/herd, house/ship, continuous magnitude, organism, health/beauty/virtue examples | Unity is required for each thing to be what it is; dispersal or loss of relevant organization destroys that thing's former identity. Health, beauty and virtue also involve coherent unity. | Identity of an organized whole is the demonstrated explanatory target. The examples do not establish that its material constituents cease to exist, nor that every intrinsically simple individual gets unity from an external giver. |
| VI.9.1, ensuing soul discussion through the chapter's conclusion | Soul organizes and gives unity, but the text distinguishes what gives unity from unity itself. Soul is one yet has multiple powers—reasoning, desire and perception—even if it is not made of parts; these are held together. Its own unity therefore comes from another. | This is a structured case against soul as absolute first, not a purely verbal “two would be many” argument. It assumes a real explanatory distinction between soul and its unity and the derivative status of its power-unity. It does not by itself show every proposed simple root has such powers or such a distinction. |
| VI.9.2, proposed identification of being/Intellect with unity, then human example and whole intelligible being | Human essence has rational-animal and other constituents; comprehensive intelligible Being contains all beings, life and Intellect; Forms and Intellect are multiple. A Form's constituents are prior to what is constituted from them. Thinking/intelligible duality also prevents Intellect from being the absolutely simple One. | Constituents-to-constituted priority supports the existing composition argument. The intelligible-domain premises must not be promoted to “every roster member in ExistsAt has multiple real constituents”. The argument does not independently classify two proposed unreceived whole essences as derivatives. |
| VI.9.3, epistemic difficulty, ascent, then description of the first before Intellect/Being and causal language | Form-dependent cognition struggles to grasp what is prior to form. The first is described as generative of all without being one of its products; calling it cause concerns what recipients have from it rather than adding an accidental property to it. | Generative reach is a substantive part of the source ontology here. The paragraph does not derive universal causal reach merely from absence of components or from modal necessary existence. |
| VI.9.4, presence beyond discursive knowledge, instruction and preparation | Discursive cognition introduces plurality; teaching directs the reader toward a unity/presence not exhausted by a proposition or description. The source presents a path of preparation and contemplative recognition. | The claimed presence is not an extra machine-checkable premise-truth warrant and is not supplied by an assistant's agreement. It provides no independent numerical individuation inference between rival simple sources. |
| VI.9.5, explicit audience restriction; ascent through soul and intelligible multiplicity; explanation of the name One | The argument addresses those already allowing a nonbodily nature, soul and Intellect, rather than those explaining reality only through bodily causes/chance. Intellect is an undivided-yet-differentiated intelligible plurality, so it is not first. The first produces beings while remaining itself; the name One points toward simplicity and is distinguished from point/unit as quantitative principles. | The range supplies a qualified philosophical argument, not an unconditional conclusion from neutral observation alone. Its producer-of-being ontology and primary/derivative order remain substantive. The distinction from numerical unit prevents treating its capitalized name as a ready-made cardinal uniqueness proof. |
| VI.9.6, nonquantitative infinity, then self-sufficiency/need argument and final discussion of cognition/good | Infinity concerns unrestricted power, not traversing an endless magnitude or number. A multiple constitution needs its constituents, their coexistence and unity; a completely self-sufficient principle cannot have that need. The source distinguishes what is first from what seeks its own existence, goodness or position, and rejects relational cognition as introducing otherness into the first. | This adds a positive need-based defense of simplicity. It does not show that two individually intrinsic simple candidates each have multiple constituents merely because they form a pair. The first's self-sufficiency and universal first-principle status are not the same as a bare no-incoming-edge predicate. |

The strongest reconstructed argument actually delivered by this range is:
organized and intelligible multiplicities need their unity and constituents;
soul and Intellect are such multiplicities despite being more unified than
bodies; the fully self-sufficient first cannot be constituted that way; hence
it is prior to them and not identical with soul, Intellect or a compound Form.
This provides genuine grounds to investigate the parts/whole dependence and
self-sufficiency commitments, rather than merely attributing a first's
simplicity. Its crucial premises still require philosophical defense and a
faithful map to the case's priority/dependence relation.

### Common numerical source and the strongest plural reply

Keep three propositions distinct: each entity must have the relevant unity;
a derivative unity needs an appropriate unifying source; and ALL numerically
distinct unities derive from the SAME numerical source. The first two alone
leave room for several intrinsically unified independent simples. VI.9.1
asserts and explains derivative unity for bodies and soul, VI.9.2 extends the
analysis through the intelligible hierarchy, and VI.9.3–6 situates them under
one generative first. This is substantially richer than the V.4 sentence
about a pair not being one. It nevertheless does not supply a separately
defended individuation step excluding two proposed intrinsic simple whole
natures under the current root semantics.

The strongest reply grants that armies, organisms, souls with multiple powers
and comprehensive Intellect need an explanation of their coherent unity. It
denies that every individual simple root is one such multiplicity, or that
being one must mean receiving unity from one common numerical object. Two
unreceived candidates can each be internally one even though their aggregate
is plural. Applying VI.9.6 to the aggregate does not show either individual
needy without an additional whole/individual or common-domain premise. A
similarity in the predicate “one” supplies no common giver by itself. These
are rival commitments awaiting assessment, not a new verified Plotinian model.

A stronger reading treats genuine unity itself as one transcendent explanatory
principle and all other alleged individuals as participations. This reading
fits the text's definite-One and procession framework, but its universal
coverage and first-principle individuation are precisely what the plural-simples
reply challenges. They must not be installed as an opaque “all things have one
source” premise and advertised as a newly defended exclusion. No passage in
this range was found showing that a second intrinsic simple must acquire a
numerically distinct constitutive/prior factor solely because it is a second.
This is a bounded reading conclusion, not a claim that Plotinus nowhere offers
another argument or that his unity account is false.

### Being, priority and modal boundaries for the current root

Plotinian Being in VI.9.2–3 is often the structured intelligible reality of
Forms, life and Intellect. The first's being “beyond Being” denies its placement
in that articulated intelligible order. It must NOT be translated as absence
from the corpus's broad `ExistsAt` extension or as literal nonexistence.
Conversely a broad entity/roster predicate does not give the rich intelligible
multiplicity needed by the source argument. The One is not automatically the
Thomistic equality of the q3 Profile's essence/esse maps, and refusing
relational intellection in VI.9.6 cannot be imported into a Catholic divine-
intellect conclusion without separate interpretation.

Likewise ontic firstness, common causal coverage and modal necessity remain
separate. The text's constituent priority is not automatically
`PriorSimply`, its generative reach is not automatically the selected
world-indexed grounds relation, and its self-sufficiency is not a proof of
`NecessaryAt` over accessible worlds. VI.9.6's necessity-style explanatory
language is not an encoded Kripke quantifier. Nothing here establishes
all-world absence of support, numerical identity of all necessary individuals,
or explanatory adequacy of the newly supplied actual root.

`RootWithoutLimitingPrinciple`-style absence of composition, represented
esse/essence nonidentity and distinct simple predecessors does not identify
its witness with the One. The source's real nonbodily power/form plurality
would need to fall under the SAME supplied composition/dependence notions
before existing simplicity certificates apply. If that correspondence is
established, the existing first-being composition inference is reusable; a
new renamed theorem would add no source defense.

### Disposition of the exhausted candidate

The candidate **PLOTINIAN-DEPENDENCE-UNIQUENESS-BRIDGES** named V.4.1–2 and
VI.9.1–6. Both prescribed ranges have now been read and their substantive
findings persisted; it is removed from the source queue rather than retained
as a philosophical-gap tracker. No arbitrary successor source is seeded.
The exact remaining source-choice gap is a primary argument that derives
common numerical sourcehood, or a distinct constituent/prior ground for a
second intrinsically simple whole candidate, without assuming universal
participation in the already unique One. The unread remainder VI.9.7–11 has
not been assessed as supplying that bridge, and is not cited as evidence or
queued merely because it follows numerically.

Actual premise comparison: no added philosophical premise or claim, no
inference/Lean theorem or root-route edge, no premises discharged. Existing
composition and unity interfaces are retained. The new witnesses and argument
map advance the source investigation while leaving numerical common-source
coverage, its applicability to this root, modal necessity and Catholic
identification open. No formalization is proposed until one of these precise
bridges is independently supported.
