# Power and existence: two omitted bridges (#319)

`POWER-EXISTENCE-SIMPLICITY-SCOPE-BOUNDARY` is an original, finite
countermodel result, not an interpretation of Aquinas, a positive argument for
God, or a proof of metaphysical possibility. Its role is to identify exactly
what the current finite power-grounding result does **not** prove.

## Two models

Both models have three distinct beings—source, instrumental effect, and a
conserver/component—and two universally accessible worlds. Every recorded
relation connects beings that exist in the relevant world. At the actual
world, an instrument receives causal power from an intrinsic source through
a finite `FinitelyGroundedPower` derivation. The theorem now requires the
actual `source → effect` transmission edge and asserts that the effect has
no independent intrinsic power in the model; the inductive constructor alone
would not have guaranteed either fact. The source receives no power from
another through the *same* transmission relation.

| Question | Model 1: contingent conserved source | Model 2: necessary composite source |
| --- | --- | --- |
| Finite instrumental power derivation | Yes | Yes |
| Original power at source in the selected respect | Yes | Yes |
| Source exists at every accessible world | **No** | Yes |
| Another existent directly supports source's esse | **Yes** | No relation recorded |
| Source has a numerically distinct proper component | No relation recorded | **Yes** |

The first model separates **original power** from **original existence**.
The second separates both modal necessity and the absence of an external
existence supporter from **simplicity**. Neither absence of a recorded support
relation nor de re necessity asserts the stronger Thomistic identity of
essence and esse. A `properPartOf` witness is only one kind of composition.

## Interpretive audit: what do *existence* and *power* mean?

These are distinguishable readings, **not equivalent definitions**. The
source-based Thomistic notions have their own corpus records; the model's
relations are analyst-defined proxies, not interpretations attributed to a
source without evidence.

| Phrase | Current model / scope | Distinct reading still to test |
| --- | --- | --- |
| "x exists" | `ontic.ExistsAt w x`: the candidate x actually occurs at w | Quantifier-based existence/instantiation; the metaphysical act of being (`DEF-ESSE`) |
| "x exists necessarily" | `NecessaryAt`: x exists at each accessible world, even though no reason is specified | Necessary **per se**, intrinsic intelligibility of its existence, or identity of essence and esse |
| "x has power" | `intrinsicPower w x`: a source-status predicate in a chosen power channel | A capacity or disposition that need not be exercised; an ability sustained by something else |
| "x exercises power" | `transmitsPower w x y`: an actual modeled link to y, with `Coherent` requiring that x causes y | Temporal production, continuous simultaneous instrumental efficacy, and act/potency as a metaphysical theory |
| "x's power is underived" | `UnborrowedPowerAt`: no incoming **same-channel** transmission to x | No enabling causes whatsoever; underived actuality of every power; underived being of x itself |
| "x receives existence" | `supportsEsse w y x`: one existing being supports another, as an uninterpreted model edge | Conservation of esse in ST I q.104; derivation of an existence-fact's sufficient reason; participation in esse |
| "x is simple" | `Composite`: x has a distinct proper part | Composition of matter/form, essence/esse, act/potency, substance/accident, or other constitutive principles |

### Important negative results of this audit

1. **Capacity is not exercise.** A being may have a disposition even when
   nothing is happening. The model now includes an actual transmission, but
   still says nothing about the capacity of a dormant being. Its selected
   respect is supplied by the relation itself; no universal quantification
   across respects occurs.
2. **Exercise is not existential independence.** An agent can be actively
   causing one effect while depending on another being for its own existence.
   The first model represents precisely that logical possibility; whether
   such a case is *metaphysically* possible depends on further principles.
3. **World-invariance is not intrinsic explanation.** Necessity as truth
   across possible worlds is distinct from why an existent is necessary.
   A PSR demanding explanatory adequacy must say what qualifies as an
   informative **intrinsic** reason rather than merely labeling existence
   "necessary" or constructing a circular explanation.
4. **No incoming supporter is not a proof of self-subsisting esse.** An
   absent model edge says less than an argued positive account of what
   makes the being exist. Likewise, lack of proper parts would not by itself
   eliminate all the broader kinds of composition.

The choice of metaphysics matters. A Thomistic account asks about the
actualization of potency and the distinction between essence and esse; a
dispositional-powers account can give causal capacity a primitive role; a
Humean account may decline to postulate necessary power-transmission at all;
an explanatory-PSR account can ask for a sufficient reason for a fact even
when no efficient cause of that fact is proposed. None is established or
refuted by these finite fixtures, and each needs its own non-circular
semantics and source-grounded argument.

For a next proof-bearing test, compare the *same actual exercise* under
these rival accounts while holding its bearer contingent and externally
supported. Identify the weakest metaphysical proposition that rules out
that interpretation; only then try to compose it with the established
necessary-per-se, simplicity, and uniqueness results. In particular, do
not insert the conclusion "the source's esse is underived" into the
definition of its causal power.

## What actually remains to be defended

1. **BR-POWER-TO-BEING:** Provide a justified metaphysical principle that
   excludes the first model. A candidate is that direct conservation of the
   bearer's being must transmit its very exercise of causal power *in the
   same relevant respect*. This principle is not already in the finite power
   model and could be rejected by rival accounts of causation. It must be
   sourced and tested without defining `supportsEsse = transmitsPower`.
   `originalPowerBlocksEsseSupportIfItTransmits` verifies the **conditional**
   consequence of that open bridge, with no purported proof of the bridge.
2. **BR-SIMPLICITY:** Even if a bearer exists necessarily and has no external
   conserver, establish why any internal composition requires an actuality
   or support external to it that contradicts ultimate independence. This
   is distinct from the assertion that the bearer has no proper parts.
3. **BR-NECESSITY:** A de re `NecessaryAt` predicate ranges over accessible
   worlds; it is not already "necessary per se", a self-explaining being, or
   an identity of essence and esse.

These are candidate premise investigations, not new theorems. Reuse
`TruthCore.Causality.FinitelyGroundedPower`,
`TruthCore.Results.Causality.FiniteGroundingHasSource.finiteGroundingHasSource`,
and the existing ST I q.3 and q.11 results. The present result does **not**
close #319 or the Catholicism frontier.

**Premise comparison:** no old premises discharged; zero new philosophical
premises admitted; one independently checked logical-independence statement
added. The metaphysical bridges remain open for source investigation.


## Integration reuse audit (2026-10-28)

The #319 integration inventory reuses the existing results rather than
recreating their omission models. This is an audit of encoded propositions,
not a new source reading or a new proof of any metaphysical premise.

| Existing result | Exact reusable consequence | Boundary for the integration |
| --- | --- | --- |
| `TruthCore.Results.Causality.PowerExistenceBoundary.originalPowerBlocksEsseSupportIfItTransmits` | Same-channel unborrowed power excludes external esse support if every support edge transmits that power | The support-to-transmission premise is still open; the existing `powerExistenceBoundary` already contains both requested omission models |
| `TruthCore.Results.Alternatives.RespectSwitch.consecutiveRespects` (#591) | Consecutive motion edges have distinct respects under its four local act/potency premises | It supplies neither a map from power to esse support nor existential independence in every respect |
| `TruthCore.Causality.NecessarilyUnderived.underived_of_lifting_and_excludedMiddle` (#495) | Given necessary existence, actual support well-foundedness, predecessor lifting and explicit excluded middle, some actual necessary individual has no incoming support from an existent at any admitted world | This conclusion says nothing about power origination, composition, explanation tokens, or identity with a different existential witness |
| `TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverSimple.firstMoverSimple` | A first unmoved mover is simple under its first-being, component-priority, proper-component and composition-kind premises (and the no-body premise for its bodily conclusion) | It already derives simplicity; an integration must supply the first-being relation for this same mover rather than repeat the theorem |
| `TruthCore.Results.Case.Catholicism.StageTwo.GodIsSimple.godIsSimple` | Maximality in being, a distinct uniting cause of every composite, and causal comparison exclude composition for a God witness | Neither #495 nor existence-PSR supplies maximality or the God identification |
| `TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryPerSeIsMaximeEns.necessaryPerSeIsMaximeEns` | A necessary-per-se individual equals **each given** maximum in being under the genus-causality, has-being, cause-of-necessity and excluded-middle premises | Its conclusion is universal over a maximum; it does not produce one. `NecessaryAt` and the temporal `IsNecessaryPerSe` remain different predicates |

A precise candidate interface for the remaining **simplicity** connection is
visible without introducing a simplicity flag. Keep the existing
`CompositeHasAUnitingCauseReading Composite CausesIn esse` and the same
individual `x` furnished by `NecessarilyUnderived`. One would need to justify,
for that individual, that a distinct cause `c` of its being corresponds to a
`supportsEsse w c x` edge at some admitted world where `c` exists. The uniting
cause then contradicts the no-incoming-support conjunct. This is a proposed
relation between existing typed vocabularies, **not** a theorem or an admitted
premise in this audit. In particular, the uniting-cause reading alone does not
supply world-indexed presence of its witness. The generic `Ontic` type also
does not impose endpoint soundness on causal edges.

This interface differs from the existing maximum-based simplicity proof,
but it cannot honestly be treated as a discharge until that correspondence is
independently defended. Merely assigning `supportsEsse := CausesIn … esse`
would select a semantic profile, not prove metaphysical applicability.
`PowerExistenceBoundary.Composite` means a proper-part witness; the broader
`Composite` parameter of the q.3 reading is not identified with it here.

The **common-witness** gap also remains: the power theorem and the #495
theorem supply separate existential witnesses. Their sharing a `Being` type
would not establish equality. The PSR vocabulary relates `Reason` tokens to
`ExistenceFact`s and supplies no denotation map making a reason token an esse
supporter. A uniqueness theorem can transport properties only after both
witnesses satisfy the same independently specified domain and relations.

The strongest surviving rivals are the existing contingent conserved power
source, the necessary composite power source, and accounts in which a reason
for existence is not an external cause. They are not ruled out by a change of
labels. No new model or source claim was needed to retain these boundaries.

**Actual premise comparison:** zero statements, arguments, inferences or
results added; zero metaphysical premises added or discharged. Every root
open-premise set is unchanged. At the audited revision, the eight route costs
are 31, 32, 36, 38, 39, 39, 40 and 41 (the designated efficient-regress route is
40). #495 and the necessary-per-se convergence statement are not themselves
open leaves on these routes. The audit therefore supplies a reusable
interface and rejects duplicate work; it makes no root-closure claim.


## Same-support-source composition after #633

`TruthCore.Results.Causality.UnderivedCommonSource.named_support` now
connects `NamedNecessarilyUnderived m R w n` (#608) to source uniqueness
without identifying support with ordinary causation. The task module's
`actualSupportGraph m R w` reuses `Actual m w` and the existing `Graph`,
with edge `R w source target`. Named underivedness makes **this same n** an
actual source. The proof imports and applies
`TruthCore.Results.Causality.SourceForest.atMostOne_of_confluent` (#633).
It concludes that n is a source and every actual R-source at w equals n.
`exists_support` unpacks exactly `NecessarilyUnderived m R w` (#495),
retaining that witness's named necessity and no-support properties alongside
its unique selected-world R-source property.

The primary direct premise vector is:

- `STMT-NAMED-NECESSARILY-UNDERIVED` (or, for `exists_support`,
  `STMT-NECESSARILY-UNDERIVED`);
- `STMT-SOURCE-FOREST-WEAKLY-CONNECTED`, instantiated on
  `actualSupportGraph m R w`;
- `STMT-SOURCE-FOREST-UPSTREAM-CONFLUENT`, instantiated on that same graph.

This is useful proof assembly, not independent defense of any premise.
Named actual presence supplies population; it is not inferred from necessity
on a non-reflexive frame. There is no ordinary-world well-foundedness,
maximality, reciprocal potential causation or accessibility assumption.
Uniqueness is at this **one selected world** and on its actual-node support
carrier. No source at an inaccessible or different world is identified, and
no finite upstream path from every actual node to n is asserted.

The optional ordinary-causal corollaries `named` and `exists_common` instead
use `actualGraph m w`. Their direct vector has the same named/existential
underived premise, causal-graph connectivity and confluence, **plus**
`STMT-ACTUAL-CAUSE-SUPPORTS-ESSE`. That last interface is explicitly OPEN:
every ordinary causal edge whose source and target both exist at w gives an
R-support edge there. It is one-way, limited to actual endpoints at w, and
neither source-attributed nor a definition identifying R with Causes. It
converts the named underived witness into an ordinary-causal source before
the same imported uniqueness theorem applies. Nothing identifies either
source with the original instrumental-power source unless that witness is
separately proved to have the corresponding graph-source property.

The existing V-shaped `SourceForest.fork` remains the decisive rival to
connectivity alone: its two distinct roots share a dependent target, so it
is weakly connected and even well-founded while both roots are sources.
The imported confluence uniqueness theorem excludes that two-root profile
when confluence is added. This is a conditional graph constraint, not a
claim that the metaphysical support relation is confluent. The existing
source-free integer chain explains why graph uniqueness alone supplies no
source; here the underived witness, not a hidden WF premise, supplies one.

**Premise comparison:** the support route retains the existing named or
existential underived premise and adds the two explicit structural premises
to that conditional argument; the ordinary-causal alternative additionally
requires the open causal-to-support interface on its distinct graph. Zero
metaphysical premises are independently established or discharged. These
assembly results create no connection to God, simplicity or personhood, and
make no root-frontier change. Two end-to-end certificate records distinguish support from ordinary-causal
semantics; the named and existential-fiber lemmas are implementation helpers,
not additional corpus arguments or independent philosophical discoveries.


The advertised end-to-end results are `from_union` and `causal_from_union`.
Both **import and apply** the existing
`TruthCore.Results.Causality.NecessarilyUnderived.PositiveUnion.checks`,
rather than adding its proved conclusion as a fresh ordinary premise. Their
exact retained five-premise vector is
`STMT-KANT-CONVERSION-NECESSARY-WITNESS`,
`STMT-ACTUAL-MODAL-REFLEXIVITY`,
`STMT-NO-CONTINGENT-GROUND-OF-NECESSARY`,
`STMT-WELL-FOUNDED-UNION-NECESSARY-SUPPORT`, and
`STMT-EXCLUDED-MIDDLE`. The primary support-graph route adds connectivity and
confluence (seven direct premises); the ordinary-causal route adds its
corresponding graph constraints and the open map (eight direct premises).
The necessary-support **union WF is retained**. Only ordinary-world causal WF
is absent. Neither configuration establishes its five original metaphysical
inputs or the structural extensions; root open premises remain unchanged.

## Same-witness noncomposition after #636

`NECESSARY-UNION-COMMON-NONCOMPOSITE` imports and applies the exact
`TruthCore.Results.Causality.UnderivedCommonSource.causal_from_union`
theorem. It retains that theorem's eight premises and its **same named
individual**, including necessary existence, absence of R-support and
unique actual causal sourcehood. Its additional conclusion is
`¬ Composite n` for the supplied q.3 predicate. It neither supplies a God
identification nor asserts the other classical attributes.

Three further direct premises do the work:

1. The existing `CompositeHasAUnitingCauseReading` gives a distinct
   `CausesIn c n esse` witness for a composite n.
2. `UnitingCausesPresent` says such a cause of an actually existing target
   itself exists at the selected world.
3. `UnitingCausesAreActual` says such a cause with actual endpoints gives
   an ordinary `m.Causes w c n` edge.

That incoming edge contradicts sourcehood of this same n. Both new interfaces
are explicit **open analyst commitments**, not attributed to Aquinas and not
asserted as identities between `CausesIn`, `m.Causes` and R. The proof does not
need the existing maximum-based route's maximality or causal-comparison
premises, nor the first-mover route's first-being premise. This compares
conditional routes; it does not defend one by counting its premises.
Necessary-support **union well-foundedness remains an input** through #636.
Connectivity and confluence are retained for its unique-source conclusion,
even though noncomposition alone requires only sourcehood.

The whole pinned article `AQUINAS-ST-I-Q3-A7` was materialized and read.
Its third proof says that a composite requires a cause uniting what is diverse
in itself, and that God has no cause as first efficient cause. The existing
claim already records reading that as a distinct cause of being. Neither the
passage nor the old Lean type supplies the modern `Ontic` world's endpoint
existence or the relation correspondence. Hence this connection creates no
new historical claim and provides no independent source defense of its two
interfaces. OCR defects elsewhere in the pinned transcription do not alter
the consulted third-proof clause; no source bytes were repinned.

`UNITING-CAUSE-INTERFACE-OMISSION-CONTROLS` separately witnesses both gaps:

- In `absentCause`, false is the only existing individual and is necessarily
  present, R-underived and the unique actual source. It is composite and has
  the alleged uniting cause true. The world-local causal edge is recorded,
  but true is absent. Presence fails; the actual-node graph has no incoming
  predecessor. This deliberately violates endpoint soundness: it tests the
  weaker encoded types, not a genuine cause by a nonexistent thing.
- In `differentCause`, both candidates exist and false causes true. False is
  again the same necessarily underived unique actual source and composite.
  The atemporal alleged uniting cause is true-to-false; this does not map to
  an actual causal edge. Presence holds and correspondence fails.

Both retain the existing q.3 uniting-cause reading. Their distinct cause need
not be outside the composite's parts: `c ≠ n` is numerical distinctness only.
No material-fusion, parthood or temporal claim is introduced. They establish
logical omission boundaries, not metaphysical possibility or a refutation
of actual composites. The original power-source countermodels remain the
stronger warning against transferring underivedness in one respect to whole
being without any interface.

**Actual premise comparison:** all eight #636 premises retained; the q.3
uniting-cause statement plus two open interfaces added to this conditional
connection. Zero open root premises independently defended or discharged;
no existing root argument rewired. Source correspondence, cause actuality,
the relation R's metaphysical applicability, and the original regress
premises remain open. The adjacent PSR audit in
[psr-scope-countermodels.md](psr-scope-countermodels.md) independently preserves
the distinction between an explanation and a necessitating reason; the
present causal connection does not discharge that explanatory bridge either.
