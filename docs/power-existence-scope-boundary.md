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

## Shared interfaces for the four-area foundation investigation

The inventory below fixes the reuse boundaries for the owner's dependence,
composition, individuation and necessity investigation. It inspects existing
declarations and dossiers, not new primary-source evidence. It does not identify
an arbitrary mathematical interpretation with a metaphysically adequate account.

| Arena | Reuse | Interface still requiring justification |
| --- | --- | --- |
| World-relative existence and causation | `German.Kant.CosmologicalInference.Ontic` has independent `frame`, `ExistsAt` and world-local `Causes` fields. `NecessaryAt` quantifies over accessible worlds; `NecessaryBeing` additionally supplies an actual existent. | Actual presence does not follow from a non-reflexive box, and `ExistsAt` does not analyze Thomistic esse. There is no separate `Modal.Ontic` declaration. |
| Power and existential support | `PowerExistenceBoundary.Profile` separates `transmitsPower`, `supportsEsse`, `intrinsicPower` and `properPartOf`. Its `Coherent` conditions give endpoint presence and transmission/support-to-ordinary-cause inclusions. | Underived exercised power in the selected respect is not independence of the whole being. The inclusions have no converse. |
| Named underivedness | `NamedPotentialCauser.NamedNecessarilyUnderived m R w n` retains the same actual necessary n and excludes incoming R edges from existing sources at every admitted world. | The no-support quantifier is broader than root accessibility. It is not uniqueness, an intrinsic reason, or absence of a different causal relation. |
| Explanation | `ExistencePSR.Model` relates `Reason` tokens to `ExistenceFact`s while preserving the underlying `Ontic`. `Sound` supplies existence-factivity; `WorldwiseExplanation.StableExplanation` and `ReasonInvariant` are guarded by existence at the target world. | An `intrinsic` tag is not essence–esse identity or adequate intrinsic explanation. Stable explanatory assignment is not `BruteFoundationExplanations.NecessitatesExistenceAt`. Reason tokens are not automatically concrete causes. |
| Conservation | `DEF-PER-SE-ESSE-CONSERVATION` and `STMT-DIVINE-ESSE-CONSERVATION-CONTINUES-GIVING-ESSE` record the q.104 a.1 account; `DEF-CAUSE-OF-BECOMING` and `DEF-CAUSE-OF-ORIGIN` retain different roles. | This conservation record supplies no Lean conservation relation or theorem equating it with `supportsEsse`, `CausesIn`, production at successive instants, or a nonexistence counterfactual. |
| Composition and priority | `Article7.MatterFormAndEsseEssenceAreCompositionsReading`, `CompositePosteriorToComponentsReading` and `CompositeHasComponentOtherThanItselfReading` feed `FirstMoverSimple.firstMoverSimple`. | The implemented kind inclusions cover matter/form and distinct essence/esse. The primitive q.3 `Composite` remains broader than proper material parthood. Quantitative and genus–difference realization are not supplied by these inclusions. |
| Genus and difference | `MetaphysicsIII3` supplies strict `IsGenus`, `DifferentiaOf` and `SaidOf` readings; q.3 a.5 adds `InGenus : Being → Term → Prop`. | Conceptual predication does not itself give a real component, a potency/act principle, or an efficient cause. No generic classified-bearer structure is needed merely to put these parameters beside the q.3 a.4 profile. |
| Essence and efficient esse-causation | q.3 a.4 `Profile` represents `essenceOf` and `esseOf` in a common `Principle` sort. `distinctEsseExternalFromExhaustion` reuses two separately open causal premises. | This result is explicitly a transcription of the exhaustive dichotomy and its exclusion. Its efficient self-cause exclusion does not refute all intrinsic or noncausal reasons. The profile is not modal. |
| Individuation | `Q11NatureUniqueness.godIsOneFromNature` uses injectivity of `suppositumOf`, suppositum/nature identity, and one common nature; its three Bool omission controls remain the exact reusable controls. | Mere necessity, absence of represented components and equality of an individual's own essence and esse do not supply a common nature or injective individuation. The three separate controls do not already certify a joint two-necessary-simple-being model. |

Two minimal shared declarations make the direct connection explicit.
`TruthCore.Causality.ExistenceActuality.ExistingInActAt` retains its one-way
actuality role. Its exact type is
`∀ x, m.ExistsAt w x → InAct x esse`, with `m`, `InAct`, `esse` and `w`
supplied. This is the open `STMT-EXISTING-IN-ACT-AT` interface, not an axiom or
an asserted equivalence. It supplies target actuality for a q.3 a.4 application;
it does not supply the actual presence of a proposed cause, causal-to-support
correspondence, all-perfection actuality, necessary existence, or essence–esse
identity. `EXISTENCE-TO-ACT-IN-ESSE-INTERFACE` records the independent
interpretive obligation. Shared authorship is integrated with the consuming
necessity/actuality result rather than creating a second theory profile.


`ExistenceActuality.ActualEsseCausesSupportAt m R CausesIn esse w` is the
separate direct interface: from `m.ExistsAt w c`, `m.ExistsAt w x`, `c ≠ x`
and `CausesIn c x esse`, it gives `R w c x`. This is the open
`STMT-ACTUAL-ESSE-CAUSES-SUPPORT-AT`, not an identification of causes and support.
It does not mention `m.Causes`. In particular, ordinary event-causal edges need
not all be existence-support edges. Both endpoints' presence is an antecedent,
not a conclusion, and the act-in-esse interface remains independent.

The stronger pair of cause-in-esse-to-ordinary-cause correspondence and
`ActualCauseSupportsEsse` can supply this direct map by composition. The
ordinary route retains its original eleven-premise Challenge; a separately
frozen direct Challenge replaces that pair by the qualified direct interface.
No existing Challenge is weakened. The consuming investigation must demonstrate
its claimed strictness with an actual model and preserve the independent
cause-presence premise. A possible ordinary event cause that is not a cause of
esse is not ruled out merely by calling the bearer underived with respect to R.

The direct q.3 a.4 route can therefore be compared with the q.3 a.7 route
without silently identifying their premises. A named underived actual bearer,
target actuality, the source's distinct-esse external-cause conclusion, and
explicit cause-presence/correspondence interfaces can exclude distinct esse.
Constructively that yields a double negation of essence–esse equality;
positive equality requires an appropriate further logical principle. This
paragraph identifies the proposed consuming argument, not a newly certified
theorem in this inventory. The actual result must import the existing q.3 a.4
theorem and retain its open causal premises.

The live joint rival model uses two actual necessary roots with a common actual
dependent effect. Deriving represented simplicity through the existing
`firstMoverSimple` theorem is stronger than assigning a free `Simple` flag,
but a proper-component interpretation still does not cover all q.3 composition
kinds. A fork's common dependent target does not supply upstream confluence.
Equal represented perfections also do not establish numerical identity: the
Q11 common-nature/individuation or differentiation-in-act premises must be
stated and defended separately. This inventory approves no new metaphysical
possibility claim and does not certify the worker's forthcoming joint model.

**Premise comparison:** two analyst-defined interfaces are added as explicitly
unproved vocabulary items. No philosophical premise is endorsed, removed or
discharged; no new root route, source claim or consequence result is added by
this inventory. The existing root-path commitments remain open. In particular,
q.104 conservation's formal relation, genus–difference realization, the actual
cause mappings and the common-nature/individuation bridges remain live gaps.
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

## Five questions for direct existential support (#680, #686)

This audit concerns **R itself**, not the validity of the theorems parameterized
by R. It reuses `PresentEsseSupport`, `ActualNecessaryWellFounded`,
`PowerExistenceBoundary.Profile` and its existing boundary theorem; it does not
introduce another dependence relation. The actual-world theorem (#686) and
the union theorem used by #680 remain conditional consequences. Their intended
metaphysical interpretation has the following status.

### 1. What would R mean in ordinary reality?

The proposed reading is: **c is now actively responsible for b's existing at
all, as this very bearer, rather than merely for something b does or a state b
has.** The action is a cause of b's being, not only an earlier action making b
begin. “Now” selects the actual situation; it does not require repeated
creation, temporal succession in the giver, or instantaneous physical action.
This prospective concurrency is an interpretive requirement, not a consequence
of `ExistsAt w x`: Ontic has no time argument, and w may represent a complete
history. The existing `HistoryTimeScope` controls (#622) separate World and
Time; world-existence does not imply presence at a selected time or concurrent
activity. Any temporal application needs its own justified history/time and
causal interpretation. Worlds must not silently be treated as times.
“Direct” selects the esse-giving role itself, rather than every condition that
allows it to operate. This is an intended causal reading, not a completed
reductive analysis or an observation already established for every bearer.

For a positive application one must identify c and b independently, fix what
counts as the same bearer b, and explain the actual activity attributed to c
and why its effect is that bearer's existence. That last explanation must
exclude the weaker diagnosis that c changes a persisting bearer, maintains an
arrangement or removes a threat. Calling the activity “existence giving” does
not supply that explanation. R would be false on this reading where only
those weaker roles occur; a dispute over whether any giver is needed remains
a dispute over R's instantiation, not a reason to redefine the weaker role as R.
A claim that b would disappear without c can be evidence within an independently
specified causal account, but is not sufficient by itself: removal may destroy
b, remove a protector, or track a common cause. Mere covariance supplies no
direction or directness either.

There is an important gap between this interpretation and the exact code.
`PresentEsseSupport m R w c b` is only `m.ExistsAt w c ∧ R w c b`.
It does not establish the target's presence, distinctness, a causal mechanism,
or any of the ordinary-language conditions just described. The necessary-bearer
restrictions in the consuming arguments supply their own guards. A faithful
application must justify the relevant target presence and interpretation;
the wrapper's name cannot certify them. Self-support has not been excluded by
definition: the existing formal results exclude it when their WF premise holds.

### 2. What are clear examples, and which are only analogues?

No undisputed empirical example of **directly maintaining a substantial bearer's
existence as such** is supplied by the current corpus. This is a limitation of
the supplied examples, not a finding that R has no instances. Neither empirical
observability nor absence of philosophical disagreement is a requirement for
justification: a defended philosophical argument could establish an instance
or property despite dispute. The proposed central
instance, God continually giving creatures esse, is a substantive metaphysical
thesis whose defense cannot assume the conclusion of the regress argument.
The materialized `AQUINAS-ST-I-Q104-A1-EN`, response's paragraph beginning
“Now every creature may be compared” and reply 4, articulates that thesis through
participated being and continued esse-giving; it does not make it an independent
empirical observation. The article's complete objections and replies were reread
for this audit. The source's account and its truth retain separate statuses.

The following are useful **scope tests**, not new physical research claims or
verified R-instances. A powered lamp's illumination can illustrate a causal
exercise requiring an ongoing supply. The lamp's ceasing to shine does not
establish that the lamp ceases to exist. A maintained current or oscillation
can illustrate a continuing process; identifying b with that process changes
the target from its enduring material bearer. An arrangement maintained by
pressure, tension or control illustrates dependence of a structural state;
the continued existence of the materials is a different question. Life support
raises the more serious question whether an organism ceases to exist at death,
but neither that identity judgment nor the distinction between preventing
lethal corruption and directly giving esse follows from the phrase “life
support.” These cases need not be denied to prevent their being overread.

If processes or states are admitted as beings, some of these may become
candidates for a restricted R. One must then defend their identity criteria,
what maintains that very process or state, and its causal account. A theorem
about such bearers would concern that restricted domain. It cannot be exported
to every substance, or to the material subject that survives the process,
without a further argument. Naming light itself as b does not silently turn
an illumination example into conservation of the air's existence.

### 3. What is excluded, including near misses?

The q.104 a.1 response distinguishes preserving a child from fire, building a
house, and directly preserving being; objection 2 and reply 2 address persistence
after a maker ceases. Those distinctions prohibit an inference from “causal
condition for b” to “direct giver of b's esse.” A builder's completed production
is not already concurrent support; a guardian's prevention of corruption is
not already esse-giving. A prerequisite, fuel, permission or environmental
condition is not made direct merely because it is indispensable in a selected
scenario. A cause of movement, warmth or exercised power is not on that account
a cause of the bearer's being. The existing
`originalPowerBlocksEsseSupportIfItTransmits` states the conditional bridge
needed for one such transfer; it does not establish that bridge.

Nor are constitutive ground, efficient cause and adequate reason synonyms.
That the arrangement accounts for a house *as a house* leaves open whether the
arrangement is an agent, whether the parts are direct existential supporters,
and whether an additional uniting cause exists. A law or an explanation token
can explain a fact without being an existing individual actively conserving
its bearer. The existing PSR and q.3 vocabularies must retain their distinct
roles. Conversely, excluding those explanations from this **causal** R does
not refute them as accounts of persistence. It limits what the R-theorem answers.

### 4. Which structural properties have independent justification?

None of the following is independently established by choosing this meaning.
They must be defended for the same R, bearers and scope used in the theorem.

| Proposed property | Present status and exact burden |
| --- | --- |
| Actual endpoint presence | Intelligible for an actual causal application, but not supplied for b by `PresentEsseSupport`; the typed cause-presence and target-actuality interfaces remain separate. |
| Irreflexivity and asymmetry | OPEN. The thought that a recipient cannot confer its own existence needs an argument about causal priority in the same respect. Mutual dependence of activities or components does not settle whether reciprocal **esse**-giving is possible. Excluding efficient self-causation alone does not exclude a two-member cycle. WF implies these restrictions mathematically; that implication cannot defend WF. |
| Transitivity | OPEN, and potentially inappropriate for a **direct** relation. If c directly supports d and d directly supports b, c may be an indirect supporter of b without another direct edge. Closure under chains requires an independent account, or a separately stated indirect conclusion. Replacing R by its transitive closure changes the intended immediate/direct reading and must not happen silently. |
| Actual necessary-support WF (#686) | OPEN. Finite observed chains, local asymmetry and absence of known cycles do not rule out a beginningless upstream dependence series. The claim needs a reason why every such series must reach a nondependent source within this same existential sense. A theorem extracting a source from WF proves no such reason. |
| Union necessary-support WF (#680) | OPEN and stronger in scope. Even an independent defense at each world would not rule out a descending chain assembled from different worlds. The existing rotating-union controls already isolate that omission. A cross-world compatibility argument is required; an actual physical chain supplies none. |
| Necessity inheritance | OPEN. Actual support of a necessary bearer does not alone entail that this particular supporter exists at all accessible worlds. That requires the same supporter's indispensability across those alternatives, rather than interchangeable or optional support. The global no-contingent premise additionally quantifies over every admitted support world; the actual restriction does not. |

A defense must not build asymmetry or WF into the English definition and then
announce the needed premise as proved by that definition. Conversely, directness
is no license to assume transitivity. Independent arguments about causal
priority, essential dependence or infinite series may address these burdens,
but their applicability to existence as such remains part of what they must
show. Pure mathematical WF lemmas settle only their conditional consequences.

### 5. Why would the physical-to-existential abstraction survive?

The current evidence does **not** license that transfer. Abstraction is justified
when the discarded details do no work in the inference being preserved. In a
physical sustaining example, the relevant work can be done by an energy supply,
a dissipative process, a selected state variable or an identity criterion for
an organized system. Removing those details leaves no demonstrated reason that
a persisting bearer needs a concurrent giver of existence. A physical law that
settles when illumination stops does not by itself settle when the lamp,
material subject or substance ceases to be. This is a missing preservation
argument, not a technical inconvenience addressed by a more general graph.

A successful transfer needs (a) an independently supported account of why the
same bearer's existence is received or presently actualized rather than merely
its activity; (b) a reason that the causal dependence is on a present giver,
rather than adequately explained by prior existence plus no destructive change;
(c) a justified map to R and the supplied `CausesIn ... esse`, with their actual
endpoints; and (d) separate defenses of whichever order and modal restrictions
the chosen result consumes. A participation or essence–esse argument is a
candidate for (a), but only after its premises and causal exhaustiveness are
defended; merely applying that vocabulary to a lamp supplies no bridge.

The live replacement is the already inspected existential-inertia account:
prior existence together with no destructive causal change can explain
persistence without concurrent efficient sustenance. Its strongest form is
not “no explanation.” The Feser response recorded in
[eternity-dependence-connection.md](eternity-dependence-connection.md#existential-inertia-the-live-rival-and-the-remaining-bridge)
contests the sufficiency of that explanation through present actualization
and the alleged dependence of persistence powers on their substances. Those
are discriminating arguments, but their direction and actualization premises
remain disputed. No new source attribution or rival refutation is claimed here.

**Disposition and premise comparison:** retain R as a stipulated parameter for
the existing conditional results; withhold their use as actual metaphysical
evidence until the stated interpretation and property burdens are met. There
is no newly defended bridge, no source claim, no Lean type change and no
additional admitted premise. All root-route open-premise sets are unchanged
(delta zero). This audit narrows the proposed reading and identifies where
analogy stops; it neither discharges WF nor denies that a later independent
metaphysical argument could establish existential conservation.

## Same-respect self-actualization: reusable proof and application limit

On `research/lean-existential-self-actualization-20261031`, the two existing
First Way intermediate inferences are now separately exposed as
`SameRespectActualization.noSelfMotion` and `movedByAnother` under
`TruthCore.Results.Causality`. The source is the unchanged first-way reading
of ST I q.2 a.3 co.; the complete pinned `AQUINAS-ST-I-Q2-A3` passage was
materialized and reread. No new source claim or philosophical predicate is
introduced. The new result records consume the **existing** statement and
inference IDs rather than creating synonyms.

The four-line brief is:

- **Target:** make the same-respect no-self step reusable in an existential
  actualization investigation without strengthening its conclusion.
- **Reuse:** the existing three act/potency premise statements, mover-existence
  premise, no-self/moved-by-another statements and inference applications.
- **Missing step:** standalone Challenge/Solution/Comparator contracts and
  composition by both strong and relative First Way proofs.
- **Premise comparison:** identical end-theorem hypotheses and conclusions;
  no philosophical premise discharged. Existing end Challenges stay frozen.

The first theorem derives

```
∀ x r, MovedIn x r → ¬ MovesIn x x r
```

from `MovedOnlyAsInPotencyReading`, `MovesOnlyAsInActReading`, and
`NotActAndPotencyInSameRespectReading`. A self-mover that is being moved in
that respect would be both actual and potential there. The second theorem
adds the separately stated existence-of-a-mover law and derives

```
∀ x r, MovedIn x r → ∃ y, y ≠ x ∧ MovesIn y x r
```

The existential witness comes from the mover-existence premise; no-self only
makes that witness distinct. The two First Way Solutions import these results
instead of repeating both local derivations. The regress proof, its premises,
and the end theorem types are unchanged.

For an existential application, one may instantiate `r` with a supplied
`esse` respect **only after** justifying the interpretation of `MovedIn` and
`MovesIn` there. This theorem does not give `MovedIn x esse` from
`ExistsAt w x`, from `InAct x esse`, or from modal contingency. Nor does it
identify `MovesIn` with continuing existential support, a complete-history
explanation or a noncausal intrinsic reason. The existing actuality-as-being
law has direction from act in a respect to being; it supplies no reduction
premise in the reverse direction. The source's same-time/same-respect contrast
is represented at one implicit context, not a license to identify two times.

Three claims must remain distinct: a moved subject cannot be its own mover in
that same respect; an efficiently caused thing cannot efficiently originate
itself under the second-way priority premises; and a being cannot have any
intrinsic explanation of its existence. Only the first is concluded here.
The second has its own source/type and premises; the third is not supplied by
either the First Way intermediate or q.3 a.4's exclusion of efficient
self-origination. Different-respect activity and temporally separated feedback
are not refuted by dropping the qualifications from the first formula.

The standalone results are conditional consequences, not premise truth or a
proof of a necessary being. Existing act/potency omission controls remain the
authority for independence from their tested premises; no new omission model
or exhaustive metaphysical fork is claimed. This step improves composition
without silently treating a contingent bearer as an actualization event.

Verification: both new standalone results and the affected `AQUINAS-ST-I-Q2-A3-PRIMA-VIA`
and `AQUINAS-ST-I-Q2-A3-PRIMA-VIA-RELATIVE` results passed focused builds, exact
corpus type binding and Comparator/NanoDa with zero permitted axioms. The new
Challenge SHA256 is `3adfec801af9d4e6c63bca6d2b68cb7212af6c3e18d3f08d9c70f2105537cb25`.
Both original end Challenges are unchanged. Before/after route reports are
byte-identical, and open-root-premise membership is identical: 11 routes,
62 open premises (13 bare,49 sourced). No philosophical discharge is claimed.
Final delivered-head CI retains full-library and reverse-dependency coverage.
