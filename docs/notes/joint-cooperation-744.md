# Can independent foundations explain their joint cooperation? (#744)

Result `JOINT-COOPERATION-CERTIFICATE`, module `TruthCore.Explanation.JointCooperation`.
Semantic profile: the #733 `Exercise` records and #734 `Supply`, unchanged. Everything
below is relative to one supplied scenario space and event carrier.

## Thesis tested

The unity argument says two independent foundations could only cooperate by luck, so a
deeper one is needed. Its best source form is ST I q.11 a.3's third proof. The certificate
tests whether that argument separates one source from several.

**Finding.** In this semantics it does not. It forces a choice among the branches below.
Of the exclusions tested, the fit denial is a per-record at-most-one and the total reading
gives at most one source outright, while the brute denial and the pairwise reading hold
with two sources.

## Meaning of the relations

| Term | Ordinary sense | Example | Near miss |
| --- | --- | --- | --- |
| Coexistence | Both are there | Two strangers in one city | Does not involve any shared effect |
| Compatibility | They could both be there | Two tenants who never overlap | Need not be actual |
| Coordination | Both take part in one exercised record | Two people carrying one table | Records membership, not how the work is shared |
| Sufficiency | Given both, the effect follows across the scenarios | Two switches in series with supply held fixed | Has no causal direction (#733) |
| Needed | Removing one leaves an allowed failure | Either series switch, open | Relative to the scenario space |
| No cooperation needed | One can go without an allowed failure | A second key-holder when one key opens the door | |
| Common source | One prior event determines both | A storm behind both the falling barometer and the rain | A shared ancestor that does not determine them is not enough |
| Mutual fit | They never come apart | Two theorems that hold in all models | Says nothing about why they never come apart |
| Brute coincidence | They actually coincide, can come apart, and nothing here determines both | Two friends who turn up in one café unplanned | Relative: a fuller carrier may supply a source |

These are analyst notions. Structural properties are not assumed: ancestry is transitive
by construction (`TransGen`), and no asymmetry or well-foundedness is claimed in general.
Generalizing from ordinary examples to foundations is exactly what is under test, so the
examples only motivate the distinctions. Rival accounts would read the same table
differently: a Humean sees only the regularity, an interventionist treats scenarios as
interventions, a powers theorist wants production, which the table does not state.

## The fork

For a coordinated, jointly sufficient pair (`Coverage`):
`NoCooperationNeeded ∨ (TwoWayVariation ∧ (CommonSource ∨ BruteCoincidence))`.
The four-way form also lists mutual fit. Branches overlap; only the listed incompatibilities
are proved. Mutual fit is not a separate survivor: in one scenario space it makes both
contributors redundant.

| Branch | Witness | What it brings | What excluding it costs |
| --- | --- | --- | --- |
| No cooperation needed, mutual fit | `fit`, `narrow` | Both redundant; effect occurs everywhere; the empty set suffices for it | Requiring both needed refutes occurrence of either at every allowed scenario, so a pair of foundations occurring everywhere is out |
| Common source | `guided` | Each contributor also occurs without it, if both are needed | Dropping it leaves the pair redundant or brute |
| Brute coincidence | `exercisePlural`, `single` | Two-way variation, no common source | With both needed, no exercised source can be a contributor of the pair, at one source or two |

## What each exclusion amounts to

- **Deny fit among contributors occurring everywhere.** Exactly per-record at-most-one
  (`FitExclusionIsAtMostOne`). This agrees with #771's warning: on this background such a
  premise is not independent of uniqueness.
- **Deny brute coincidence.** `IncompatibleCore`: coordination, sufficiency, one exercised
  source contributor and needing both force brute. Each of the five members can be
  dropped with the other four kept (`CoreDeletions`). No source count appears. `guided`
  meets the denial with two sources or one, and `single` violates it with one source.
- **Pairwise reading of q.11 a.3.** Excludes a source as a coordinated contributor, holds with
  two sources and no least event (`guided true`).
- **Total reading of q.11 a.3.** Gives at most one exercised source outright, so it is not an
  independent step. The readings are two claims, `AQUINAS-ST-I-Q11-A3-ONE-ORDER-A` and `-B`.

## Strongest replies

**Pluralist.** Two necessary foundations pose no coincidence problem. A coincidence needs a
space where they could have come apart, and in the modal space they cannot. `FitRival` keeps
this model, with a contingent further event through a non-sufficient exercised record.
Its costs are that neither contributor is needed, the jointly sufficient effect is
necessary in that overlay, and scenario tests say nothing about production there.

**Pluralist, wider space.** Keep indispensability by intervening on necessary beings.
`VariationRival` keeps this model. Its cost: the scenarios are not worlds of either overlay,
and on that space the pair is brute. The same records restricted to the actual scenario
move to the fit branch, so the branch depends on the chosen scenario space.

**Unity.** The sufficiency law linking two independent natures is an extra brute fact. This
is the best remaining line, and the table cannot test it, since the law is simply part of
the occurrence table for one source as well as for two. It needs the per se premise of
q.11 a.3 ("multa non sunt causa unius nisi per accidens"), now candidate
`MANY-CAUSE-ONE-PER-ACCIDENS`, and it must apply the same standard to a single source's law.

## Parity

Uniqueness does not by itself remove the problem. `single` has one least source, occurring
everywhere, with a needed pair that is brute. If an event occurring everywhere suffices for a
contributor, both cannot be needed, so a single determining source occurring everywhere
has the same no-need result.

### Stronger shared-response control (`COMPLETE-RESPONSE-PARITY`, 2026-11-04)

The original `single` fixture was a deliberately **incomplete** response comparison:
its root `r` occurs at all four Boolean-pair scenarios, but `a` and `b` each
sometimes fail. Thus the records `r → a` and `r → b` are not jointly sufficient.
Comparing that fixture to a plural exercise with all records jointly sufficient
would leave the unequal record-completeness objection unanswered.

The new `completedSingle` control changes only the *off-scenario occurrence*
of the hidden root: `r` now occurs exactly when both Boolean inputs occur.
The public occurrence table stays unchanged, as do actual occurrence,
contributors, group records, exercise flags and the graph:

| Scenario `(a,b)` | Public target, both models | Hidden `r`, completed single | `r` in original single |
| --- | --- | --- | --- |
| `(false,false)` | `false` | `false` | `true` |
| `(false,true)` | `false` | `false` | `true` |
| `(true,false)` | `false` | `false` | `true` |
| `(true,true)` | `true` | `true` | `true` |

In **both** `completedSingle` and #735's `exercisePlural`, every admitted,
exercised group is jointly sufficient over all four allowed scenarios. Both
have coherent actual exercises, both target contributors are separately needed,
and every event has inductive `Supply`. Nevertheless:

- `completedSingle` has the least graph event `r` and an exercised common
  ancestor that scenario-suffices for both public inputs.
- `exercisePlural` has distinct source events `0` and `1`, with neither a
  common ancestor nor a least graph event.
- The original one-source `single` control demonstrably fails the stronger
  all-record-sufficiency requirement (`OriginalGap`).

The comparison matches **only** the three explicitly mapped observations
over one common scenario carrier. It does not identify the two different
hidden event/bearer carriers or imply observational equality for every hidden
event, let alone invariance under actual interventions. Here `Supply` is
syntactic inductive supply from a source and records; and `jointlySufficient`
is truth-preserving implication over selected scenarios, **not** actual
causal production. The hidden single root was allowed to disappear exactly
when the observed conjunction is false; this is a mathematical construction,
not an independently motivated explanation of why such a source exists.

The failed candidate discriminator is: *public input/effect truth tables plus
joint sufficiency of every record, with inductive supply, determine a unique
underlying source*. They do not in these two stipulated interpretations.
To discriminate these models requires stronger **and independently justified**
information about hidden causal mechanism, interventions, or productive/per se
grounding. In particular, a stronger productive criterion must apply to the
one-source control as well as the strongest plural rival; only then can we
test whether it excludes the latter without merely assuming unity.

Premise/root delta: none. This bounded result neither closes #735's ultimate
explanatory adequacy bridge nor warrants treating the Boolean scenarios as
possible worlds or the graphs as real existential dependence.

### Surgical public-input experiment (`MECHANISM-INTERVENTION-PARITY`, 2026-11-04)

The next question is whether a *productive* criterion can separate an actual
input-to-effect mechanism from an idle regularity, and then discriminate one
ultimate source from several. This certificate tests **only the first half**
with explicit Boolean surgery. It reuses Hume's existing `Changes` test from
`TruthCore.Modern.Hume.Regularity`; it does **not** rename #733 scenario
variation or #752 `ProductivelyEssential` as an intervention. Indeed #752
already permits plural productively essential roots, so indispensability of
intrinsic supply alone does not settle uniqueness.

For the public contributors `a,b`, the intervention `some x` substitutes `x`
for a contributor's normal value while holding the background state fixed.
Under `none`, the original equation remains. Three models agree on all four
*natural* public triples `(a,b,effect)` (effect is `a ∧ b`):

1. **Two slots, active:** separate Boolean background inputs, then compute
   `effect := a ∧ b` from the potentially overridden public contributors.
2. **One slot, active:** one root-state *slot* holds a **pair of Booleans**;
   unpack them to run exactly the same effect equation.
3. **Idle lookup:** report the overridden public contributors, but compute
   `effect` directly from the untouched background. It matches the active
   models naturally while ignoring public surgical overrides.

| Background `(a,b)` | Override | Active effect (one or two slots) | Idle effect |
| --- | --- | --- | --- |
| `(false,true)` | none | false | false |
| `(false,true)` | force `a=true`, `b=true` | **true** | **false** |

The formal `Changes` certificate proves that either contributor, when tested
with the other on, can change the active effect and cannot change the idle
one. This is a nontrivial **model-relative** discriminator between response
mechanisms sharing natural observations. It is conditional on the intended
meaning and admissibility of the surgical operation, especially questionable
for supposedly necessary foundations.

The relation's interpretive limits are explicit:

- **Meaning and positive analogy:** response sensitivity says that setting one
  switch differently would change a powered lamp while the other switch and
  background are held fixed. The Boolean AND equation models two series
  switches. Neither the analogy nor the formula proves that the recorded
  settings are physically possible for the proposed ultimate foundations.
- **Negative analogy and exclusions:** a dashboard lamp copying an engine's
  state can covary perfectly with the engine without changing it when the
  indicator itself is overridden. The idle lookup models this exclusion.
  Sensitivity alone is not a sufficient account of efficient causation,
  metaphysical grounding, persistence or conservation of a prior state.
- **Properties:** only finite input sensitivity, inverse state packaging,
  and the stated capacity bound are proved. No asymmetry, transitivity,
  well-foundedness, cross-relation closure, or necessity of real effects is
  postulated for the metaphysical interpretation.
- **Abstraction — OPEN:** granting an intervention on two ordinary switches
  does not grant interventions on necessary beings, or show how a dependence
  of *existence* arises from a dependence of Boolean outputs.
- **Strong rivals:** a Humean can take the tables as stipulated counterfactual
  patterns without productive powers; an interventionist can accept the
  narrower idealized contrast; a powers or per se account can demand a further
  production condition on the root. None is refuted by the two-slot packing.

However, pack/unpack is a bijection and the active one-slot and two-slot
models remain **identical under every public override**, not just at natural
settings. Naming one slot a root does not make its two state components
intrinsically unified, simple, or unproduced. In the opposite direction,
an additional finite-capacity lemma shows that *one Boolean bit* cannot
realize all four independently selectable pairs. This rules out that specific
one-bit toy representation, **not** one bearer with at least four states.

The certificate retains the independently established #974 `RootParity`
between its one- and plural-graph records. It links the new natural public
response table to #974's completed single control, but does not assert that
the old scenario-sufficiency records survive the new surgery, that the newly
packed state is literally the same event graph, or that source *interventions*
are available. All source counts remain interpretation-dependent.

**Answer so far:** A stipulated public intervention can distinguish an active
equation from a merely correlated lookup, but it **cannot** distinguish a
single pair-valued slot from two separate slots. The next substantive task is
to defend a causal-production or per se explanatory criterion that applies
to the **ultimate root itself**, does not assume unity in advance, and tests
the strongest plural competitor under the same admissibility conditions.
No root premise is discharged; #735's adequacy bridge remains open.

## Boundaries

- Shared effect and weak connectivity do not give a unique source: `PluralMinima` (#707, #733)
  and `Structural` (#735) are consumed unchanged.
- `Supply` holds in the rivals as the existing proposed standard, not as adequacy.
- Models establish satisfiability of the encoding, not metaphysical possibility.
- Fidelity of the q.11 a.3 readings is uncertain: "deserviunt" and "ordinarentur" are not
  event ancestry, and the source's reason is not encoded.
- `RootMultiplication` (#771) and `CondensationSufficiency` (#768) were unmerged when this
  work started and are not imported.

## Open

Is there an independently defended productive or per se causal notion that separates
producing from idle co-occurrence, applied alike to one source and several? Root delta: none.
