# Condensation, causal-group cuts and joint Supply (#752)

The question is whether collapsing cycles or cutting causal groups preserves
explanatory sufficiency. The checked answer is relative to `Supply`, the #734
proposed inductive standard. Nothing here defends that standard as actual
productive explanation. Root premise delta: none.

## Meanings

- **Group, contributor, enabler, exercise:** unchanged #733 records
  (`DEF-JOINT-CAUSAL-GROUPS`). A group indexes a record; a hyperedge's members
  are not individually sufficient.
- **Power, intrinsic, Supply, Trap, Escape:** unchanged #734
  (`DEF-DERIVATIVE-JOINT-SUPPLY`). Intrinsic is an independently supplied
  predicate, not graph sourcehood.
- **Component:** Mathlib's `Quiver.StronglyConnectedComponent` of the projected
  graph, a reachability class (`DEF-SCC-CONDENSATION`). It is no cause or ground.
- **Source:** a node with no incoming edge. A source of the condensation is a
  reachability-minimal component and need not contain an intrinsic event.
- **Ground, cause:** this module asserts no grounding or causal relation between
  actual things. Edges are analyst records, per `DISAMB-CAUSAL-POWER-GROUNDING`.
- **Adequacy:** not a predicate here. The results relate Supply to graph facts.

No source claim is added and no source was newly read for this slice. The #734
note's audit of `AQUINAS-ST-I-Q2-A3` and `AQUINAS-ST-I-Q46-A2` stands: those
passages do not state a hypergraph cut principle, so none is attributed.

## What survives condensation

`GraphInvariants`, for every graph: the condensation is acyclic; finite
reachability, weak connection and leastness hold in the graph exactly when they
hold of the components; a source's component is a source. On a finite carrier the
condensation is well-founded. `(condenseGroups h).graph = condensed h.graph`.

## What is lost

Take s → t, u → t, t → u, with s the only intrinsic event. All three record
structures below have this exact membership graph, hence every graph-determined
summary: components {s} and {t, u}, one weak component, source s, least s, and a
condensation that is a two-node chain.

| Records | Supply of t and u | Component escape |
| --- | --- | --- |
| `conj`: t from s and u; u from t | none | fails |
| `disj`: t from s; t from u; u from t | both | holds |
| `enabling`: t from s, u enabling; u from t | both | holds |

## Intrinsic support sets (follow-up)

The relation `IntrinsicSupport h I S target` retains the whole admitted-group
record: `S` contains only events permitted by intrinsic predicate `I`, and
the target has inductive `Supply` from exactly that seed set. The operator
`supportStep h S` requires **all** contributors of an admitted record (AND)
and permits different admitted records as alternatives (OR). Its least fixed
point equals that inductive `Supply` interpretation
(`support_eq_lfp`). Enablers are intentionally not productive inputs; their
occurrence remains an independent exercise/coherence requirement.

`MinimalIntrinsicSupport` selects inclusion-minimal seed sets, not one
individual and not a least cause. Distinct minimal sets cannot contain one
another (`minimal_support_antichain`); the existence and uniqueness of a
minimal support are NOT asserted for arbitrary event types or infinite
contributors. The generic `no_empty_support` uses the explicit assumption
that all admitted contributor sets are nonempty; empty productive records
would be counterexamples.

| Existing fixture and target | Minimal allowed intrinsic seed | Why |
| --- | --- | --- |
| #735 `plural`, target 2 | exactly `{0,1}` | Both unproduced contributors are required; this is a two-*individual* support despite one recorded production group |
| #752 `conj`, target t | none | Cyclic AND-dependence blocks inductive Supply |
| #752 `disj`, target t | `{s}` | There is an admitted alternative requiring only s |
| #752 `enabling`, target t | `{s}` | u is an enabler, not a productive contributor to t |

### Further consequences: roots, support bases, and interventions (2026-11-02)

Three quantities that are easily conflated are **the number of ordinary graph
sources**, **the number of minimal adequate intrinsic input SETS**, and **the
number of individually indispensable productive inputs**. The same checked
models separate them:

| Model and intrinsic policy | Ordinary graph sources | Minimal support sets for target | Individually productive-essential inputs |
| --- | --- | --- | --- |
| #735 `plural`, `I={0,1}`, target 2 | two, 0 and 1 | exactly one: `{0,1}` | both 0 and 1 |
| #752 `disj`, original `isS`, target t | one, s | exactly one: `{s}` | s |
| #752 `disj`, rival `isSU`, target t | one, s | at least two, `{s}` and `{u}` | neither s nor u |
| #752 `conj`, `isS`, target t | one, s | none | none (the nonvacuity condition fails) |

The two `disj` rows have **identical admitted group records and graphs**;
only which independent inputs the analyst permits changes. The rival `isSU`
supplies u intrinsically although u is not an ordinary graph source. A premise
identifying intrinsic supply with ordinary sourcehood would exclude that row,
but that premise is *not* licensed by these graph results. This is not a claim
that u really is a first cause. Conversely, the plural group requires BOTH
distinct root inputs, so its sole minimal basis is a two-member SET and not a
single substance.

`BlockedBy h I B target` fixes the group records and disables intrinsic
inputs in B. The exact `blocked_iff_hits_every_support` theorem states, for
**arbitrary** event/group types and without finiteness: B blocks the target
iff B intersects every adequate intrinsic support set. The nonvacuous
`ProductivelyEssential` predicate holds of one input exactly when the target
has Supply originally and deleting that singleton blocks it
(`essential_iff_singleton_blocked`). Enlarging a blocker cannot restore
Supply (`blocked_mono`). These are hypergraph **hitting-set/intervention
duals**, not causal-world counterfactuals: enabler occurrence and admitted
record validity are held fixed. Only if every adequate support contains a
minimal one (for example on a finite intrinsic domain) may the hitting test
be reduced to the antichain of *minimal* adequate support sets. That existence
condition is not silently assumed for infinite supports.

The `disj_alternative_intervention_cut` control makes the difference exact:
deleting s alone or u alone still supplies t; deleting both blocks t. By
contrast #735's 0 and 1 are *each* productively essential. With the
unchanged `modal .plural true` overlay both bearers are necessarily existing
while still jointly essential to this productive-Supply calculation
(`plural_necessary_and_productively_essential`). Changing intrinsic input
availability is **not** removing a necessarily existing bearer from an
accessible metaphysical world. Any connection to an actual intervention,
explanation of existence or necessity needs a separate bridge.

### Component-local obstruction and object-level simplicity

The complete-cause source result has a sharper pointwise form:
`ordinary_sources_eq_of_K_connected_pair`. Under the SAME carrier, K included
in ordinary causation, and the two complete-producer cover policies only on
K, any two ordinary sources connected in a **single K weak component** are
equal. No *global* connectivity or well-foundedness is needed. Thus distinct
ordinary sources must lie in different K components
(`ordinary_distinct_sources_separate_components`). Applied to #735, K cannot
even connect both root 0 and root 1 *through effect 2* in the same component
(`plural_two_roots_cannot_meet_in_complete_component`). This explains
locally, rather than by an all-or-nothing global no-go statement, which
ordinary partial causal links a proposed complete-production K must leave
cross-component. K components are mathematical edge-connectivity classes,
not complete producers or metaphysical entities.

A distinct conditional consequence also follows from the very SAME
participant-cover policy, even without a connected graph. If a particular
complete producer c covers two **distinct object-level productive
participants** of its effect, c has a proper part
(`distinct_participants_force_composite_producer`). Equivalently, a
non-composite c can cover only itself as a participant
(`simple_complete_producer_collapses_participants`). Here *non-composite*
means `¬ Composite c`, with `Composite c := ∃p, p<c` under the supplied
parthood PartialOrder. It is **not** a proof about stronger theological
divine simplicity. Nor does #735 supply such a c: its joint-group index is
not a third object, and there is no automatic reification of a group record
as a covering producer. The conditional makes a further pressure point
precise: plural distinct productive participants + complete covering by a
single individual + that individual's partlessness cannot all hold under
this object-level reading. Rejecting the cover interpretation or treating
the contributors as non-object-level factors remains open.

These are supporting Lean propositions, not a new registered argument route,
not evidence for a metaphysical bridge, and not a discharge of any root
premise. No corpus frontier or proof-cost change follows.

All three #752 cases still have the identical projected graph, SCCs,
ordinary source and weak component. The fixed-point calculation therefore
needs the typed group records, even when SCCs help organize their cycles.
Moreover, `plural_no_spanning_complete_subgraph` applies the complete-cause
source-transfer theorem to #735's TWO rooted yet fully supplied contributors:
no subset of its ordinary causal edges, on the entire same carrier, can
satisfy both complete-producer cover policies AND be weakly connected under
any proposed parthood partial order. The complete joint GROUP record remains
available; it is not a third individual in that graph.
The operator is a **mathematical least-fixed-point specification**, not yet
a bounded executable SCC/antichain enumerator. In general, infinite
contributor families do not justify stopping after finitely many rounds.
No group-to-individual complete-producer identification, intrinsic-to-esse
bridge, claim of physical/ontic adequacy, or root-premise discharge is added.

Over the on scenario, `conj` and `disj` also share bearers, occurrence, allowed scenarios, actual
scenario, exercise and actual graph. Condensed Supply holds for both, because
condensing `conj` drops u from t's record. **So the chain after condensation is
misleading:** it shows s supplying a node, and hides that t's only record needs a
member of t's own component. On this carrier no function of the projected graph
and intrinsic set agrees with Supply. The acceptance's same-summary witness
therefore exists, in the stronger form of the same graph.

An illustration, not an empirical claim: a plant whose only start needs outside
fuel and power from its own generator cannot start from fuel alone, while one with
a separate starter can; both draw the same arrows. A plant already running is the
rival's case. It sustains itself now, and locally its equations hold. Calling its
present activity deficient needs more than the failure of `Supply` in one context.

## What reflects Supply

The reduction: over a well-founded condensation, `Escape` holds exactly when
`ComponentEscape` holds. Take a component minimal among those meeting the set; a
contributor in the set but outside that component would contradict minimality.
Composing #734's `escape_iff`: under LocalPower, PoweredGroups and a well-founded
condensation, Supply of every active event coincides with `ComponentEscape`. A
finite carrier supplies that well-foundedness.

LocalPower with an acyclic membership graph gives `ComponentEscape`. LocalPower
with a well-founded membership graph gives Supply of every active event, without
PoweredGroups. So, given LocalPower, a well-founded graph settles Supply, and the
warning above concerns nontrivial components, self-loops and non-well-founded graphs.

Each hypothesis is tested:

| Model | Well-founded condensation | Component escape | Supply |
| --- | --- | --- | --- |
| `conj` | yes | no | no |
| `disj` | yes | yes | yes |
| #734 records on the #634 graph, least node | no | yes | none for derivative events |
| `disjOverlap` on the same graph | no | not stated; `Escape` holds | every event |
| source-free `unrootedGroups` | no | yes | none |
| `loopChain`, with condensed Supply | no | yes | none for `some n` |
| `circle`, no intrinsic member | yes | no | none |
| `circle`, one intrinsic member | yes | yes | every event |

`disjOverlap` shows well-foundedness is not necessary for Supply. `loopChain`
refutes a conjecture tried here, that condensed Supply could replace it: each
`some n` has a record needing itself and one needing `some (n + 1)`, so every
singleton escapes and all condensed Supply holds, yet no `some n` has Supply.
The #735 plural fixture has Supply of every event, one weak component, two source
components and no least component, so plural foundations survive.

## Cuts

`GraphCut` (no intrinsic member, no incoming edge from outside) with nonempty
contributor sets is a `Trap`. The converse fails: {t, u} is a `conj` trap with an
incoming edge from s. The empty record shows nonemptiness is needed. `Trap` reads
records, so it distinguishes `conj` from `disj`.

`Trap` does not track scenario indispensability. With `conj`'s records, u is
indispensable over both scenarios and redundant over the on scenario alone, and
Supply has no scenario parameter. Deleting u from the record gives Supply. Hence
whether u belongs among t's contributors is input to this analysis, and neither
scenario sufficiency nor a graph settles it. That is the open semantic commitment
behind reading a trap as actual causal failure.

## Enablers and PSR scope

`enabling` differs from `conj` only in u's role. The membership cycle stays, the
contributor projection is acyclic, and Supply holds. An SCC on membership can thus
report a cycle Supply ignores, which bears on #545's enabling-SCC question. Contributor projection does not
solve the problem generally, since `conj` and `disj` both keep its cycle.

`recordArena` reads a #757 arena's reasons as a fact's contributors in an exercised
record, a stipulated token. On the bare `circle` every occurring fact has a reason,
so `FactPSR` holds without Supply. `disj` has Supply and fails `FactPSR` because s
has no record. Under this reading neither implies the other. It does not
compare other reason readings.

## Rivals and open bridges

The result excludes no rival outright. A circular or coherentist rival can accept
every theorem and reject `Supply`: `circle` is a model of LocalPower with a reason
for each fact. The foundationalist gets only the conditional: if Supply is the
standard, then the bare `circle`, with no record from outside it and no intrinsic
member, fails it, though the same cycle with one intrinsic member does not. The cycles
of `disj` and `enabling` have no intrinsic member and every event has Supply, through
the source s. So cycles as such are not the defect, and neither is a cycle's lacking
an intrinsic member. An infinite graph
with a non-well-founded condensation can have Supply of every event
(`disjOverlap`), so that graph fact alone does not decide Supply.

For the necessary-being route, a source component carries no modal content. The
module has no modal clause; #735's overlays already keep a graph while varying
necessity. Open: exercise-to-Supply, whether contributor classification can be
independently fixed, the move from a productive respect to existence, and
intrinsic contribution to necessity. These feed #735; #749 may consume the table
above as an explanation-focused example, and no UI is changed here.

## Prose and comparison

No registry configuration is added or eliminated; no numerical scoring is used. The
proof is an induction and minimal-element argument, not a transcription. Root
frontier before and after is identical; see the PR for the comparison.
