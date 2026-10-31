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
  reachability-minimal component and can contain no intrinsic event.
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
PoweredGroups. There the graph does settle Supply, so the warning above concerns
nontrivial components, self-loops and non-well-founded graphs.

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
standard, then a cycle without an intrinsic member fails it, though a cycle with
one does not, so cycles as such are not the defect. An infinite graph
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
