# #487 — conditional necessary-concrete root

This is a mathematical elimination result, **not** a sourced proof that the
premises describe reality. It reuses the already verified Kantian theorem
`wellFoundedCausesBlockAllContingent` (now factored through the strictly weaker
actual-world lemma `wellFoundedCausesBlockAllContingentAt` without changing the
original theorem's type or induction). Both the typed bridge and the omission
tests are in `TruthCore/Causality/NecessaryConcreteRoot*.lean`.

## Exact meaning and implications

- `m : Ontic W E` supplies a **fixed individual roster**, complete-history
  possible worlds, their explicit accessibility, world-relative existence and
  a directed generic `Causes` relation. Its `ContingentAt m w x` means that x
  exists at w but not at some accessible world. It does **not** mean that x
  began to exist at some time inside w.
- `ActualConcrete m concrete w` is the subtype of candidates that are both
  concrete under a supplied criterion and actually present **somewhere in
  history w**. `WellFoundedConcreteAt` tests only causal predecessors within
  this actual-concrete subtype.
- `ContingentConcreteDependenceAt m concrete w` requires **every** such
  contingent x, including a causal root, to have an immediate predecessor y
  which is concrete and actual in w. It does not allow an absent predecessor
  or an abstract explanation token to satisfy the requirement.
- `KantRegressYieldsNecessary` derives an actual fixed witness present in
  every **accessible** world from the older global local-causality premise,
  well-founded actual-world Causes relation, actual inhabitation, and the
  explicitly supplied `ExcludedMiddle`. It introduces no concreteness.
- `ConcreteRootConditional` derives the same de re accessibility-relative
  conclusion for an actual **concrete** bearer, requiring only actual-world
  typed dependence and well-foundedness restricted to actual concrete beings.
- `GlobalConcreteRootConditional` adds `∀ v, m.frame.access w v` before
  concluding `∀ v, m.ExistsAt v x`. The accessible-world and all-world
  conclusions must not be interchanged on an arbitrary frame. The separate
  `UniversalAccessibilityAt` and `EveryWorldConcreteAt` predicates let the
  model verifier test the extra bridge independently.

Excluded middle is **a premise in the theorem's Lean type**, not an imported
classical axiom. The negative-universal contradiction and its four-member
core are constructive; choosing a particular noncontingent witness uses the
recorded logical principle.

## Minimal contradictory core

All four share precisely the same `m`, `concrete`, and `w`:

| Statement | Exact role |
|---|---|
| `STMT-CAUSAL-ROOT-POPULATED` | There exists an actual concrete individual. |
| `STMT-CAUSAL-ROOT-WELL-FOUNDED` | The actual concrete predecessor relation is well-founded. |
| `STMT-CAUSAL-ROOT-DEPENDENCE` | Every actual contingent concrete individual has an actual concrete immediate predecessor. |
| `STMT-CAUSAL-ROOT-ALL-CONTINGENT` | Every actual concrete individual is contingent (the negation of the de re conclusion under excluded middle). |

`CAUSAL-ROOT-CORE-INCOMPATIBLE` derives the existing
`STMT-CONFIGURATION-FALSE` with exactly those four statement hypotheses.
The contradiction does **not** require excluded middle, finite branching,
finitely many ancestors, a finite temporal past, or one cause shared by all
concreta. Its mathematical inclusion-minimality is witnessed by four finite
single-deletion controls, not inferred merely from unsuccessful proof searches.

| Dropped commitment | Certified remaining commitments | Registered control |
|---|---|---|
| Actual-root dependence | Populated, well-founded, all contingent, no necessary bearer | `MODEL-CAUSAL-ROOT-OMIT-DEPENDENCE`: alternating worlds and no causal edges |
| Well-foundedness | Populated, universally dependent, all contingent, no necessary bearer | `MODEL-CAUSAL-ROOT-OMIT-WELL-FOUNDED`: two distinct contingent beings per world, mutually causally related |
| Actual population | Well-founded, dependence, all contingent, no necessary bearer | `MODEL-CAUSAL-ROOT-OMIT-POPULATION`: empty existence extensions with nonempty world type |
| All-contingency | Populated, well-founded, dependence, a necessary bearer | `MODEL-CAUSAL-ROOT-OMIT-ALL-CONTINGENT`: fixed always-present roster |
| Concrete predecessor typing | Populated, well-founded, weak *untyped* dependence, no necessary concrete bearer | `MODEL-CAUSAL-ROOT-ABSTRACT-PREDECESSOR`: a present abstract predecessor explains/causes the only actual concrete candidate |

A sixth control, `MODEL-CAUSAL-ROOT-OMIT-UNIVERSAL-ACCESSIBILITY`,
retains actual concrete population, typed WF and root-inclusive dependence,
**and** gives an accessible-world necessary concrete witness. Its two
inhabited histories only access themselves, so the selected witness is absent
from the other, inaccessible history and the all-world conclusion is false.
This proves the accessibility bridge is a substantive extra assumption, not
mere theorem presentation.

These are **satisfying interpretations of a stipulated encoding**. They do not
independently establish that a world with brute contingent roots, a two-node
causal cycle, or an abstract producer is metaphysically possible.

## Epistemic frontier and next premise

The formal boundary is now sharp: if actual concrete reality is inhabited and
its relevant *existential dependence* is well-founded, then rejection of a
fixed necessary concrete existent entails rejecting the **root-inclusive**
dependence principle. Keeping ordinary causation for later/noninitial events,
or granting merely a reason token, does not close this escape.

The next high-value philosophical obligation is to defend, independently of
the desired conclusion, why **even an initial contingent concrete reality**
must have an actual concrete source/ground. Distinguish an efficient cause of
an event from a ground of a being's existence, from a reason selecting one
history over another, from a necessary agent whose contingent action need not
be necessitated. Separately defend well-foundedness of the chosen existence-
grounding relation, the actual concreteness criterion, rigid transworld
identity/counterpart semantics, and which histories are metaphysically
accessible. These are not derived by Lean or by the models.

Even if the premises are defended, this result establishes **some necessary
concrete individual**, not uniqueness, pure act, absolute simplicity,
timelessness, intelligence, will, goodness, a cause of the entire universe,
God, or Catholicism. There is no automatic #143 root-premise discharge.

## Persistence and configuration engine boundary

The five results have individual statement/inference/argument/Challenge/
Solution/Comparator records. The six independent finite controls are registered
under `corpus/models/`, and the investigation attempt under
`corpus/attempts/`. This uses the existing #477 model and argument ledger;
no parallel prover, graph, ontology or proof-status database was introduced.

At this revision, the automated `corpus/configurations/` composition engine
only accepts the five roles `W, I, F, present, w` and a single Kripke-presence
vocabulary. It cannot replay a profile adding `Ontic`, concrete status and a
causal predecessor relation without extending the **existing** engine. The
four-premise incompatibility is nevertheless a registered typed result and
the deletion controls are checked models; no unsupported configuration case
has been inserted or misleading explorer elimination claimed. The present
model ledger can be inspected with `python3 scripts/corpus.py models`.

Related separate current work: #505 / PR #510 studies brute roots, potency,
and explanatory necessitation. This slice specifically derives the #487
bridge by composing the earlier verified Kantian result and certifying the
premise deletion matrix; it does not identify grounding with efficient cause.
