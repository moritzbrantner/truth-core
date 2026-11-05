# Finite population cover bridge (#533)

This note persists the conditional investigation and its proof packaging.
The shared population-closure vocabulary in PR #614 is now merged. Baseline: `origin/main`
`0f1059ba`; required API: #614 head
`a4e46117af7c9734ad16fa0002905e1ed83d4e09`, `PopulationClosure.lean`.
The branch owns no copy of that API. No source attribution is claimed.

`TruthCore/Results/Case/Catholicism/StageOne/FinitePopulationCover/Proof.lean`
contains finite-list omission induction, full-cover joint absence, constructive
refutation of individual contingency, explicit-excluded-middle positive DeRe,
a complete-roster sufficient condition, alternating failure of amalgamation,
Nat-tail failure of finite cover, and a successor-free empty-roster control.
A cover bounds every accessible population, rather than merely hitting it.
The ambient roster is unrestricted and need not be finite. The successor
hypothesis is essential to the empty-list base; empty individuals plus no
successors otherwise makes contingency/cover/amalgamation vacuous.

Reuse search found the existing alternating model in `Quantifiers.lean` but no
merged #484 Nat-tail API. The task-local Nat model uses existing `Frame` and
`ExistsAt`; its populations are exactly `n ≤ x`. Its max-world witnesses
amalgamation; populated tails and individual absence refute finite cover by
composition with the newly proved incompatibility. This is a typed infinite
model, not a finite-registry certificate.

Warm-service evidence: HTTP 200, `/lean/diagnostics`, workspace
`/home/brantner/privat/truth-core-sprint-proof`, detached head
`75192b1c3efdf19f25601e52a06116e706420f11`, existing session `causal-harvest`,
request-only `Scratch/issue533/FiniteCover.lean`, under
`flock /tmp/truth-core-lean.lock`. No workspace or imports were edited.
The self-contained preview inlined exactly the approved #614 API for diagnostics.
Final preview SHA256:
`c36aafcfa626fe35337b15469b13f46aadee7622e02d7b3d71ce9b143ae330d2`.
Version 8 reported no errors and printed zero axioms for `finite_omission`,
`finite_cover_deRe`, `tail_control`, `alternating_not_amalgamation`, and
`successor_free_control`. HTTP call completed with 0.217s service elaboration;
lock wait was not separately measured. These diagnostics are not Comparator,
NanoDa, build, or bind-check certification.

Rejected implementation details: `simp` in the empty-list branch introduced
`Quot.sound`/`propext`; `List.mem_cons.mp` and standard `Nat.le_max_left`
introduced `propext`. Direct membership cases and explicit conditional max
bounds remove these axioms. This is a proof-engineering change with no
philosophical premise change.

Claim/type self-sweep: the induction omits every listed individual at one
successor; the cover transfers that omission to every present individual;
DeDicto contradicts this joint absence. Positive DeRe is proved only with the
explicit `TruthCore.Logic.ExcludedMiddle` hypothesis. None of these types
asserts cover/amalgamation truth or closes a Catholic-case root premise.
Expected and actual root-frontier delta: zero; existing root routes and
reaching-root leaves unchanged because no corpus graph edge was added.
Dossiers inspected: `STMT-NECESSARY-INDIVIDUAL-DE-DICTO` and
`STMT-NECESSARY-INDIVIDUAL-INDIVIDUAL-CONTINGENCY`.

Delivery update: #614 was merged at main `db7b74b5`. Reusable vocabulary now
lives in `NecessaryIndividual/FinitePopulationCover.lean`; the helper proofs
retain their previously checked terms. `FinitePopulationCoverLaws` and
`FinitePopulationCoverControls` each have frozen Challenge, Solution, statement,
argument, inference, result and zero-axiom Comparator/NanoDa configuration.
Neither adds root support. No source-derived claims were added.

Packaging diagnostic evidence: same warm session and workspace, request-only
`Scratch/issue533/Packaged.lean`, version 2, HTTP 200. SHA256
`de9beaeddb3455950023ae2e87333e41b9b4644724c47a3388ce2e8f628952d8`.
Both result `checks` declarations print no axioms; no error diagnostics.
Canonical CI will check delivered imports, bindings, Comparator and NanoDa.
The successful attempt records proof search success, not completed CI.

Final claim/type self-sweep: both universal laws and controls match their
statement paraphrases, argument meanings, result descriptions and doc comments.
World/roster quantifiers are explicit. The positive existential follows only
under the EM hypothesis, never from merely refuting universal contingency.
The zero-premise laws certify a universal conditional, not the policies inside
its arrows. Rigid identity, actualist presence, population closure and scope
reuse the linked definitions/disambiguation; finite full cover and successor
existence receive the new stipulative definition. No attributed source reading
or new root edge is present. Expected/actual root-premise delta remains zero.

Cross-lane edit: the new StageOne vocabulary and helper/wrapper result modules
are minimal lane A additions for this lane C issue; generated Case and Results
imports follow those modules. No shared vocabulary definition was duplicated.


## Limit admission extension (#486)

The #533 tail ontology is reused literally: `tailProfile n b = true` iff
`finiteCoverTailPresent b n`, i.e. `n ≤ b`. The exact imported
`FinitePopulationCoverControls.checks` remains part of the certificate. Each
finite list is jointly absent after its maximum, but every admitted tail
remains inhabited. Mathlib's product topology proves coordinatewise convergence
to `falseProfile`; the empty profile lies in `closure tailWorlds` and never in
`tailWorlds`. Thus that family is not closed. This supplies the topology that
#484's reconciliation left open, without requiring an unimplemented #484 API.

`TruthCore/Logic/LimitAdmission.lean` fixes the typed mathematical interpretation;
`Results/Logic/LimitAdmission/{Challenge,Solution}.lean` freezes and checks it.
`ClosureLaws` says, for any topological space, Nat-indexed `f` and `x`,
`Tendsto f atTop (nhds x)` implies `x ∈ closure (range f)` and, for any closed
`A` containing the range, `x ∈ A`. `LIMIT-CLOSED-ADMISSION` exposes exactly three
separate premise heads: `Converges`, `ClosedAdmission`, `StagesAdmitted`.
`ClosedAdmission` is a named OPEN domain policy, not a consequence of the first
or third premise. `LimitAdmitted` is membership in the selected set; no bridge
identifies ambient closure with actual admission.

The modal, temporal and supertask conditional transfers have separate theorem
obligations and checked `instance_of_schema` links to the universal law. Their
shared mathematical proof pattern identifies neither their data nor their
actual-domain policies. Modal worlds are compared under rigid candidate
identity, never traversed or physically subtracted. The profile's topology is
explicitly the product of discrete Bool topologies, not an unspecified notion
of metaphysical similarity or a proof of modal compactness.

The reciprocal temporal schedule is `eventTime n = 1/(n+1)`. It lies in `(0,1]`
and converges to 0, while its event range excludes 0 and has an earlier event
for each event. The ambient interval `[0,1]` has first point 0. Thus bounded
duration and a first time point do not force a first event. This is the exact
reciprocal example requested in #486; the existing `TemporalEventControls`
uses the distinct reflected geometric Zeno schedule. Neither is an actual
history or a causal-relation model. Closed occurrence sets containing every
reciprocal stage admit an event at 0. Without that closedness assumption the
same event range is a certified negative control. Its mathematical closure is
a closed positive control; identifying this extension with actual occupancy
remains OPEN. No causal priority or first cause is inferred from event time.

The reciprocal supertask schedule is `stageTime n = 1 - eventTime n`, strictly
increasing in `[0,1)` and converging to 1. It assigns clock readings to the
EXISTING `SupertaskMoment`; `.limit` is not any `.stage n`. The event set that
contains exactly those stages excludes 1, although 1 is an ambient limit.
Again its closure is a closed positive admission model. The imported
`supertaskStableEndpoint` theorem remains abstract order/stability mathematics,
not finite physical completion. The same convergent clock can accompany the
existing oscillating output, whose lack of eventual stability is upgraded to
lack of topological Bool convergence using the proved equivalence between
these two notions for DISCRETE Bool only. No eventual-constant replacement for
real convergence is introduced.

Even convergent apparatus states do not fix a separately assigned endpoint:
`mismatchedState` has true at every finite stage and false at `.limit`.
`TerminalOutcome` explicitly requires convergence TO the assigned endpoint.
Together with convergence to `b`, uniqueness of limits in Bool forces the
endpoint to equal `b`. The everywhere-true state is a positive coherent model.
Endpoint-state coherence and closed event occupancy remain separate inputs;
neither gives a final indexed operation, a law of nature, or a physically
possible supertask. Completion as another operation would require an explicit
extension of the operation carrier, rather than relabeling the existing limit.

The strongest positive rival accepts closed admissibility/occurrence for its
own domain, or supplies an endpoint law satisfying `TerminalOutcome`; the
conditional results then admit the boundary. The strongest negative rival
accepts every finite stage and the mathematical limit but withholds just that
policy, as the same-profile controls demonstrate. Which policy applies to
actual worlds, event histories and apparatus remains OPEN independently in
each domain. Encoding the real applicability judgment needs a defended domain
interpretation or physical model; the topology alone cannot supply it.

These are infinite Mathlib/topological interpretations, outside the existing
finite-model and configuration registry's supported data roles. They are kept
as exact statements/results/attempts and checked schema links. The registry is
not widened and no finite certificate or global minimality is claimed. No new
sources, passages, claims, external dependencies, solver or status store.

Preview trial: the coordinator-owned service returned a response bound to HEAD
`a2d97ecf1429e86b3e12f15b91b735f85e27822e`, workspace
`/home/moenarch/moritzbrantner/truth-core`, session `workloop-20261105`, scratch
`Scratch/limit486/Vocabulary.lean`, content SHA256
`60ba2c274da4a54ca22160811ccaca0197e1689a248af6fa360547d830629d8d`.
It rejected importing the old cached non-module `FinitePopulationCover` from a
new Lean module. That is diagnostic failure, not proof evidence. The isolated
warm-seeded canonical CLI compiled the new vocabulary and all three controls;
no preview session/cache was rebuilt. Retain the preview helper for compatible
inputs, but revise its preparation before modern-module work; CLI fallback
keeps research unblocked. Final build/binding/Comparator/NanoDa and CI remain
the proof authority.

Claim/type self-sweep: universal topology is conditional; each negative model
uses exactly its declared ambient space and admission set. Positive closures
are mathematical extensions, not realized worlds/events. Bool convergence is
identified with stability only through a theorem under the discrete topology.
The real schedules never become constant. No causal relation, actual event,
physical completion, divine identity, necessary concretum or root truth is
introduced. Closedness/applicability and terminal-outcome commitments remain
OPEN. Intended root-premise discharge: zero; the actual computed frontier delta
is reported in the PR/CI. Shared convention sourceRevision:
`625cb04ca568aebc8d45c90033e107a05e9bd2a0`.
