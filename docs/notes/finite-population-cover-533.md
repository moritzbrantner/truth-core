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
