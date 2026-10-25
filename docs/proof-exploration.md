# Bidirectional proof exploration

The graph's proof exploration is an advisory projection of existing statement,
inference, argument and result records. It matches exact statement IDs only.
Equal wording, synonyms and apparent philosophical equivalence cannot merge
nodes. No new canonical graph, runtime service, axiom or witness is introduced.

Forward seeds come from `corpus.py frontier --json`'s established statements,
projected onto the graph. A selected scope can restrict these facts; selecting an
open statement cannot establish it. The forward search proposes applications of
recorded checked arguments only when **all** their premises are available. Its
newly reachable propositions remain proposals, distinct from authoritative
establishment. The graph's closure/status projection is never mutated.

Backward exploration enumerates existing inference applications into a selected
goal. Each application requires all its inputs (AND); different applications are
alternative branches (OR). Local assumptions and discharged assumptions remain
inspectable, and never become global forward facts. An inference without a
containing result remains visibly unverified. Reciprocal arrows with no ground
produce no forward facts. Search failure means unresolved, not refuted.

Exact-ID junctions propose a composition. Their argument/result provenance and
each branch's remaining premises can be inspected. A proposed meeting is not a
new verified result: record its precise statement, frozen Challenge, Solution,
inference composition and result, then pass Lean, binding checks, Comparator and
NanoDa. Existing source, interpretation, definition and empirical obligations
remain visible after formal consequence is checked.

The search visits a deterministic, bounded number of work items (at most 10,000),
memoizing goal/argument, selected scope and available-premise situations for that
run. It yields regularly to the browser event loop for cancellation. A changed
goal, budget, scope or graph discards the old run. The budget is a useful-search
bound, not a shortest-proof guarantee; exhausted/cancelled runs report partial
results and cannot trigger a claim that reuse has failed.

When a completed search cannot reach its goal, a transient, explicitly unverified
and unformalized intermediate-lemma suggestion joins the existing derived
research queue. It lists its intended bridge, missing premises, exact search
provenance, and source/definition/disambiguation/formal-verification needs. It
creates no corpus statement or fabricated source-range candidate. Actual research
still uses the existing source-range candidate pipeline.

## Checked pilot composition

`PILOT-COMPOSED-WITNESS` imports the #207 pilot's independent proof of
`STMT-SOME-LEAN-PROPOSITION-HOLDS`, applies the existing
`someImpliesNotAll` theorem to produce
`STMT-NOT-EVERY-LEAN-PROPOSITION-FAILS` as an actual intermediate proof, then applies the checked `pairFromConsequence` B → C helper to construct `STMT-PILOT-WITNESS-AND-CONSEQUENCE`. The helper imports the existing reciprocal B → A result to recover the witness, then introduces the conjunction. The composed argument reuses all three existing pilot inference records and adds conjunction introduction. It has no premises or
permitted axioms. This is a bounded logical fixture, not philosophical progress
on the Catholicism root or verification of external truth.

The existing pilot stability bridge provides the non-meeting: a checked
conditional from `STMT-PILOT-LOGICAL-SENTENCE-STABLE` does not establish its
conclusion while that interpretation premise remains open. Synthetic fixtures
also exercise partial AND obligations, independent OR branches, ungrounded
cycles, scope restrictions, budget exhaustion and cancellation.
