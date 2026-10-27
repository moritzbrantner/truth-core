# Configuration elimination and theorem composition

Research strategy for #477. This is an additional *use* of Truth Core's existing corpus loop, not a new ontology or status authority. The source-reading loop in [systematic-corpus-loop.md](systematic-corpus-loop.md) and the proof boundaries in [AGENTS.md](../AGENTS.md) remain binding.

## Purpose

Prefer a small number of general, verified constraints that eliminate whole families of incompatible configurations to independently evaluating every combination of propositions. Persist each attempt and theorem so that later work composes earlier results. Progress means a justified change in known implications, incompatible theories or root-premise closure, **not** larger proposition counts or a smaller graph.

A configuration is a finite set of **existing statement IDs** interpreted under an explicitly named semantic profile. Its profile fixes the pertinent logic, accessibility relation, quantifier domains, cross-world identity and any other choices that affect the meanings of those statements. Different profiles cannot silently share a contradiction or a model. Statements that only *sound* equivalent remain distinct until a checked equivalence is available.

## Research cycle

1. **Select a load-bearing seed.** Take it from an end-to-end case and its decisive fork ([argument-first method](systematic-corpus-loop.md#frontier-investigations-argument-first-decomposition-on-demand)), not from an inventory of distinctions. Start with an unresolved dossier and its existing statements, definitions, disambiguations and related registered models/schemas. Prefer root-reaching premises, shared dependencies or an objection with a falsifiable target. For necessary existence, begin with #435–#441 and PR #445.
2. **Compose what is already established.** Search bound Lean theorem types and checked schema instances, not merely prose similarity or `supports`/research graph edges. Track exact hypotheses and theorem IDs. Do not restate a derived theorem as a new independent premise.
3. **Try to eliminate families.** Formalize proposed contradictory combinations as explicit hypotheses and derive `False` in Lean. Verify with the applicable Comparator/NanoDa gate. Minimize the premise core by independently checking each proposed removal. Only a checked unsatisfiability theorem licenses pruning its supersets *under the same semantics*.
4. **Try to witness survivors.** Reuse the certified finite-model registry. An explicit model satisfying all selected commitments witnesses formal satisfiability in that specified semantics; no model found means **unresolved**, not impossible. A finite search is exhaustive only for its declared bound unless a separate general small-model result is proved.
5. **Persist every substantive outcome.** Store a new formal statement/argument/result only for an actual proposition/inference. Store successful, failed and blocked investigation records in `corpus/attempts/` with exact targets and evidence. Use `corpus/models/` for certified model evaluations and `instance_of_schema` for checked theorem instances. Fix inaccurate attempt records in place; do not erase genuinely earlier failed approaches.
6. **Recompute the frontier.** Run `corpus.py frontier --routes` and `--reaching-root`, compare root-path open premises before/after, and report what genuinely closed versus what merely moved or gained a research link. The existing closure engine remains sole authority.
7. **Choose the next question.** Prefer an open premise whose resolution would affect several verified paths or yield a general incompatible core, while retaining meaningful alternatives as complete theories with replacement explanations.

## Reporting contract

A configuration report should distinguish:

- **Verified incompatible:** a checked theorem proves the conjunction inconsistent; include the semantics and inclusion-minimal certified core. In classical logic, do not promote arbitrary consequences of the inconsistent conjunction as explanatory results.
- **Model witnessed:** a checked model satisfies all chosen commitments. This establishes satisfiability of the encoding, not metaphysical or physical possibility.
- **Unresolved:** neither certificate exists; a failed proof search is not a refutation.
- **Conditional implication:** a checked theorem derives a conclusion from the listed premises, independently of whether those premises are true.

An overlap can have both a valid model and an alleged inconsistency certificate only if encodings/profiles differ or something is wrong; treat that as a verification defect, not as a fourth philosophical status. Do not create new fields that compete with frontier closure or attempt outcomes.

For every delivered slice, report: exact seed and semantic profile; certified minimal cores; witnessed controls; surviving unknowns; newly composed theorems; root-route premise delta; limitations and next blocker. Count syntactic configurations only with their dimensions/bounds; report independently whether provable equivalences allow a reduction in distinct theories.

## First end-to-end slice

Use necessary nonemptiness versus a necessary individual (#435, #445) as the seed, with fixed identity/domain semantics made explicit. Verify at least one nontrivial incompatibility core and one model-witnessed alternative, and leave a genuinely undecided variant unresolved. Then expose the report from the existing corpus CLI/dossier and frontier explorer, with deterministic ordering and a focused regression test. Implementation acceptance and follow-on tasks are tracked in #477.

The existing finite models (#414/#443), proved schemas (#412/#447) and proposed bridge search (#415) are reusable inputs. No graph database, duplicate SAT infrastructure, assumption guessing by text similarity, or automatic promotion of research relations to implication is justified by this loop.

## Incompatibility clean-up pass

The clean-up pass (#576) is the standing complement of [argument-first investigation](systematic-corpus-loop.md#frontier-investigations-argument-first-decomposition-on-demand) (#565). Argument-first paints a case in large strokes: a thesis, its end-to-end route and its strongest rivals. The clean-up pass comes afterwards and removes positions that cannot hold together, by running the research cycle above routinely instead of ad hoc. It adds no entity kind, schema or status: its outputs are the configuration, model, attempt and result records already described here.

1. **One shared vocabulary only.** A candidate group is a set of existing statements whose Lean declarations take the same typed parameters, read under one semantic profile. Statements in different vocabularies are not compared until a reviewed interpretive bridge relates them; similarity of names or prose is never a bridge (#415 stays candidates-only).
2. **Non-trivial cores only.** Every member is a held position: a sourced claim, a root-path premise or a recorded rival. A core that only shows that a strong enough premise contradicts anything is not reported as a dilemma.
3. **Seed from the root.** Start from root-path open premises (`corpus.py frontier --reaching-root`) and their recorded rivals, then take the vocabulary those statements share.
4. **Certify, minimize, witness.** Derive `False` in Lean from exactly the group (a `STMT-CONFIGURATION-FALSE` result, composing existing theorems where they exist), check each single removal with a registered model, and register the models for the maximal surviving subsets.
5. **Classify and persist.** Each examined set is *verified incompatible* (a certified core), *model witnessed* (a registered model of all members) or *unresolved*; unresolved is never impossible. Persist the group as a configuration record, the search as an attempt (including rejected seeds and why), and each certified core as a result.
6. **Count eliminations, not dilemmas.** A core is progress when it eliminates a family of rival positions or closes or moves a root-path premise. Report the root-route premise delta, usually "no change".

First slice: `CONFIG-MEGARIAN-CAPACITY-MOTION`. In the *Metaphysics* IX.3 capacity/actuality vocabulary (`Being`, `Respect`, `MovedIn`, `InAct`, `CanBe`), the Megarian thesis, present motion (a root-path premise), motion's incompleteness and the ability of what is moved are jointly inconsistent (`MEGARIAN-CAPACITY-MOTION-INCOMPATIBLE`), and each three-member subset has a registered model. The Kripke modal and necessary-individual vocabularies have certified cores (`CONFIG-NECESSARY-INDIVIDUAL`) but no root-path premise yet, so they cannot reach the root-seeded territory matrix; `ATTEMPT-MEGARIAN-CAPACITY-CORE-CLEANUP` records this inventory and the rejected seeds. Results that conclude the negation of a rival, rather than `False`, reach the matrix only after #548.

## Emergent positions and the territory matrix

`python3 scripts/corpus.py territory [--json]` (#512) computes positions from existing records only; it names no worldview and writes no record. The `scripts/territory.py` docstring lists exactly which records feed each relation: certified cores (registered non-transcription results deriving `STMT-CONFIGURATION-FALSE`, and `refutes` relations with such a result, premises plus refuted statement), entailments (all other registered non-transcription results except consistency results), witnesses (registered models' satisfied sets, consistency results' commitment sets) and attestation (claims grouped by source author). The atom universe is bounded and built in one round from the open root-path premises and their recorded rivals. A local position is a maximal subset of one conflict-linked component containing no certified conflict, closed under entailment; global positions are their products and are counted exactly but enumerated only up to a bound. Each position is `witnessed` or `not_known_inconsistent`, with a hash ID. The matrix marks each root-path premise `in`/`out` for the positions of its component and `undetermined` elsewhere. Split rows are territories ranked by root routes and dependents. `common_ground_candidate` rows (in every position of their component, at least one witnessed, no recorded rival) are candidates only: marking one still needs the #501/#378 evidence, and on sparse rival sourcing "no recorded rival" usually means unexamined, not agreed. A recorded rival without a certified conflict leaves the row `contested_uncertified`.
