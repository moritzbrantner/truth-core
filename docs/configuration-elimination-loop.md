# Configuration elimination and theorem composition

Research strategy for #477. This is an additional *use* of Truth Core's existing corpus loop, not a new ontology or status authority. The source-reading loop in [systematic-corpus-loop.md](systematic-corpus-loop.md) and the proof boundaries in [AGENTS.md](../AGENTS.md) remain binding.

## Purpose

Prefer a small number of general, verified constraints that eliminate whole families of incompatible configurations to independently evaluating every combination of propositions. Persist each attempt and theorem so that later work composes earlier results. Progress means a justified change in known implications, incompatible theories or root-premise closure, **not** larger proposition counts or a smaller graph.

A configuration is a finite set of **existing statement IDs** interpreted under an explicitly named semantic profile. Its profile fixes the pertinent logic, accessibility relation, quantifier domains, cross-world identity and any other choices that affect the meanings of those statements. Different profiles cannot silently share a contradiction or a model. Statements that only *sound* equivalent remain distinct until a checked equivalence is available.

## Research cycle

1. **Select a load-bearing seed.** Start with an unresolved dossier and its existing statements, definitions, disambiguations and related registered models/schemas. Prefer root-reaching premises, shared dependencies or an objection with a falsifiable target. For necessary existence, begin with #435–#441 and PR #445.
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
