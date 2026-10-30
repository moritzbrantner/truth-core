# Configuration elimination and theorem composition

Research strategy for #477. This is the default frontier research strategy within Truth Core's existing corpus loop, not a new ontology or status authority. The source-reading loop in [systematic-corpus-loop.md](systematic-corpus-loop.md) and the proof boundaries in [AGENTS.md](../AGENTS.md) remain binding.

## Purpose

Prefer a small number of general, verified constraints that eliminate whole families of incompatible configurations to independently evaluating every combination of propositions. Persist each attempt and theorem so that later work composes earlier results. Progress means a justified change in known implications, incompatible theories or root-premise closure, **not** larger proposition counts or a smaller graph.

A configuration is a finite set of **existing statement IDs** interpreted under an explicitly named semantic profile. Its profile fixes the pertinent logic, accessibility relation, quantifier domains, cross-world identity and any other choices that affect the meanings of those statements. Different profiles cannot silently share a contradiction or a model. Statements that only *sound* equivalent remain distinct until a checked equivalence is available.

## Certified forks as the default frontier workflow

The unit of research is a constrained space of serious alternatives around one substantive question. Existing issues supply evidence and ownership; completing issues or generating propositions is not the objective. First harvest consequences of the existing corpus, then add only the records required to certify a consequential finding.

### Fix the arena and the proposed finding

State the question, typed vocabulary, semantic profile, background `B`, and existing theorem/statement IDs. Expose domain nonemptiness, modal frame, identity, and dependence assumptions. Test the background for satisfiability; a contradiction in `B` makes every branch theorem vacuous. If no background witness is available, report that limitation and keep conclusions conditional.

Choose one bounded certificate target:

| Finding | Proof obligation | Meaning |
| --- | --- | --- |
| Exhaustive fork | `B → (A ∨ C ∨ D)` | At least one branch holds under B |
| Exclusive fork | Coverage plus pairwise incompatibility under B | Exactly one branch holds |
| Incompatible core | `B → ¬(P ∧ Q ∧ R)` | At least one commitment must be rejected |
| Forced consequence | `B → (P → Q)` | Accepting P also commits to Q |
| Equivalence | `B → (P ↔ Q)` | The alternatives coincide under B |
| Branch witness | An explicit model satisfying B and all branch commitments | The encoded branch is satisfiable in that model class |

The letters are schematic obligations, not new opaque philosophical atoms. Use typed existing content. `P ∨ ¬P` alone is not a substantive finding: show differing consequences for serious alternatives. Coverage and exclusivity are distinct; branches may overlap. An inconsistent bundle gives a dilemma about which commitment to abandon, not a refutation of a preferred member. A bounded list of explored configurations is not an exhaustive metaphysical partition.

### Search, certify, minimize, propagate

1. **Harvest first.** Run `python3 scripts/corpus.py related <STMT-ID>` for the seed to find recorded connections and earlier attempts (discovery only). Inspect exact bound theorem types and dossiers; compose implications before introducing premises. Use `python3 scripts/corpus.py territory --json` and existing configuration/model tools for orientation. Territory positions are derived bounded projections, not automatically model-witnessed or collectively exhaustive philosophical alternatives.
2. **Explore a bounded family.** Declare the commitments, model sizes or other search bounds, and the next candidate certificate. Try proof search and explicit model construction together. Lean tactics, evaluation, enumeration and already available solvers propose evidence; failed search and timeouts leave a target unresolved. No new solver dependency or service is authorized by this method.
3. **Certify the exact claim.** Freeze Challenge before Solution. Use existing statement, inference, argument, result, model and attempt records and the required Lean/binding/Comparator/NanoDa checks. A proposed coverage theorem must be checked just like an implication. A formal model is not a proof of metaphysical possibility.
4. **Minimize honestly.** Reduce an inconsistent bundle by testing removals under the same B. A checked model for every single-member deletion certifies inclusion-minimality, not minimum cardinality. Failure to prove a smaller core does not certify minimality. If a deletion is unresolved, publish the certified incompatible bundle with minimality explicitly unproved. Likewise, do not call an implication's assumptions weakest merely because proof search needed them.
5. **Propagate without enumerating everything.** A certified core excludes every superset in the same semantic arena. Apply certified implications transitively, compose forks, and reuse checked equivalences to avoid redundant search. Keep exact dependencies; background assumptions do not disappear during composition. Do not mix witnesses from different models to claim joint satisfiability. Preserve distinct canonical IDs even when equivalent.
6. **Recompose and persist.** Explain which choices are now forced, which bundles are excluded, which branches have joint witnesses, and which remain unresolved. Persist each substantive attempt and its blockers before changing direction. Recompute the existing frontier and territory views; neither a conditional elimination nor a position lacking known conflicts closes a premise.

### Bounded cycles and sustained work

Use one current investigation/handoff. Record the baseline revision, question/profile, next certificate, search bound or effort budget, and completion criterion before each cycle. A cycle ends with a verified constraint, a checked witness, or a precise persisted blocker. After two consecutive cycles without new certified evidence, change tactic or candidate within the same arena; do not repeat failed searches or grow a speculative premise tree. If no useful bounded target remains, checkpoint and report the obstruction.

A long run repeats these cycles until its user-specified deadline, cancellation, resource limit, or a genuine blocking decision. Checkpoint at every reviewable slice and before context handoff. Continue from that checkpoint rather than assuming one agent invocation will run all day. Keep expensive verification queued and ownership isolated according to AGENTS.md; interactive Lean diagnostics do not replace final verification. The existing local-service experiment is bounded and must fall back to the CLI rather than delaying research.

For every slice, report one compact result: question and B; exact certificates and witnesses; eliminated families with counting bounds if counted; surviving branches; unresolved coverage/minimality; root-premise delta; next decisive test. A conditional fork may be a completed research finding while its root conclusion remains open. No quota of lemmas, issues, PRs or eliminated configurations substitutes for this evidence.

For an initial existence/dependence arena, test whether the existing vocabulary supports coverage by a necessary existent, a contingent dependence-root, or non-well-founded dependence. This is a candidate, not an established theorem or required ontology. Keep contingent distinct from merely nonnecessary unless the background justifies identification; do not equate non-well-foundedness with an infinite descending sequence without proving the connection under explicit assumptions. Use a different fork if the existing semantics do not support this one faithfully.

## Research cycle

1. **Select a load-bearing seed.** Take it from an end-to-end case and its decisive fork ([argument-first method](systematic-corpus-loop.md#frontier-investigations-argument-first-decomposition-on-demand)), not from an inventory of distinctions. Start with an unresolved dossier and its existing statements, definitions, disambiguations and related registered models/schemas. Prefer root-reaching premises, shared dependencies or an objection with a falsifiable target. For necessary existence, begin with #435–#441 and PR #445.
2. **Compose what is already established.** Search bound Lean theorem types and checked schema instances, not merely prose similarity or `supports`/research graph edges. Track exact hypotheses and theorem IDs. Do not restate a derived theorem as a new independent premise.
3. **Try to eliminate families.** Formalize proposed contradictory combinations as explicit hypotheses and derive `False` in Lean. Verify with the applicable Comparator/NanoDa gate. Minimize the premise core by independently checking each proposed removal. Only a checked unsatisfiability theorem licenses pruning its supersets *under the same semantics*.
4. **Try to witness survivors.** Reuse the certified finite-model registry. An explicit model satisfying all selected commitments witnesses formal satisfiability in that specified semantics; no model found means **unresolved**, not impossible. A finite search is exhaustive only for its declared bound unless a separate general small-model result is proved.
5. **Persist every substantive outcome.** Store a new formal statement/argument/result only for an actual proposition/inference. Store successful, failed and blocked investigation records in `corpus/attempts/` with exact targets and evidence. Use `corpus/models/` for certified model evaluations and `instance_of_schema` for checked theorem instances. Fix inaccurate attempt records in place; do not erase genuinely earlier failed approaches.
6. **Recompute the frontier.** Run `corpus.py frontier --routes` and `--reaching-root`, compare root-path open premises before/after, and report what genuinely closed versus what merely moved or gained a research link. The existing closure engine remains sole authority.
7. **Choose the next question.** Prefer the next constraint, witness or fork that discriminates surviving positions across several verified paths. Investigate an open premise when it has that demonstrated role, while retaining meaningful alternatives as complete theories with replacement explanations.

## Reporting contract

A configuration report should distinguish:

- **Verified incompatible:** a checked theorem proves the conjunction inconsistent; include the semantics and inclusion-minimal certified core. In classical logic, do not promote arbitrary consequences of the inconsistent conjunction as explanatory results.
- **Model witnessed:** a checked model satisfies all chosen commitments. This establishes satisfiability of the encoding, not metaphysical or physical possibility.
- **Unresolved:** neither certificate exists; a failed proof search is not a refutation.
- **Conditional implication:** a checked theorem derives a conclusion from the listed premises, independently of whether those premises are true.

An overlap can have both a valid model and an alleged inconsistency certificate only if encodings/profiles differ or something is wrong; treat that as a verification defect, not as a fourth philosophical status. Do not create new fields that compete with frontier closure or attempt outcomes.

For every delivered slice, report: exact seed and semantic profile; certified minimal cores; witnessed controls; surviving unknowns; newly composed theorems; root-route premise delta; limitations and next blocker. Count syntactic configurations only with their dimensions/bounds; report independently whether provable equivalences allow a reduction in distinct theories.

## Vacuity audit for a configuration verdict

For each incompatible bundle and omission witness, report the following distinctions before interpreting the result philosophically (#471). State which are ruled out by explicit hypotheses, witnessed in the same interpretation, or unresolved. Do not silently add a nonvacuity premise to an already frozen Challenge.

| Boundary | Required report |
| --- | --- |
| Unreachable worlds | Identify the selected root and the worlds quantified over. A root-component theorem does not constrain disconnected worlds. A witness outside the accessible component does not establish a possibility at that root. |
| Empty concrete extension | Distinguish `∃ x, ExistsAt w x` from an inhabited candidate carrier. A populated carrier can have no concrete existent at the selected world; guarded universal causal/explanatory claims can then hold vacuously. |
| Empty Lean carrier | State whether the world and individual types can be empty. A supplied `w : World` excludes an empty world type for that application, but not an empty individual type or empty concrete extension. Globally quantified validity can hold on an empty world type without supplying any actual world. |
| Inconsistent background | A proof of `B → C` does not witness B. Supply a joint model of all of B, or mark satisfiability unresolved. Separate a contradiction already in B from one introduced by the tested commitments. |
| Non-serial accessibility | At a root without successors, every `Box P` holds and every `Dia P` fails. Necessary population or necessary-if-existent conditionals need not provide an actual/possible bearer. State seriality or reflexivity where used; neither follows merely from having a root. |

These are separate checks: seriality supplies an accessible world, not an existent there; candidate inhabitedness supplies a term, not `ExistsAt`; and a model of each background conjunct separately is not a joint background model. A deletion witnessed only by an empty extension remains a valid logical deletion control, but must not be advertised as a populated rival ontology.

Existing controls illustrate the boundaries without adding new philosophical commitments. `WellFoundedSource.emptyWorld` has Unit worlds and Bool candidates but no existents; its well-foundedness and universal external-cause certificates coexist vacuously. `S5Research.disconnected` distinguishes a root component from the whole frame. `StandardCorrespondence.d_iff_serial` explicitly permits empty world types and identifies D validity with seriality, without asserting that a world exists. These examples are not substitutes for checking the exact background of a new configuration.

## First end-to-end slice

Use necessary nonemptiness versus a necessary individual (#435, #445) as the seed, with fixed identity/domain semantics made explicit. Verify at least one nontrivial incompatibility core and one model-witnessed alternative, and leave a genuinely undecided variant unresolved. Then expose the report from the existing corpus CLI/dossier and frontier explorer, with deterministic ordering and a focused regression test. Implementation acceptance and follow-on tasks are tracked in #477.

The existing finite models (#414/#443), proved schemas (#412/#447) and proposed bridge search (#415) are reusable inputs. No graph database, duplicate SAT infrastructure, assumption guessing by text similarity, or automatic promotion of research relations to implication is justified by this loop.

## Incompatibility clean-up pass

The clean-up pass (#576) is the standing complement of [argument-first investigation](systematic-corpus-loop.md#frontier-investigations-argument-first-decomposition-on-demand) (#565). Argument-first paints a case in large strokes: a thesis, its end-to-end route and its strongest rivals. Run the clean-up pass during case construction and branch exploration, removing positions that cannot hold together through the research cycle above; do not postpone it until after recursive premise expansion. It adds no entity kind, schema or status: its outputs are the configuration, model, attempt and result records already described here.

1. **One shared vocabulary only.** A candidate group is a set of existing statements whose Lean declarations take the same typed parameters, read under one semantic profile. Statements in different vocabularies are not compared until a reviewed interpretive bridge relates them; similarity of names or prose is never a bridge (#415 stays candidates-only).
2. **Non-trivial cores only.** Every member is a held position: a sourced claim, a root-path premise or a recorded rival. A core that only shows that a strong enough premise contradicts anything is not reported as a dilemma.
3. **Seed from the root.** Start from root-path open premises (`corpus.py frontier --reaching-root`) and their recorded rivals, then take the vocabulary those statements share.
4. **Certify, minimize, witness.** Derive `False` in Lean from exactly the group (a `STMT-CONFIGURATION-FALSE` result, composing existing theorems where they exist), check each single removal with a registered model, and register the models for the maximal surviving subsets.
5. **Classify and persist.** Each examined set is *verified incompatible* (a certified core), *model witnessed* (a registered model of all members) or *unresolved*; unresolved is never impossible. Persist the group as a configuration record, the search as an attempt (including rejected seeds and why), and each certified core as a result.
6. **Count eliminations, not dilemmas.** A core is progress when it eliminates a family of rival positions or closes or moves a root-path premise. Report the root-route premise delta, usually "no change".

First slice: `CONFIG-MEGARIAN-CAPACITY-MOTION`. In the *Metaphysics* IX.3 capacity/actuality vocabulary (`Being`, `Respect`, `MovedIn`, `InAct`, `CanBe`), the Megarian thesis, present motion (a root-path premise), motion's incompleteness and the ability of what is moved are jointly inconsistent (`MEGARIAN-CAPACITY-MOTION-INCOMPATIBLE`), and each three-member subset has a registered model. The Kripke modal and necessary-individual vocabularies have certified cores (`CONFIG-NECESSARY-INDIVIDUAL`) but no root-path premise yet, so they cannot reach the root-seeded territory matrix; `ATTEMPT-MEGARIAN-CAPACITY-CORE-CLEANUP` records this inventory and the rejected seeds. Results that conclude the negation of a rival, rather than `False`, reach the matrix only after #548.

## Emergent positions and the territory matrix

`python3 scripts/corpus.py territory [--json]` (#512) computes positions from existing records only; it names no worldview and writes no record. The `scripts/territory.py` docstring lists exactly which records feed each relation: certified cores (registered non-transcription results deriving `STMT-CONFIGURATION-FALSE`, and `refutes` relations with such a result, premises plus refuted statement), entailments (all other registered non-transcription results except consistency results), witnesses (registered models' satisfied sets, consistency results' commitment sets) and attestation (claims grouped by source author). The atom universe is bounded and built in one round from the open root-path premises and their recorded rivals. A local position is a maximal subset of one conflict-linked component containing no certified conflict, closed under entailment; global positions are their products and are counted exactly but enumerated only up to a bound. Each position is `witnessed` or `not_known_inconsistent`, with a hash ID. The matrix marks each root-path premise `in`/`out` for the positions of its component and `undetermined` elsewhere. Split rows are territories ranked by root routes and dependents. `common_ground_candidate` rows (in every position of their component, at least one witnessed, no recorded rival) are candidates only: marking one still needs the #501/#378 evidence, and on sparse rival sourcing "no recorded rival" usually means unexamined, not agreed. A recorded rival without a certified conflict leaves the row `contested_uncertified`.
