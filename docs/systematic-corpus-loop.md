# Systematic corpus loop

Advance substantial arguments toward the [root goal](https://github.com/moritzbrantner/truth-core/issues/143), not statement or theorem counts. Constraint discovery within frontier investigations leads; source campaigns serve decisive gaps. `AGENTS.md` governs source fidelity, Lean/Comparator verification, and review.

## Frontier investigations: argument-first, decomposition on demand

For one owner-scoped thesis or argument (#565):

1. **Map the whole case.** State the conclusion and downstream purpose, strongest positive argument and serious rivals, existing statement/theorem IDs, explicit assumptions, and current bottleneck.
2. **Verify the conditional structure.** Formalize load-bearing inferences and test omissions or rival models. A verified implication does not establish its premises.
3. **Force choices before expanding premises.** Follow the [certified fork workflow](configuration-elimination-loop.md#certified-forks-as-the-default-frontier-workflow): compose implications, certify incompatible bundles, prove coverage of substantive branches, and seek models of survivors under a fixed background. Investigate a child premise only when its resolution would discriminate those branches; do not default to another layer of assumptions.
4. **Decompose on demand.** Separate canonical statements/tasks only when inference, a real disagreement, independent justification, reuse, or a source/proof invariant requires it. Do not manufacture atomized taxonomies or duplicate issues.
5. **Recompose immediately.** Connect the child's actual result to its parent, update unresolved assumptions and alternatives, and continue the same argument. A failed route yields a recorded countermodel or precise blocker, not a stronger invented premise.

Keep the readable case and rivals in its existing issue/note; keep proofs, sources, countermodels, and substantive attempts in their canonical records/dossiers. No parallel research registry. The [#565 pilot note](notes/argument-first-pilots-565.md) illustrates the method with #564 and #563.

### Machine-checkable issue acceptance (#949)

An issue can declare its completion evidence in **one** fenced block in its body
or one designated comment. This is an optional reconciliation aid, not another
corpus registry or a permission to close issues automatically:

````markdown
```truth-core-acceptance
results: [RESULT-ID]
theorems: [TruthCore.Namespace.theorem]
statements: [STMT-ID: closed, STMT-OTHER: sourced]
configurations: [CONFIG-ID]
attempts: [ATTEMPT-ID]
```
````

Each field is optional; at least one nonempty bracketed list is required. IDs
are comma-separated and unquoted. `results` requires an existing
`solution-present` result record. `theorems` requires a registered result's
theorem and its corresponding source declaration in the checked-out revision.
For statements, `closed` accepts any computed frontier closure, `proved`
requires the non-transcription `proved` closure, and `sourced` requires an
attributed source claim with a locator. Configuration and attempt IDs require
records to exist; a failed attempt is **not** evidence of derivability.

```bash
python3 scripts/corpus.py issues                        # read-only gh issue list
gh issue list --state open --limit 1000 --json number,title,body,url,comments > /tmp/truth-core-issues.json
python3 scripts/corpus.py issues --from /tmp/truth-core-issues.json --json
python3 scripts/corpus.py issues --from /tmp/truth-core-issues.json --for STMT-ID
python3 scripts/corpus.py dossier STMT-ID --issues-from /tmp/truth-core-issues.json
```

The report distinguishes `delivered`, `missing`, `malformed` and `untracked`;
its JSON includes a reverse index from canonical IDs to issue numbers. It is a
read-only projection of the checked-out corpus and optional issue snapshot,
not a live Lean/Comparator/source verification or proof of philosophical truth.
Run it on `main` to reconcile the current main branch; a feature checkout
reports that checkout's hypothetical state. Human/coordinator review decides
whether an issue can actually close.

## Semantic grounding of metaphysical relations

For newly introduced or substantially reinterpreted relations involving causation,
dependence, grounding, contingency, necessity or explanation, follow the semantic
grounding requirement in `AGENTS.md`. Before philosophically significant relations
support a metaphysical conclusion, answer these questions in their existing
definition/disambiguation records or linked research notes, with evidence and
explicit **OPEN** burdens where answers remain
undefended:

1. **Meaning.** What does the relation mean in ordinary language, without relying
   on its symbol or formal properties to explain it?
2. **Phenomena.** What are its clearest concrete examples and counterexamples,
   and why do they instantiate or fail to instantiate this meaning? Explicitly
   record why examples remain unavailable when that is the case.
3. **Exclusions.** Which nearby cases fail to instantiate it, and what excludes
   them? Distinguish efficient causation, grounding and conservation rather than
   treating their names as interchangeable.
4. **Properties.** What independently justifies each property the argument uses,
   especially asymmetry, transitivity and well-foundedness, for this interpreted
   relation on the stated domain? A physical example or the word “essential” is
   not a proof of well-foundedness. A finite or inductively generated model proves
   properties of that construction; it does not silently discharge well-foundedness
   of actual dependence. State whether a property concerns one local relation or
   a union of relations: properties of each component need not hold for the union.
5. **Abstraction.** Why does an interpretation illustrated by physical causation,
   electricity, motion or support license the proposed claim about existence or
   general metaphysical dependence? Identify and defend the bridge, its domain
   and limits; shared vocabulary or relational form does not supply it.
6. **Rivals.** How does the interpretation fare against serious competing accounts
   of the same phenomena and explanatory task? Preserve their strongest objections
   and any unresolved disagreement.

Prioritize the independent property justifications and the abstraction bridge
(questions 4–5). A pure relational theorem establishes a conditional mathematical
consequence, not the causal applicability of its relation. Such theorems remain
useful and may be developed with open interpretive burdens, but must not be
advertised as metaphysical support until those burdens are defended. Preserve
the exact assumptions and unmet burdens in the existing records; this requirement
adds no registry or verification gate and changes no source-fidelity standard.
Independent justification may be a defensible philosophical argument, with its
assumptions and defeaters explicit; it need not be empirical evidence or a kernel
proof of every premise. Source attribution and formal consequence remain distinct
from that independent defense.

## Progress is depth on the root path, not volume

Use `python3 scripts/corpus.py frontier --routes` and `--reaching-root`. Report exactly what changed for root-facing open premises, including **no change** for unconnected outposts.

- An open premise is **bare** (no source claim states or supports it), **supported** (only a `supports` relation backs it, its note recording the gap, or only a bibliographic citation without pinned bytes or a permanently unavailable witness states it) or **stated** (a claim on a pinned source states it); supported and stated premises are undefended (#987). First remove bare gaps, then close the recorded gaps of supported premises and independently defend stated ones.
- A transcription (`opaque_atoms`, `single_application`, `assembly`, `instantiation`) does not close an open conclusion; it propagates closure only when **all** its premises are closed. An alleged refutation counts only when verified **and** all its premises are closed.
- Replacing one open premise with narrower leaves ("relocation") is legitimate exploration even when it adds bare premises; `frontier-diff` lists them for visibility and `thickness` reports the derivations gained (owner decision 2026-11-07, superseding the no-bare rule of #987). Report supported leaves as supported, not as stated.
- **Idle verified work is a defect, not progress (owner direction 2026-11-07).** A library of verified results that reaches no root route does nothing for the case. The modal library (about 89 results) sat disconnected while the necessary-being routes never used modal necessity. Before each round, list the disconnected verified families (`truth orphans`) and connect them first. Fork every load-bearing ambiguous term in this order: COVERAGE and EXCLUSIVITY premises, then a typed sense enum, then a result per sense, then a joint theorem by cases. Only after that attack rival definitions. See AGENTS.md, "Connect every library to the case".
- Neither source attribution, a conditional theorem, a narrative, nor an unverified model proves a premise. Preserve exact semantics, assumptions, and surviving rivals; see [configuration elimination](configuration-elimination-loop.md).

## 1. Campaign: a meaningful source objective

A coarse GitHub issue names a coherent source objective and completion criteria; it is not a second status tracker. Choose source reading when a live argument needs that evidence, not just to grow coverage.

## 2. Candidate: the next contiguous source range

`corpus/candidates/*.json` queues chapter-sized or similarly coherent ranges. Use `python3 scripts/corpus.py next` when doing source ingestion:

1. Materialize the verified witness; read the whole range and context before splitting it.
2. Proceed in source order. Record substantive readings and inferential steps, reuse existing identities, and preserve defensible alternatives. Skip filler; not one claim per sentence.
3. Apply the atomic research/proof contract in `AGENTS.md`. Keep the same candidate and advance its locator after a partial batch; delete it only when its range is exhausted.

## PR boundary

Ship one coherent verified argument cluster, a complete candidate range, or a reviewable part of it (about 5–10 claims at most, not a quota). Report premise effects and remaining gaps; persist substantive failed attempts before handoff. A PR boundary does not end the investigation.

## Parallel lanes

Follow the A/B/C ownership in `AGENTS.md` (#416). Shared Lean imports and documentation tables are generated, never hand-edited; rerun `scripts/root-imports.sh --write` and `python3 scripts/docs_index.py --write` after merging `origin/main` before pushing.

## Completion and coverage

A source range is complete once read and its relevant substantive content represented or explicitly judged out of scope; it need not generate a claim for every sentence. A frontier slice ends only when its conclusion is established under the stated standards, the route is decisively defeated, or a precise obstacle requires owner judgment. A conditional result with open premises is not established.

## Failed proofs feed research

Record the missing premise and strongest countermodel, not an added axiom or stronger source reading. First test whether the failure exposes a countermodel, incompatible bundle or useful fork. Pursue a targeted child argument or source candidate when it can resolve that fork; do not automatically expand the premise queue.

## Campaign handoff

When a campaign finishes, follow its known successor, seed its first source-range candidate, then close it. Keep one current handoff. Stop only for genuinely unavailable evidence, a scope/modeling choice requiring the owner, a repository defect, or an ambiguous successor.

## Campaign ordering

Prioritize the active frontier slice and its blockers; source campaigns follow those needs. Within a campaign, finish the current range, backfill necessary foundations, then continue the source while useful. The original Aristotle `Physics` III → I–II → IV–VIII order remains a fallback, not a competing global priority.
