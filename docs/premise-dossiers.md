# Premise dossiers and research attempts

`python3 scripts/corpus.py dossier STMT-ACT-SIMPLY-PRIOR-TO-POTENCY` collects the
statement, Lean declaration, source readings/support, linked definitions and
senses, alternatives/objections, arguments and results, transcriptions, attempts,
and current root-route contribution. `--json` emits the same projection as JSON;
`--root STMT-…` selects a different root. `--all --json` emits the complete index
in one call for static explorer generation. Unknown statements or roots fail.

The explorer links `/dossiers/<STMT-ID>/` from every statement page. CLI and
explorer consume the same Python projection and authoritative frontier rules.
Closure classification and *established* are separate: a conditional proof can
be classified as proved while depending on open premises. Dossiers do not
introduce another closure rule.

A route contribution is membership in the route's current
`open_premise_statement_ids`: the statement is either one counted open leaf or
it is not. The full route cost is shown alongside it. This is **not** a
counterfactual claim about how much the route would shrink if the premise were
proved; alternative proofs and shared leaves can change that calculation.

## Attempt records

The owner approved `corpus/attempts/*.json` in #413. These records describe work,
not propositions, source readings or inference steps. They do not participate in
the logical graph or establish/refute their targets. Backfilled records refer to
the original merged evidence and preserve its limitations.

```json
{
  "id": "ATTEMPT-EXAMPLE",
  "statement_ids": ["STMT-ACT-SIMPLY-PRIOR-TO-POTENCY"],
  "date": "2026-10-26",
  "kind": "source-search",
  "outcome": "blocked",
  "summary": "The available interpretation does not supply the required premise.",
  "evidence": [],
  "blocker": "Obtain and inspect the required pinned witness."
}
```

- `statement_ids` is nonempty and names existing independent statements; duplicates
  are rejected. One attempt may concern several precisely named targets.
- `date` is a calendar date in `YYYY-MM-DD` form.
- `kind` is `derivation`, `refutation`, `reading`, `countermodel`, or `source-search`.
- `outcome` is `succeeded`, `failed`, `blocked`, or `superseded`. It describes the
  attempt, never the truth status of its targets. A successful omission model, for
  example, can leave every philosophical premise open.
- `summary` records the finding, rejected interpretation or failed inference and
  its limits. `blocker` is required for blocked attempts, optional otherwise.
- `evidence` lists existing result or claim IDs, or `PR-<positive number>` for a
  truth-core pull request. It may be empty when no evidence reference exists yet;
  the dossier makes that absence visible. Local result/claim references resolve
  during `corpus.py check`. PR references are syntax-checked and link to this
  repository; checking their remote existence is outside the offline validator.
  Neither a PR reference nor an attempt outcome is proof verification evidence.

IDs are stable. Correct an inaccurate attempt record in place; preserve earlier
failed approaches as separate attempts when the approach genuinely differs.
A later successful proof does not rewrite the earlier failure into success.

## Explicit links, not semantic guesses

Countermodel attempts are linked by their target `statement_ids` and `kind`.
Their evidence links to the relevant existing result or PR. A result description
containing the word "countermodel" is not itself a structured model registration.
The dossier also lists existing results explicitly classified as instantiations
by the frontier report; these are not automatically instances of a future generic
schema. No separate mode-2 model registry (#414) or mode-5 schema registry (#412)
exists at this point. The dossier states that boundary and does not infer missing
links from similar words, theorem names or embeddings. Those registries can later
supply their own explicit links without changing premise identity or closure.
