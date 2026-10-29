# Proposition structure inspector

## Design and migration scope

Statement identity remains in `corpus/statements`; definitions and disambiguations
remain semantic records. `BindTypes.lean` and `corpus.py bind-check` own theorem
binding, `UnusedPremises.lean` owns conservative proof-term usage, and the existing
result/Comparator/NanoDa pipeline owns certification. This inspector adds a derived
view of elaborated expressions, without changing any of those authorities.

The first migration slice covers the broad and distinct-cause readings in
`TruthCore/Greek/Plato/Timaeus.lean` and the Catholicism classical-attributes
boundary. It does not migrate the corpus to a new formula language. Whole
arguments remain the research unit; internal nodes require no authored records.

The Lean extractor preserves ordered full applications, binder domains and
scope, expression types, readable expressions and declaration references.
Connective labels annotate the actual expression tree rather than replacing it
with independent atoms. Node addresses are local to the declaration and report
inputs; they are not new statement identities. Unsupported or bounded extraction
remains visible as a typed boundary. A primitive parameter or field is distinct
from an extraction failure.

Unfolding is explicit, project-owned and bounded. Library declarations remain
named boundaries. Reachable structures expose their field types, including laws;
displaying a law is not evidence that an arbitrary interpretation satisfies it.
No logical normalization or semantic rewrite is introduced. In particular no
branch is selected from a disjunction and no quantifiers are commuted.

`HasClassicalAttributes` remains a primitive signature field. The nine predicates
imply that field only under `ClassicalAttributesSuffice`, an explicit open
one-way premise. The relevant existing definition record explains the mapping;
neither the field nor its presentation is replaced by a conjunction or an
equivalence.

The static explorer consumes a report generated from Lean during its input
preparation. Browser expansion reveals this bounded derived view. Source/input
digests bind the artifact to its inputs; a Git revision is context, not a cached
proof verdict. Formula structure, corpus interpretation and argument/result
support are displayed separately. Missing reports and coverage limits remain
visible. Structural presentation discharges no root premise.

## Implementation handoff

Generate the bounded static input after building with the pinned environment:

```bash
python3 scripts/worker_env.py -- python3 scripts/corpus.py structure-report --build-input
python3 scripts/corpus.py structure-report --check-input
```

Inspect a statement with an explicitly selected project body:

```bash
python3 scripts/worker_env.py -- python3 scripts/corpus.py structure \
  STMT-CAUSE-PRINCIPLE-BROAD --json \
  --unfold TruthCore.Greek.Plato.Timaeus.CausePrinciple
```

The command asks Lake to establish compiled/source freshness for selected
modules before extraction. The static artifact records input hashes and rejects
changed source/corpus inventories. CI and Pages produce it alongside the existing
configuration input; browser builds validate it without running Lean. Local
builds without the artifact visibly report unavailable coverage. Published
expansion is limited to the selected first-slice bodies; arbitrary requested
project bodies remain available through the CLI. The default extraction depth
is bounded and truncation stays typed and visibly partial. Source discovery is a
locator; Lean validates the declaration, not the locator's textual match.

Focused regressions are `scripts/test_proposition_structure.py`,
`scripts/test_proposition_structure_lean.py` and the explorer's structure tests.
The Lean fixture checks two-element separators for argument order, shared
versus separate existential witnesses, and alternating versus uniform
quantifiers. These are tooling fixtures, not new corpus research results.

Branch: `feat/proposition-structure`, based on
`47635b55a2684af6f164e8b03397bac25291e536`. The repository has no installed
`conventions.json`, lock or `.conventions/`; the requested public agent-tool
catalog was consulted, and no conventions were installed or updated.

Implementation is split between the Lean extractor, Python derived-report
pipeline and existing explorer presentation. Integration owns CI artifact
generation, final validation and the reviewable PR. Validation results and exact
delivered head will be recorded in the PR; this document is the design and scoped
handoff, not another proof-status registry.
