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

## Inspector commands

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

The inspector was delivered by merged PR #726. Its implementation remains the
expression-presentation authority, not a certificate or proof-status authority.

## Current handoff: certified strength comparisons

Selected base: `65176b5c` (merged PR #727). Follow-up branch:
`fix/strength-application-binding`. Exact delivered revision and CI are recorded
in the follow-up PR handoff. This stage uses the
existing statement, inference, argument, result and relation records; there is
no all-pairs search and no solver service.

`scripts/strength_comparisons.py` is the single semantic owner of the narrow
comparison registration carried by relations. A registered Lean specification
fixes shared vocabulary/typeclass parameters, an ordered explicit background,
stronger and weaker formulas, a named proposed delta, and an allowed-case
remainder. `scripts/CheckStrength.lean` checks complete certificate types against
those applied formulas using Lean definitional equality. Every named field and
background also has an explicit ordered parameter-index correspondence into the
shared telescope, including implicit carriers and relevant instances. Dependent
argument types, declaration heads, each ordered argument, and complete
applications must agree. Fields may omit unused parameters (DecidableEq in the
cause fields; LinearOrder in equality/inequality), but may neither specialize G
to True nor permute same-typed arguments. Maps must be strictly increasing; no
type/name heuristic or argument membership test selects a correspondence. Corpus head binding
identifies statement records; it is insufficient for certificate application
binding. Neither declaration names nor pretty-printed text establish matching.

A proved exact factorization needs all three implications: stronger to
weaker, stronger to delta, and weaker plus delta to stronger, together with the
advertised equivalence certificate. Sufficiency alone leaves exactness
unresolved. Equivalence of stronger and weaker is a separate question. A strict
strengthening additionally needs a checked setting of the same specification
whose background holds and which satisfies weaker and not stronger. Failure to
find a converse supplies no separator. Multiple registrations may propose
different named deltas; no uniqueness or minimality follows. A delta
definitionally equal to the stronger formula or weaker-implies-stronger cannot
pass the definitional degeneracy guard. This guard detects only definitional
matches; a negative check establishes no semantic nonredundancy. Exact
factorization does not certify explanatory usefulness: S padded with True can
factor S perfectly. Informativeness remains a reviewed interpretation, with
linked controls as evidence. No logical inequivalence to W → S is required:
at-most-one is a meaningful delta despite being equivalent to existence →
unique existence. No general semantic-restatement solver is supplied.
A separator refutes the general converse for the advertised comparison, not
the converse on every fixed carrier or interpretation. The present examples
use Type 0; closed settings can directly instantiate higher universes too.

The remainder of cases admitted only by the weaker formula is weaker and not
stronger, not the conjunctive additional requirement. A named remainder such as
equality needs checked identification with that formula as well as its
disjunctive decomposition. Classical or decidability dependencies are displayed
with the evidence, not silently attributed to the source. Comparing open
formulas never treats their independently available proofs as an equivalence.
Premise weakening, conclusion strengthening and proof-term use remain distinct.

The selected real comparison reuses the two Timaeus cause principles. The
proposed delta requires a distinct alternative cause for a generated self-causing
being; it neither prohibits all self-causes nor replaces a shared existential
witness by unrelated witnesses. Its constructive reconstruction explicitly
selects decidable equality. A finite self-cause setting separates the principles;
a mixed self/nonself-cause control checks the weaker interpretation of the
delta. The report links all three existing controls (mixed self/other causes,
no causes, and non-restatement) through their canonical result pages and
verifier configurations; they provide no implication/exactness/strictness role.
These are formal settings, not claims of metaphysical possibility.
Reconstruction retains the broad witness when it is distinct. If that witness
is the generated being itself, the delta supplies an alternative witness whose
distinctness and causation are asserted together.
Generic checks cover existence/unique existence with at-most-one as the delta,
and pinned Mathlib linear order with inequality as delta and equality as the
extra admitted case. PR #723's `AtLeastIn` and `MoreIn` remain primitive:
`SynonymousCauseAtLeast.lean` explicitly leaves their compatibility with ordinary
order open. No ordinary order identity is transferred to them here.

The trusted producer builds dependencies, checks existing theorem/corpus
bindings, checks exact applications and uses the existing Comparator/NanoDa
result machinery. The explorer consumes only that derived report and validates
its source/dependency inputs. A definition edit or changed background/application
must invalidate old output even when record IDs and declaration names persist.
The formula view reuses the structure inspector; proof links and semantic
interpretation stay distinct. Intended and actual root-premise delta: none.
No corpus proposition, Challenge, or proof is changed.
Binding regressions include valid specialized causal certificates, a valid
swapped-argument certificate, and a valid mismatched-background certificate,
all rejected at field binding before report publication. Positive coverage
includes all three live comparisons, omitted parameters and polymorphic
certificates. The existing verifier gates remain required for delivered CI.

To verify a requested registration, or produce the registered explorer slice:

```bash
python3 scripts/worker_env.py -- python3 scripts/corpus.py strength-comparisons \
  REL-STRENGTH-CAUSE --json
python3 scripts/worker_env.py -- python3 scripts/corpus.py strength-report --build-input
python3 scripts/corpus.py strength-report --check-input --json
```

The first two commands run the existing result gates. The last only validates
the trusted producer output against current inputs; it does not execute proofs
again. `strength-comparisons --registered --json` is a provenance-only view and
reports no proof verdicts. The current exact-delta label conservatively requires
the three directions and a result for the displayed biconditional. Named
allowed-case exactness requires both its identity and decomposition results.
Inherited model/typeclass law structures remain named library boundaries; the
inspector does not claim an exhaustive recursive inventory of Mathlib laws.
The explorer build cache directly includes Lean sources, corpus records,
certificate configurations and producer/verifier inputs. Report validation
therefore cannot be bypassed by restoring a cached export after a dependency
changes while statement IDs and declaration names remain fixed.
