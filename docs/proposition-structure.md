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

## Prior delivery: certified strength comparisons

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


## Prior delivery: complete classical attributes (#730)

Prompt 3 continuation from integrated main
`ea537f38d664ceb21dcc8afc1ab9a4b6b7814d4c` (#728/#729), branch
`refactor/classical-attributes-all`. The delivery PR records the exact final
head and CI identity. Verified implementation revision:
`e6df0bc9f2acdc57025da620ed0d53f983574f88`; this handoff follow-up changes
only documentation. This is one bounded migration: ALL, its three immediate same-witness
consumers, and a separate identity-decision interface. The prior 69-record
[audit](notes/classical-attributes-migration.md) remains valid reused evidence;
the [new audit/self-sweep](notes/classical-attributes-all-migration.md) and
[inventory](notes/classical-attributes-all-migration.json) account for 146
existing records plus three new argument/inference/result records.

All four existing Challenges and interfaces remain unchanged. Five complete
expression contracts bind the specialized `IsImmutable InPotency`, every other
attribute application, original signature/carriers and shared witnesses.
The nine-attribute conjunction implies the primitive field only through the
open sufficiency bridge. The God-to-maximality converse remains explicit in
ALL and the two original witness consumers; Q11-NATURE retains its three
alternative uniqueness premises. The disambiguation note now states that
exception. Preexistence has the existing term links added. No source reading
or philosophical interpretation changes.

The separate `CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES-IDENTITY` proves the same
universal conditional field with explicit `DecidableEq σ.Being` and
`DecidableEq Principle`, retaining the other 18 original premises. Comparator
and NanoDa accept it with zero permitted axioms. This is a sufficient interface,
not a necessity/minimality result, assertion of either equality instance, or
root premise discharge. Legacy EM interfaces and the First Way's separate
existence disjunction remain unchanged. Same-witness controls reject combining
unrelated existentials and deriving God uniqueness from a unique maximum alone.

Verified: library build, corpus/binding, five isolated contract comparisons,
five result Comparator/NanoDa checks, specialized controls and focused
contract/audit/impact tests. Source evidence is reused from #729 because source
inputs are unchanged; final CI retains its required integration coverage.
Explorer production export and all three bounded-audit/structure browser tests
pass (66 assertions): all five pages, desktop inspection, touch expansion at
390px and no horizontal overflow. Current-head review/final CI status is recorded
in the delivery PR.
Root-reaching premise identities and eight route costs are unchanged:
`31, 32, 36, 38, 39, 39, 40, 41`; designated route remains cost 40. Dependency
counts/order change only because the alternative argument is registered.

No service endpoint/workspace/session was supplied. The documented CLI fallback
was used; no service experiment or service-health evidence is claimed.

Next coherent migration: `MaximeEnsIsGodViaFullDescription` and
`FirstMoverIsMaximeEns`, then immediate root compositions. Bind their naming and
identity transports, check separate equality-decision interfaces, and preserve
the distinction from the First Way's particular existence disjunction. The
unrestricted strict causal ascent, sufficiency/naming/first-being bridges and
formal/eminent interpretation remain open. Do not expand this audit into a
claim of whole-corpus migration or renewed source fidelity.


## Current handoff: bounded corpus migration

Naming/identity continuation from integrated #730 main
`e634f01f6f77a8592f256cd72548ffa299a49613`, branch
`refactor/naming-first-mover-route`. Verified implementation revision:
`9e22dd5ea66103846c5c50e317855461c7d7487c`; the following handoff-only commit
does not change checked inputs. The delivery PR records its exact delivered head,
final CI run and completed current-head review.

Scope is **six legacy bundles**: full-description naming, first-mover identity,
Stage1 full-description, original same-witness consumer, Prima root composition,
and `CATHOLICISM-FROM-EFFICIENT-REGRESS-WITH-CLASSICAL-ATTRIBUTES`. The
[bounded self-sweep](notes/naming-first-mover-migration.md) and
[exact inventory](notes/naming-first-mover-migration.json) persist 146 initial
record dispositions plus 15 new argument/inference/result records for five
separately frozen equality interfaces: **161 records**. Reuse #730's unchanged
attribute/source/control evidence and same-witness expression contract. All six
legacy Challenges **and Solutions** remain byte-identical. The first-mover
argument gains existing semantic links; no statement or source claim changes.

The audit binds description-to-God only, supplied f/m identity, transported
maximality and the same named/attributed f through the root route. Neither naming
nor identity supplies existence. Maximum uniqueness alone cannot establish
original IsGod uniqueness. The retained God-to-maximality premise matches #730's
attribute identity interface, which the alternative consumer imports without
strengthening its original inputs. All causal, first-being, naming and field
bridge directions are preserved. The historical end remains a structural
transcription under its original open bridges.

The two new bridge variants use explicit `DecidableEq Being`; three composition
variants additionally use `DecidableEq Principle`. Same-witness/Prima variants
retain `FirstUnmovedMoverExistsOrNot`; the efficient-regress variant adds that
explicit hypothesis when dropping full EM. All other proposition inputs remain
(7/5/30/37/38 respectively). Equality instances are assumptions outside frontier
proposition counts; neither is established. There is no minimality, necessity,
strict-strength or existence-disjunction replacement certificate.

Verified implementation evidence: library build; corpus and complete binding
(648 bound, two pinned, zero mismatch); ten isolated frozen Challenge/Solution
contracts and ten result Comparator/NanoDa checks with zero permitted axioms;
new inhabited no-existence control; six focused audit, 35 impact and five
structure tests. Inspector input includes the two bridge conclusions, naming
premise and existence disjunction; existing presentation/verification authorities
remain separate. Production browser acceptance is recorded in the delivery PR.
Final CI retains all required integration, source, Comparator and NanoDa checks.
No unchanged source checks or full dependency reviews are repeated locally.

Intended/actual philosophical premise discharge: **none**. All 63 root-reaching
open-premise identities and all eight legacy route rows remain unchanged;
designated cost stays 40. Registration adds two alternative root rows at costs
39/40 with 37/38 proposition inputs; these counts exclude their two equality
instances. Root selection is unchanged. The existing attempt retains findings,
rejected inferences and the exact audit references. No new source-fidelity
question was discovered within this structural review; existing q.105 translation
basis, formal/eminent compatibility, strict causal ascent, perfections,
first-being, naming sufficiency/converse, primitive attributes and
historical/authority burdens remain open.

No installed convention artifacts exist; none was installed or updated. No
service setup was supplied; documented CLI fallback was used, with no health or
service-experiment claim. Cross-lane work is limited to necessary lane C audit,
contract/fixture/impact and inspector/explorer presentation files and this
handoff; no lane B proof is changed. Stop at this coherent route.

Next substantive question: which retained causal or naming bridge can
discriminate the strongest surviving rival on this route? That investigation,
other root routes and new source work belong to the next bounded task. Next
concrete delivery step, if CI/review is pending in the PR: wait for the required
checks and delivered-head review, fixing concrete findings only.
