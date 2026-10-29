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


## Current handoff: causal perfection transfer

Continue from merged #731, starting synchronized main
`aab5dcf4827b03dcc18be2c2b115990de0fcf7cc`. The bounded structural migration
is complete; its [naming audit](notes/naming-first-mover-migration.md) and
[inventory](notes/naming-first-mover-migration.json) remain the preservation
evidence. The current substantive bundle is on
`research/causal-perfections-transfer`. Checked implementation revision:
`c55af5ec6e6e451a870fa7a87fc0650e55060f6c`; this handoff-only follow-up changes
no checked inputs. The delivery PR records its exact delivered head, CI run and
current-head review request/status.

Target: `STMT-CAUSE-OF-BEING-CAUSES-EVERY-PERFECTION`. Reuse: existing
`CausesIn`/`CausesAllInGenus`, q.4/q.6 support, the read pinned q.4 a.2,
q.6 a.2 and q.44 a.1 witnesses, naming/reduced-description/goodness,
`AtMostOneMaximeEns.atMostOneMaximeEns`, prior rival sourcing, and the existing
omission/nonlogical controls at their original scopes. Missing step: active
causal responsibility for each particular actuality rather than mere
existential dependence. Premise comparison: preserve legacy route; substitute
restricted universal transfer only in three separately frozen applications;
no philosophical discharge.

Investigation thesis/purpose: determine what causal transfer is needed to name
and attribute the selected witness. Strongest positive case: participation of
forms/powers plus active primary concurrence (q.44 and q.105). Strongest rival:
universal conservation with proper secondary production, without primary
responsibility for each particular exercise. The decisive fork is whether
existential dependence supplies that active contribution. The source's
God-indexed concurrence cannot identify a pre-naming witness without an
independent applicability bridge.

[Source/semantic findings and claim/type self-sweep](notes/causal-perfection-transfer.md)
persist precise locators, ordinary examples and rejected readings, model
backgrounds, exact application premise lists, and the remaining inference.
`ATTEMPT-CAUSAL-PERFECTION-TRANSFER` and the existing nominal-description
candidate link the evidence through the corpus/dossier. No source claim of
unrestricted or universal transfer is fabricated. Papineau/Hume remain silent;
the prior unsourced Durandus label is explicitly not adopted.

The ten-result bundle compares universal-source/distinct-effect transfer with
the unrestricted premise, factors the residual nonuniversal/self cases, and
propagates the narrower sufficient assumption through reduced naming, full
naming and goodness. The source condition is the existing universal esse
predicate, supplied by genus at esse **before** naming; it says neither God nor
the desired causation of perfections. Comparison alone uses explicit decisions
of identity and universal scope; no new instance is required by the three
applications. All legacy Challenges and Solutions remain unchanged.

Two populated four-role interpretations satisfy the identical genus,
strict-ascent, actuality-to-being and preexistence background, with a universal
esse maximum, no incoming distinct esse cause, and active particular/secondary
causes. One separates restricted from unrestricted transfer. The other denies
even restricted transfer while preserving existential dependence and possession
of perfections. It exposes the missing concurrence inference, not physical or
metaphysical possibility or a whole-root countermodel. The exact strength
relation uses the existing certifier and explorer; no tooling or explorer code
is changed.

Actual premise accounting: all ten pre-existing route costs, input counts,
selection and exact open-premise sets are unchanged; designated cost remains
40 with 38 proposition inputs. The three new applications replace only legacy
transfer with universal transfer: 8/5/5 inputs remain 8/5/5. Reconstruction
classifies legacy transfer as conditionally proved but **unestablished**.
The global open-item list changes 63 → 62 for that classification; legacy
transfer is still a route leaf, and both universal and residual transfer remain
unestablished. Root-reaching graph size is 74 → 76. Only the four mathematical
decomposition/model facts become established. The direct implication is a
detector-classified transcription, not an independent defense. No philosophical
premise closes and no new root route is registered.

Verified local evidence: library build; source manifest/claim binding; corpus
consistency; complete binding (658 bound, two pinned, zero mismatch); all ten
new Comparator/NanoDa results with zero permitted axioms. The existing strength
producer binds the comparison parameters, four exact-delta obligations and
closed separator; explanatory controls include both populated backgrounds.
Explorer loaders resolve all ten results, the certified comparison and target
attempt. Generated imports/docs and diff whitespace pass. Browser/export is
not newly claimed. Independent final CI and current-head review are pending
delivery obligations.

The implementation uses the documented CLI fallback: no coordinator service
workspace/session was supplied, and no service-health or new experiment claim
is made. Necessary cross-lane edits from lane A are this handoff, its linked
research note and the alternative-campaign entry/generated table. No lane B
proof, tooling code, dependency, registry or verification authority is changed.

Next concrete research step: independently justify application/concurrence for
the universal esse witness, or defend an additional subsistent/first-cause
characterization and prove that the witness satisfies it before naming.
Universal coverage and absence of incoming esse cause alone are insufficient
under the witnessed background. Source attribution and a narrower sufficient
premise are not discharges. Final CI and current-head review remain delivery
obligations, recorded in the PR; reuse unchanged successful evidence.
