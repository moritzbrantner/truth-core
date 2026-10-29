# Complete classical attributes and same-witness migration

Bounded Prompt 3 continuation from main `ea537f38d664ceb21dcc8afc1ab9a4b6b7814d4c`
(integrated #728/#729). The prior [assembly audit](classical-attributes-migration.md)
and its source/proof evidence are reused. The exact before hashes, reviewed hashes,
record dispositions and limits are in [the inventory](classical-attributes-all-migration.json).
The explorer shows this same inventory on each of the five scoped result pages.

## Brief and exact scope

1. **Target:** `CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES-ALL` and its immediate
   same-witness consumers `CATHOLICISM-STAGES-ONE-TWO-SAME-WITNESS`,
   `CATHOLICISM-STAGES-ONE-TWO-Q11-NATURE`, and
   `CATHOLICISM-QUARTA-VIA-CLASSICAL-WITNESS`.
2. **Reuse:** all four unchanged Challenges; `StageTwo.GodIsOne.godIsOne`,
   `GodIsSimple.godIsSimple`, `GodIsPerfect.godIsPerfect`,
   `GodIsSupremelyGood.godIsSupremelyGood`, `GodIsImmutable.godIsImmutable`,
   `GodIsEternal.godIsEternal`, `GodIsInfinite.godIsInfinite`,
   `GodHasIntellect.godHasIntellect`, `GodHasWill.godHasWill`, the imported
   First/Fourth Way and naming/identity proofs, and
   `Q11NatureUniqueness.godIsOneFromNature`. Exact namespaces remain in the
   solution imports and corpus results. Reuse `classicalAttributesSuffice_iff`,
   `classicalAttributesFromNine` and `isImmutable_iff_noPotency` without changes.
3. **Missing step:** bind actual specialization and witness transport, correct
   overgeneral prose, and check a separate identity-decision interface instead
   of inferring logical necessity from syntactic premise use.
4. **Premise comparison:** retain every old hypothesis/interface. New separate
   `CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES-IDENTITY` omits the EM hypothesis,
   retaining the other 18 premises under explicit `DecidableEq σ.Being` and
   `DecidableEq Principle` parameters. Neither instance is independently proved.
   This connects results, discharging no philosophical or root obligation.

The scope was stated before editing: **146 existing records** (4 results,
4 arguments, 18 inferences, 50 statements, 46 definitions, 23 disambiguations,
1 reused source claim). Three new records register the separate identity
argument/inference/result, bringing the inventory to **149**. The identity
Challenge was separately frozen before checking its proof. The four existing
Challenges remain byte-identical. Unchanged source claims are prior evidence,
not newly certified interpretations. No source reading is introduced or revised.
Dispositions: 111 inspected, 32 unresolved, three repaired existing records
(ALL argument prose, God disambiguation, preexistence term links), and three new
interface records. The schema uses `repaired` for the latter six rows and
classifies the three new ones as `new_sufficient_interface`. A repaired metadata
row does not close its philosophical premise. The prior audit is retained; only its two shared metadata rows are refreshed
with the exact reason for the new review.

## Specialization and claim/type sweep

All attribute applications below use `g : σ.Being`, `r : Respect`, and the
same supplied predicates throughout. `Principle` is a separate carrier;
`essenceOf`/`esseOf` take values there. `σ` is the same signature in the
sufficiency premise, the conclusion and each witness package.

| Attribute at g | Exact application and dependency |
| --- | --- |
| Simple | `IsSimple Composite g = ¬Composite g`; maximality plus a distinct uniting cause and strict causal ascent |
| Perfect | `IsPerfect InAct g = ∀x r, InAct x r → InAct g r`; same/other being split, actuality-to-being and preexistence |
| Good | `IsSupremelyGood InAct GoodIn CausesIn esse g`; goodness at esse **and** causes every instantiated perfection of each other being |
| One | `IsTheOneGod σ.IsGod g = ∀g′, σ.IsGod g′ → g′ = g`; no existence or `IsGod g` hidden in this predicate |
| Infinite | `Infinite g`; simplicity excludes `esseOf g ≠ essenceOf g`, identity decision recovers equality, the explicit subsistent-being reading gives infinity |
| Immutable | `IsImmutable InPotency g = PureAct InPotency g = ∀r, ¬InPotency g r`; **InPotency**, on this same Being/Respect, not InAct or present nonmotion |
| Eternal | `Eternal g`; `ImmutableIsEternalReading InPotency Eternal` consumes exactly that same no-potency property |
| Intellect | `HasIntellect g`; simplicity plus composition inclusion excludes matter/form composition, first-being/no-component excludes being a component, the explicit immaterial/intellectual reading supplies intellect |
| Will | `HasWill g`; the same intellect predicate and same g feed `WillFollowsIntellectReading` |

`GodHasClassicalAttributes σ` is exactly
`∀g, σ.IsGod g → σ.HasClassicalAttributes g`. Its 19 legacy hypotheses remain
explicit. The final application now uses `classicalAttributesFromNine` at g,
whose existing biconditional preserves the old curried bridge. The bridge
remains an **open one-way sufficiency law**. Neither `NineClassicalAttributes`
nor its presentation defines the primitive field or supplies its converse.
The old argument's misleading "definitional bridge" prose is corrected.
This is a correction of the description, not an interpretation change.

The new argument, inference, result description and Lean comments all say the
same thing: under the two explicit carrier identity instances and the other 18
old premises, conclude the same universal conditional field. Bind-check treats
the instances as type/vocabulary parameters, **not established premises**; the
complete-expression contract pins both instance binder types. Consequently a
count of proposition premises alone must not be read as an assumption discharge.
No premise is silently introduced to make a proof work. The nonlogical premises
and their attributed readings are unchanged; the new logical interface is
explicitly unattributed.

The shared preexistence statement has added links to the existing cause, act,
respect and esse definitions and the formal/eminent disambiguation; its type
and paraphrase are unchanged. The shared God disambiguation now qualifies its
last same-witness paragraph: the original consumers retain the naming converse;
Q11-NATURE uses three explicit alternative premises. This corrects an overgeneral
note without changing any proposition or source reading. Existing definitions
and disambiguations cover the load-bearing terms in both arguments, including
composition, priority, infinity, eternity and cognition. No metaphysical relation
is introduced or reinterpreted by this migration.

On these encoded meanings the conditional conclusions follow. This acceptance
does not endorse their open philosophical premises or renew source fidelity.

## Existence and witness identity

| Result | Witness and exact scope |
| --- | --- |
| ALL | No witness supplied: instantiate every conditional attribute at a given `g` and `hg : σ.IsGod g`. Empty IsGod remains permitted. |
| QUARTA-VIA-CLASSICAL-WITNESS | Fourth Way supplies `m` with maximality; full-description naming supplies `σ.IsGod m`. Eight proofs instantiated with the local predicate `Maximal` apply to **m**. Ninth uses original `σ.IsGod` and retained God-to-maximality. Field and uniqueness are packaged with the same m. |
| STAGES-ONE-TWO-SAME-WITNESS | First Way plus the explicit first-mover-exists-or-not premise supplies **f**. Fourth Way supplies m; imported `FirstMoverIsMaximeEns` proves f = m. Transport maximality to f, then name f and prove its attributes. The final package retains f throughout. |
| STAGES-ONE-TWO-Q11-NATURE | Same f and transport. The ninth attribute uses original `σ.IsGod` with `hIndividual`, `hNature`, `hCommon`, via `godIsOneFromNature`, rather than the God-to-maximality converse. All other attributes and the field concern f. |

Every witness conclusion is exactly
`∃g, σ.IsGod g ∧ IsTheOneGod σ.IsGod g ∧ σ.HasClassicalAttributes g`.
No statement about an arbitrary other witness is inferred. The local `Maximal`
predicate instantiates a generic theorem parameter; it never redefines
`σ.IsGod`. Maximum uniqueness does not rule out nonmaximal IsGod instances.
The stronger full-description naming direction is not reversed.

All three consumers now explicitly group their same-witness conjunction through
the existing checked bridge equivalence. None is refactored to demand a universal
God-to-maximum law where it previously used a weaker local identity adapter.

`scripts/fixtures/ClassicalAttributesAllMigration.lean` applies the new complete
specialization in an inhabited Unit setting with all its nonlogical premises
and both identity instances, without full EM. A Bool control rejects combining
separate existential witnesses; another has a unique maximum and two IsGod
instances, rejecting silent inference of God uniqueness. These are formal
controls, not metaphysical possibility claims. Reuse the prior empty-IsGod and
field-without-nine controls unchanged.

## Logical floor and remaining gaps

Inspection of the imported proofs located three uses of full EM: equality of
beings in maximum uniqueness, same/other equality in perfection, and equality
of esse/essence values in `Principle` for infinity. The new proof reconstructs
those three steps using the two stated equality instances, and composes the
other six unchanged attribute proofs. Comparator/NanoDa accepts it with **zero
permitted axioms**. This establishes a sufficient interface. It proves neither
necessity nor minimality of identity decisions, nor a strict logical separation
from full EM. The four legacy theorem types and all downstream EM interfaces
remain unchanged; a proof-term usage report would not settle those questions.
The First Way's particular existence disjunction remains a separate assumption
in the witness consumers, never confused with equality decisions.

Still open: the nine-to-field bridge; God-to-maximality where retained; the
cause-of-being/every-perfection and maximum/first-being bridges; unrestricted
strict causal ascent; consistent formal/eminent interpretation and applicability
of source readings. Reuse the previous rejection of silently identifying the
unrestricted strict causal premise with Aristotle's synonymous at-least reading.
Primitive infinity, eternity, intellect and will still need their independently
defended intended meanings. The immaterial/intellectual attempt's reception
and grade gaps remain open. No conjunction repackaging or new connection closes
them. No declared fork application is introduced.

## Verification and premise comparison

Five complete-expression contracts pin the original specialized telescope,
ordered applications and recursive project dependencies (ALL 35; original
same-witness 49; Q11 51; Fourth-Way witness 40; identity interface 34). Frozen
Challenges and Solutions are extracted in separate processes. Existing generic
argument-order/context/law regressions are reused; the existing checker rejects
missing coverage, stale record review and a missing scoped consumer contract.
The only tooling extension lets this same audit checker and explorer loader
handle a second bounded inventory with its explicit consumer list. No formula
language, proof-status authority or source semantics is added. Build/impact
inputs include that inventory.

Affected verification passed: library build, corpus check, bind-check (including
all five contracts), isolated Challenge/Solution preservation, all five result
Comparator/NanoDa checks, audit/contract/impact tests and specialized controls.
Unchanged pinned source evidence is reused from #729; final CI retains source,
Lean, binding, Comparator and NanoDa coverage for the delivered revision.
Explorer acceptance passed on the production export: all five scoped result
pages, desktop inspection, touch expansion at 390px, no horizontal overflow,
and the existing structure inspector (three browser tests, 66 assertions).
Reproduce in `apps/corpus-explorer` after `bun run build` with
`bun --max-http-header-size=65536 test tests/bundle-audit.browser.test.ts tests/proposition-structure.browser.test.ts`.
Current-head review and final CI evidence belong in the delivery PR and current
handoff. Reproduction:

```bash
python3 scripts/bundle_audit.py
python3 scripts/expression_contracts.py CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES-ALL
python3 scripts/expression_contracts.py CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES-IDENTITY
python3 scripts/worker_env.py -- scripts/verify-result.sh CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES-IDENTITY
python3 scripts/worker_env.py -- lake env lean scripts/fixtures/ClassicalAttributesAllMigration.lean
python3 -m unittest discover -s scripts -p test_bundle_audit.py
```

Actual root-premise delta: **none**. `frontier --routes` is byte-identical before
and after, with eight costs `31, 32, 36, 38, 39, 39, 40, 41` and designated cost
40. `frontier --reaching-root` has identical premise identities; dependency counts
and ordering reflect the added alternative argument. No route is switched and
no new logical instance is asserted true by registering that alternative.

Next coherent scope: full-description naming and first-mover/maximal-being
identity (`MaximeEnsIsGodViaFullDescription`, `FirstMoverIsMaximeEns`), then their
immediate root compositions. Audit those witness transports and separately
check equality-decision interfaces while preserving the First Way's distinct
existence-disjunction premise. The [current handoff](../proposition-structure.md#current-handoff-bounded-corpus-migration)
remains the one delivery handoff.
