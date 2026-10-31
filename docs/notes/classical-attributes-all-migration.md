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

## Root-to-attribute configurations (#826, 2026-10-31)
This current research section is separate from the frozen #730 migration inventory above. Existing-input baseline: public main `d3f85cfcd603dd7626169fb255b8da2129d60b70`. All 76 existing result/argument/statement and frozen Challenge/Solution files used for the nine-row inventory were byte-compared against this public revision; the original local inspection head was `5aeed9a3842cbdb9a2a691c32b6c855e76c368f8`. It classifies existing consequences and selected next tests; it does not certify new proofs merely by listing them. Exact theorem declarations and premises remain authoritative in the linked corpus records.
The eight per-individual Stage 2 results have the form `∀ g, IsGod g → attribute g`; unity instead requires any two IsGod instances to coincide. An actual necessary concrete root is supplied instead by an ontic grounding profile; the two domains are not identified by naming. Root variants are not a presumed hierarchy: firstness/potency, essence/esse and maximality/cause profiles retain their own explicit interfaces.
| Attribute | Existing Stage 2 result and exact input statement IDs | Same-witness root classification / added interface |
| --- | --- | --- |
| one | [CATHOLICISM-STAGE2-GOD-IS-ONE](../../corpus/results/CATHOLICISM-STAGE2-GOD-IS-ONE.json): `STMT-GOD-IS-MAXIMAL-IN-BEING`, `STMT-MAXIMUM-IN-GENUS-CAUSES-ALL-IN-GENUS`, `STMT-CAUSE-OF-QUALITY-IN-ANOTHER-IS-MORE-SUCH`, `STMT-EXCLUDED-MIDDLE` | A necessary root alone does not identify all roots. Existing direct-esse root uniqueness needs its explicit causal/maximality package; God uniqueness additionally uses the naming predicate. The certified genus-omission control retains two roots when I is withheld. |
| simple | [CATHOLICISM-STAGE2-GOD-IS-SIMPLE](../../corpus/results/CATHOLICISM-STAGE2-GOD-IS-SIMPLE.json): `STMT-GOD-IS-MAXIMAL-IN-BEING`, `STMT-COMPOSITE-HAS-A-UNITING-CAUSE`, `STMT-CAUSE-OF-QUALITY-IN-ANOTHER-IS-MORE-SUCH` | ROOT-WITHOUT-LIMITING-PRINCIPLE certifies the same necessary root lacks Composite as one of its three excluded horns. This needs the recorded eleven-input package; it is not inferred from necessity alone. |
| perfect | [CATHOLICISM-STAGE2-GOD-IS-PERFECT](../../corpus/results/CATHOLICISM-STAGE2-GOD-IS-PERFECT.json): `STMT-GOD-IS-MAXIMAL-IN-BEING`, `STMT-MAXIMUM-IN-GENUS-CAUSES-ALL-IN-GENUS`, `STMT-ACTUALITY-ONLY-INSOFAR-AS-BEING`, `STMT-PERFECTIONS-OF-EFFECT-PREEXIST-IN-CAUSE`, `STMT-EXCLUDED-MIDDLE` | Root firstness, no potency and represented essence identity do not by themselves supply positive perfections. Same-root maximality plus the listed causal/perfection inputs is a candidate specialization; the combined root-to-perfect result is not registered yet. |
| supremely good | [CATHOLICISM-STAGE2-GOD-IS-SUPREMELY-GOOD](../../corpus/results/CATHOLICISM-STAGE2-GOD-IS-SUPREMELY-GOOD.json): `STMT-GOD-IS-MAXIMAL-IN-BEING`, `STMT-MAXIMUM-IN-GENUS-CAUSES-ALL-IN-GENUS`, `STMT-ACTUALITY-ONLY-INSOFAR-AS-BEING`, `STMT-GOODNESS-IS-ACTUALITY`, `STMT-CAUSE-OF-BEING-CAUSES-EVERY-PERFECTION` | CausalPerfectionTransfer.goodness offers an existing restricted transfer route. Same-root maximality and its exact universal-being-cause interface still need composition; necessary existence alone gives neither goodness nor causal scope. |
| infinite | [CATHOLICISM-STAGE2-GOD-IS-INFINITE](../../corpus/results/CATHOLICISM-STAGE2-GOD-IS-INFINITE.json): `STMT-GOD-IS-MAXIMAL-IN-BEING`, `STMT-COMPOSITE-HAS-A-UNITING-CAUSE`, `STMT-CAUSE-OF-QUALITY-IN-ANOTHER-IS-MORE-SUCH`, `STMT-MATTER-FORM-AND-ESSE-ESSENCE-ARE-COMPOSITIONS`, `STMT-EXCLUDED-MIDDLE`, `STMT-SUBSISTENT-BEING-IS-INFINITE` | The eight-input ROOT-ESSENCE-IDENTITY output matches the exact maps of SubsistentBeingIsInfiniteReading. Applying that existing interface would be an assembly, not an independent derivation of its primitive Infinite predicate. Receivedness/individuation remains a separate boundary. |
| immutable | [CATHOLICISM-STAGE2-GOD-IS-IMMUTABLE](../../corpus/results/CATHOLICISM-STAGE2-GOD-IS-IMMUTABLE.json): `STMT-GOD-IS-MAXIMAL-IN-BEING`, `STMT-MAXIMUM-IN-BEING-IS-FIRST-BEING`, `STMT-ACT-SIMPLY-PRIOR-TO-POTENCY`, `STMT-NOTHING-IN-ACT-AND-POTENCY-IN-SAME-RESPECT` | NECESSARY-FIRST-BEING-PURE-ACT preserves one actual necessary root under seven explicit inputs. StageTwo.IsImmutable is definitionally that same PureAct predicate; this is a vocabulary connection, not an independently richer theory of change. |
| eternal | [CATHOLICISM-STAGE2-GOD-IS-ETERNAL](../../corpus/results/CATHOLICISM-STAGE2-GOD-IS-ETERNAL.json): `STMT-GOD-IS-MAXIMAL-IN-BEING`, `STMT-MAXIMUM-IN-BEING-IS-FIRST-BEING`, `STMT-ACT-SIMPLY-PRIOR-TO-POTENCY`, `STMT-NOTHING-IN-ACT-AND-POTENCY-IN-SAME-RESPECT`, `STMT-IMMUTABLE-IS-ETERNAL` | The same-root pure-act result can feed STMT-IMMUTABLE-IS-ETERNAL. That primitive eternity interface is retained; the combined root endpoint is not registered yet. Modal necessity is not silently timelessness. |
| intellect | [CATHOLICISM-STAGE2-GOD-HAS-INTELLECT](../../corpus/results/CATHOLICISM-STAGE2-GOD-HAS-INTELLECT.json): `STMT-GOD-IS-MAXIMAL-IN-BEING`, `STMT-COMPOSITE-HAS-A-UNITING-CAUSE`, `STMT-CAUSE-OF-QUALITY-IN-ANOTHER-IS-MORE-SUCH`, `STMT-MATTER-FORM-AND-ESSE-ESSENCE-ARE-COMPOSITIONS`, `STMT-IMMATERIAL-IS-INTELLECTUAL`, `STMT-MAXIMUM-IN-BEING-IS-FIRST-BEING`, `STMT-NO-COMPONENT-IS-FIRST-BEING` | Selected vertical slice: the eleven-input nonlimitation root plus composition-kinds, no-component-first-being and immaterial-intellect. Firstness and the no-component law supply remoteness from every other being; noncomposition alone does not. ROOT-INTELLECT-WILL and ROOT-INTELLECT-WILL-L-OMISSION are merged in #829 after all required checks and current-head review. The reduced route retains eleven inputs rather than fifteen and is delivered in #830 after required CI and exact-head review passed. |
| will | [CATHOLICISM-STAGE2-GOD-HAS-WILL](../../corpus/results/CATHOLICISM-STAGE2-GOD-HAS-WILL.json): `STMT-GOD-IS-MAXIMAL-IN-BEING`, `STMT-COMPOSITE-HAS-A-UNITING-CAUSE`, `STMT-CAUSE-OF-QUALITY-IN-ANOTHER-IS-MORE-SUCH`, `STMT-MATTER-FORM-AND-ESSE-ESSENCE-ARE-COMPOSITIONS`, `STMT-IMMATERIAL-IS-INTELLECTUAL`, `STMT-WILL-FOLLOWS-INTELLECT`, `STMT-MAXIMUM-IN-BEING-IS-FIRST-BEING`, `STMT-NO-COMPONENT-IS-FIRST-BEING` | The selected intellect slice adds STMT-WILL-FOLLOWS-INTELLECT for the same witness (fifteen original inputs, eleven in the reduced route, including EM). It promises only the existing supplied will predicate, not omniscience, libertarian freedom or explanatory sufficiency. |

### Exact root packages and comparison boundary
These are inspected sufficient packages, not globally minimal sets. All are conditional; no owner ledger selection beyond actual existence is inferred.

- `root-essence-identity`: `STMT-COGITO-INHABITED-CONCRETE-WORLD`, `STMT-WHOLE-ROSTER-NOT-TRAPPED`, `STMT-EVERY-CONTINGENT-GROUNDED-AT`, `STMT-EXCLUDED-MIDDLE`, `STMT-EXISTING-IN-ACT-AT`, `STMT-ESSE-CAUSE-IS-ACTUAL-CONCRETE-GROUND`, `STMT-Q3A4-DISTINCT-ESSE-CAUSE-DICHOTOMY`, `STMT-Q3A4-ESSENTIAL-PRINCIPLES-NOT-DISTINCT-ESSE-CAUSE`.

- `root-without-limiting-principle`: `STMT-COGITO-INHABITED-CONCRETE-WORLD`, `STMT-WHOLE-ROSTER-NOT-TRAPPED`, `STMT-EVERY-CONTINGENT-GROUNDED-AT`, `STMT-EXCLUDED-MIDDLE`, `STMT-EXISTING-IN-ACT-AT`, `STMT-ESSE-CAUSE-IS-ACTUAL-CONCRETE-GROUND`, `STMT-Q3A4-DISTINCT-ESSE-CAUSE-DICHOTOMY`, `STMT-Q3A4-ESSENTIAL-PRINCIPLES-NOT-DISTINCT-ESSE-CAUSE`, `STMT-SIMPLY-PRIOR-IS-ACTUAL-CONCRETE-GROUND`, `STMT-COMPOSITE-POSTERIOR-TO-COMPONENTS`, `STMT-COMPOSITE-HAS-COMPONENT-OTHER-THAN-ITSELF`.

- `necessary-first-being-first`: `STMT-COGITO-INHABITED-CONCRETE-WORLD`, `STMT-WHOLE-ROSTER-NOT-TRAPPED`, `STMT-EVERY-CONTINGENT-GROUNDED-AT`, `STMT-EXCLUDED-MIDDLE`, `STMT-SIMPLY-PRIOR-IS-ACTUAL-CONCRETE-GROUND`.

- `necessary-first-being-pure-act`: `STMT-COGITO-INHABITED-CONCRETE-WORLD`, `STMT-WHOLE-ROSTER-NOT-TRAPPED`, `STMT-EVERY-CONTINGENT-GROUNDED-AT`, `STMT-EXCLUDED-MIDDLE`, `STMT-SIMPLY-PRIOR-IS-ACTUAL-CONCRETE-GROUND`, `STMT-ACT-SIMPLY-PRIOR-TO-POTENCY`, `STMT-NOTHING-IN-ACT-AND-POTENCY-IN-SAME-RESPECT`.

- `direct-esse-root-god-uniqueness`: `STMT-COGITO-INHABITED-CONCRETE-WORLD`, `STMT-WHOLE-ROSTER-NOT-TRAPPED`, `STMT-EXCLUDED-MIDDLE`, `STMT-MAXIMUM-IN-GENUS-CAUSES-ALL-IN-GENUS`, `STMT-EXISTING-IN-ACT-AT`, `STMT-ESSE-CAUSE-IS-ACTUAL-CONCRETE-GROUND`, `STMT-GOD-IS-MAXIMAL-IN-BEING`.

The selected new slice is **noncomposition/represented identity → immateriality → intellect → will**, retaining the same actual necessary root. It imports the eleven-input nonlimitation result and adds only `STMT-MATTER-FORM-AND-ESSE-ESSENCE-ARE-COMPOSITIONS`, `STMT-NO-COMPONENT-IS-FIRST-BEING`, `STMT-IMMATERIAL-IS-INTELLECTUAL`, and `STMT-WILL-FOLLOWS-INTELLECT`. No genus causality, maximum or God-naming input is proposed. Its two registered results passed local full build, binding, Comparator and NanoDa with zero exported theorem axioms; independent claim/type review found no unresolved findings. The original fifteen-input route and its omission are delivered in #829; the reduced variants below are delivered in #830.
Its selected structural omission test preserves the original #681 interpretation: roots are individually noncomposite but are components of other beings. Thus no-component-first-being can fail independently of noncomposition. ROOT-INTELLECT-WILL-L-OMISSION certifies all fourteen other exact inputs with a false intellect/will assignment; it retains the original joint certificate and checks q14 through the component/matter-form alternatives. Merely setting an otherwise unconstrained Infinite predicate false would locate an opaque interface, but would not be presented as a substantive metaphysical refutation. Existing [plurality findings](necessary-simple-plurality.md) and [part-free comparison](part-free-plurality.md) preserve the stronger rival distinctions.
`CLASSICAL-GOD-ASSEMBLY` still consumes existence, unity and a primitive attributes field. `ClassicalAttributesFromNine` reaches that field only with the existing `ClassicalAttributesSuffice` bridge; neither assembly proves the nine predicates. A verified root attribute does not by itself make that root an instance of IsGod.
Configuration progress so far: nine attributes classified against exact existing inputs; genus causality omission certified and merged as #825; the same-root structural intellect/will composition and its L omission certified locally. Formal root-frontier change from this inventory: **none**. No designated route is changed.

### Verified minimization and alternative purity configurations

`ROOT-INTELLECT-WILL-REDUCED` reaches the **exact same** `STMT-ROOT-INTELLECT-WILL` endpoint under eleven explicit inputs, a subset of the original fifteen. It removes `STMT-EXISTING-IN-ACT-AT`, `STMT-ESSE-CAUSE-IS-ACTUAL-CONCRETE-GROUND`, `STMT-Q3A4-DISTINCT-ESSE-CAUSE-DICHOTOMY` and `STMT-Q3A4-ESSENTIAL-PRINCIPLES-NOT-DISTINCT-ESSE-CAUSE`, adding none. Composition-kinds was already retained: after firstness and the component rules exclude composition, its nonidentity-to-composition clause yields the represented essence/esse identity. This is a real deletion of explicit inputs for this endpoint, not independent proof that those four principles are true or redundant everywhere.

The chain is explicit: existing five-input necessary-first-being inference → `ROOT-NONLIMITATION-FROM-COMPOSITION-KINDS` → existing six-input intellect/will tail. The new no-limitation intermediate has eight inputs. Compared with the old eleven-input no-limitation route it adds composition-kinds while removing the four causal/actuality inputs, so those two intermediate bundles are different rather than globally ordered. The old fifteen-input Challenge/type remains unchanged and its Solution delegates to the shared tail. The existing L-omission control projects onto the reduced ten-input non-L background without a new model.

`STRICT-PRIORITY-PURE-ACT` separately reaches the existing `STMT-NECESSARY-FIRST-BEING-PURE-ACT` endpoint with seven inputs. It retains the same six inputs as the earlier route and substitutes `STMT-STRICT-SIMPLE-PRIORITY` for global same-respect act/potency exclusivity. The new framework commitment is exactly standard `Std.Irrefl` on the selected candidate priority relation; it is not the separate mixed being/event relation. Firstness forces an alleged prior actualizer to be the same root, contradicting irreflexivity. Two joint controls show that neither replacement premise entails the other alongside the common background. These are formal interpretations, not complete rival explanations or metaphysically realized worlds.

All four new results, the refactored old intellect/will result, and their relevant compiled modules passed full build, binding (795 bound / two legacy pins / zero mismatches), Comparator, result NanoDa and scoped library NanoDa (458 declarations, zero typechecker errors). Exported theorem axiom reports are empty. Independent claim/type reviews found no unresolved findings. These variants are delivered in #830, merge `e9a184dcd521c0d17314adb639c3d3d5a357636c`; required CI run `41247640825` and exact-head review passed. Computed target costs are 10 versus 14 non-floor leaves for intellect/will, 7 versus 10 for the different no-limitation bundles, and 6 for each pure-act bundle. These figures are not global logical-minimality certificates; philosophical root closure remains unchanged.

### Joint constraints are separate from isolated attributes

The existing [rigid-act investigation](simplicity-collapse-555.md), results `SIMPLICITY-COLLAPSE-CORE`, `SIMPLICITY-ROOT-EXPOSURE` and `SIMPLICITY-BRANCH-COSTS`, already constrains combinations involving contingent creation. Necessity of the **same act token**, strict efficacy and a contingent effect are incompatible; bearer necessity alone is not act necessity. Connecting immutability to modal invariance additionally retains `ModalCapacity` and the decree-as-respect interpretation. Optional-act and extrinsic-condition branches relocate a nonnecessitating explanatory link rather than automatically removing it. Those are conditional constraints, not a blanket refutation of simplicity or an endorsement of a rival. None is silently assumed in the new root-attribute packages, which contain no creation/decree field. A nine-row inventory does not by itself certify a complete joint metaphysical worldview.

### Same-root intellect, will and pure act

The next registered target, `STMT-ROOT-INTELLECT-WILL-PURE-ACT`, retains every
conjunct of the existing reduced intellect/will endpoint and adds `PureAct`
**inside the same existential**. Both new routes first consume
`ROOT-INTELLECT-WILL-REDUCED` once, obtaining its particular witness and
firstness. They do not identify witnesses from separate existence theorems.

- `ROOT-INTELLECT-WILL-PURE-ACT`: the existing eleven inputs plus
  `STMT-ACT-SIMPLY-PRIOR-TO-POTENCY` and
  `STMT-NOTHING-IN-ACT-AND-POTENCY-IN-SAME-RESPECT`. It applies the existing
  pointwise first-being/no-potency theorem to that witness.
- `ROOT-INTELLECT-WILL-STRICT-PURE-ACT`: the same eleven inputs plus
  act-priority and `STMT-STRICT-SIMPLE-PRIORITY`. Any alleged potency supplies
  a prior actualizer; firstness identifies it with the root, contrary to
  irreflexivity of that very priority relation.

Each route has thirteen explicit inputs including EM. The same q3 profile
supplies the act dictionary, and potency uses its respect domain. No positive
actuality, exhaustive respect domain, eternity, unique necessary individual,
God identification or richer cognition/volition follows. The older separation
controls use a smaller background and do not certify incomparability under
these full thirteen-input packages. Full build4316 and binding798/two legacy pins/zero mismatch passed. Both
routes and the plurality control passed Comparator and independent result
NanoDa. Scoped library NanoDa checked474 declarations with zero typechecker
errors and one known axiom pretty-printer warning; all three theorem axiom
reports are empty. Independent claim/type review found no findings.
These three results are delivered in #831, merge `ea184c10f892f9b0513e9fc6804ad1da6be483f8`, after required CI run `41249114042` and exact-head review passed.

The proposed positive plurality control reuses the unchanged later five-being
`PartFreePlurality` model. Both replacement conditions together give a
fourteen-input union including supplied EM. Its previously unspecified
intellect/will predicates are assigned to the existing root predicate. The
verified test retains two distinct witnesses with the whole joint attribute
tuple, and explicit nonroot potency, motion and composition. This is a formal
compatibility/uniqueness-boundary test; causal and cognitive adequacy is not
established, and contingent coverage remains vacuous in the old all-present
ontology. The same three-result check set verifies the control. Root routes, root-reaching
statement IDs, open-premise count and depth counts are unchanged. Each joint
attribute route has twelve non-floor leaves; this is not a global minimum.
The new established finite-control statement is not a truth certificate for
its stipulated causal or cognitive interpretation.

### Fixed-esse scope of the root-uniqueness route

`DIRECT-ESSE-ROOT-UNIQUENESS-AT-BEING` preserves the exact existing
`UniqueNecessaryActualRootAt` endpoint with eight explicit inputs. Relative
to `DIRECT-ESSE-ROOT-UNIQUENESS`, it replaces the all-respects genus-causality
input by the existing `STMT-MAXIMUM-IN-BEING-CAUSES-ALL-BEINGS`, and the
all-respects grades-to-maximum input by the explicit fixed-esse
`STMT-GRADES-TO-MAXIMUM-AT-BEING`. Both old global principles specialize to
these interfaces. The proof consumes the old theorem on Unit-restricted
respect dictionaries; beings, worlds, grounds and the conclusion stay the
same. This reduces quantifier scope, not the number of premises or the
independent burden of maximum-to-cause. Ledger H/I selections remain pending;
rejecting their global forms would not automatically reject the restrictions.

`DIRECT-ESSE-ROOT-UNIQUENESS-SCOPE-CONTROLS` uses the existing Boolean
CrossedTops carrier/act/esse dictionaries and an explicitly new all-present,
all-concrete grounding-profile view. Both assignments retain the full new
background and a positive esse grade. One satisfies global grades while
failing global genus causality outside esse; the other satisfies global genus
causality while failing global grades outside esse. The latter assigns a
universal, reflexive nonesse comparison with self-loops. These separate scope
under the current unconstrained MoreIn signature, not under strict/asymmetric
order semantics, and are not proposed metaphysical explanations. All-present
contingent grounding is vacuous. Both candidates are necessary, while only
one is a selected root: the endpoint is not uniqueness of all necessary beings.

Both results pass full build4321, binding801/two legacy pins/zero mismatch,
Comparator and independent result NanoDa. The combined scope/count library
check covers888 dependency declarations with zero typechecker errors and one
known axiom pretty-printer warning. Both result axiom reports are empty;
independent claim/type review found no findings. Required delivered-head
CI/review remains pending. Root routes, reaching-root IDs, open-premise count
and depth counts are unchanged against the verified joint-attribute baseline.
