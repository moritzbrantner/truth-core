# Classical attribute assembly migration

This is one bounded audit at `3cd9545a75c975314ea9ebd146d9757bbb754158`, not
an audit of the corpus. The exact record inventory, before hashes, reviewed
hashes, dispositions and remaining reasons are in
[classical-attributes-migration.json](classical-attributes-migration.json).
The existing explorer displays those same 69 dispositions on result
`CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES`, with links and unresolved bridges.

## Brief and before-state

1. **Target:** the conditional assembly argument/result
   `CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES`, concluding
   `STMT-GOD-HAS-CLASSICAL-DIVINE-ATTRIBUTES` on the discovered root paths.
2. **Reuse:** the unchanged `ClassicalAttributes.godHasClassicalAttributes`
   Challenge; `GodIsOne.godIsOne`, `GodIsSimple.godIsSimple`,
   `GodIsPerfect.godIsPerfect`, `GodIsSupremelyGood.godIsSupremelyGood`, and
   `AtMostOneMaximeEns.atMostOneMaximeEns`; existing attribute definitions and
   `PureAct`. Exact namespaces/modules remain in the corpus result records.
3. **Missing step:** replace duplicated encoded vocabulary and misleading
   definitional prose, preserve the complete original conditional, enforce its
   parameter/dependency contract, and expose bounded reviewed coverage.
4. **Premise comparison:** retain every original premise, add/remove/discharge
   none. No meaning correction to an existing Lean proposition is proposed.

`corpus.py frontier --routes` discovers root `STMT-CATHOLICISM-TRUE` and designated
route `CATHOLICISM-FROM-EFFICIENT-REGRESS-WITH-CLASSICAL-ATTRIBUTES` (cost 40).
Before and after, the eight route costs are `31, 32, 36, 38, 39, 39, 40, 41`.
The root-reaching premise identities are unchanged. The cheapest route remains
`CATHOLICISM-SKELETON`; it is not silently substituted for the designated route.

Scope is one result, one argument, its six inference records, their 21 input/output
statements, 24 directly linked definitions plus reused `DEF-PURE-ACT`, 14 directly
linked disambiguations and one clarified source claim. Imported results and
other source claims remain reusable prior evidence, not newly migrated contracts
or renewed source-fidelity certifications. Exact IDs and each disposition are in
the inventory rather than duplicated here.

## Findings and repairs

**Defects repaired.** Some prose called `ClassicalAttributesSuffice` a definition
or an abbreviation, despite the existing definition note correctly identifying
an open one-way implication. Corrected the argument, inference, source-claim
explanation and Lean comments. Re-read the full materialized
`VATICAN-I-DEI-FILIUS-CH1`, DS 3001–3002: its confession of God's attributes
motivates the list, not a universal bridge over arbitrary predicates. The source
statement and its claim identity are unchanged. The frozen Challenge is unchanged.

`IsImmutable` duplicated `PureAct`'s exact `∀ r, ¬InPotency g r` body. It now calls
`PureAct`, retaining both public semantic names and both senses' existing
interpretation notes. `isImmutable_iff_noPotency` checks preservation under the
original arbitrary `Sort` parameters by `Iff.rfl`. This does not equate general
philosophical immutability with pure actuality.

`NineClassicalAttributes` names the meaningful nine-predicate conjunction at one
being. `classicalAttributesSuffice_iff` proves that mapping it to the primitive
field is equivalent to the original curried bridge under precisely the original
parameters, without excluded middle or any new assumption. The selected proof's
final application uses that equivalence through `classicalAttributesFromNine`.
Ordinary conjunction occurrences are generated expressions, not new statements.

**Intentional abstractions.** `Signature` has data/predicate fields and no law
fields. `jesus : Being` and `catholicChurch : Society` imply inhabited carriers;
there is no hidden `Nonempty`, order, causal or modal typeclass law. `MoreIn`
remains a primitive comparative. `IsMaximumIn` is possession plus no incoming
strict comparison, not a total-order greatest element or built-in uniqueness.
The pinned Mathlib linear-order strength example supplies no bridge to it.
The inherited essence definition/disambiguation links are contextual metadata: this
assembly has no essence/esse identity parameter. They supply no hidden premise.

The five final attribute wrappers accept primitive predicates in this earlier
assembly. In particular its `Immutable` parameter is not automatically
`IsImmutable InPotency`; the existing definition and disambiguation already
explain the specialization in the later complete argument. Eternal has no
internal time/succession semantics, and intellect/will no internal cognition or
appetite semantics. These are interpretation burdens, not claims that the
conditional proof is invalid. `IsPerfect` covers perfections instantiated by
some being; it does not cover every arbitrary respect. Numerical uniqueness
alone asserts neither the identity predicate at its parameter nor existence.

**Open premises.** The God-to-maximality converse, esse-to-every-perfection cause
bridge, and nine-attributes-to-field sufficiency remain independent premises.
The unrestricted strict causal-ascent premise remains unattributed and stronger
than Aristotle's sourced synonymous at-least reading. Reused
`ATTEMPT-ARISTOTLE-SYNONYMOUS-CAUSE-SCOPE` and the degree-fork audit reject the
silent replacement: shared defining accounts, strict comparison and ties matter.
The formal/eminent `InAct` interpretation must be defended consistently across
all premises. No open philosophical premise is classified as a defect merely
because it is open.

All 15 hypotheses are reported used by `UnusedPremises.lean`, including through
imported proofs. Conservative proof-term use does not establish logical
necessity. Only equality instances of excluded middle are needed by these
proofs; certifying a weaker shared identity-decision interface across the imported
results is recorded as subsequent work, not claimed here.

**Vacuity.** `Being` is inhabited but `IsGod` may be empty. The result is
`∀ g, IsGod g → HasClassicalAttributes g`, so it supplies no God-existence
witness. The regression fixture constructs that empty-predicate setting. It
also constructs one same-witness Unit setting satisfying all nonlogical
premises, conditional on the original explicit excluded-middle hypothesis.
This is a formal consistency control relative to that logical floor, not
metaphysical model existence. A further setting satisfies the field and
sufficiency while all nine attributes fail, refuting the unadvertised converse.
Finite-model existence is not imposed as a universal proof requirement.

**Extraction limits.** The expression inspector is bounded, with typed partial
boundaries and named library declarations. Full binding recursively records
project definition bodies and declaration types, including constructor field
laws; library internals remain version-pinned boundaries. Neither tool decides
source fidelity or whether the model interpretation is philosophically adequate.

**Forks.** Reused #720's existing `forkUses` declared-inference projection and its
fabricated-related-edge regression. The selected six inference records contain
no declared disjunction-elimination use. No fork coverage/exclusivity/downstream
consumption is claimed by this assembly, and related degree-fork records add no
inference. Full-expression preservation does not certify any such missing use.

## Claim/type self-sweep

Here `I = σ.IsGod`; all parameters retain their original order. Every pointwise
property is applied to the very same `g` and the same `σ`.

| Record(s) | Exact encoded content checked against the prose |
| --- | --- |
| `STMT-GOD-HAS-CLASSICAL-DIVINE-ATTRIBUTES` | `∀ g, I g → σ.HasClassicalAttributes g`; neither existence nor a recovered conjunction |
| `STMT-CLASSICAL-ATTRIBUTES-SUFFICE` | `∀ g, Simple g → Perfect g → Good g → One g → Infinite g → Immutable g → Eternal g → HasIntellect g → HasWill g → σ.HasClassicalAttributes g`; one-way open law |
| `STMT-GOD-IS-MAXIMAL-IN-BEING` | `∀ g, I g → IsMaximumIn InAct MoreIn esse g`; independent converse naming premise |
| `STMT-MAXIMUM-IN-GENUS-CAUSES-ALL-IN-GENUS` | `∀ r m, IsMaximumIn InAct MoreIn r m → ∀ x, x ≠ m → InAct x r → CausesIn m x r` |
| `STMT-CAUSE-OF-QUALITY-IN-ANOTHER-IS-MORE-SUCH` | `∀ c x r, c ≠ x → CausesIn c x r → MoreIn r c x`; unrestricted unattributed premise |
| `STMT-EXCLUDED-MIDDLE` | `∀ p : Prop, p ∨ ¬p`; explicit retained logical hypothesis |
| `STMT-COMPOSITE-HAS-A-UNITING-CAUSE` | `∀ x, Composite x → ∃ c, c ≠ x ∧ CausesIn c x esse`; same cause witness |
| `STMT-ACTUALITY-ONLY-INSOFAR-AS-BEING` | `∀ x r, InAct x r → InAct x esse` |
| `STMT-PERFECTIONS-OF-EFFECT-PREEXIST-IN-CAUSE` | `∀ c x r, CausesIn c x esse → InAct x r → InAct c r`; no extra time variable |
| `STMT-GOODNESS-IS-ACTUALITY` | `∀ x r, GoodIn x r ↔ InAct x r`; difference of notion outside the type |
| `STMT-CAUSE-OF-BEING-CAUSES-EVERY-PERFECTION` | `∀ c x r, CausesIn c x esse → InAct x r → CausesIn c x r`; open, not inferred from preexistence |
| `STMT-GOD-IS-INFINITE`, `STMT-GOD-IS-IMMUTABLE`, `STMT-GOD-IS-ETERNAL`, `STMT-GOD-HAS-INTELLECT`, `STMT-GOD-HAS-WILL` | Each `∀ g, I g → P g` for its same supplied primitive predicate; no implicit unfolding of intended infinity, time or cognition |
| `STMT-AT-MOST-ONE-MAXIMUM-IN-BEING` | Any two given maxima equal; no maximum-existence assertion |
| `STMT-GOD-IS-ONE` | `∀ g, I g → ∀ g′, I g′ → g′ = g` |
| `STMT-GOD-IS-SIMPLE` | `∀ g, I g → ¬Composite g` |
| `STMT-GOD-IS-PERFECT` | `∀ g, I g → ∀ x r, InAct x r → InAct g r` |
| `STMT-GOD-IS-SUPREMELY-GOOD` | `∀ g, I g → GoodIn g esse ∧ ∀ x r, x ≠ g → InAct x r → CausesIn g x r` |

The changed argument/inference/result proof comments describe composition of
these statements, not their establishment. Every external `Prop` binder remains
listed in the argument. The new conjunction and preservation theorems have no
source attribution. Changed source prose explicitly disclaims the universal
arbitrary-predicate law. No relation is renamed causal or explanatory merely
because it has a mathematical shape. On this encoded evidence the conclusion
follows conditionally; its open source/interpretation burdens remain open.

## Mechanical contract and reproduction

`BindTypes.lean` emits an alpha-canonical complete dependent telescope/expression
for the selected result. `scripts/contracts/classical-attributes.json` pins the
original Challenge type and 28 recursive project dependencies, including
`Signature.mk`'s constructor type. `corpus.py bind-check` fails if the selected
contract is missing, a same-head argument is swapped, any binder/context changes,
a project definition body changes, or structure/typeclass requirements change.
It retains the normal statement/head binding. The method intentionally requires
exact alpha identity, which is stricter than definitional equality; a future
meaning-preserving dependency refactor needs explicit reviewed preservation
and a deliberate contract revision. There is no automatic pin-refresh command.

```bash
python3 scripts/expression_contracts.py CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES
python3 scripts/bundle_audit.py
python3 -m unittest discover -s scripts -p 'test_expression_contracts.py'
python3 -m unittest discover -s scripts -p 'test_bundle_audit.py'
python3 scripts/worker_env.py -- python3 scripts/corpus.py bind-check
python3 scripts/worker_env.py -- scripts/verify-result.sh CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES
```

The first command imports the unchanged Challenge and Solution in **separate**
processes, avoiding their identical theorem names. Its Challenge `sorry` is only
the frozen type authority, never proof evidence. The other controls are in
`scripts/fixtures/ClassicalAttributesMigration.lean`. Existing
build/source/Comparator/NanoDa gates remain authoritative for final inputs.
The record checker enforces inventory and review freshness; it does not prove
that a reviewer interpreted a term correctly.

The current handoff and next migration scope remain in
[proposition-structure.md](../proposition-structure.md#current-handoff-bounded-corpus-migration).

Browser acceptance: the production export passed the bounded-audit and existing
structure browser tests, including desktop inspection, touch expansion and
390px overflow checks. [Captured audit panel](../images/classical-attributes-audit.png).
Reproduce after `bun run build` in `apps/corpus-explorer`:
`bun --max-http-header-size=65536 test tests/bundle-audit.browser.test.ts tests/proposition-structure.browser.test.ts`.
