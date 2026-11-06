# Definitions audit (#1103)

This audit checks the established definitions in priority order. It starts
with the concrete/abstract distinction (Part 1) and then covers the
definitions linked from the open leaves of the 12 root routes (Part 2,
tier 1: 140 definitions).

The checklist has six kinds:
1. missing category or sort constraints;
2. typed vs opaque;
3. prose ↔ Lean mismatch;
4. duplicates and near-synonyms;
5. circularity;
6. unrecorded strength forks.

Severity follows the review guidelines in `AGENTS.md`:
- **P1** changes what is proved or misstates the Lean;
- **P2** is a coverage or clarity gap;
- **P3** is cosmetic.

Of the 140 tier-1 definitions, 81 are clean. The rows below cover the rest.
Tiers 2 and 3 (40 + about 1,100 definitions) are tracked in #1114.

## Part 1: concrete and abstract

| Finding | Kind | Sev | Resolution |
|---|---|---|---|
| `concrete : B → Prop` is a free parameter in 25 library files, with no shared meaning. `DEF-INHABITED-CONCRETE-WORLD` left the criterion open (#544). | 1, 2 | P1 | Done (#1105, merged): the shared vocabulary `TruthCore/Ontology/ConcreteAbstract.lean` uses the owner's adopted sense, concrete = esse in re and abstract = its contradictory. The exact dichotomy is derived from excluded middle, and rival criteria are sibling senses. Pending (#1108, not yet merged): migration of the reaching-root uses. |
| 40 constant instantiations (`concrete := fun _ => True`, `abstract := fun _ => False`). In `Models/CountTemporalControls` the necessary candidate is "concrete" only by stipulation. | 1 | P2 | `corpus.py check` warns about constant category predicates. Every existing site is declared with its reason. Pending (#1107, not yet merged). |
| The #1094 adapters (`doubledExample`, `rigidExample`) and the `ActualCoverStrictness`/`WorldwiseCompositeGround` witnesses have an empty abstract extension, yet they were described as intended interpretations. | 1 | P2 | They cannot supply the owner's anchors. `EsseIntendedProfile` is the intended contract, and they are recorded as compatible with the weaker #1094 contract only. Pending (#1108, not yet merged). |
| The owner principle "only concrete things have causal power or cause" was an OPEN premise. It was not tied to any criterion, and its strength fork was unrecorded. | 6 | P2 | Pending (#1106, not yet merged): the owner approved the weak version as a floor item on #1103, but the marking is not yet in the corpus. Once merged, the weak version is marked with four rivals at full strength, the strong version is an unapproved sibling with a verified `strengthens` relation, and a conditional derivation from operari sequitur esse is added. Until then the statement stays OPEN. |
| World-indexed `concrete` in `NecessaryIndividual.Quantifiers` and `EmptyTruthmakerReplies`. | 4 | P3 | Disambiguated as a world-varying sense. The Lean names are kept because frozen Challenges use them. Pending (#1108, not yet merged). |
| `ExistenceActuality.ExistingInActAt` makes every existing thing `InAct x esse`, i.e. concrete in the adopted sense, but nothing links it to `Profile.concrete`. | 1 | P2 | Modelling decision for the owner: #1113. |

## Part 2, tier 1: root-route definitions

### Fixed in this audit's root-route PR

| Definition | Kind | Sev | Finding | Fix |
|---|---|---|---|---|
| DEF-FOUNDED-BY-GOD-THROUGH-ENVOY | 3 | P2 | The prose made envoy founding require `HoldsMandate`, which `EnvoyFoundingIsPrincipalsFounding` (StageThree/DivineFounding.lean:109) does not require. It also read distinctness of Jesus from God into the definition without encoding it. | The prose now states only `FoundedInMandate` and `CommissionedToTeach`, and says that `HoldsMandate` and distinctness are not encoded. |
| DEF-DERIVATIVE-JOINT-SUPPLY | 3 | P2 | The Escape prose omitted the condition that the supplier's effect lies in D (DerivativeJointPower.lean:50), which made it read much weaker. | The condition is added. |
| DEF-BRUTE-ROOT-RELATIVE-GROUNDING | 3 | P2 | The term said "contingent", but the definition has no contingency condition. | The term is corrected, and the definition says contingency is added explicitly where meant. |
| DEF-CLASSICAL-ATTRIBUTES-BUNDLE | 5 | P2 | The attribute "one" is `IsTheOneGod σ.IsGod`, so the bundle mentions `IsGod`, whose content DEF-GOD-OF-CLASSICAL-THEISM gives through the bundle. It holds vacuously when nothing is God. | Recorded as a dependency, not a circular proof (`ClassicalAttributesSuffice` is one-way). |
| DEF-SIMPLE-PRIORITY, DEF-PRIORITY-IN-SUBSTANCE, DEF-PER-SE-EFFICIENT-CAUSE-LINK | 2, 3 | P2 | Each defines a primitive relation by a gloss and links the premise that constrains it as if it were the definition. | Each now says that the relation is a primitive and that the linked declaration is the constraining premise. |

### Follow-up issues

| Definitions | Kind | Sev | Finding | Issue |
|---|---|---|---|---|
| DEF-MORE-IN, DEF-ONTOLOGICAL-TRUTH-COMPARISON, DEF-ONTOLOGICAL-TRUTH, DEF-Q11-INDIVIDUATING-BASIS, DEF-Q11-GOD-SUPPOSITUM-NATURE, DEF-Q11-COMMON-DIVINE-NATURE, DEF-ALTOGETHER-IMMATERIAL, DEF-BEING-AS-TRUTH-OF-A-PROPOSITION, DEF-CAUSE-OF-ORIGIN, DEF-CAUSE-OF-PERFECTION, DEF-GENUS-BROAD, DEF-GENUS-STRICT, DEF-LEAN-PROPOSITION-HOLDING | 3 | P2/P3 | `lean_declaration` is a premise that uses the term, not a definition of it. The two Q11 records are open premises stored as definitions. | #1110 |
| DEF-ACT, DEF-BEING-AS-ENTITY, DEF-MOTION-AS-REDUCTION, DEF-POTENCY, DEF-RESPECT, DEF-GOD-OF-CLASSICAL-THEISM, DEF-SKELETON-OPEN-PREDICATES, DEF-PARTICIPATION-GROUND, DEF-RESURRECTION-PILOT-HISTORY | 3 | P3 | `lean_declaration` is a whole structure, not the field it defines. | #1110 |
| DEF-NECESSARY-INDIVIDUAL-DOMAIN, DEF-HOML-ACTUALIST-NECESSITY, DEF-MAXIMUM-IN-A-PERFECTION, DEF-MAXIME-ENS, DEF-IMMUTABLE, DEF-ESSENCE-THOMISTIC-NATURE, DEF-REGRESS-DOMAIN-ADAPTERS, DEF-GREATEST-BEING-STRICT | 3 | P3 | Wrong or missing link target, or a stale "unused" note. | #1110 |
| DEF-BRUTE-ROOT-RELATIVE-GROUNDING, DEF-ACTUAL-CONCRETE-GROUND-ANCESTRY, DEF-NONNECESSARY-ROOT | 4 | P2 | "Actual concrete root" is defined three times, and `NecessaryRootFork.ActualRoot` is never linked. | #1111 |
| DEF-INHABITED-CONCRETE-WORLD | 4 | P2 | `InhabitedConcreteAt` has the same body as `BruteFoundationBoundary.InhabitedAt`, and its note is stale. | #1111 |
| DEF-HISTORY-TIME-COMMON / DEF-HISTORY-TIME-SCOPE; DEF-MODAL-FIXTURE-FRAME / DEF-QML-KB-NECESSITY / DEF-KANT-MODAL-NECESSITY; DEF-MAXIMUM-IN-A-PERFECTION / DEF-GREATEST-DEGREE-IN-A-PERFECTION; DEF-JOINT-CAUSAL-GROUPS; DEF-ABSTRACT-CONCRETE-DISJOINTNESS | 4 | P2/P3 | Overlapping definitions, or senses missing from their disambiguation. | #1111 |
| DEF-PER-ACCIDENS-ORDERED-SERIES, DEF-PER-SE-ORDERED-SERIES | 2, 5 | P2 | The series conjunction is a decorative `P ∧ Q` over opaque Props. "Each cause after the first" presupposes the first. | #1112 |
| DEF-UNDERIVED-ROOT-ROUTE, DEF-ROUTE-BRIDGE-MODAL-READING, DEF-NONNECESSARY-ROOT, DEF-SELECTED-ANCESTRY-CONE, DEF-NECESSARY-INDIVIDUAL-QUANTIFIERS, DEF-ACTUAL-GROUNDING-WF, DEF-ESSE-CAUSE-IS-ACTUAL-CONCRETE-GROUND, DEF-EXISTING-IN-ACT-AT | 1 | P2 | Their counterexamples ("an abstract individual supports…") depend on what concrete means. | The sense is fixed by #1105/#1108. Instantiation in route compositions: #1113. |
| DEF-JOINT-CAUSAL-GROUPS, DEF-PRESENT-ESSE-SUPPORT, DEF-KANT-MODAL-NECESSITY | 3 | P3 | The term or title says more or less than the body (for example "another individual" while c = b is admitted). | #1110 / #1111 |

No unrecorded strength fork (kind 6) was found in tier 1 apart from the owner
principle above.

## Route-cost effect

None of the PRs so far changes a route cost: `frontier-diff` stays at 90 open
premises (30 bare, 18 supported, 42 stated), with the cheapest route at 31.

- Once #1106 merges, the floor item is established, but no route argument uses it yet.
- Applying it to `STMT-ESSE-CAUSE-IS-ACTUAL-CONCRETE-GROUND` or
  `STMT-NECESSITY-CAUSES-ARE-ACTUAL-CONCRETE-GROUNDS` would discharge only
  their "concrete" conjunct. The "exists at w" and "grounds" conjuncts would
  remain, and an identification bridge to `Ontic.Causes` would be needed.
  That is about +1 leaf per premise unless the bridge is itself established.
- Removing the constant-True fixtures as evidence weakens only satisfiability
  and control claims. No closure depended on them.
