# Definitions audit (#1103)

The original Parts 1–2 record the earlier definition-quality audit. Part 3 below
records the owner’s later repository-wide competing-definition investigation;
the older snapshot counts are not a claim of whole-corpus completion.

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


## Part 3: competing definitions as propositions (2026-11-06)

Owner direction in the [current handoff](https://github.com/moritzbrantner/truth-core/issues/418#issuecomment-6686091684):
encode worldview-specific meanings as explicit propositions, compare their
consequences, and construct meaningful definition disjunctions. Prove coverage
where possible; otherwise retain a named coverage proposition as an open
framework premise and an exact remaining relevant interpretation. Conditional
elimination can proceed before that premise is independently established.
Coextension, property identity, contradiction, non-entailment, triviality for a
purpose, and loss of an objection's force remain different outcomes.

The review is repository-wide, not only a goodness/evil retrofit. It does not
rewrite every occurrence of a word, equate similar meanings, or add an untestable
Other rival to every noun. A new interpretation can agree with the target; it
then is not automatically a rival to that target. A coverage remainder opposes
its exact coverage claim, not every conclusion mentioned by the investigation.
Original statements, source readings and frozen Challenges remain distinct.

### Inventory baseline and coverage limits

The mechanical inventory at main
`85e1e24371136494f8ee937534155f751f0527ca` enumerated **3153 statements,
1302 definitions, 350 disambiguations, 1022 arguments, 1020 results and 379 attempts**.
The following partition counts every definition once, by its declared namespace;
it is a discovery inventory, not an assertion that every source or theorem was
re-reviewed. 459 definitions name exactly the same Lean declaration string as at
least one statement; that aids discovery but proves neither philosophical identity
nor correctness. 267 definitions have no single `lean_declaration` field; some
already describe several separately encoded predicates, so this is not a count
of missing formalizations.

| Declared area(s) | Definitions | Audit treatment / remaining scope |
|---|---:|---|
| Causality + Explanation |338| Scope/bridge and reason/ground definitions inspected in the first synthesis; much of the typed configuration library still needs consequential-use review. |
| Modal + German + Isabelle |141| Necessity, per-se necessity and essential/accessibility distinctions inspected; bounded formal profile alternatives are not a census of all modal theories. Remaining semantic calibrations are open. |
| Logic + Epistemology |110| Truth/meaning/reason/knowledge lane; targeted objective-truth and epistemic-role gaps identified below. |
| Latin + Greek + Modern + English |233| Source-linked definitions cross several clusters. Existing attribution is preserved; proof/meaning review does not reauthenticate all texts. |
| Case + History |46| Founding/authority/name/revelation lane; first founding correction is under implementation, transfer gaps remain below. |
| Ontology + Alternatives |56| Existing concrete/abstract, naturalism, motion and rival frameworks; active potency/cogito work is counted rather than duplicated. |
| Mereology |40| Existing explicit identity, fusion, overlap and scope controls are candidates for use-level review; whole-cluster completion not claimed. |
| Metaethics + Ethics |30| Active goodness/evil definition forks plus previously explicit realist/expressivist and population-policy contrasts; no blanket closure from a list of schools. |
| Science + Spacetime + Space + Teleonomy |16| Existing observation/calibration/coordinate/directedness scopes need use-level review; mathematical distinction alone does not defeat a worldview. |
| Hiddenness |11| Correct-sort question remains to inspect: ability, access, relationship and culpability are not interchangeable. |
| Decision + Politics |5| Payoff/ranking and district/individual consent are already typed separately; no unencoded inference to truth or authority is licensed. Remaining comparative-use review is open. |
| Models + Comparison + Results + external mathematics |9| Review only their advertised philosophical interfaces; do not manufacture competing-definition forks for standard mathematics. |
| No single declared Lean head |267| Review through their linked statements/arguments and existing notes; mixture of multi-predicate typed records, source glosses and real encoding gaps. |

The baseline frontier had **zero** closures classified `alternatives_refuted`.
Two statements nevertheless also satisfied the all-recorded-rivals-refuted
pattern: `STMT-CASE-NON-CONTRADICTION` and `STMT-SOMETHING-CHANGES`. Both were
independently owner-floored. No identified closure therefore depended solely
on an unproved philosophical exhaustion of its recorded rival list. This
does not establish philosophical completeness of those lists.
Consequential latent coverage/transfer gaps are still recorded below before
future refutations can be promoted across senses. The frontier engine itself
is unchanged by this audit batch.

### Targeted findings and actual adjustments

| Cluster / exact seed | Finding and adjustment | Boundary / remaining work |
|---|---|---|
| `STMT-THERE-ARE-ORDINARY-ROLE-EPISTEMIC-REASONS`; `STMT-THERE-ARE-PREFERENCE-INDEPENDENT-EPISTEMIC-REASONS` | Their prior note withheld Lean declarations because encoding would not establish actual normative instantiation. Now encoded conditionally in `Logic/EpistemicReasonDefinitionFork.lean`: four calibration propositions, explicit consideration-presentation, named coverage/remaining interpretation, strength order, and finite controls. Six results bind the exact declared obligations. | Unchanged thin F6 approval supplies no stronger interpretation. Calibration transport/structural coverage are transcriptions; actual warrant, force and coverage stay open. See the existing [reason investigation](notes/epistemic-reasons-preconditions.md). |
| `DEF-OBJECTIVE-TRUTH`; `DISAMB-TRUE`; `POE-EXTERNAL-PREMISE-VS-EMOTIVISM` | Targeted truth-lane implementation: explicit truth-component bridge, stronger actual-truth-plus-profile-invariance calibration and invariant-only rival. False-but-invariant control prevents stance independence from being confused with objective **truth**. | Source ObjectiveTruth predicates and claims remain general. Profile invariance is one operational account, not all philosophical objectivity. Published separately: [PR1129](https://github.com/moritzbrantner/truth-core/pull/1129), head `848dcae7`, six zero-axiom results. |
| `STMT-ENVOY-FOUNDING-IS-GODS-FOUNDING`; `DISAMB-FOUNDED-BY-GOD` | Targeted authority-lane implementation: immediate/inclusive calibration propositions, exact strong-exclusion scope, explicit coverage/Other, overlap and countermodels. Old prose's categorical “immediate-only makes it false” needs an actual commissioned-event witness and the exclusion condition; the generic type also lacks a HoldsMandate hypothesis. | Weak principal-own-act and stronger no-envoy/creature readings are not silently equated. Existing Challenges and source claims remain. Published separately: [PR1128](https://github.com/moritzbrantner/truth-core/pull/1128), head `2e63c05f`, eight zero-axiom results. |
| `DISAMB-NAME-APPLICATION`; practice no-reference vs nominal God leaves | Three recorded alternatives cross a practice-reference predicate and proper nominal IsGod without a typed transfer. Existing noBeingExcludes proofs specialize the generic schema; they do not supply a cross-sense implication. | Implemented in [PR1132](https://github.com/moritzbrantner/truth-core/pull/1132), head `0508fcc0`, eight zero-axiom results: explicit proper-to-practice transfer, stronger coextension, description witnesses and exact proper-profile negation endpoints preserve the serious rival without unsafe raw practice-to-nominal alternatives. |
| `STMT-REVELATION-POSSIBLE-AND-RECOGNIZABLE`; practice CutOff | Practice-move cutoff and God-capability predicates are distinct; the existing relation admits the shared-reason bridge is not a recorded premise. | Need a same-profile mapping and actual/modal recognition witness bridge. Mere capability does not supply an actual practice move. This is additional to the already recorded canon/two-bridge/conjunction gap in the [Moorean note](notes/moorean-floor-candidates.md). |
| Verificationism's cognitive meaning | Existing VerificationPrinciple is a one-way condition, not a full definition. Criterion verdict, pre-theoretic meaning, and truth conditions are already separated. | Later truth batch: explicit calibrated meaning propositions and coverage/Other, composing existing Church/V2 trivialization and V4 survivor. Trivial demarcation does not by itself falsify a definition on an all-meaningful domain. |
| Intrinsic vs external mutability; timeless vs temporal duration | `DEF-MUTABLE-THROUGH-ANOTHER` / `DEF-MUTABILITY-IN-ANOTHER` have no exact Lean definition; root Eternal remains a primitive while BoethianEternal is typed. | Next modal/causal batch should encode exact meaning/scope calibration and counterprofiles without identifying externally dependent existence with subject potency or endless succession with timelessness. |
| Time-neutral composer / current efficient cause | `STMT-COMPOSER-IS-EFFICIENT-CAUSE-OF-COMPOSITE` is intentionally untyped because the available relation was read at a selected time. | A separate typed time-neutral interpretation can be explored conditionally; missing source/warrant is not a reason to leave its relational scope implicit. Preserve the existing time-local statement. |

### Existing distinctions preserved rather than re-created

The truth/meaning read lane inspected 38 disambiguation resolutions, catalogued 100
linked definitions and 280 linked statements, and inspected exact relevant Lean
modules/declaration indexes. This is narrower than re-verifying every linked
theorem or source attribution. Its cluster dispositions are:

- Truth/relativism (`DISAMB-TRUE`, `DISAMB-TRUTH-APT`,
  `DISAMB-ASSERTED-TRUTH-SENSE`, `DISAMB-NO-ABSOLUTE-TRUTH-SCOPE`,
  `DISAMB-PILOT-RELATIVITY`, `DISAMB-TRUTH-COLLAPSE-LEVEL`): fixed-sense
  retorsion, relative/exempted survivors and capture bridges are already explicit.
  Target the objective-truth calibration gap; do not reclassify indexed truth
  variation as a blanket denial of objective or ontological truth.
- Meaning (`DISAMB-VERIFICATIONIST-MEANINGFUL`, `DISAMB-VERIFIABILITY-VARIANT`,
  `DISAMB-V4-PROPOSAL-MEANING-AND-TRUTH`,
  `DISAMB-ACTUAL-EXISTENCE-VERIFICATION-RELEVANCE`): preserve the existing
  diagnostic/proposal/source distinctions while adding consequential calibration.
- Role/authority (`DISAMB-EPISTEMIC-REASON-EXISTENCE-ROLE-AUTHORITY`,
  `DISAMB-PLAN-GUIDANCE-VS-CATEGORICAL-REASON`,
  `DISAMB-TRANSCENDENTAL-ACCESS-AND-DUTY`): an actual favoring instance,
  extensional successful classification and preference-independent authority
  are separate. The reason batch repairs the actual conditional-encoding gap.
- Knowledge/justification (`DISAMB-KNOWLEDGE-ASSERTION`,
  `DISAMB-FIRST-HIGHER-ORDER-JUSTIFICATION`, `DISAMB-FITCH-OPERATOR-SCOPE`,
  `DISAMB-CC100-124-TRUTH-COMMON-KNOWER`, `DISAMB-PARM-KNOWLEDGE`): factivity,
  higher-order access and distributed/fixed-agent knowledge already have
  explicit propositions. No universal sceptical theory census was asserted.
- Correctness/warrant (`DISAMB-FIRST-PRINCIPLE-WARRANT`,
  `DISAMB-CORRECTION-CRITERION-AND-JUSTIFICATION`,
  `DISAMB-INSTRUMENT-ACCURACY-AND-ENTITLEMENT`,
  `DISAMB-VALIDATION-RISK-AND-WARRANT`,
  `DISAMB-GOLDMAN-STATUS-ACCESS-AND-REVISION`,
  `DISAMB-FALLIBLE-CORRECTION-AND-WARRANT`, `DISAMB-SCIENCE-TEST-ADEQUACY`,
  `DISAMB-ADAPTIVE-FAILURE-AND-WARRANT`,
  `DISAMB-BINARY-TRUTH-FITNESS-WARRANT`): preserve the explicit controls; a
  classifier's successful performance is not a warrant or authority definition.
- Method/regress (`DISAMB-INFINITIST-AVAILABILITY-AND-WARRANT`,
  `DISAMB-ARISTOTLE-ANPOST-DEMONSTRATION-AND-ENTITLEMENT`,
  `DISAMB-CONTRASTIVE-WORLDVIEW-JUSTIFICATION`,
  `DISAMB-SCIENCE-INDUCTION-SELECTION`, `DISAMB-SEXTUS-EPISTEMIC-REGRESS-SCOPE`,
  `DISAMB-HUME-INDUCTION-REASON-PRACTICE`,
  `DISAMB-SELLARS-FOUNDATION-RELIABILITY-AND-RECIPROCITY`): the stipulated
  GeneratedWarrant norm and historical readings are not all possible
  justification theories; no general exhaustive Agrippan taxonomy is advertised.
- Logical classification (`DISAMB-THRESHOLD-BELIEF-REASON-AND-TRUTH`,
  `DISAMB-SHARED-AND-INDEXED-BELIEF-CLOSURE`,
  `DISAMB-INTUITIONISTIC-FORCING-AND-NONFORCING`,
  `DISAMB-SORITES-TOLERANCE-CLASSIFICATION`): K3/LP, indexed pools,
  pointwise/Heyting negation and binary/partial tolerance already have separate
  typed profiles and controls. They are bounded alternatives, not a census of
  all possible logics or vague-language accounts.

The authority/history lane inspected 16 disambiguations and 31 linked definitions
at the same baseline. The first founding batch is an actual adjustment; the
remaining dispositions preserve these exact obligations:

| Cluster | Disposition and exact scope |
|---|---|
| Founding / mandate | Existing implication and narrow/universal mandate-scope results are reusable; the immediate/inclusive definition calibration and nonvacuous exclusion gap is the first active correction. |
| Proper nominal God / practice reference (`DISAMB-NAME-APPLICATION`, `DISAMB-GOD`) | Add a weakest proper-application→practice-reference transfer before crossing the 3 current alternative relations; a practice-reference-empty model need not make a proper nominal predicate empty. |
| Revelation / CutOff | Capability and actual correct shared-reason moves differ; exact practice/world mapping and witness scope must be explicit, as described above. |
| Natural reason (`DISAMB-NATURAL-REASON`, `DISAMB-PRACTICE-SENSITIVITY-AND-FIDEIST-INSULATION`) | Shared-reason bridge is typed; the theological-horizon reply remains untyped. A theological description of reason may coexist with outsider usability. Encode exclusive insulation separately from theological presentation; outsider-to-Christianity is not neutral-to-every-horizon. |
| Grammar fixing | Existing `FIDEISM-GRAMMAR-CASES-PARTITION` already proves authorities / not-authorities-and-use / neither under excluded middle. Reuse it; do not call it a census of named schools or turn the surviving neither branch into a refutation. |
| Visible/spiritual Church (`DISAMB-CHURCH-VISIBLE-SPIRITUAL-ASPECTS`) | Spiritual counterpart lacks a typed calibration. Future visible-only/spiritual-only/joint-aspect comparison must preserve possible coexistence, membership/body/jurisdiction distinctions, and separate historical founding/identity obligations. |
| Commission powers | Existing preach/teach/governance table is explicitly stipulated; institutional founding needs its open link. A governing-power calibration should distinguish announcement, delegated jurisdiction and constitutive authority, preserving report/event and promise/actual-conferral scopes. |
| Christological words (`DISAMB-JOHN-I-AM-CONTEXT-AND-TRUTH`, `DISAMB-MARK-HIGH-PRIEST-EXCHANGE`, `DISAMB-MARK-FORGIVENESS-AUTHORITY`, `DISAMB-PHIL-CHRISTOLOGY`) | Current report/letter propositions correctly avoid inferring historicity, divine authority or identity. Further divine-name, preexistence, ideal-priority and delegated-agent definition propositions/forks remain to encode; no new attribution is licensed. |
| Resurrection (`DISAMB-RESURRECTION-PILOT-EVIDENCE`) | The pilot compares a supplied bounded theory roster and bodily-event predicates. If a later elimination relies on the roster exhausting rivals, that is an additional premise; no universal exhaustiveness is presently proved. |
| God-like / most-real / divine being-person (`DISAMB-KANT-GOD-IDENTIFICATION`, `DISAMB-POSITIVE`, `DISAMB-Q11-GOD-BEING-PERSON`) | Existing fixed interpretations are distinct; no new fork is needed merely because “God” recurs in several frameworks. Preserve the exact identification and person/being bridges. |
| Electoral authority / historical consent (`DISAMB-ELECTORAL-MAJORITY-CONSENT-AUTHORITY`, `DISAMB-HISTORICAL-RAPE-AND-NONCONSENT`) | Existing mathematical/source scopes do not infer individual consent, legitimate authority or a historical rape concept from majority counts. No current cross-sense inference was identified to rewrite. |

Initial causal/modal checks likewise preserve the explicit statement types in
`DISAMB-CAUSE`, `DISAMB-PSR-EXPLANATION-CAUSE`,
`DISAMB-BRUTE-EXISTENCE-AND-GROUNDING`,
`DISAMB-COMPLETE-CAUSE-PARTIAL-GROUND`, `DISAMB-NECESSARY`,
`DISAMB-ESSENTIAL-VS-ACCESSIBLE-EXISTENCE`, and `DISAMB-CHANGE-A-SERIES`.
Existence-PSR is not an external-cause principle; local no-brute existence is
not all-world PSR or grounding-root exclusion; necessary existence is not
essential explanation or uncaused necessity; A-series change, general change
and potency/act motion require their explicit bridges. Their existing checked
separations are reused. Full use-level review of the remaining module groups
is still open; this first batch does not declare the repository-wide audit done.

### Active or delivered related work counted in scope

- [#1125](https://github.com/moritzbrantner/truth-core/pull/1125): generic and
  adopted-potency configurations; original Challenges retained, rival senses
  not globally refuted by choosing a definition.
- [#1122](https://github.com/moritzbrantner/truth-core/pull/1122): adopted esse
  profile/cogito bridge with explicit generic/interpretation boundary.
- [#1126](https://github.com/moritzbrantner/truth-core/pull/1126): external
  evil-premise truth, target-internal challenge, affective protest and precise
  remainder; not an exhaustive account of every possible objection.
- [#1127](https://github.com/moritzbrantner/truth-core/pull/1127): open form/end
  goodness proposition, semantic named coverage, additional account and
  intensional/property-identity fork. No automatic goodness definition adoption.

Audit continuation: finish the actual batches above, then continue the unreviewed
causal/modal/mereological, source, hiddenness, science and decision clusters.
A keyword inventory or the first three corrected examples is not completion.


### Subsequent reviewed clusters (same audit, 2026-11-06)

- Epistemic-reason adjustment above is [PR1131](https://github.com/moritzbrantner/truth-core/pull/1131), original reviewed head `131390dc`; six exact zero-axiom results, computed root89→89 and cheapest31→31.
- [PR1133](https://github.com/moritzbrantner/truth-core/pull/1133), `c23db91c`, adds six meaning-definition results. The existing `Ayer1946ExcludesANegation` package already contains its full meaning calibration; the exact-type audit rejected the suspected identification gap and reuses that theorem unchanged. New V1/V2/V3 calibrations, admitted-scope coverage/remainder and independently excluded target expose the actual conditional elimination inputs. Its analytic-only meaning control witnesses remainder/one-way-versus-biconditional strictness, not all family premises. Computed root89→89, cheapest31→31.
- [PR1134](https://github.com/moritzbrantner/truth-core/pull/1134), `97e8da8e`, encodes the independent time-neutral composer attribution and separate selected-time/existential-time calibrations. Ten zero-axiom results expose coverage/Other, local persistence versus global persistence, and all-time versus current no-self. Historical production plus local persistence reaches the old current bridge; historical production plus all-time no-self reaches the SAME old distinct-uniter conclusion without persistence. A nonvacuous past-self model proves a current-time-only ban insufficient. Computed root89→97 (seven bare inputs and one stated input added), cheapest31→31: conditional connections, no discharge. Full boundaries and the unchanged source reading are in [the composer note](https://github.com/moritzbrantner/truth-core/blob/97e8da8efd6bce42e149a2d892b47f76a1b7edb7/docs/notes/composer-temporal-definition-fork.md).
- Two further unsafe rival endpoints are under exact-type review: raw actual practice cutoff versus possible recognizable revelation; quasi-realist moral truth versus robust truth without a shared moral-content witness. Notes alone do not constrain frontier closure, so scoped negation endpoints and checked transfer/nonvacuity premises are required where the raw predicates can coexist.
- External mutability through another's power is already distinguished from subject potency in `DISAMB-MUTABILITY-CHANNEL`, `DISAMB-POTENCY-IN-SUBJECT-VS-IN-ANOTHER`, and the Boethian module's boundary premise. No current recorded argument was found silently crossing these channels; the untyped q.9/q.10 descriptions remain encoding opportunities, not evidence of a faulty current inference.
- The typed Boethian result still has no registered transfer to the root's primitive `Eternal`. This is a consequential remaining calibration task: the existing module expressly requires recognition, and the duration disambiguation already keeps endless succession distinct from the partial Boethian predicate.

These references describe delivered cluster work, not a completed whole-corpus audit. Later additions and merges require refreshing the initial mechanical count at the eventual delivery head. Successful checks apply to their exact inputs; known strength-registration display failures are handled by tooling PR1130 without weakening proof labels or gates.


### Additional consequence and no-change dispositions

- [PR1138](https://github.com/moritzbrantner/truth-core/pull/1138), `e6402fab`, supplies the previously missing operational-Boethian→primitive-Eternal recognition and composes the existing typed result into the EXACT all-beings root premise. All three old typed inputs remain visible, including pure-act-life and the boundary-to-subject-potency bridge. Five zero-axiom results; computed root89→92, cheapest31 unchanged. The old target gains a checked-consequence classification while remaining unestablished. The controls preserve the partial Boethian scope, endless succession, recognition strictness, overlap and remainder.
- [PR1141](https://github.com/moritzbrantner/truth-core/pull/1141), `387e2b5d`, supplies a weaker selected-perfection maximal→greatest bridge from active-pair degree calibration, local directedness and explicit excluded middle; no homogeneous all-being partial order or uniqueness is needed. The unchanged source-shaped greatest-degree causal premise then reaches the EXACT old selected-esse all-maximal premise. Six checked results (five zero-axiom; finite control uses propext under approved Mathlib policy), computed root89→97, cheapest31 unchanged. The incomparable control's greatest-degree causal conditional is explicitly vacuous, not refuted; tied bearers block strict supremacy/uniqueness. Three existing maximum audit rows were re-reviewed without changing their historical/source boundaries.
- [PR1135](https://github.com/moritzbrantner/truth-core/pull/1135), `c929ab21`, corrects quasi-realist versus robust-truth rivalry: a shared moral-content witness is necessary to derive exact negation of the robust universal. Existing empty-domain overlap and nonempty-neither controls are reused; raw source commitments remain distinct. This is an actual endpoint correction, not a note-only restriction.
- [PR1137](https://github.com/moritzbrantner/truth-core/pull/1137), semantic repair `5bfbc1f0`, separates assertion-policy withholding from object-level excluded middle. Refuted `∃p,¬(p∨¬p)` is not global `¬∀p,(p∨¬p)`. The exact global complement is now an unrefuted analyst rival, and withholding moves to its exact policy target. The legacy owner floor is preserved. Actual-record regressions ensure removing that floor does not let a finite rival-list artifact establish EM. Notes alone were expressly rejected as an adequate engine constraint. A metadata overclaim about incidental control witnesses was corrected to the exact exported compatibility/nonimplication properties before the required rereview.
- [PR1136](https://github.com/moritzbrantner/truth-core/pull/1136), updated head `d37016f9`, corrects actual practice cutoff versus a possible recognizable-revelation capability. Ten zero-axiom results expose capacity realization, shared recognition, admissible-state coverage and nonempty God as separate premises; actual cutoff persists to other admissible states only under its explicit additional commitment. The exact root capability-negation sibling replaces the unsafe rival endpoint. A model has actual cutoff and recognizable capacity realized elsewhere. Computed root89→89, cheapest31 unchanged.
- [PR1140](https://github.com/moritzbrantner/truth-core/pull/1140), `910da687`, encodes visible, spiritual and joint Church calibrations, open named coverage/remainder, and standalone visible/joint→existing-stage5 connections with actual selected founding witnesses. Spiritual does not mean invisible, and its insufficiency for stage5 is a countermodel, not falsity. Five zero-axiom results; computed root89→93 (five bare inputs added, old stage5 stated→checked classification), cheapest31 unchanged. Modern-society identity remains independent.

Hiddenness was inspected through all five disambiguations, eleven namespace-bound definition records, `Hiddenness/Vocabulary.lean`, model interfaces and the nine registered argument/result types. Its target is already explicit conscious reciprocal access; belief, voluntary acceptance, capacity, causal resistance, sufficient love-compatible reason and nonpersonal ultimacy are separate. The unqualified and qualified norms are separate propositions and the old finite `QualifiedDoesNotForceAlways` control checks the difference. No current result transfers salvific/mediated presence into conscious access or identifies this signature with the root's God. No theory-roster exhaustion is asserted. These are already handled distinctions, not a reason to manufacture another definition fork for the same word.

The Science/Spacetime/Teleonomy extension reviewed twenty definition records, thirty-two linked statements, thirteen exact result/argument packs and five disambiguations. Calibration/recoding/induction-selection/boost-simultaneity mathematics has no discovered cross-sense inference: response equality is not empirical warrant, reversible coding is not physical naturalness, a set-valued answer is not probability/action, and coordinate simultaneity is not privileged metaphysical presence. The one consequential gap was an untyped global no-director summary used as an alternative to a universal director principle without a shared noncognitive-tending witness. [PR1139](https://github.com/moritzbrantner/truth-core/pull/1139), `5c75c258`, replaces that endpoint by exact negation derived from an explicit undirected-tending witness. Its empty-tending overlap and prior governed/unguided fragments prevent natural mechanism from being equated with exclusion of ultimate direction. The full raw summary remains unchanged, with an OPEN semantic-witness bridge. Two zero-axiom results; root89→89, cheapest31 unchanged. Exact reviewed IDs and source/typed scope dispositions are durably listed in that PR's teleonomy note.

Remaining work still includes the precise united-soul/body reception fork, the modal single/plural and pointwise/collective possible-causer scope, broader source-specific metaphysical interfaces and the remaining corpus namespace/disambiguation inventory. Mereology read coverage is being deepened separately; its catalogue counts alone are not treated as a completed semantic audit. The latest owner example of unrestricted versus theological proof skepticism is being checked against actual prior records, with class criterion, proof standard, barrier and matched controls kept distinct.


### Completed cluster findings and remaining sweep (continuation)

This section supersedes earlier “remaining” descriptions for delivered batches;
the baseline inventory remains historical. It does not claim the whole
semantic sweep is complete. The coordinator's single handoff records current
heads, CI and integration status. Per-batch frontier counts below are computed
comparisons, not additive predictions for the combined repository.

- [PR1143](https://github.com/moritzbrantner/truth-core/pull/1143) encodes the
  united-soul communication/reception fork. Actual union, soul/body role maps,
  communicated-act identity, same-sense reception and recipient/essence
  distinction are independent inputs. The old infinity theorem only uses
  own-essence reception for esse=essence candidates; its imported proof on that
  subtype reaches the EXACT old conclusion with a strictly weaker premise. A
  nonidentity reception counterexample and separate identity candidate witness
  strictness without claiming the rest of the infinity bundle. Eleven zero-axiom
  results; computed root89→90, cheapest30 unchanged. Source claims retain only
  their original communication/reception senses.
- [PR1147](https://github.com/moritzbrantner/truth-core/pull/1147) corrects the
  global quantifier-shift schema as a purported rival to collective possibility.
  It was a proposed positive proof method; its refutation cannot refute the
  conclusion it proposed to license. A strictly weaker local shift plus explicit
  distributive realization and realized-common-absence-to-Possible reaches the
  exact old target. An exact unrefuted complement and precise individual-possible/
  joint-impossible countercase retain meaningful opposition. The existing full
  perpetual-succession rival is unchanged. Actual-record counterfactual: before
  repair, removing only that unencoded rival edge caused false finite-roster
  closure from refuting the positive method; after repair the exact complement
  blocks it. Seven zero-axiom results; root114→114, cheapest30 unchanged.
- [PR1145](https://github.com/moritzbrantner/truth-core/pull/1145) distinguishes
  unrestricted from theological proof skepticism through explicit category
  criteria, proof standards and a deciding finite-observation barrier. No old
  unrestricted-self-refutation→theology-refutation was found. Matched ordinary
  hidden-content and theological-tautology controls prevent an exception label
  from doing the work. Five checked results, no general theological-unprovability
  conclusion or new historical attribution.
- [PR1149](https://github.com/moritzbrantner/truth-core/pull/1149) corrects four
  further semantic-rival edges: truth-as-provability versus thought-composition
  accounts can coexist; anti/realist explanation directions need asymmetry and
  an actual moral witness to contradict; the raw Tractatus no-divine-sense reply
  needs an explicit meaning/proof-standard mapping before denying natural
  theology's arguability; competing PLA text readings are interpretive objections,
  not exhaustive object-level denials. Five zero-axiom results and actual-record
  closure regressions; root 116→116, cheapest 30 unchanged. Details and rejected
  readings are durable in `docs/notes/semantic-rival-scope.md`.

The authority lane delivered seven applicable clusters: founding (#1128), proper
name/practice transfer (#1132), recognizable revelation (#1136), visible/spiritual
Church (#1140), natural-reason horizon versus outsider usability (#1142), commission
criterion (#1144), and conciliar theological content versus normative role
(#1150). Together these register 54 checked results. Their original source
accounts stay intact; the exact negative endpoints require explicit transfer,
exclusion and nonvacuity premises. The existing authorities/use/neither grammar
partition was already a structural fork and was reused, not called a census of
worldviews. A separate mandate-scope control (#1151) retains teaching in the
Catholic-only weak scope: restricting the two-society model's attested mandate
to the Catholic society preserves that weak scope and the other three old
inputs but defeats the old universal bridge at the second society. This
justifies the original argument's `strong_version_needed`; weak+Stage6→strong
was already encoded and no new root route is claimed.

Authority non-applicability is use-sensitive: all eleven literal Mark2/Mark14/
John8–9/Phil2 pilot report statements have zero argument premise/commitment/
conclusion occurrences; four disambiguations already distinguish report, history
and divine-authority interpretation. There is no present inference to repair.
The Resurrection pilot's six theories and seven results are bounded answer-map
consistency/availability, not historical ranking or completeness of all theories.
Stage4 still needs actual JesusClaims and Rose on the SAME State.core; no report
or answer count is transferred into an event. Exact IDs and source/typed
boundaries are persisted in `docs/resurrection-pilot.md`.

The Mereology extension read all thirteen vocabulary modules, forty definitions,
seventeen disambiguation resolutions, seventy-one linked statement paraphrases
and fifty-five direct argument/result headers (twenty-three namespace-local).
Thirty-three attempts were inventoried with bounded summary/blocker inspection;
this is not fresh verification of every linked historical source note or kernel
proof. No present cross-sense inference was found: Sum1/2/3, supplementation,
atomic versus gunk profiles, actual versus necessary parts, unity/soul,
identity/turnover, intervention closure and externality already have separate
predicates, explicit bridges and controls. None of the inspected cluster's
seventy-one statements had an `alternative_to` edge. These already-handled
distinctions are not grounds to create a new fork for every noun.

Exact reviewed Mereology definitions: `DEF-ATOMIC-FUSION-CONTRAST`, `DEF-UNIVERSAL-FUSION-PROFILE`, `DEF-NO-NECESSARY-PARTS-AT`, `DEF-MODAL-PARTHOOD-NECESSITY-DOWNWARD`, `DEF-POSITIVE-BOOLEAN-MEREOLOGY`, `DEF-OVERLAP-FUSION`, `DEF-THESEUS-OCCURRENCE-BEARER`, `DEF-MEREO-STRUCTURAL-UNITY`, `DEF-SELECTED-NECESSARY-PARTS-FUSION`, `DEF-UNIVERSAL-FUSION-DOMAIN`, `DEF-MEREO-SOUL-AS-FUNCTIONAL-ORGANIZATION`, `DEF-FUSION-DISTINCT-CAUSE`, `DEF-SUM1-FUSION-COMPARISON`, `DEF-THESEUS-IDENTITY-PRINCIPLES`, `DEF-MEREO-SOUL-AS-FORM`, `DEF-SUM1-LEAST-UPPER-BOUND`, `DEF-FUSION-OUTSIDE-CAUSE`, `DEF-BINARY-SUM2-FORMATION`, `DEF-PROCESS-TURNOVER-REPRESENTATION`, `DEF-MEREOLOGICAL-SUPPLEMENTATION`, `DEF-SUPPLEMENTATION-FUSION-RIVAL`, `DEF-MEREOLOGICAL-COMPLEMENTATION`, `DEF-SUM1-COMPLEMENTATION-RIVALS`, `DEF-OVERLAP-EXTENSIONAL-PARTHOOD`, `DEF-MEREO-INTERVENTION-DYNAMICS`, `DEF-NECESSARY-PART-FUSION-DECOMPOSITION`, `DEF-MATERIAL-HISTORY-CORRESPONDENCE`, `DEF-MATERIAL-SLICE-COINCIDENCE`, `DEF-MEREO-OPERATIONAL-LIFE-PROFILE`, `DEF-GENUS-CAUSE-FINITE-CONTROL`, `DEF-ACTUAL-FUSION-PROFILE-CERTIFICATE`, `DEF-PRINCIPAL-IDEAL-ACTUALITY`, `DEF-MEREO-PRIMITIVE-BEARER-PROFILE`, `DEF-REGULAR-REAL-REGION-MEREOLOGY`, `DEF-FUSION-GROUND-INTERPRETATIONS`, `DEF-FINITE-NO-GUNK`, `DEF-MEREO-SUBSTANTIAL-UNITY`, `DEF-THESEUS-COMPONENT-INVENTORY`, `DEF-MEREOLOGICAL-AXIOM-COMPARISON`, `DEF-MATERIAL-TEMPORAL-WHOLE`.

Exact reviewed Mereology disambiguations: `DISAMB-SUM1-AND-SUM2-FUSION`, `DISAMB-ARISTOTLE-H6-UNITY-AND-CAUSATION`, `DISAMB-MEREO-SOUL`, `DISAMB-DOWNWARD-ACTUALITY-AND-FIXED-WHOLE`, `DISAMB-FUSION-CAUSE-EXTERNALITY`, `DISAMB-GENUS-PREDICATION-REAL-COMPOSITION`, `DISAMB-SELECTED-NECESSARY-FUSION-AND-ACTUAL-PART`, `DISAMB-MEREO-UNITY`, `DISAMB-PROCESS-CARRIER-MATERIAL-STAGE`, `DISAMB-GUNK-FUSION-AND-PHYSICAL-COMPOSITION`, `DISAMB-THESEUS-IDENTITY-CONTINUITY-MATERIAL`, `DISAMB-NO-NECESSARY-PARTS-AND-ACTUAL-CONTINGENCY`, `DISAMB-EXACT-REMAINDER-AND-SUPPLEMENT`, `DISAMB-SUM2-AND-SUM3-FUSION`, `DISAMB-ACTUAL-FUSION-BARE-NE-AND-NECESSARY-CAUSE`, `DISAMB-MATERIAL-EXTENSION-TEMPORAL-SCOPE`, `DISAMB-MEREO-DESCRIPTION-BEARER`.

At the ecabfd9d+modal-repair snapshot, a mechanical check found zero argument
premises without a Lean declaration. This is an inventory result, not a semantic
adequacy claim: an existing declaration can still use the wrong sense or scope.
The 57-edge `alternative_to` snapshot is being reviewed at exact endpoints.
Removing only a target's own floor in actual-record copies leaves EM, causal
concreteness, general change, movedness and thin epistemic reasons unestablished.
The independently floored case noncontradiction still has an exact classical
negation rival; it is not a refutation of paraconsistent object negation. The
weak meaningful-negation principle remains inherited from its independently
floored strong sibling. These counterfactuals preserve every real approval and
do not create hypothetical proofs or statuses. Two floored targets also had
all-recorded-rivals-refuted patterns; baseline classification count zero for
`alternatives_refuted` alone must not be confused with absence of such patterns.

Remaining substantive scope: productive abstract causal accounts and selected
world/classification guards; the Megarian ability thesis versus moved-in-potency
requires a real moved witness and the appropriate unactualized-potency bridge;
UniverseUncaused excludes every candidate cause while the current positive
asks for an existing cause, so actuality/negation scope needs a precise guard;
no-well-foundedness versus an infinite descending chain needs actual coverage
under its logic/choice policy; general change versus its stronger McTaggart
bundle needs the exact no-change comparison; and modal single/plural and
pointwise/collective possible-causer source boundaries remain to be fully
disposed. The sorted disambiguation-resolution sweep now covers all 350 baseline
entries, including the reread nature/limitation entry. At semantic snapshot
79909898 (base607ff3ae plus the universe scope batch), the five added current
entries and nine changed baseline resolutions were also read. This completes
resolution-text discovery for all 355 then-current disambiguations, not exact
source/proof/use review of every statement in the repository.
These are semantic tasks, not satisfied by namespace counts or the absence of
unbound argument premises. No whole-repository completion is claimed.

The causal/concrete batch now addresses the first remaining scope item above:
productive set/Form witnesses and mathematical relevance have explicit no-esse,
productive-reading and selected-world interfaces. Four broad automatic rival
edges become guarded attacks; the exact selected-profile negative is the
unrefuted formal alternative. Structural commitment/countercase and explicit
named-coverage/remainder forks connect through sixteen checked results and
separate visible AND premises to the EXACT old commitment. The dormant abstract
power control manifests at an accessible other world but lies outside all three
named selected productive accounts. Raw theories are not refuted by declaring
them insufficient for that target. An existing source-backed event-set statement
loses only an unsupported appended inference from the set-of-two anchor to all
impure sets; its source account and claim identity remain. Exact witness,
interpretation, rejected readings and reproducible own-floor-removal check are
persisted in `docs/notes/causal-concrete-rival-boundary.md`. Computed comparison
against721bab8e: root116→116 (52bare/20supported/44stated), cheapest30 unchanged.
This preserves owner approval and introduces no new floor or premise discharge.


### Additional endpoint corrections and resolution coverage

[PR1152](https://github.com/moritzbrantner/truth-core/pull/1152) is now integrated.
Its coverage premise is explicitly **existential support**: if any selected
causal countercase exists, some named productive case exists. It does not
classify every witness. Review caught and corrected the original universal
prose overclaim; exact definitions/proofs and elimination were unchanged. A
remainder requires a selected countercase while no named productive case exists
anywhere in that selected profile. A named case can coexist with unrelated
capacity-only examples. This distinction must also govern future coverage prose.

[PR1153](https://github.com/moritzbrantner/truth-core/pull/1153) exposes the
Megarian guard and a precise moved/not-potent countertuple, with six zero-axiom
results. The raw Megarian thesis becomes a guarded objection; actual movement
and the SAME-sense weak moved-tuple potency interpretation yield the analyst
countertuple. The original occasionalist candidate remains stronger in prose
than its existing countertuple-only Lean envelope. A one-way envelope projection
does not derive its divine re-creation story. Explicit-EM structural coverage
and four extensions of old models preserve both missing-input coexistence
cases. Computed root 116→116, cheapest 30 unchanged; clean targeted review at
`7438cb17`. Existing source claims, models, Challenges and approvals are unchanged.

[PR1154](https://github.com/moritzbrantner/truth-core/pull/1154) handles three
remaining truth-lane edges. Generic ScopedScientism needs actual scope coverage
before denying a nonempirically established witness. All-established-in-scope,
pointwise nonempirical-witness coverage and sufficient existential coverage are
separate strength levels; the route uses the existential form. Constancy of
moral meaning coexists with occasion-based attitude meaning if expression is
constant; actual free-standing attitude and embedded loss plus a moral witness
are explicit before the old exact emotivist-meaning negation follows. Kripke's
no-fact report and PU noninterpretive grasp are preserved as distinct source
readings, with an interpretive attacks edge instead of automatic formal rivalry.
Six checked results and actual-record closure regressions; root 116→116, route 30
unchanged. The linked note preserves quantifiers and exact controls.

The universe-causer scope batch reuses the existing full endpoint-actuality
policy and weakens it to causers of the selected whole. The old no-edge rival is
preserved; exact no-existing-cause is a separate, weaker complement. A checked
existing-causer/no-edge/only-absent-causers trilemma exposes generic Ontic scope.
The usual two-way fork explicitly requires selected-whole-causer actuality.
The third generic assignment violates intended causal actuality and is not
claimed to be actual or metaphysically possible. Eight zero-axiom results
connect that scope choice to the EXACT old existing-cause target and export
whole population/actuality in the controls. Seven earlier fusion/cover/atomistic
records explain why a policy about a separately selected spacetime whole cannot
replace their chosen source/sum/cover actuality inputs without a mapping. No
claim that their full both-endpoint interfaces are minimal is made. See
`docs/notes/universe-cause-scope-boundary.md`. Against base 607ff3ae the computed
root frontier remains 116 (52 bare / 20 supported / 44 stated), route 30 unchanged.

The 355-resolution discovery snapshot consists of the original 350 plus
DISAMB-GOODNESS-UNRESTRICTED-DUE-AND-ULTIMATE, DISAMB-EVIL-OBJECTION-SEMANTICS,
DISAMB-SCOPED-PROOF-STANDARD-AND-THEOLOGICAL-DOMAIN, DISAMB-POTENCY and
DISAMB-MEANING-DEFINITION-CALIBRATIONS. Nine baseline resolutions changed and
were reread: duration, in-act, causal-power-concreteness, uniting-cause,
verificationist-meaningful, esse-reception, existence-esse-support, maxime-ens
and epistemic-reason-existence-role-authority. Semantic snapshot 79909898 has
3,313 statements, 1,344 definitions, 355 disambiguations, 1,133 arguments,
1,131 results, 346 relations and 392 attempts. These are actual JSON-record counts at that
snapshot, not a new claim of semantic completion or summed PR frontier effects.

Concrete remaining endpoint work includes accepted explanation truth versus
truthful nonselection; exact general no-change versus the stronger McTaggart
bundle; explicit WF/descending-chain coverage using the existing classical
coincidence theorem; the untyped quantifier-shift-versus-plenitude textual
interpretation edge; and final dispositions of all 57 baseline rival edges against
the integrated delivery head. The authority lane is correcting two further
OnlyMessage endpoints with actual mandate/founding witnesses and distinguishing
local face-value language from cross-discourse semantic uniformity. Broader
source-only possible-causer plurality remains an explicitly separate reading,
not a detected current typed quantifier exchange. Full source/argument use-level
coverage and final integrated additions still need their precise dispositions;
the completed resolution-text sweep does not substitute for those tasks.


### Exact rival-edge dispositions and remaining use coverage

This ledger revisits every **57 baseline** `alternative_to` record at
85e1e24371136494f8ee937534155f751f0527ca. The integrated comparison snapshot is
`c39cdc1c8b2b10abbb5efa658f5dff07220eed4f`. “Pending” identifies a published correction that is not in this
snapshot; it is not an assertion that the old endpoint has already changed.
The table records consequential scope and proof boundaries, not merely shared
words. Existing source accounts, approvals and frozen Challenges remain intact.

| Baseline relation ID | Integrated relation | Disposition / exact remaining boundary |
|---|---|---|
| `REL-CHANGE-UNREAL-BUT-APPEARS-ALTERNATIVE-TO-SOMETHING-IS-MOVED-IN-THIS-WORLD` | alternative_to | Exact no-movement complement also exists (row 30); stronger appearance bundle is not the whole opposition. |
| `REL-PERPETUAL-SUCCESSION-ALTERNATIVE-TO-COLLECTIVE-POSSIBILITY` | alternative_to | #1147 preserves full succession story and adds the exact collective negative; positive method is not a rival. |
| `REL-COUNCIL-TEACHING-THEOLOGY-ALTERNATIVE-TO-CONCILIAR-DEFINITION-OWN-STANDARD` | alternative_to | #1150 requires an actual defined move and matching exclusion before the exact practice-standard negative. |
| `REL-INTUITIONISM-ALTERNATIVE-TO-EXCLUDED-MIDDLE` | alternative_to | #1137 separates withholding/assertion policy from logical denial and retains unrefuted global ¬EM. |
| `REL-TRUTH-IS-PROVABILITY-ALTERNATIVE-TO-THOUGHT-TRUE-BY-COMPOSITION` | removed | #1149 removes automatic rivalry: provability and composition-based truth classification can coexist. |
| `REL-PHILLIPS-LATE-ALTERNATIVE-TO-FACE-VALUE-THEORY` | alternative_to | #1159 pending: distinguish local face-value semantics from cross-discourse uniformity; raw P2 alone is insufficient. |
| `REL-CHANGE-WITHOUT-ANY-MOVER-ALTERNATIVE-TO-NOTHING-REDUCED-TO-ACT-EXCEPT-BY-A-MOVER` | alternative_to | Exact moved-with-no-fitting-mover countertuple under the same motion and mover predicates. |
| `REL-KRIPKE-NO-FACT-ALTERNATIVE-TO-PU-GRASP-NOT-INTERPRETATION` | attacks | #1154 makes this interpretive attacks: no-fact report does not negate noninterpretive grasp by itself. |
| `REL-OCCASIONALIST-MOVER-LINK-WITHOUT-CAUSE-ALTERNATIVE-TO-PER-SE-MOVER-LINK-IS-PER-SE-CAUSE-LINK` | alternative_to | Exact link/noncause envelope in the same per-se predicates; not a formalization of every occasionalist doctrine. |
| `REL-GLOBAL-EPISTEMIC-NIHILISM-ALTERNATIVE-TO-THERE-ARE-EPISTEMIC-REASONS` | alternative_to | Exact ∀ no-reason versus ∃ reason in the same reason relation; F6 approval preserved. |
| `REL-MAXIME-ADDITIONAL-OPPOSES-COVERAGE` | alternative_to | Actual additional scoped definition opposes named coverage only; existing certified maxime fork reused. |
| `REL-WF-CUT-OFF-ALTERNATIVE-TO-REVELATION-RECOGNIZABLE` | alternative_to | #1136 distinguishes actual/possible recognition, admitted situations and capability/nonempty God guards. |
| `REL-UNQUALIFIED-ALL-OPINIONS-TRUE-ALTERNATIVE-TO-ITS-FAILURE` | alternative_to | Exact doctrine versus its negation; self-application remains conditional on explicit scope/disquotation. |
| `REL-ACTUALITY-WITHOUT-BEING-ALTERNATIVE-TO-ACTUALITY-ONLY-INSOFAR-AS-BEING` | alternative_to | Exact actual-without-esse countertuple under the same InAct/respect dictionary. |
| `REL-SOME-POTENCY-NOT-BEING-ACTUALIZED-ALTERNATIVE-TO-EVERY-POTENCY-IS-BEING-ACTUALIZED` | alternative_to | Exact inactive-potency countertuple; adopted/generic potency and Night admissibility remain distinct. |
| `REL-TELEONOMY-ALTERNATIVE-TO-NON-COGNITIVE-TENDING-NEEDS-KNOWING-DIRECTOR` | alternative_to | #1139 requires actual unguided tending and an explanatory exclusion bridge; natural mechanism alone is compatible. |
| `REL-MOVED-WITHOUT-POTENCY-ALTERNATIVE-TO-NOTHING-MOVED-EXCEPT-AS-IN-POTENCY` | alternative_to | #1153 preserves full occasionalist candidate and projects only its envelope into an exact analyst countertuple. |
| `REL-MEASURE-DOCTRINE-ALTERNATIVE-TO-ITS-FAILURE` | alternative_to | Exact qualified doctrine versus its negation; does not eliminate relativism without the scope concession. |
| `REL-UNIVERSE-UNCAUSED-ALTERNATIVE-TO-UNIVERSE-CAUSED` | alternative_to | #1155 distinguishes no edge from no existing causer; selected causer actuality is separate. |
| `REL-TLP-GOD-SENTENCES-ALTERNATIVE-TO-NATURAL-THEOLOGY-ARGUABLE` | attacks | #1149 makes raw source thesis an attacks edge; matched semantic/warrant bridges connect a typed negative. |
| `REL-POTENCY-PRIOR-TO-ACT-ALTERNATIVE-TO-ACT-SIMPLY-PRIOR-TO-POTENCY` | alternative_to | Exact same-respect classical counterpattern to actual-prior witness; independent priority investigation remains open. |
| `REL-PER-SE-CAUSAL-LOOP-ALTERNATIVE-TO-NO-INFINITE-PER-SE-EFFICIENT-CAUSE-SERIES` | alternative_to | Loop is a stronger failure case; row 54 and #1156 supply classical descending-chain coverage. |
| `REL-PHILLIPS-NO-OBJECT-ALTERNATIVE-TO-UNIQUE-PURE-ACT-FIRST-MOVER-IS-GOD` | alternative_to | #1132 pending: actual proper-name witness and matching transfer connect the practice-internal reading to exact naming failure. |
| `REL-SOME-MEANINGFUL-NEGATION-DOUBLE-NEGATION-NOT-MEANINGFUL-ALTERNATIVE-TO-CLOSURE-WEAK` | alternative_to | Exact failure of the weak meaningfulness closure, same content and negation dictionary. |
| `REL-STRONG-SCIENTISM-ALTERNATIVE-TO-NON-EMPIRICAL-KNOWLEDGE` | alternative_to | #1154 requires relevant scope coverage; all, pointwise and existential sufficient forms are distinguished. |
| `REL-UNSELECTED-EXPLANATION-ALTERNATIVE-TO-SELECTION` | alternative_to | #1157 adds accepted-false cases and factivity; truthful nonselection alone is not exhaustive. |
| `REL-GLOBAL-NO-ABSOLUTE-TRUTH-ALTERNATIVE-TO-SOME-ABSOLUTE-TRUTH` | alternative_to | Exact ∀ no-absolute-truth versus ∃ absolute truth in one predicate; source-concession guards remain. |
| `REL-CONCRETE-NOT-SPATIOTEMPORAL-ALTERNATIVE-TO-N2` | alternative_to | Exact selected concrete-outside-spacetime countertuple for N2, not every naturalism variant. |
| `REL-CHANGE-UNREAL-BUT-APPEARS-ALTERNATIVE-TO-OPINION-IS-A-MOTION` | alternative_to | #1160 adds the exact local opiner countertuple; global no-motion-with-appearance is strictly stronger. |
| `REL-PLATONIC-FORMS-ARE-EFFICIENT-CAUSES-ALTERNATIVE-TO-CAUSAL-POWER-CONCRETENESS` | attacks | #1152 replaces automatic rivalry by no-esse/productive/world guards; full Forms claim preserved. |
| `REL-ELEATIC-NOTHING-IS-MOVED-ALTERNATIVE-TO-SOMETHING-IS-MOVED-IN-THIS-WORLD` | alternative_to | Exact same-signature no-movement complement, without attributing every historical Eleatic commitment. |
| `REL-MATHEMATICAL-FACTS-ARE-CAUSALLY-RELEVANT-ALTERNATIVE-TO-CAUSAL-POWER-CONCRETENESS` | attacks | #1152 distinguishes explanatory relevance from productive causation and selected-world no-esse. |
| `REL-SOME-CASE-PREDICATE-CONTRADICTION-ALTERNATIVE-TO-CASE-NON-CONTRADICTION` | alternative_to | Exact native-classical predicate contradiction; not a rejection of every paraconsistent logic. |
| `REL-PAST-IS-FINITE-ALTERNATIVE-TO-PAST-IS-INFINITE` | alternative_to | #1156 proves the pointwise predecessor/no-predecessor fork under EM; not cardinal or physical finitude. |
| `REL-ACT-AND-POTENCY-IN-SAME-RESPECT-ALTERNATIVE-TO-NOTHING-IN-ACT-AND-POTENCY-IN-SAME-RESPECT` | alternative_to | Exact same-respect act/potency countertuple; #1125 preserves adopted versus generic senses. |
| `REL-EXCLUDED-MIDDLE-DENIAL-ALTERNATIVE-TO-EXCLUDED-MIDDLE` | alternative_to | #1137 distinguishes explicit denied instance from the global ¬∀EM complement; no intuitionist attribution. |
| `REL-PLA-NONSENSE-ALTERNATIVE-TO-REDUCTIO-READING` | attacks | #1149 treats source interpretation as attacks, not automatic formal opposition/exhaustion. |
| `REL-QUASI-REALIST-MINIMAL-TRUTH-ALTERNATIVE-TO-REALIST-ROBUST-TRUTH` | alternative_to | #1135 requires a shared moral witness and links exact negative; empty moral scope can overlap. |
| `REL-PHILLIPS-NO-OBJECT-ALTERNATIVE-TO-UNIQUE-MAXIME-ENS` | alternative_to | #1132 pending: same proper-name transfer/witness boundary as row 22, for the maxime target. |
| `REL-SOME-MEANINGFUL-NEGATION-NOT-MEANINGFUL-ALTERNATIVE-TO-CLOSURE-STRONG` | alternative_to | Exact failure of strong meaningfulness closure; approved strong/weak authority unchanged. |
| `REL-TERTIA-VIA-STEP-QUANTIFIER-SHIFT-READING-ALTERNATIVE-TO-PLENITUDE-READING` | attacks | #1156 makes textual interpretation attacks; refuting a quantifier-shift reading does not license plenitude. |
| `REL-QUANTIFIER-SHIFT-ALTERNATIVE-TO-COLLECTIVE-POSSIBILITY` | removed | #1147 removes a positive proposed proof method from opposition; original schema/refutation preserved. |
| `REL-MCTAGGART-UNREALITY-OF-TIME-ALTERNATIVE-TO-SOMETHING-CHANGES` | alternative_to | #1156 adds exact general NoChange; stronger source bundle has two separately bound AND commitments. |
| `REL-EXPRESSIVIST-MEANING-ALTERNATIVE-TO-EMOTIVIST-MEANING` | alternative_to | #1154 exposes constant-expression coexistence and actual free-standing/embedded-loss/moral-witness guards. |
| `REL-PHILLIPS-NO-OBJECT-ALTERNATIVE-TO-FULLY-DESCRIBED-PRINCIPLE` | alternative_to | #1132 pending: same proper-name transfer/witness boundary as row 22, for the fully described target. |
| `REL-JESUS-MANDATE-COVERS-ONLY-MESSAGE-ALTERNATIVE-TO-COMMISSION-REPORTS-GO-BACK-TO-JESUS` | alternative_to | #1158 pending: actual historical/commission witnesses and weak governing link are required; full raw claim preserved. |
| `REL-MOVED-MOVER-MOVES-NOT-AS-MOVED-ALTERNATIVE-TO-SECOND-MOVERS-MOVE-ONLY-AS-MOVED` | alternative_to | Exact countertuple to the strong as-moved link; 17 actual strong-version consumers are separately reserved for audit. |
| `REL-ANTIREALIST-ORDER-ALTERNATIVE-TO-REALIST-ORDER-OF-EXPLANATION` | alternative_to | #1149 requires matching direction, asymmetry and an actual moral witness; directions can otherwise coexist. |
| `REL-SOME-CAUSE-LACKS-ESSE-IN-RE-ALTERNATIVE-TO-CAUSAL-POWER-CONCRETENESS` | attacks | #1152 exposes selected-world mapping; an other-world abstract cause alone does not defeat this owner commitment. |
| `REL-INERTIAL-UNIFORM-MOTION-WITHOUT-MOVER-ALTERNATIVE-TO-NOTHING-REDUCED-TO-ACT-EXCEPT-BY-A-MOVER` | alternative_to | Inertial subclass is stronger; row 6 already gives exact general countertuple; becoming/state bridges stay explicit. |
| `REL-JESUS-MANDATE-COVERS-ONLY-MESSAGE-ALTERNATIVE-TO-MANDATE-SCOPE-OF-CATHOLIC-CHURCH` | alternative_to | #1158 pending: actual mandate/founding/visible witness is required; raw OnlyMessage can coexist vacuously. |
| `REL-UNIVERSAL-DOUBT-ALTERNATIVE-TO-UNIVERSAL-DOUBT-FAILS` | alternative_to | Exact universal-doubt proposition versus its negation; hinge/OC bridges remain open. |
| `REL-MEGARIAN-ABILITY-ONLY-WHEN-ACTING-ALTERNATIVE-TO-NOTHING-MOVED-EXCEPT-AS-IN-POTENCY` | attacks | #1153 makes Megarian objection guarded by actual motion and weak SAME-sense moved-tuple analysis. |
| `REL-SOME-CAUSES-ARE-SETS-ALTERNATIVE-TO-CAUSAL-POWER-CONCRETENESS` | attacks | #1152 requires productive/no-esse/world guards and removes unsupported universal impure-set source inference. |
| `REL-INFINITE-PER-SE-CAUSE-SERIES-ALTERNATIVE-TO-NO-INFINITE-PER-SE-EFFICIENT-CAUSE-SERIES` | alternative_to | #1156 reuses existing classical choice coincidence theorem; repeated members/loops allowed, applicability open. |
| `REL-CAUSE-MOVES-WITHOUT-BEING-IN-ACT-ALTERNATIVE-TO-NOTHING-MOVES-EXCEPT-AS-IN-ACT` | alternative_to | Exact mover/not-in-act countertuple in the chosen formal/virtual dictionary; source emergence not inferred. |
| `REL-NATURAL-REASON-HORIZON-ALTERNATIVE-TO-NATURAL-REASON-SHARED` | alternative_to | #1142 pending: theological horizon can coexist with outsider use; actual exclusive insulation/witness required. |

At that exact integrated snapshot there are **82** `alternative_to` records:
46 retained baseline records and **36 additions**. Eleven baseline records were
removed or changed to attacks; this is not eleven refutations. The additions
below were checked against their actual statement/paraphrase and declared
profile. Exact complements and calibrated remainders serve different purposes.
A remainder opposing coverage does not automatically oppose an old conclusion.

| Added rival statement | Exact target | Scope / consequence boundary |
|---|---|---|
| `STMT-ACCEPTED-ARRANGEMENT-EXPLANATION-FACTIVITY-FAILS` | `STMT-ACCEPTED-ARRANGEMENT-EXPLANATIONS-ARE-TRUE` | Exact matching-profile negation, preserving all stronger source/analyst accounts separately. Conditional proof is not independent warrant or an actual historical refutation. |
| `STMT-ACTUAL-MOVED-NOT-POTENT-COUNTERTUPLE` | `STMT-NOTHING-MOVED-EXCEPT-AS-IN-POTENCY` | Exact unrefuted analyst countertuple. Existing stronger occasionalist candidate remains intact; refuting a full re-creation story would not eliminate every moved/not-potent tuple. Structural coverage is explicit in MOVED-POTENCY-EXACT-COUNTERCASE-FORK. |
| `STMT-CHURCH-HAS-ADDITIONAL-CRITERION` | `STMT-CHURCH-NAMED-CRITERIA-COVER` | The selected extension matches none of the three named criteria. It contradicts named coverage, not the original stage-5 statement: separate controls witness it with either target verdict. |
| `STMT-EMPIRICAL-PROOF-ADDITIONAL-BARRIER` | `STMT-EMPIRICAL-PROOF-BARRIER-COVERAGE` | The scoped unprovable target without ObservationBarrier contradicts that barrier coverage. It need not contradict restricted unprovability; the law control witnesses both facts together. |
| `STMT-DIVINE-FOUNDING-HAS-ADDITIONAL-READING` | `STMT-DIVINE-FOUNDING-NAMED-READINGS-COVER` | The precise remaining reading is the negation of both named extension calibrations, hence contradicts their disjunction. It is an alternative to named coverage, not automatically an alternative to the old envoy bridge: the finite remainder controls admit opposite bridge verdicts. |
| `STMT-COMMISSION-HAS-ADDITIONAL-GOVERNANCE-CRITERION` | `STMT-COMMISSION-NAMED-GOVERNANCE-CRITERIA-COVER` | A genuinely different selected criterion contradicts named coverage only. The controls give Other with opposite mandate-scope verdicts; it is not automatically a rival to the old institutional or mandate conclusion. |
| `STMT-COLLECTIVE-POSSIBILITY-FAILS` | `STMT-ALL-CAN-NOT-BE-THEN-NOTHING-POSSIBLE` | Exact unrefuted analyst complement of the same conditional. The existing perpetual-succession rival is preserved separately; refuting a positive proof method or a finite named roster cannot establish this premise. |
| `STMT-UNITED-ESSE-COMMUNICATION-RECEPTION-TRANSFER-FAILS` | `STMT-UNITED-ESSE-COMMUNICATION-COUNTS-AS-RECEPTION` | Exact negative proposition, derived only under its registered explicit premises; no unconditional philosophical defeat is claimed. |
| `STMT-COMPLETE-ARRANGEMENT-SELECTION-REQUIREMENT-FAILS` | `STMT-COMPLETE-CHAIN-EXPLANATION-SELECTS-ARRANGEMENT` | Exact matching-profile negation, preserving all stronger source/analyst accounts separately. Conditional proof is not independent warrant or an actual historical refutation. |
| `STMT-EFFICIENT-ATTRIBUTION-ADDITIONAL-TEMPORAL-DEFINITION` | `STMT-EFFICIENT-ATTRIBUTION-NAMED-TEMPORAL-DEFINITIONS-COVER` | Both named calibrations fail; this opposes coverage, not the original independent composer attribution or the composite conclusion. |
| `STMT-EPISTEMIC-REASON-BARE-PRODUCTION-DEFINITION-FAILS` | `STMT-EPISTEMIC-REASON-BARE-PRODUCTION-DEFINITION` | Exact profile-specific negation of this bare-production calibration, not a denial of naturalistic realization. |
| `STMT-EPISTEMIC-REASON-ADDITIONAL-DEFINITION-REMAINS` | `STMT-EPISTEMIC-REASON-DEFINITION-CANDIDATES-COVER` | The remaining calibration conjunction negates the four-way named coverage proposition in the same fixed profile. It is not a blanket rival to ordinary support or independent authority. |
| `STMT-EPISTEMIC-REASON-BARE-REWARD-DEFINITION-FAILS` | `STMT-EPISTEMIC-REASON-BARE-REWARD-DEFINITION` | Exact profile-specific negation of this bare-reward calibration, leaving informative reward accounts open. |
| `STMT-PRIMITIVE-ETERNITY-ADDITIONAL-DEFINITION` | `STMT-PRIMITIVE-ETERNITY-NAMED-DEFINITIONS-COVER` | Both named calibration propositions fail; no rival to the primitive eternity conclusion is inferred from this remainder alone. |
| `STMT-NOTHING-CHANGES-IN-GENERAL` | `STMT-SOMETHING-CHANGES` | Exact analyst complement in the SAME general-change signature, not attributed to a historical school. Existing McTaggart1908 rival and observation approval are preserved. Refuting that stronger bundle alone cannot exhaust opposition. |
| `STMT-OPINER-LACKS-ITS-OPINION-MOTION` | `STMT-OPINION-IS-A-MOTION` | Exact matching-sense countertuple under the SAME designated respect; preserves the full stronger raw account separately. Refuting that stronger account alone does not exhaust denial of the universal norm. |
| `STMT-GOODNESS-ADDITIONAL-RELEVANT-DEFINITION` | `STMT-GOODNESS-NAMED-DEFINITIONS-COVER` | Explicit analyst structural/scope rival under one fixed supplied profile. No counted refutation is registered; conditional/modelled failure is not independent philosophical defeat. |
| `STMT-GOODNESS-ADDITIONAL-SEMANTIC-DEFINITION` | `STMT-GOODNESS-SEMANTIC-NAMED-DEFINITIONS-COVER` | An explicit admissible extension differs from every named account. No counted refutation is registered. The fixed mixed-artifact fourth proposal is such a formal witness; no actual-world exhaustion conclusion follows. |
| `STMT-GOODNESS-OMITS-DUE-ACTUALITY` | `STMT-GOODNESS-DUE-TO-FORM-AND-END` | Explicit analyst structural/scope rival under one fixed supplied profile. No counted refutation is registered; conditional/modelled failure is not independent philosophical defeat. |
| `STMT-GOODNESS-SURPLUS-BEYOND-DUE-ACTUALITY` | `STMT-GOODNESS-DUE-TO-FORM-AND-END` | Explicit analyst structural/scope rival under one fixed supplied profile. No counted refutation is registered; conditional/modelled failure is not independent philosophical defeat. |
| `STMT-DIVINE-FOUNDING-IMMEDIATE-READING-FAILS` | `STMT-DIVINE-FOUNDING-IS-IMMEDIATE-ONLY` | Exact contextual negation of the direct-only calibration in one supplied signature/agency/direct relation. It does not refute immediate founding universally or identify the inclusive interpretation as exhaustive. |
| `STMT-PROPER-REFERENCE-LOST` | `STMT-PROPER-REFERENCE-PRESERVED` | Actual counterexample to one-way preservation in the fixed profile; not another named reference theory. Explicit EM proves the structural coverage result. |
| `STMT-MEANING-REMAINING-DEFINITION` | `STMT-MEANING-NAMED-COVERAGE` | Under the same frame, predicate and scope, the remaining conjunction negates all named branches. It is not automatically a rival to a separate meaning/truth target; no philosophical admissibility or exhaustive named survey is claimed. |
| `STMT-CONCILIAR-DEFINITION-STATUS-MIXED` | `STMT-CONCILIAR-NAMED-DEFINITION-STATUS-COVERAGE` | Actual endorsed and nonendorsed defined witnesses exclude both uniform status profiles. This opposes named uniform coverage, not theology, authority, ordinary religious life or a whole worldview. |
| `STMT-NAMED-PRODUCTIVE-CAUSAL-COVERAGE-FAILS` | `STMT-NAMED-PRODUCTIVE-CAUSAL-COUNTERACCOUNTS-COVER` | Exact selected-profile complement, unrefuted. Broad category or other-world accounts require their explicit interfaces; no finite named-theory roster is treated as exhaustive. |
| `STMT-NOT-ALL-EXCLUDED-MIDDLE-INSTANCES-ASSERTED` | `STMT-ALL-EXCLUDED-MIDDLE-INSTANCES-ASSERTED` | Exact logical negative of the same stage-indexed assertion target. Derived from full raw withholding via WITHHOLDING-IMPLIES-NOT-UNIVERSAL-ASSERTION; no logical holding-to-assertion bridge or full intended intuitionist-model claim follows. |
| `STMT-NOT-EXCLUDED-MIDDLE` | `STMT-EXCLUDED-MIDDLE` | Exact global complement in the same logic, unrefuted and analyst-only. The constructive refutation of ∃p¬(p∨¬p) does not refute this ¬∀p(p∨¬p) statement. No historical attribution or coverage proof is inferred. |
| `STMT-OBJECTIVE-TRUTH-ADDITIONAL-DEFINITION` | `STMT-OBJECTIVE-TRUTH-NAMED-DEFINITIONS-COVER` | RemainingDefinition is exactly the conjunction of negations of the three calibrations in NamedCoverage, under the same frame/comparison class. This additional-extension branch opposes named coverage, not every target truth-component claim: the checked remaining classifier itself satisfies objective-implies-truth. No refutes relation or counted defeat is registered. |
| `STMT-OUTSIDE-ADMISSIBLE-RECOGNITION` | `STMT-ADMISSIBLE-RECOGNITION-COVERAGE` | An actual relevant God/capability/correct-recognition witness exists outside the admitted subset and no admitted witness exists. It contradicts coverage in the fixed candidate carrier; it is not an asserted census of real possible situations. |
| `STMT-NATURAL-THEOLOGY-PROFILE-NOT-ARGUABLE` | `STMT-NATURAL-THEOLOGY-PROFILE-ARGUABLE` | Exact logical negative on the same explicit profile. Strong no-divine-sense is only one sufficient input; refuting it does not establish arguability. The two old untyped source/question propositions remain independent; their profile-adequacy and argument/warrant bridges are OPEN. |
| `STMT-EMPIRICAL-PROOF-REMAINING-DOMAIN` | `STMT-EMPIRICAL-PROOF-NAMED-DOMAIN-COVERAGE` | Same table/predicate; the remainder denies each named calibration. It is not a proof-status rival. |
| `STMT-SELECTED-CAUSAL-CONCRETENESS-COMMITMENT-FAILS` | `STMT-CAUSAL-POWER-AND-ACTIVITY-REQUIRE-CONCRETENESS` | Exact selected-profile complement, unrefuted. Broad category or other-world accounts require their explicit interfaces; no finite named-theory roster is treated as exhaustive. |
| `STMT-CHURCH-SPIRITUAL-CRITERION-FAILS` | `STMT-CHURCH-HAS-SPIRITUAL-CRITERION` | Exact negation of this fixed spiritual calibration; mere insufficiency for the visible stage target is not this negation. |
| `STMT-ESSE-RECEIVED-IN-OWN-ESSENCE-FAILS` | `STMT-ESSE-RECEIVED-IN-OWN-ESSENCE` | Exact negative proposition, derived only under its registered explicit premises; no unconditional philosophical defeat is claimed. |
| `STMT-SPACETIME-WHOLE-HAS-NO-EXISTING-CAUSE` | `STMT-UNIVERSE-HAS-EXISTING-CAUSE` | Exact matching-scope unrefuted negative, not a presumed complete list of historical accounts. |
| `STMT-SELECTED-WHOLE-CAUSER-ACTUALITY-FAILS` | `STMT-SELECTED-WHOLE-CAUSERS-ACTUALLY-EXIST` | Exact matching-scope unrefuted negative, not a presumed complete list of historical accounts. |

The finite-roster counterfactuals distinguish authority from coverage. At the
earlier baseline, no statement was newly classified `alternatives_refuted`,
but two independently floored patterns had every then-recorded rival refuted
(CaseNonContradiction and SomethingChanges). This did not certify a census of
philosophical theories. Removing only the target's own floor in actual-record
copies leaves EM, causal concreteness, F3, moved-potency and F6 unestablished;
the weak meaningfulness closure may still inherit the independently approved
strong closure. Native-classical contradiction refutation is restricted to its
fixed negation signature. No approval is revoked by these tests.

A concrete finite-roster defect was reproduced in #1147: removing the unencoded
perpetual-succession edge let a refuted **positive proof method** count as all
opposition to collective possibility. The endpoint repair removes that category
error and adds an unrefuted exact complement. #1137 likewise keeps global ¬EM
distinct from a constructively refuted explicit denied instance. New conditional
eliminations carry checked structural coverage or a separate OPEN named-coverage
premise. They do not use a finite list of refuted named schools as philosophical
exhaustion. Reproduction commands and actual-record boundaries remain in the
[collective route](notes/collective-possibility-route-boundary.md),
[causal concreteness](notes/causal-concrete-rival-boundary.md) and
[change/regress/past](notes/causal-temporal-rival-coverage.md) research notes.

#### Delivered definition-pointer dispositions (#1110)

[PR1161](https://github.com/moritzbrantner/truth-core/pull/1161), merged as
`5fcedc5299bf9acb9cdbb937531e4285b897f6b4`, resolves the 32 pointer/scope
dispositions below. Thirty records receive a correction or qualification;
potency and immutability had already been repaired. A pointer to a primitive
field locates vocabulary; it does not supply a philosophical analysis.

| Definition | Delivered disposition | Exact locator, where available |
|---|---|---|
| `DEF-ACT` | field/predicate/partial-carrier pointer corrected | `TruthCore.Latin.Aquinas.SummaTheologiae.MotionModel.InAct` |
| `DEF-ALTOGETHER-IMMATERIAL` | exact parameter/constraint or family/local-clause scope clarified | `TruthCore.Latin.Aquinas.SummaTheologiae.ImmaterialIsIntellectualReading` |
| `DEF-BEING-AS-ENTITY` | field/predicate/partial-carrier pointer corrected | `TruthCore.Latin.Aquinas.SummaTheologiae.MotionModel.Being` |
| `DEF-BEING-AS-TRUTH-OF-A-PROPOSITION` | exact parameter/constraint or family/local-clause scope clarified | `TruthCore.Latin.Aquinas.SummaTheologiae.EvilIsAsPropositionalTruthReading` |
| `DEF-BRUTE-ROOT-RELATIVE-GROUNDING` | field/predicate/partial-carrier pointer corrected | `TruthCore.Causality.NecessaryRootFork.ActualRoot` |
| `DEF-CAUSE-OF-ORIGIN` | exact parameter/constraint or family/local-clause scope clarified | `TruthCore.Latin.Aquinas.SummaContraGentiles.WhatComesToBeAnewHasInnovatingCauseReading` |
| `DEF-CAUSE-OF-PERFECTION` | exact parameter/constraint or family/local-clause scope clarified | `TruthCore.Latin.Aquinas.SummaTheologiae.CausesAllInGenus` |
| `DEF-RESURRECTION-PILOT-HISTORY` | exact parameter/constraint or family/local-clause scope clarified | `TruthCore.History.Resurrection.State` |
| `DEF-ESSENCE-THOMISTIC-NATURE` | field/predicate/partial-carrier pointer corrected | `TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile.essenceOf` |
| `DEF-FOUNDED-BY-GOD-THROUGH-ENVOY` | exact parameter/constraint or family/local-clause scope clarified | `TruthCore.Case.Catholicism.StageThree.DivineFounding.Agency` |
| `DEF-GENUS-BROAD` | exact parameter/constraint or family/local-clause scope clarified | `TruthCore.Latin.Aquinas.SummaTheologiae.MaximumInGenusCausesAllInGenusReading` |
| `DEF-GENUS-STRICT` | exact parameter/constraint or family/local-clause scope clarified | `TruthCore.Greek.Aristotle.Metaphysics.BeingIsNotAGenusReading` |
| `DEF-GOD-OF-CLASSICAL-THEISM` | field/predicate/partial-carrier pointer corrected | `TruthCore.Case.Catholicism.Signature.IsGod` |
| `DEF-GREATEST-BEING-STRICT` | exact parameter/constraint or family/local-clause scope clarified | `no single defining declaration` |
| `DEF-HOML-ACTUALIST-NECESSITY` | field/predicate/partial-carrier pointer corrected | `TruthCore.Isabelle.AFP.GoedelGod.Box` |
| `DEF-LEAN-PROPOSITION-HOLDING` | exact parameter/constraint or family/local-clause scope clarified | `TruthCore.Logic.TruthPilot.SomePropositionHolds` |
| `DEF-MAXIME-ENS` | field/predicate/partial-carrier pointer corrected | `TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximalIn` |
| `DEF-MAXIMUM-IN-A-PERFECTION` | field/predicate/partial-carrier pointer corrected | `TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximalIn` |
| `DEF-MORE-IN` | exact parameter/constraint or family/local-clause scope clarified | `TruthCore.Latin.Aquinas.SummaTheologiae.GradesFoundInThingsReading` |
| `DEF-MOTION-AS-REDUCTION` | field/predicate/partial-carrier pointer corrected | `TruthCore.Latin.Aquinas.SummaTheologiae.MotionModel.MovedIn` |
| `DEF-NECESSARY-INDIVIDUAL-DOMAIN` | field/predicate/partial-carrier pointer corrected | `TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1.ExistsAt` |
| `DEF-ONTOLOGICAL-TRUTH-COMPARISON` | exact parameter/constraint or family/local-clause scope clarified | `TruthCore.Latin.Aquinas.SummaTheologiae.GradesFoundInThingsReading` |
| `DEF-ONTOLOGICAL-TRUTH` | exact parameter/constraint or family/local-clause scope clarified | `TruthCore.Latin.Aquinas.SummaTheologiae.MostTrueIsMostBeingReading` |
| `DEF-PARTICIPATION-GROUND` | field/predicate/partial-carrier pointer corrected | `TruthCore.Greek.Plato.ParticipationGrounding.Explanation.Grounds` |
| `DEF-Q11-COMMON-DIVINE-NATURE` | exact parameter/constraint or family/local-clause scope clarified | `TruthCore.Latin.Aquinas.SummaTheologiae.ProperGodInstancesHaveCommonNatureReading` |
| `DEF-Q11-GOD-SUPPOSITUM-NATURE` | exact parameter/constraint or family/local-clause scope clarified | `TruthCore.Latin.Aquinas.SummaTheologiae.GodSuppositumIsNatureReading` |
| `DEF-Q11-INDIVIDUATING-BASIS` | exact parameter/constraint or family/local-clause scope clarified | `TruthCore.Latin.Aquinas.SummaTheologiae.IndividuatingBasisIsIncommunicableReading` |
| `DEF-REGRESS-DOMAIN-ADAPTERS` | exact parameter/constraint or family/local-clause scope clarified | `no single defining declaration` |
| `DEF-RESPECT` | field/predicate/partial-carrier pointer corrected | `TruthCore.Latin.Aquinas.SummaTheologiae.MotionModel.Respect` |
| `DEF-SKELETON-OPEN-PREDICATES` | exact parameter/constraint or family/local-clause scope clarified | `TruthCore.Case.Catholicism.Signature` |
| `DEF-POTENCY` | already repaired on main: AdoptedPotency.InPotency | `no single defining declaration` |
| `DEF-IMMUTABLE` | already repaired on main: IsImmutable with no-potency scope note | `no single defining declaration` |

The necessary-individual-domain pointer is only the `ExistsAt` carrier locator,
not the whole de-re quantifier analysis. Maximality remains distinct from
greatestness and strict supremacy. Constraint/bundle locators for primitive
truth, genus, nature and other open predicates are explicitly qualified; none
is silently adopted as the predicate's meaning. No premise change or new floor
results from this metadata work.

#### Discovery completed; use-level investigation still active

The completed 350 baseline plus five then-added disambiguation resolution reads
do **not** exhaust definitions used by arguments. A subsequent actual-use scan
at snapshot 308602fa plus the opining batch found 453 used definition records
outside every disambiguation sense list: 355 parent-owned, 79 truth/meaning and
19 authority/history. “Used” here means direct argument definition links or
links on its premise/conclusion statements, not semantic dependence inferred
from a keyword. Later additions are not retrospectively included in these counts.

The truth worker's 79 full records and mapped consumers are persisted in
`docs/notes/truth-definition-use-audit.md` and its per-ID JSON in pending #1162;
84 selected exact result types were inspected, not every descendant proof.
That pass found a consequential weaker goodness input. Its review caught a
coextension issue: existence of a correct named support witness also implies
semantic namedness of every admissible **correct** account in the same GoodIn
dictionary. It is weaker than coverage of arbitrary admissible candidates,
including wrong ones; the companion equivalence and corrected prose remain
under required P1 rereview. No result or disposition from that pending revision
is counted as integrated here. The authority 19-record use pass is active.

The parent-owned 355 still require full record and actual consumer/type review
where earlier cluster work has not already supplied it. The large remaining
families are causal and explanatory interfaces, then the Greek/Latin source
reconstructions and residual modal/ontology profiles. Existing complete
Mereology, Science and Hiddenness cluster reads can be reused only for their
precise inspected IDs. The fresh Greek/Latin/no-head definition-text read is
discovery, not completed use-level certification.

Distinct reserved investigations are not duplicated in this pass: #1111's seven
same-dictionary overlaps; #1112's opaque per-se/per-accidens conjunction and
first-member presupposition (typed sibling required); 17 second-mover and three
absolute-first-mover strong-version consumers; the separate actual-priority
investigation; and #1109's laws/spacetime/logic/math/God naturalism remainder.
Their exact delivered records and proof boundaries must be incorporated when
available. Current source-only plurality of possible causers is still a
prospective source-candidate formalization, not a repaired current typed route.
No whole-repository completion or exhaustive philosophical survey is claimed.

The first bounded follow-through in the parent 355 reads the full typed physical
motion vocabulary and the frozen result interfaces for VIII.4 literal mover,
VIII.4 per-se mover, physical-to-broad scope, VII.1 contact regress and
per-se-to-local regress. The existing five-way AND input with two nested OR
divisions already distinguishes natural/forced, self/passive, and per-se/per-accidens
movers. Its explicit literal-reading countermodel blocks silently promoting a
remover to a per-se mover. The physical-to-broad reduction bridge is separately
OPEN and its omission control blocks scope promotion. No new definition fork is
needed for these already separated readings. VII.5 alteration/growth/threshold
records and their sole consumer remain explicitly opaque transcriptions; they
assert no measured dynamics or modal possibility. This is not a completed audit
of every Physics statement.

That read identified a useful weaker sufficient VII.1 composition premise:
`TouchingChainFormsOneReading` currently ranges over every injective touching
chain, whereas the contact regress needs it only for chains of the SAME local
moved-mover links. The old reading explicitly calls its broader scope a
generalization. A local-chain sibling, checked strength relation, exact-target
route and populated strictness control are the next concrete implementation;
the global source reading and frozen proof remain unchanged.

The reserved overlap and series investigations have now published #1164
(`d1d71036`, seven same-dictionary dispositions and one zero-axiom connection
certificate) and #1163 (`22eb1dc3`, typed essential/history-series distinction).
Both are pending review/CI at this ledger revision. The latter exhibits a
nonempty well-founded essential order and infinite history on the same members;
old opaque source conjunction is preserved and temporal/removal bridges remain
OPEN. Neither is counted as a merged repair or premise discharge here.
