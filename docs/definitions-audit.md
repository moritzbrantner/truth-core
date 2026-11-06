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
| `DEF-OBJECTIVE-TRUTH`; `DISAMB-TRUE`; `POE-EXTERNAL-PREMISE-VS-EMOTIVISM` | Targeted truth-lane implementation: explicit truth-component bridge, stronger actual-truth-plus-profile-invariance calibration and invariant-only rival. False-but-invariant control prevents stance independence from being confused with objective **truth**. | Source ObjectiveTruth predicates and claims remain general. Profile invariance is one operational account, not all philosophical objectivity. Active separate batch. |
| `STMT-ENVOY-FOUNDING-IS-GODS-FOUNDING`; `DISAMB-FOUNDED-BY-GOD` | Targeted authority-lane implementation: immediate/inclusive calibration propositions, exact strong-exclusion scope, explicit coverage/Other, overlap and countermodels. Old prose's categorical “immediate-only makes it false” needs an actual commissioned-event witness and the exclusion condition; the generic type also lacks a HoldsMandate hypothesis. | Weak principal-own-act and stronger no-envoy/creature readings are not silently equated. Existing Challenges and source claims remain. Active separate batch. |
| `DISAMB-NAME-APPLICATION`; practice no-reference vs nominal God leaves | Three recorded alternatives cross a practice-reference predicate and proper nominal IsGod without a typed transfer. Existing noBeingExcludes proofs specialize the generic schema; they do not supply a cross-sense implication. | Next authority batch must expose coextension/one-way transfer and correct profile scope, retaining the serious rival at full strength rather than deleting it. |
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
