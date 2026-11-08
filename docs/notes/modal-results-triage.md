# Modal results triage (#1233)

Owner direction 2026-11-07 ("Connect every library to the case"): every one of
the 84 verified results of `TruthCore.Modal` that did not reach
`STMT-CATHOLICISM-TRUE` (`truth orphans`, built from PR #1229, any-verified-route
rule) is classified here. Each row was read with `corpus.py context`.

Categories:

- **A**: its conclusion feeds a root-route step directly; connected by this
  batch (`specs/modal-sense-support.toml`).
- **A-deferred**: it could feed a root-route node, but only with more than one
  missing bridge; the target and the missing bridge are named. Not connected.
- **B**: it refutes or constrains a rival (modal collapse, necessitism,
  ontological symmetry, ditheism, the "no necessary individual" rival, Scott's
  essence-based senses). The rival and, where one exists, the opposed root
  premise are named.
- **C**: a control, countermodel, witness or piece of infrastructure, not meant
  to connect.
- **D**: off-case.

Counts: A 2, A-deferred 5, B 27, C 40, D 10 (84).

## Finding

The root route that uses modal necessity is the necessary-classical-God route
with the "necessary" sense fork (#1230). Its necessity is the Kripke box of the
modal library (`necessaryAt_iff_boxExistsAt`, `Iff.rfl`) in frame class K. The
only questions that route asks of modal logic are the frame conditions of its
T, S4, KTB and S5 readings. The modal library answers exactly those through its
correspondence theorems, and this batch now uses them: the frame condition is
derived from a modal principle (the T, 4, B or 5 schema is valid on the route's
frame) instead of being assumed as a semantic premise. Both correspondence
results are recorded as assembly certificates (transcription kind `assembly`),
so the non-transcription orphan count of the group is unchanged.

Almost everything else in the library is about modal collapse, ontological
symmetry, domains and finite controls. Those results constrain rivals, but the
root path contains no premise that a collapse rival contradicts: the route never
asserts that an actual contingent being exists. A contingency premise on the
route (for example, that the Cogito bearer or some moved thing is contingent at
the actual world) is the missing node that would turn the collapse laws into
refutations of a rival of a root premise.

## Follow-up: the contingency node

The blocker named above is now addressed by `specs/contingent-being-node.toml`
(map `explorations/contingent-being-node.toml`). `STMT-SOME-ACTUAL-CONTINGENT`
(OPEN; some actual concrete being is CONTINGENT_1, absent at some accessible
world) is on the root path through `CONTINGENT-NODE-INHABITS`, an assembly into
`STMT-COGITO-INHABITED-CONCRETE-WORLD`. Five collapse rivals are recorded
`alternative_to` it and refuted by verified arguments that apply the modal
library:

| Rival | Refuted by (reading) | Modal result applied | Counts for closure? |
|---|---|---|---|
| `STMT-ALL-ACTUAL-CONCRETE-NECESSARY` | `NOT-ALL-NECESSARY-FROM-CONTINGENT` (any) | none (exact contradictory) | No: rests on the OPEN node |
| `STMT-ROUTE-COLLAPSED` | `NO-COLLAPSE-K` (K) | `MODAL-K-LAWS` | No: rests on the OPEN node |
| `STMT-ROUTE-NEC-COLLAPSED` | `NO-NEC-COLLAPSE-T` (KT) | `MODAL-T-LAWS`, `MODAL-K-LAWS`, T correspondence | No: node and `STMT-ONTIC-T-SCHEMA` OPEN |
| `STMT-ROUTE-POSS-COLLAPSED` | `NO-POSS-COLLAPSE-KTB` (KTB) | `MODAL-B-LAWS`, `MODAL-K-LAWS`, B correspondence | No: node and `STMT-ONTIC-B-SCHEMA` OPEN |
| `STMT-ROUTE-POSS-COLLAPSED` | `NO-POSS-COLLAPSE-S5` (S5) | `MODAL-S5-LAWS`, T and 5 correspondences | No: node, `STMT-ONTIC-T-SCHEMA`, `STMT-ONTIC-5-SCHEMA` OPEN |
| `STMT-NECESSARY-ACT-YIELDS-ALL` | `NO-NECESSARY-ACT-YIELDS-ALL` (any) | `SIMPLICITY-COLLAPSE-CORE` | No: rests on the OPEN node |

Every refutation rests on the node itself, so none can defend the node; each
would count for another premise only once the node is established. Necessary
and possible collapse are compatible with the node in K (and possible collapse
in KT); the controls exhibit the frames. The rivals are not recorded against
`STMT-EVERY-CONTINGENT-GROUNDED-AT`: concrete necessitarianism makes that premise
vacuously true (`CONTINGENT-NODE-CONTROLS`, Scope), and no other root-path premise
is contradicted by collapse.

`truth orphans` still lists these Modal results as disconnected (group count
82): it counts a result as connected only when its conclusion reaches the root,
and a refutation's conclusion is not a route node. The applying arguments show
the link as `refutes` contacts.

## Connection table (A)

| Modal result | Root-route node | Argument |
|---|---|---|
| `MODAL-STANDARD-CORRESPONDENCE-CERTIFICATE` | `STMT-NECESSARY-ROOT-ON-INTENDED-READING` | `MODAL-FORK-T`, `MODAL-FORK-S4`, `MODAL-FORK-KTB`, `MODAL-FORK-S5` (reflexivity from the T schema) |
| `MODAL-HIJK-CONVERGENCE-CERTIFICATE` | `STMT-NECESSARY-ROOT-ON-INTENDED-READING` | `MODAL-FORK-S4` (transitivity), `MODAL-FORK-KTB` (symmetry), `MODAL-FORK-S5` (Euclideanness) |

The same arguments put `STMT-NECESSARY-ROOT-BOX-K` on the root path, which
connects the Causality results `NECESSARY-ROOT-BOX-K` and
`NECESSARY-ROOT-ACTUALIST-K-STRENGTHENS-BOX-K`.

`MODAL-FORK-T` is a cheaper derivation of the fork node: it replaces the three
OPEN fork premises (coverage, exclusivity, side condition) by two (the T schema
and the KT reading), so `NECESSARY-CLASSICAL-GOD-CASE-SENSE-FORK` drops from 53
to 52. The S4, KTB and S5 branches each need three OPEN premises and do not
lower the cost.

## Refutations (B)

| Rival | Refuted by | Counts for closure? |
|---|---|---|
| `STMT-MODAL-DITHEISM` (two distinct necessary universal potential causers) | `NECESSARY-POTENTIAL-CAUSERS-NOT-DISTINCT` (`REL-NO-DISTINCT-CAUSERS-REFUTES-DITHEISM`) | No: `STMT-ACTUAL-MODAL-REFLEXIVITY` and `STMT-WELL-FOUNDED-UNION-NECESSARY-SUPPORT` are OPEN. The first follows from the T schema (reflexive frame) but that premise is itself OPEN. |
| `STMT-NECESSARY-ACT-STRICT-CONTINGENT` (an act done at every accessible world strictly yields a contingent effect) | `SIMPLICITY-COLLAPSE-CORE` (`REL-SIMPLICITY-CORE-REFUTES-STRICT-CONTINGENT`) | The refutation has no premises, so it is unconditional in the frame semantics. It defends no root premise: the refuted statement is a reading the route itself must avoid, not a rival of a root premise. |

Neither rival is recorded as `alternative_to` a root premise. Modal ditheism
would oppose God-uniqueness only through a bridge identifying necessary
universal potential causers with God; that bridge is missing. The batch
controls check that each refuting conclusion is exactly the negation of its
rival (`RivalNegations`).

## Triage table

| Class | Result | Conclusion | Reason, target or blocker |
|---|---|---|---|
| A | `MODAL-HIJK-CONVERGENCE-CERTIFICATE` (assembly) | `STMT-MODAL-HIJK-CONVERGENCE-CERTIFICATE` | Connected by this batch: its 4/B/5 correspondences derive transitivity, symmetry and Euclideanness of the route frame for the S4, KTB and S5 branches of STMT-NECESSARY-ROOT-ON-INTENDED-READING (MODAL-FORK-S4/-KTB/-S5). |
| A | `MODAL-STANDARD-CORRESPONDENCE-CERTIFICATE` (assembly) | `STMT-MODAL-STANDARD-CORRESPONDENCE-CERTIFICATE` | Connected by this batch: its T correspondence (T schema valid iff reflexive) derives the KT, S4, KTB and S5 frame conditions of the fork node STMT-NECESSARY-ROOT-ON-INTENDED-READING (MODAL-FORK-T/-S4/-KTB/-S5). |
| B | `NECESSARY-IF-EXISTENT-COVERAGE` | `STMT-NECESSARY-IF-COVERAGE` | #437 ontological-argument symmetry: with a Euclidean frame and the boxed conditional, possible existence gives necessary existence and possible non-existence gives impossibility (coverage, no exclusivity). Rival: the reverse ontological argument. On the necessary route the root is already box-existent, so the reverse premise is refuted by the K node directly; the modal theorem is needed only on a route that starts from possibility (none on the root path). |
| B | `NECESSARY-IF-EXISTENT-EXACT-FRAME` | `STMT-NECESSARY-IF-EXACT-FRAME` | #437 ontological-argument symmetry: with a Euclidean frame and the boxed conditional, possible existence gives necessary existence and possible non-existence gives impossibility (coverage, no exclusivity). Rival: the reverse ontological argument. On the necessary route the root is already box-existent, so the reverse premise is refuted by the K node directly; the modal theorem is needed only on a route that starts from possibility (none on the root path). |
| B | `NECESSARY-IF-EXISTENT-NEGATIVE` | `STMT-NECESSARY-IF-IMPOSSIBLE-EXISTENCE` | #437 ontological-argument symmetry: with a Euclidean frame and the boxed conditional, possible existence gives necessary existence and possible non-existence gives impossibility (coverage, no exclusivity). Rival: the reverse ontological argument. On the necessary route the root is already box-existent, so the reverse premise is refuted by the K node directly; the modal theorem is needed only on a route that starts from possibility (none on the root path). |
| B | `NECESSARY-IF-EXISTENT-POSITIVE` | `STMT-NECESSARY-IF-NECESSARY-EXISTENCE` | #437 ontological-argument symmetry: with a Euclidean frame and the boxed conditional, possible existence gives necessary existence and possible non-existence gives impossibility (coverage, no exclusivity). Rival: the reverse ontological argument. On the necessary route the root is already box-existent, so the reverse premise is refuted by the K node directly; the modal theorem is needed only on a route that starts from possibility (none on the root path). |
| B | `SIMPLICITY-COLLAPSE-CORE` | `STMT-SIMPLICITY-COLLAPSE-CORE` | #462/#555 modal-collapse objection to a simple necessary root. Its first clause refutes STMT-NECESSARY-ACT-STRICT-CONTINGENT (REL-SIMPLICITY-CORE-REFUTES-STRICT-CONTINGENT, zero premises, so the refutation counts): the route cannot read the root's creative act as both performed at every accessible world and strictly efficacious for a contingent creature. A constraint on the route's own reading, not a rival of a root premise. Its first clause is also applied by NO-NECESSARY-ACT-YIELDS-ALL, which refutes STMT-NECESSARY-ACT-YIELDS-ALL (a necessary sufficient cause of all), a rival of STMT-SOME-ACTUAL-CONTINGENT. |
| B | `SIMPLICITY-ROOT-EXPOSURE` | `STMT-SIMPLICITY-ROOT-EXPOSURE` | #555 exposure of STMT-GOD-IS-IMMUTABLE (on the root path) to collapse of the root's respects, through the OPEN unattributed bridge ModalCapacity. Rival: collapse of divine decrees. Not refuted: it is the objection, not its answer; recording it as an attack needs a decree vocabulary on the route. |
| B | `FINITE-HITTING` | `STMT-FINITE-HITTING-PACKAGE` | #561 rival 'no necessary individual' (STMT-FINITE-HITTING-NO-NECESSARY): finite hitting plus absence amalgamation force a fixed necessary individual; the cores certify the incompatible bundles. Blocker: its population vocabulary (StageOne.NecessaryIndividual) has no bridge to the route's Profile/Ontic, and a contradictory core forces rejection of some member, not of the rival. |
| B | `FINITE-HITTING-CORE` | `STMT-CONFIGURATION-FALSE` | #561 rival 'no necessary individual' (STMT-FINITE-HITTING-NO-NECESSARY): finite hitting plus absence amalgamation force a fixed necessary individual; the cores certify the incompatible bundles. Blocker: its population vocabulary (StageOne.NecessaryIndividual) has no bridge to the route's Profile/Ontic, and a contradictory core forces rejection of some member, not of the rival. |
| B | `FINITE-HITTING-FINITE-WORLD-CORE` | `STMT-CONFIGURATION-FALSE` | #561 rival 'no necessary individual' (STMT-FINITE-HITTING-NO-NECESSARY): finite hitting plus absence amalgamation force a fixed necessary individual; the cores certify the incompatible bundles. Blocker: its population vocabulary (StageOne.NecessaryIndividual) has no bridge to the route's Profile/Ontic, and a contradictory core forces rejection of some member, not of the rival. |
| B | `POPULATION-EXACT-IMPLIES-AMALGAMATION` | `STMT-POPULATION-EXACT-IMPLIES-AMALGAMATION` | #561 rival 'no necessary individual' (STMT-FINITE-HITTING-NO-NECESSARY): finite hitting plus absence amalgamation force a fixed necessary individual; the cores certify the incompatible bundles. Blocker: its population vocabulary (StageOne.NecessaryIndividual) has no bridge to the route's Profile/Ontic, and a contradictory core forces rejection of some member, not of the rival. |
| B | `SIMPLICITY-BRANCH-COSTS` | `STMT-SIMPLICITY-BRANCH-COSTS` | #755 cost table of the three ways out of the collapse trilemma for an admitted reason. Constrains PSR-strength rivals; opposes no root premise. |
| B | `MODAL-B-LANGUAGE-PROPAGATION` | `STMT-MODAL-B-LANGUAGE-PROPAGATION` | Frame law for the rival modal collapse (Hume/Spinoza necessitarianism: every truth at the root world is necessary). Constrains which frame class lets possible collapse propagate to actual collapse. Opposes no root premise yet: the route never asserts an actual contingent being, so a refutation needs a contingency witness on the route (blocker). |
| B | `MODAL-B-LAWS` | `STMT-MODAL-B-LAWS` | Frame law for the rival modal collapse (Hume/Spinoza necessitarianism: every truth at the root world is necessary). Constrains which frame class lets possible collapse propagate to actual collapse. The contingency node now exists. Now applied by NO-POSS-COLLAPSE-KTB (KTB reading), which refutes STMT-ROUTE-POSS-COLLAPSED, a rival of STMT-SOME-ACTUAL-CONTINGENT. |
| B | `MODAL-B-NECESSARY-SYMMETRY` | `STMT-MODAL-B-NECESSARY-SYMMETRY` | Frame law for the rival modal collapse (Hume/Spinoza necessitarianism: every truth at the root world is necessary). Constrains which frame class lets possible collapse propagate to actual collapse. Opposes no root premise yet: the route never asserts an actual contingent being, so a refutation needs a contingency witness on the route (blocker). |
| B | `MODAL-D-LAWS` | `STMT-MODAL-D-LAWS` | Frame law for the rival modal collapse (Hume/Spinoza necessitarianism: every truth at the root world is necessary). Constrains which frame class lets possible collapse propagate to actual collapse. Opposes no root premise yet: the route never asserts an actual contingent being, so a refutation needs a contingency witness on the route (blocker). |
| B | `MODAL-K-LAWS` | `STMT-MODAL-K-LAWS` | Frame law for the rival modal collapse (Hume/Spinoza necessitarianism: every truth at the root world is necessary). Constrains which frame class lets possible collapse propagate to actual collapse. The contingency node now exists. Now applied by NO-COLLAPSE-K, which refutes STMT-ROUTE-COLLAPSED, a rival of the root-path node STMT-SOME-ACTUAL-CONTINGENT (see the follow-up section). |
| B | `MODAL-S4-LAWS` | `STMT-MODAL-S4-LAWS` | Frame law for the rival modal collapse (Hume/Spinoza necessitarianism: every truth at the root world is necessary). Constrains which frame class lets possible collapse propagate to actual collapse. Opposes no root premise yet: the route never asserts an actual contingent being, so a refutation needs a contingency witness on the route (blocker). |
| B | `MODAL-S5-LANGUAGE` | `STMT-MODAL-S5-LANGUAGE` | Frame law for the rival modal collapse (Hume/Spinoza necessitarianism: every truth at the root world is necessary). Constrains which frame class lets possible collapse propagate to actual collapse. Opposes no root premise yet: the route never asserts an actual contingent being, so a refutation needs a contingency witness on the route (blocker). |
| B | `MODAL-S5-LAWS` | `STMT-MODAL-S5-LAWS` | Frame law for the rival modal collapse (Hume/Spinoza necessitarianism: every truth at the root world is necessary). Constrains which frame class lets possible collapse propagate to actual collapse. The contingency node now exists. Now applied by NO-POSS-COLLAPSE-S5 (S5 reading), which refutes STMT-ROUTE-POSS-COLLAPSED, a rival of STMT-SOME-ACTUAL-CONTINGENT. |
| B | `MODAL-T-LAWS` | `STMT-MODAL-T-LAWS` | Frame law for the rival modal collapse (Hume/Spinoza necessitarianism: every truth at the root world is necessary). Constrains which frame class lets possible collapse propagate to actual collapse. The contingency node now exists. Now applied by NO-NEC-COLLAPSE-T (KT reading), which refutes STMT-ROUTE-NEC-COLLAPSED, a rival of STMT-SOME-ACTUAL-CONTINGENT. |
| B | `MODAL-S5-COLLAPSE-CONCEPTION-EXCLUDED` | `STMT-MODAL-S5-COLLAPSE-CONCEPTION-EXCLUDED` | Hume's conceivability route to collapse (#274): rejects a conceived collapse only given S5, an unrestricted conceivability bridge and independent contingency. Same blocker as the collapse laws: no root-route contingency premise to oppose. |
| B | `OPTIMAL-CREATION-CHOICE` | `STMT-OPTIMAL-CREATION-CHOICE` | Leibnizian optimal-creation necessitarianism (#462 family): optimal output plus at most one optimal candidate fixes the selected output. Constrains the rival that God must create the best; opposes no root premise. |
| B | `NECESSARY-POTENTIAL-CAUSERS-NOT-DISTINCT` | `STMT-NO-DISTINCT-NECESSARY-POTENTIAL-CAUSERS` | Modal ditheism: two distinct necessary universal potential causers cannot be distinct. Refutes STMT-MODAL-DITHEISM (REL-NO-DISTINCT-CAUSERS-REFUTES-DITHEISM). Does not count: STMT-ACTUAL-MODAL-REFLEXIVITY and STMT-WELL-FOUNDED-UNION-NECESSARY-SUPPORT are OPEN. Not alternative_to a root premise: the route's uniqueness is God-uniqueness and no bridge identifies such causers with God. |
| B | `ACTUALIST-DOMAIN-CORRESPONDENCE` | `STMT-ACTUALIST-DOMAIN-CORRESPONDENCE` | Necessitism / Barcan: box-forall to forall-box holds exactly on increasing domains, the converse on decreasing domains. Constrains the actualist-domain rivals of the actualist K sense. Blocker: no route premise fixes the domain policy of the route frame. |
| B | `LIMITATION-NONLIMITING-POSSIBILITY` | `STMT-LIMITATION-POSSIBLY-EXEMPLIFIED-AT` | Scott/Goedel A1a separation (#134): the limitation classifier and the possibility of a nonlimiting target. Constrains the essence-based senses left out of the fork (NECESSARY_6, NECESSARY_7), i.e. the rival readings that attack STMT-NECESSARY-SENSES-EXHAUSTIVE. Not refuted. |
| B | `LIMITATION-POSSIBILITY-SCOTT-SEPARATION-CONTROL` | `STMT-LIMITATION-POSSIBILITY-SCOTT-SEPARATION-CONTROL` | Scott/Goedel A1a separation (#134): the limitation classifier and the possibility of a nonlimiting target. Constrains the essence-based senses left out of the fork (NECESSARY_6, NECESSARY_7), i.e. the rival readings that attack STMT-NECESSARY-SENSES-EXHAUSTIVE. Not refuted. |
| B | `LIMITATION-SEPARATION` | `STMT-LIMITATION-SEPARATION-WITNESS` | Scott/Goedel A1a separation (#134): the limitation classifier and the possibility of a nonlimiting target. Constrains the essence-based senses left out of the fork (NECESSARY_6, NECESSARY_7), i.e. the rival readings that attack STMT-NECESSARY-SENSES-EXHAUSTIVE. Not refuted. |
| A-deferred | `MODAL-DEGREE-ATTAINED-FROM-NAMED` (instantiation) | `STMT-MODAL-DEGREE-ATTAINED-GLOBAL-MAXIMUM` | Degrees of being across worlds (Koons steps 6, 7, 11): a necessary individual whose degree bounds every accessible degree. Target: STMT-GOD-IS-MAXIMAL-IN-BEING. Missing bridge: the route's MoreIn/esse comparison is not the world-indexed Preorder degree; one bridge statement plus the OPEN STMT-MODAL-DEGREE-* premises. Not connected in this batch. |
| A-deferred | `MODAL-DEGREE-GLOBAL-ATTAINMENT-IFF-SELECTED-FAMILY` | `STMT-MODAL-DEGREE-GLOBAL-ATTAINMENT-IFF-SELECTED-FAMILY` | Degrees of being across worlds (Koons steps 6, 7, 11): a necessary individual whose degree bounds every accessible degree. Target: STMT-GOD-IS-MAXIMAL-IN-BEING. Missing bridge: the route's MoreIn/esse comparison is not the world-indexed Preorder degree; one bridge statement plus the OPEN STMT-MODAL-DEGREE-* premises. Not connected in this batch. |
| A-deferred | `MODAL-DEGREE-GLOBAL-MAXIMUM-FROM-ACTUAL-INVARIANCE` (assembly) | `STMT-MODAL-DEGREE-NECESSARY-GLOBAL-MAXIMUM` | Degrees of being across worlds (Koons steps 6, 7, 11): a necessary individual whose degree bounds every accessible degree. Target: STMT-GOD-IS-MAXIMAL-IN-BEING. Missing bridge: the route's MoreIn/esse comparison is not the world-indexed Preorder degree; one bridge statement plus the OPEN STMT-MODAL-DEGREE-* premises. Not connected in this batch. |
| A-deferred | `MODAL-DEGREE-NECESSARY-GLOBAL-MAXIMUM` | `STMT-MODAL-DEGREE-NECESSARY-GLOBAL-MAXIMUM` | Degrees of being across worlds (Koons steps 6, 7, 11): a necessary individual whose degree bounds every accessible degree. Target: STMT-GOD-IS-MAXIMAL-IN-BEING. Missing bridge: the route's MoreIn/esse comparison is not the world-indexed Preorder degree; one bridge statement plus the OPEN STMT-MODAL-DEGREE-* premises. Not connected in this batch. |
| A-deferred | `MODAL-RIGID-DESIGNATION` | `STMT-MODAL-RIGID-DESIGNATION` | Rigid designation of a necessary bearer: strict necessary co-reference iff the bearer exists at every successor. Target: an a-posteriori identity route to box-existence (God = the first being, necessarily). Missing: a rigid-name vocabulary for 'God' on the route (STMT-GOD-NAMES-THE-FULLY-DESCRIBED-PRINCIPLE is descriptive). Not connected. |
| C | `BEARER-CAPACITY-EXERCISE` | `STMT-BEARER-CAPACITY-EXERCISE` | Controls for #462/#456 (selected effect, bearer capacity, counterparts, rotating causers, unbounded degrees, measure equality): finite models showing a bundle is satisfiable or a step fails. Not meant to connect. |
| C | `COUNTERPART-NECESSITY-CONTROLS` | `STMT-COUNTERPART-NECESSITY-CONTROLS` | Controls for #462/#456 (selected effect, bearer capacity, counterparts, rotating causers, unbounded degrees, measure equality): finite models showing a bundle is satisfiable or a step fails. Not meant to connect. |
| C | `MODAL-DEGREE-UNBOUNDED-WORLD-CONTROL` | `STMT-MODAL-DEGREE-UNBOUNDED-WORLD-CONTROL` | Controls for #462/#456 (selected effect, bearer capacity, counterparts, rotating causers, unbounded degrees, measure equality): finite models showing a bundle is satisfiable or a step fails. Not meant to connect. |
| C | `NECESSARY-BEING-MEASURE-EQUALITY` | `STMT-NECESSARY-BEING-MEASURE-EQUALITY` | Controls for #462/#456 (selected effect, bearer capacity, counterparts, rotating causers, unbounded degrees, measure equality): finite models showing a bundle is satisfiable or a step fails. Not meant to connect. |
| C | `NECESSARY-IF-EXISTENT-CONTROLS` | `STMT-NECESSARY-IF-CONTROLS` | Controls for #462/#456 (selected effect, bearer capacity, counterparts, rotating causers, unbounded degrees, measure equality): finite models showing a bundle is satisfiable or a step fails. Not meant to connect. |
| C | `POPULATION-CLOSURE-SEPARATION` | `STMT-POPULATION-CLOSURE-SEPARATION` | Controls for #462/#456 (selected effect, bearer capacity, counterparts, rotating causers, unbounded degrees, measure equality): finite models showing a bundle is satisfiable or a step fails. Not meant to connect. |
| C | `SELECTED-EFFECT-BRIDGE-CERTIFICATE` | `STMT-SELECTED-EFFECT-BRIDGE-CERTIFICATE` | Controls for #462/#456 (selected effect, bearer capacity, counterparts, rotating causers, unbounded degrees, measure equality): finite models showing a bundle is satisfiable or a step fails. Not meant to connect. |
| C | `WORLDWISE-WF-ALLOWS-DISTINCT-NECESSARY-POTENTIAL-CAUSERS` | `STMT-ROTATING-NECESSARY-POTENTIAL-CAUSERS` | Controls for #462/#456 (selected effect, bearer capacity, counterparts, rotating causers, unbounded degrees, measure equality): finite models showing a bundle is satisfiable or a step fails. Not meant to connect. |
| C | `MODAL-B-COUNTERMODELS` | `STMT-MODAL-B-COUNTERMODELS` | Countermodel or scope boundary for the modal-collapse laws (finite frames separating frame classes, full-predicate vs fixed-language collapse). Controls; not meant to connect. |
| C | `MODAL-B-DISCONNECTED-SCOPE` | `STMT-MODAL-B-DISCONNECTED-SCOPE` | Countermodel or scope boundary for the modal-collapse laws (finite frames separating frame classes, full-predicate vs fixed-language collapse). Controls; not meant to connect. |
| C | `MODAL-B-SCOPE-BOUNDARY` | `STMT-MODAL-B-SCOPE-BOUNDARY` | Countermodel or scope boundary for the modal-collapse laws (finite frames separating frame classes, full-predicate vs fixed-language collapse). Controls; not meant to connect. |
| C | `MODAL-D-COUNTERMODELS` | `STMT-MODAL-D-COUNTERMODELS` | Countermodel or scope boundary for the modal-collapse laws (finite frames separating frame classes, full-predicate vs fixed-language collapse). Controls; not meant to connect. |
| C | `MODAL-D-LANGUAGE` | `STMT-MODAL-D-LANGUAGE` | Countermodel or scope boundary for the modal-collapse laws (finite frames separating frame classes, full-predicate vs fixed-language collapse). Controls; not meant to connect. |
| C | `MODAL-D-SCOPES` | `STMT-MODAL-D-SCOPES` | Countermodel or scope boundary for the modal-collapse laws (finite frames separating frame classes, full-predicate vs fixed-language collapse). Controls; not meant to connect. |
| C | `MODAL-K-COUNTERMODELS` | `STMT-MODAL-K-COUNTERMODELS` | Countermodel or scope boundary for the modal-collapse laws (finite frames separating frame classes, full-predicate vs fixed-language collapse). Controls; not meant to connect. |
| C | `MODAL-K-EXTENSIONALITY` | `STMT-MODAL-K-EXTENSIONALITY` | Countermodel or scope boundary for the modal-collapse laws (finite frames separating frame classes, full-predicate vs fixed-language collapse). Controls; not meant to connect. |
| C | `MODAL-K-SCOPE-BOUNDARY` | `STMT-MODAL-K-SCOPE-BOUNDARY` | Countermodel or scope boundary for the modal-collapse laws (finite frames separating frame classes, full-predicate vs fixed-language collapse). Controls; not meant to connect. |
| C | `MODAL-S4-COUNTERMODELS` | `STMT-MODAL-S4-COUNTERMODELS` | Countermodel or scope boundary for the modal-collapse laws (finite frames separating frame classes, full-predicate vs fixed-language collapse). Controls; not meant to connect. |
| C | `MODAL-S4-EXTENSIONALITY` | `STMT-MODAL-S4-EXTENSIONALITY` | Countermodel or scope boundary for the modal-collapse laws (finite frames separating frame classes, full-predicate vs fixed-language collapse). Controls; not meant to connect. |
| C | `MODAL-S4-SCOPE-BOUNDARY` | `STMT-MODAL-S4-SCOPE-BOUNDARY` | Countermodel or scope boundary for the modal-collapse laws (finite frames separating frame classes, full-predicate vs fixed-language collapse). Controls; not meant to connect. |
| C | `MODAL-S5-COUNTERMODELS` | `STMT-MODAL-S5-COUNTERMODELS` | Countermodel or scope boundary for the modal-collapse laws (finite frames separating frame classes, full-predicate vs fixed-language collapse). Controls; not meant to connect. |
| C | `MODAL-S5-DOMAIN-BOUNDARY` | `STMT-MODAL-S5-DOMAIN-BOUNDARY` | Countermodel or scope boundary for the modal-collapse laws (finite frames separating frame classes, full-predicate vs fixed-language collapse). Controls; not meant to connect. |
| C | `MODAL-S5-SYMMETRY-BOUNDARY` | `STMT-MODAL-S5-SYMMETRY-BOUNDARY` | Countermodel or scope boundary for the modal-collapse laws (finite frames separating frame classes, full-predicate vs fixed-language collapse). Controls; not meant to connect. |
| C | `MODAL-T-BRANCHING` | `STMT-MODAL-T-BRANCHING` | Countermodel or scope boundary for the modal-collapse laws (finite frames separating frame classes, full-predicate vs fixed-language collapse). Controls; not meant to connect. |
| C | `MODAL-T-FRAME-BOUNDARY` | `STMT-MODAL-T-FRAME-BOUNDARY` | Countermodel or scope boundary for the modal-collapse laws (finite frames separating frame classes, full-predicate vs fixed-language collapse). Controls; not meant to connect. |
| C | `MODAL-T-SCOPE-BOUNDARY` | `STMT-MODAL-T-SCOPE-BOUNDARY` | Countermodel or scope boundary for the modal-collapse laws (finite frames separating frame classes, full-predicate vs fixed-language collapse). Controls; not meant to connect. |
| C | `CHOICE-CONTEXT-CONTROLS` | `STMT-CHOICE-CONTEXT-CONTROLS` | Free-choice decision-table controls (Carneades choice context): stipulative, not a free-will theory. |
| C | `REASON-RESPONSE-HISTORY` | `STMT-REASON-RESPONSE-HISTORY` | Free-choice decision-table controls (Carneades choice context): stipulative, not a free-will theory. |
| C | `ACCESSIBILITY-COMPONENTS` | `STMT-ACCESSIBILITY-COMPONENTS` | Mathematical infrastructure (fixture laws, graph/quiver bridges, accessibility components, possibility transfer between frames, designated validity). Used by other modal results; no philosophical conclusion to connect. |
| C | `DESIGNATED-NECESSITATION-CERTIFICATE` | `STMT-DESIGNATED-NECESSITATION-CERTIFICATE` | Mathematical infrastructure (fixture laws, graph/quiver bridges, accessibility components, possibility transfer between frames, designated validity). Used by other modal results; no philosophical conclusion to connect. |
| C | `MODAL-FIXTURE-CHECKS` | `STMT-MODAL-FIXTURE-CHECKS` | Mathematical infrastructure (fixture laws, graph/quiver bridges, accessibility components, possibility transfer between frames, designated validity). Used by other modal results; no philosophical conclusion to connect. |
| C | `MODAL-GRAPH-BRIDGE-CERTIFICATE` (assembly) | `STMT-MODAL-GRAPH-BRIDGE-CERTIFICATE` | Mathematical infrastructure (fixture laws, graph/quiver bridges, accessibility components, possibility transfer between frames, designated validity). Used by other modal results; no philosophical conclusion to connect. |
| C | `MODAL-POSSIBILITY-TRANSFER` | `STMT-MODAL-POSSIBILITY-TRANSFER` | Mathematical infrastructure (fixture laws, graph/quiver bridges, accessibility components, possibility transfer between frames, designated validity). Used by other modal results; no philosophical conclusion to connect. |
| C | `BOUNDED-METRIC-PAST-CONTROL` | `STMT-BOUNDED-METRIC-PAST-CONTROL` | Oppy fixed-history and temporal controls (#535, #440): histories, time scope, contrastive explanation, bounded/serial past. Controls for the naturalist fixed-history rival; the rival's positive statement is not yet on a root path. |
| C | `HISTORY-CONTRASTIVE-CONTROLS` | `STMT-HISTORY-CONTRASTIVE-CONTROLS` | Oppy fixed-history and temporal controls (#535, #440): histories, time scope, contrastive explanation, bounded/serial past. Controls for the naturalist fixed-history rival; the rival's positive statement is not yet on a root path. |
| C | `HISTORY-TIME-SCOPE-CONTROLS` | `STMT-HISTORY-TIME-SCOPE-CONTROLS` | Oppy fixed-history and temporal controls (#535, #440): histories, time scope, contrastive explanation, bounded/serial past. Controls for the naturalist fixed-history rival; the rival's positive statement is not yet on a root path. |
| C | `PAST-SERIALITY-CORRESPONDENCE` | `STMT-PAST-SERIALITY-CORRESPONDENCE` | Oppy fixed-history and temporal controls (#535, #440): histories, time scope, contrastive explanation, bounded/serial past. Controls for the naturalist fixed-history rival; the rival's positive statement is not yet on a root path. |
| C | `TEMPORAL-MODAL-DEPENDENCE-CONTROLS` | `STMT-TEMPORAL-MODAL-DEPENDENCE-CONTROLS` | Oppy fixed-history and temporal controls (#535, #440): histories, time scope, contrastive explanation, bounded/serial past. Controls for the naturalist fixed-history rival; the rival's positive statement is not yet on a root path. |
| C | `ACTUAL-REASON-WITNESS-CERTIFICATE` | `STMT-ACTUAL-REASON-WITNESS-CERTIFICATE` | PSR witness and counterpossible controls: an actual-reason anchor and conservativity of a counterpossible clamp. Controls for the PSR/explanation family (TruthCore.Explanation), not for a root step. |
| C | `COUNTERPOSSIBLE-CONSERVATIVITY` | `STMT-COUNTERPOSSIBLE-CONSERVATIVITY` | PSR witness and counterpossible controls: an actual-reason anchor and conservativity of a counterpossible clamp. Controls for the PSR/explanation family (TruthCore.Explanation), not for a root step. |
| D | `DEONTIC-FUTURE-BOUNDARY` | `STMT-DEONTIC-FUTURE-BOUNDARY` | Off-case: ought-implies-can and retained duties (Carneades deontology). Deontic modality over plans; no node of the Catholicism case uses it. A connection would need a moral-argument route that the case does not have. |
| D | `RETAINED-DUTY-BRANCH-CONTROLS` | `STMT-RETAINED-DUTY-BRANCH-CONTROLS` | Off-case: ought-implies-can and retained duties (Carneades deontology). Deontic modality over plans; no node of the Catholicism case uses it. A connection would need a moral-argument route that the case does not have. |
| D | `RETAINED-DUTY-CONTROLS` | `STMT-RETAINED-DUTY-CONTROLS` | Off-case: ought-implies-can and retained duties (Carneades deontology). Deontic modality over plans; no node of the Catholicism case uses it. A connection would need a moral-argument route that the case does not have. |
| D | `RETAINED-DUTY-DIRECT-CORE` | `STMT-CONFIGURATION-FALSE` | Off-case: ought-implies-can and retained duties (Carneades deontology). Deontic modality over plans; no node of the Catholicism case uses it. A connection would need a moral-argument route that the case does not have. |
| D | `RETAINED-DUTY-LOCAL-CONTROLS` | `STMT-RETAINED-DUTY-LOCAL-CONTROLS` | Off-case: ought-implies-can and retained duties (Carneades deontology). Deontic modality over plans; no node of the Catholicism case uses it. A connection would need a moral-argument route that the case does not have. |
| D | `RETAINED-DUTY-LOCAL-DIRECT-CORE` | `STMT-CONFIGURATION-FALSE` | Off-case: ought-implies-can and retained duties (Carneades deontology). Deontic modality over plans; no node of the Catholicism case uses it. A connection would need a moral-argument route that the case does not have. |
| D | `RETAINED-DUTY-LOCAL-TEMPORAL-CORE` | `STMT-CONFIGURATION-FALSE` | Off-case: ought-implies-can and retained duties (Carneades deontology). Deontic modality over plans; no node of the Catholicism case uses it. A connection would need a moral-argument route that the case does not have. |
| D | `RETAINED-DUTY-TEMPORAL-CORE` | `STMT-CONFIGURATION-FALSE` | Off-case: ought-implies-can and retained duties (Carneades deontology). Deontic modality over plans; no node of the Catholicism case uses it. A connection would need a moral-argument route that the case does not have. |
| D | `RETAINED-DUTY-TRANSFER` (single_application) | `STMT-RETAINED-DUTY-PRESENT-DUTY` | Off-case: ought-implies-can and retained duties (Carneades deontology). Deontic modality over plans; no node of the Catholicism case uses it. A connection would need a moral-argument route that the case does not have. |
| D | `RETAINED-DUTY-UNIVERSAL-TO-LOCAL` (single_application) | `STMT-RETAINED-DUTY-LOCAL-OIC` | Off-case: ought-implies-can and retained duties (Carneades deontology). Deontic modality over plans; no node of the Catholicism case uses it. A connection would need a moral-argument route that the case does not have. |

### Current-main reconciliation of #1241 (2026-11-08)

The old frozen Challenge is retained unchanged. Five revised interfaces in
`TruthCore/Results/Causality/ContingentBeingNodeReconciled/` consume the existing
closed K/T/B/S5 and correspondence theorems directly. Only the contingency node
and applicable T/B/5 schemas remain hypotheses; the original law bundles are
no longer philosophical assumptions. Their unused definitions previously
triggered current-main sense mixing. The T/B schema premises explicitly bind
the fixture frame (NECESSARY_11) to the route's individual box-existence
(NECESSARY_2), recorded as sense bridges; no different metaphysical necessity
is inferred. The original controls still witness the omission and nonvacuity
claims. This revision does not establish the node, any schema, or God's existence.

Claim/type self-sweep: revised K and strict-act results each assume only the
node; T assumes T plus node; B assumes B plus node; S5 assumes T, 5 plus node.
Conclusions and carriers are unchanged. Imported closed certificates supply
all omitted mathematical hypotheses. Their approved Mathlib dependencies are
now visible in the revised closed terms (permitted axioms: propext,
Classical.choice, Quot.sound); the initial zero-axiom Comparator correctly
rejected propext before this policy correction. The fixed Challenge is generated before
proof completion; the original Challenge is not weakened. All five revised
interfaces build and bind (5 bound, 0 mismatch); final Comparator/NanoDa and CI
are required before merge. Specs are split by original/reconciled interfaces.
