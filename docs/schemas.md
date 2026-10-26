# Proved argument schemas

Issue #412's regress schema is mathematical structure shared by distinct
interpretations. The certified proposition is
`TruthCore.Results.Logic.RegressSchema.regressSchemaPackage`, concluding
`TruthCore.Logic.RegressDomains.DomainPackage` in
[REGRESS-SCHEMA-PACKAGE](../corpus/results/REGRESS-SCHEMA-PACKAGE.json).
Its frozen Challenge, Solution, Comparator configuration and NanoDa check cover
**every conjunct**, including the six transfers below. A conditional transfer
is the registered instance; actual well-foundedness of a philosophical domain
is not registered as proved.

The corpus uses **`instance_of_schema`**, a statement-to-statement registration
relation with explicit verification evidence. Each instance points to
`STMT-REGRESS-STRUCTURAL-SCHEMA` and names the shared verification result plus
its separate instance theorem and schema theorem. These exact theorem
obligations have frozen Challenges and are listed in the Comparator config;
`bind-check` matches both proof types to their statement declarations and
rejects additional proposition hypotheses. The verified package also contains
every transfer as a conjunct. This avoids duplicated result records while
checking each advertised instance separately. Registration is neither source
support nor an inference from an instance to the universal schema; it changes
no premise-closure rule. Metadata alone is not proof verification.

## Regress and well-foundedness

`Logic/Regress.lean` defines `Graph.edge y x` from upstream relatum to dependent.
`Source` means no incoming upstream edge; `Terminal` means no outgoing downstream
edge. Neither means temporal beginning/end or global independence. `Controls`
combines exclusion of every nonempty finite cycle, exclusion of every
Nat-indexed descending series, and a finite path from each node to **some**
relative source. The endpoint may depend on the node, and the path may have
length zero. This is not a uniform depth bound (reuse #392's unbounded-depth
control), uniqueness, or existence of God.

An edge-preserving `Graph.Map` pulls accessibility back, including between
different carriers. The source-path result uses classical logic; #392's
constructive accessibility-to-no-series theorem is imported rather than
reproved. The classical converse from absence of descending series remains
available in the existing `REGRESS-READINGS-COINCIDE-CLASSICALLY` result.

| Proved instance statement | Separate domain data and retained conditions | Transferred conclusion in the certified package |
| --- | --- | --- |
| `STMT-REGRESS-EFFICIENT-TRANSFER` | `CausesAsCaused`; #433's finite distinct **transitive** causal ancestry, no finite causal loops, same-carrier per se edge inclusion | All `Controls` for the per se efficient graph; imports #433's actual finite-history proof |
| `STMT-REGRESS-MOTION-TRANSFER` | Existing typed `MoverMovedByAnotherLink`; III.3 moving-in-the-moved, second-movers bridge, First Way accessibility | All `Controls` for the physical mover graph; imports the existing typed motion transfer |
| `STMT-REGRESS-GROUNDING-TRANSFER` | Existing `ParticipationGrounding.Explanation.Grounds` on tagged facts; every fact finitely grounded, sources receive no links, at most one immediate ground | All `Controls`; reuses #392's finite-grounding/unique-predecessor proof, without asserting #348's strict-ground calculus is implemented |
| `STMT-REGRESS-EXPLANATION-TRANSFER` | Existing PSR `Reason` and `ExistenceFact` remain different types; separately supplied `requires` records a reason's antecedent existence facts; each projected edge decreases an independently supplied well-founded rank | All `Controls` for the reason-antecedent projection, through an explicitly constructed edge-preserving map |
| `STMT-REGRESS-PARTHOOD-TRANSFER` | Strict order in a supplied `PartialOrder`, interpreted as proper parthood; strict parthood is assumed well-founded | All `Controls`, including a path to a relative atom; no fusion, supplementation or actual atomism follows |
| `STMT-REGRESS-JUSTIFICATION-TRANSFER` | Separate claims and rule tokens; each rule records its entire premise set and conclusion; all-premise inductive `GeneratedWarrant`; every inferential rule is nonempty | Every generated warrant has a finite branch to a noninferential foundation; this is a necessary condition, not sufficient warrant, epistemic justification, knowledge, or well-foundedness of unused inferential edges |

The explanatory projection adds real data: PSR alone never supplies the
`requires` relation, rank or rank-decrease law. Simply placing reasons and
facts on two levels would manufacture a shallow graph and establish nothing
about explanatory regress. Here a fact can explain another through a reason
which requires it, repeatedly; the independent rank condition does the work.

The warrant proof inducts over **all premises** of each inference. A projected
premise edge alone cannot warrant its conclusion. Nonempty rules are explicit
because an empty-premise inferential rule would otherwise terminate without
the specified noninferential foundation. Inference rules with infinitely many
premises are permitted; the proposition extracts one finite branch and does
not claim a uniform finite bound or a finite total derivation tree. The
`AllPremiseBoundary` control has a finite branch to a foundation but no warrant:
its rule also requires an unsupported premise. Thus the branch condition
cannot replace the full inference semantics.

## Least and greatest fixed points

The shared `transmission` operator is Mathlib's order homomorphism on sets:

`Φ(S) = intrinsic ∪ {x | ∃ y, edge y x ∧ y ∈ S}`.

`grounded_eq_lfp` identifies its least fixed point with the **existing**
`FinitelyGroundedPower`. `fixedPoints_equal_of_wellFounded` proves `lfp = gfp`
under accessibility, for every intrinsic predicate. These are the structural
parts of #339, not a determination of which fixed point real per se power
occupies. The package also disproves the converse without further restrictions:
a self-loop with every node intrinsic has equal total fixed points but is not
well-founded. No claim about all non-well-founded relations is made.

The source-free successor chain has every node active in its greatest fixed
point, but no node in its least fixed point. It reuses
`SuccessorBorrowingLink`, `PowerTransmissionRule`, and finite-grounding source
extraction. This gives a precise semantic choice rather than inferring that
local transmission equations select one global solution.

## Agrippa/Münchhausen boundary and skeptical response

The certified `CrossDomainBoundary` assigns the **same successor graph** to
causal transmission and inferential rules. Every node is stipulated existent
and locally active; every justification is withheld, and no all-premise
`GeneratedWarrant` can be derived because there is no foundation. Thus local
causal activity and absent foundationalist warrant are jointly satisfiable.
This is a logical model of a restricted signature, not evidence that an
actual source-free physical universe is metaphysically possible. It proves no
law about actual causal power or existence.

The strongest response is principled separation: inferential warrant may
require a noninferential basis while successive causes satisfy local physical
conditions, or a holistic/infinitist epistemology may reject the chosen
foundationalist standard altogether. The present model leaves these answers
available. Rejecting an infinite justification regress therefore yields no
automatic inconsistency verdict against accepting a causal regress.

`EpistemicBridge` makes one sufficient bridge precise: supply an
edge-preserving map from the causal graph into a justificatory graph **and**
well-foundedness of that justificatory graph. Accessibility then transfers.
Edge preservation is the minimal mapping condition used by this proof; it is
not claimed necessary for every possible argument. Neither the map nor global
epistemic well-foundedness follows from a failed warrant derivation, and this
PR provides no independent defense of either. In particular, the warrant
transfer gives a finite branch, not accessibility of the whole graph. The
remaining epistemic-frontier obligation is to defend an actual justificatory
standard and a source-faithful bridge to all-borrowed **per se** power or
explanation. Infinite **temporal** causal history remains a different relation
unless a further bridge is supplied.

The existing self-application schema tests a philosopher's positive claim to
**know** that infinite causal dependence is possible. `KnowledgeSelfApplication`
retains scope, the philosopher's own justification standard, and failure to
meet that standard as explicit hypotheses. It then derives both horns of the
existing dilemma. Suspended judgment supplies no positive knowledge claim and
no proof of either causal possibility or impossibility. This is an analyst's
norm test; no claim here is attributed to Sextus or Agrippa, so no uninspected
primary witness is being passed off as evidence.

Two further controls discriminate shape from semantics. A singleton cycle has
no injective infinite sequence but is not accessible; reversed natural-number
strict parthood is transitive, irreflexive and atomless but not well-founded.
Under parts-priority its descent violates accessibility. The theorem does not
choose parts-priority over whole-priority or declare atomless mereology
contradictory.

## Premise comparison and remaining scope

Intended and actual root-path premise change: **none**. These universally
quantified structural conditionals and countermodels do not establish the
antecedents of any actual causal, grounding, explanatory, mereological or
epistemic interpretation. No new source claims, axioms or dependencies are
added. Mathlib results permit the existing standard classical axioms
`propext`, `Classical.choice`, and `Quot.sound`; no constructive reading of the
classical source-extraction or fixed-point package is advertised.

Issue #412 stays open for participation and composition/uniting-cause schemas. The self-application schema remains in
`Logic/SelfApplication.lean`. Issues #336, #339 and #348 retain their remaining
source, semantic, and campaign obligations; this package does not declare
those campaigns complete.

## Maximum in an order

Schema 2 is `STMT-MAXIMUM-ORDER-SCHEMA`, certified by
`TruthCore.Results.Logic.MaximumOrderSchema.maximumOrderSchema` in
[MAXIMUM-ORDER-SCHEMA](../corpus/results/MAXIMUM-ORDER-SCHEMA.json).
A `System` keeps its cause-of-degree relation separate from the Mathlib
preorder. Under the explicit condition that each distinct cause is strictly
higher than its effect, a maximal member has no distinct cause of that same
degree. `IsMax` means maximal, not greatest. Existence, uniqueness, causing all
other members and identity with God are not part of the conclusion.

| Proved instance statement | Retained conditional inputs | Transferred conclusion |
| --- | --- | --- |
| `STMT-FOURTH-WAY-MAXIMUM-SCHEMA-INSTANCES` | For each named respect being (`esse`), goodness (`bonum`) and ontological truth (`verum`): homogeneous-scale representation and unrestricted cause-more-such | A maximum has no distinct cause of the same perfection; the three respects and their maxima are not identified |
| `STMT-ATTRIBUTION-MAXIMUM-SCHEMA-INSTANCE` | Approach-to-primary representation, additional universal possession of the perfection, unrestricted cause-more-such | The same exclusion, via #386's exact `homogeneousLift` and `isMaximumIn_iff_isMax` theorems on the preorder pulled back from degrees of approach |

Both statement-to-statement `instance_of_schema` registrations name separate
instance and schema theorems checked by the same seven-theorem Comparator
configuration and solution NanoDa. All philosophical conditions remain inside
the conditional statements. Registration does not defend them. In particular,
the unrestricted cause-more-such condition retains its existing open extension
beyond Aristotle's synonymous-quality formulation; the attribution reading
does not establish it for secondary causes.

The package checks four discriminating controls: Nat has no maximal member;
two distinct beings tied at one Unit degree are both maximal; ordered Bool
with empty causation has a greatest member and strict causal ascent but no
causing of its lower member; without ascent a lower member can cause the
maximum. Thus the maximum-causes-all converse cannot be inferred from this
schema. The strongest skeptical reply accepts the conditional mathematics but
withholds the homogeneous representation or causal ascent, especially for
virtual/analogical causality. Those philosophical questions remain open.

Intended and actual root-path premise delta: **none**. No root route changes,
no new source attribution, and no premise discharge. The attribution transfer
needs universal possession beyond the approach reading; strict primacy,
creature coverage and the primary's causal clause are omitted because this
conclusion differs from #386's genus-principle derivation, not because those
conditions were refuted. See [maximum-order-schema.md](maximum-order-schema.md)
for the exact proof composition, controls, premise comparison and source limits.
