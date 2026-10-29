# Infinite greatest wholes and the Fourth Way (#696)

The question is whether a greatest whole may be infinite, and whether its
order position supplies the causal or explanatory priority needed by the
Fourth Way. `INFINITE-GREATEST-WHOLE-CONTROL` gives a precise new control and
imports the established finite-top/Nat-ascent witnesses. It neither proves
the Fourth Way nor establishes the actuality of an infinite physical space.

## One geometry, two different orders

`Point := Fin 3 → ℝ`; `Region := Set Point`; `whole := Set.univ`. The order on
regions is ordinary inclusion. Every region is included in whole, so whole is
**greatest** (`IsGreatest`), not merely maximal. Both the whole's point-set and
the family of all regions are infinite: constant points inject ℝ into the
whole, and their singleton sets inject ℝ into the family. The family of regions
is order-bounded above by whole.

The separate coordinate set is `(fun p => p 0) '' whole`. It has no upper bound
in the real order: for any proposed bound a the constant point a+1 refutes it.
Thus the greatest region has unbounded first-coordinate extent, although the
inclusion order on regions has a top and is bounded. These are different
orders on different carriers. No norm-unboundedness, Euclidean metric,
topological boundary, absence of an edge, spatial travel or actual cosmology
is certified. The first-coordinate result is sufficient for the limited
extensive-infinity example; it is not unrestricted intensive perfection.
Every region whose first-coordinate image is bounded above is distinct from
the whole. This is not a formal assertion that all proper regions are bounded.

The same region structure has `inAct s () := True` and `moreIn () s t := t ⊂ s`
as an explicit **contrast** homogeneous scale. The Unit respect here means
membership in this mathematical comparison domain, not esse, goodness or
truth. Empty priority (`False`) supplies no efficient-cause, grounding or
explanatory edges. Whole remains greatest/maximal but is not a cause of the
proper region `{origin}`; the genus-at-being-shaped universal implication
fails on this interpretation. One may interpret the omitted priority as any
of those relations for the logical non-entailment test, but the empty graph is
not a physically complete universe or a proof that real space lacks grounds.
No existence of an actually instantiated region is inferred from a Lean type.

An ordinary near miss is a geographical whole containing a town: inclusion
alone supplies neither the town's production nor its continued existence.
A container may maintain an object's location without producing that object;
these are different questions and senses of dependence. A whole-system account
could instead propose constitutive or global constraints on its parts. Such
an account adds interpreted explanatory structure, not just a larger set.
The formal empty-priority control does not refute that richer account.

## Four configurations, with exact reuse

| Configuration | Certificate | What it does not give |
| --- | --- | --- |
| Finite highest degree | Imported unchanged `QuartaViaDegreeFork.FiniteTop.JointWitness` on the prior Bool causal model | Its maximum is not a proof that every real perfection has a maximum. |
| Bounded but unattained supremum | `(0,1)` in ℝ has `IsLUB` 1, excludes 1, is bounded above, and every member is exceeded by its midpoint with 1 | A least upper bound need not belong to the domain; no-maximal does not mean metric-unbounded. |
| Unbounded ascent/no maximum | Imported unchanged `QuartaViaDegreeFork.Unbounded.JointWitness` on Nat, including no causal edges and no strict causal top | Degree ascent is not causal regress; its genus implication is vacuous because no maximum exists. |
| Infinite greatest whole | All regions of the three-coordinate real point-set, with whole greatest and its coordinate extent unbounded | Inclusion or extensive infinity does not supply efficient causation, grounding or intensive perfection. |

The existing Bool/Nat full-background proofs are applied by
`QuartaViaDegreeFork.branchWitnesses`, not recreated. The new region control
**does not** satisfy that full causal background: it deliberately violates the
genus principle while retaining genuine greatestness in the model and the homogeneous
representation. It is not a third witness to all premises of the old fork.

A further selected-family control uses two disjoint singleton regions of the
same point space. Each is Mathlib `Maximal` **within that two-member family**;
neither is `IsGreatest` there, because the other singleton is not a subset.
They are incomparable, unlike the old tied-degree preorder in which distinct
members are both greatest. No claim makes those singletons maximal among all
regions.

## Vocabulary audit and compatibility

`IsMaximumIn` always meant possession plus no strictly higher member; it never
asserted comparison with every other member. The existing
`HomogeneousScaleReading.isMaximumIn_iff_isMax` already states the exact
Mathlib meaning. The canonical spelling `IsMaximalIn` now exposes that body,
while `IsMaximumIn` remains a definitionally equal compatibility name. Existing
source claims, statement IDs, conclusions and frozen Challenges keep their
original interpretation and public name. Nothing is strengthened to greatestness.

`QuartaViaUnboundedDegrees` always meant `∀ x, ∃ y, MoreIn esse y x`. Its new
canonical spelling `QuartaViaNoMaximalDegree` makes that quantifier visible;
the old spelling is definitionally equal. The bounded open interval satisfies
it, whereas the infinite greatest region does not. Existing comments claiming
only a strict extension/no-top horn remain correct. The new aliases add no
order assumptions, no global totality/comparability and no population premise.
The raw `MoreIn` parameter alone carries no irreflexivity, transitivity or
other order laws; comparison with Mathlib maximality uses the existing
`HomogeneousScaleReading` representation. The new region/interval fixtures
supply their standard mathematical orders explicitly.
The original model's Nat order is genuinely unbounded, but that special fact
is not the generic predicate's meaning. No imported theorem type changed.

## Primary-source audit and the non-circular causal proposal

The following complete pinned witnesses were materialized and read before
this analysis; no new historical claim or source manifest is introduced.

- **Aristotle, Metaphysics II.1, 993b24–31** (`ARIST-MET-II-1`): the clause from
  `ἕκαστον δὲ μάλιστα` concerns what makes the **synonymous** quality belong to
  others; fire/heat is the example, followed by the truth of eternal principles.
  Its direction is cause → most such. It does not license the converse from a
  greatest member of any ordered collection to cause. The current unrestricted
  `CauseOfQualityInAnotherIsMoreSuchReading` still drops synonymy and remains
  an explicit stronger open reading; this batch does not attribute it anew.
- **ST I q.2 a.3 co., quarta via** (`AQUINAS-ST-I-Q2-A3`): after the grades and
  maximum steps, `Quod autem dicitur maxime tale...` states the maximum-to-cause
  direction. The preceding Aristotle sentence does not supply that converse
  merely as a rule of order logic. Source fidelity therefore preserves the
  causal/genus premise separately instead of calling the region control a
  refutation of Aquinas's fully interpreted argument.
- **Metaphysics III.3, 998b22–27** (`ARIST-MET-III-3`), and **ST I q.3 a.5 co.**
  (`AQUINAS-ST-I-Q3-A5`): being/one cannot be a genus under the stated
  differentia account. Q.3 a.5 ad2 distinguishes proportioned, homogeneous
  measure from God's measure through approach. Set inclusion gives a genuine
  mathematical order; it does not identify its regions with grades of being.
- **ST I q.7 a.1 co./ad2** (`AQUINAS-ST-I-Q7-A1`): material indetermination and
  formal nonreception have different perfection roles; quantitative infinity
  is expressly not the infinity attributed to God. The whole's infinite point
  count/extent therefore cannot substitute for subsistent esse's proposed
  unrestricted formal perfection. The earlier q.7 reception-direction audit
  in `docs/notes/necessary-simple-plurality.md` is retained, not repeated or
  reversed here.
- **ST I q.13 a.5 co./ad1–3** (`AQUINAS-ST-I-Q13-A5`): medicine causes health
  without being an animal's health in the same univocal manner; urine can be
  its sign rather than its cause. Analogy's order to a primary can have causal
  content, but mere ordering/signification does not acquire it automatically.
  The creature-to-God order is explicitly *ut ad principium et causam*, not
  mere spatial inclusion or a common homogeneous genus.
- **ST I q.44 a.1 co./ad1–3** (`AQUINAS-ST-I-Q44-A1`): the positive proposal
  is received/participated esse caused by what has it essentially (heated iron
  from fire is the example), using subsistent esse and its asserted uniqueness
  to reach the universal conclusion. Ad1 distinguishes caused being from the
  definition of being simply; ad2 rejects necessity alone as immunity from a
  cause; ad3 distinguishes mathematical abstraction from actual esse.

The strongest positive bridge is therefore **not** “largest region makes its
parts exist.” It is an independently characterized reception/participation
account: establish that the relevant bearers have received esse, identify the
essential giver, and justify their actual dependence on it. This could explain
why degree is derivative rather than brute, without assuming the cause merely
from the order's top position. Its source rationale is the distinction between
having a perfection derivatively and having it essentially, not reversal of a
bare comparative. What remains disputed is whether this derivative/essential
classification and its causal direction hold in the actual case, why each
recipient must be caused in the relevant sense, whether all others are
recipients, and why there is exactly one essential giver. Q.44's appeal to
uniqueness cannot be reused to independently establish that same uniqueness.
An unreceived different-whole-essence rival and a global structural-ground
rival dispute those applications; the region certificate alone decides neither.

The existing #386 derivation already composes the exact q.13
`OrderedToPrimaryAsCauseReading.causesAllInGenus` with creature scope,
approach and strict primacy. Its additional premises are unchanged and open.
A new theorem merely assuming that same causal clause for every proper region
would transcribe the desired result. No such extra opaque bridge is added.
The independently defensible actual participation/giver application is not
established by this batch; the precise burden and strongest objection are
persisted instead, as #696 permits. The existing strict-primacy candidate remains
open, and the same dependence/individuation burden connects to #320/#697.

## Sourced whole-first rival: Schaffer

Schaffer, *Monism: The Priority of the Whole*, §§1.1–1.4, pp. 33–44
(`SCHAFFER-MONISM-FRAMEWORK`, materialized and read), offers a concrete rival
to a parts-first account. His arena is actual concrete material objects, with
an assumed cosmos and proper parts; deities and spirits are outside that arena
(p. 33). His cosmos is a material object, not the `Set Point` in the Lean
control. Parthood and metaphysical dependence are distinct relations (p. 38):
the latter is an explanatory priority, not an efficient-cause predicate.

His positive argument adds premises beyond maximality. Foundationalism assumes
a well-founded priority ordering (p. 37). A completeness argument requires
basic objects to cover the cosmos (p. 39), while recombinability and an economy
argument motivate restrictions on overlap or proper parthood among basics
(pp. 40–41). Given this framework, the whole can be the sole basic material
object and its proper parts depend on it (pp. 42–43). The completeness,
recombinability, duplication and foundationalist assumptions are disputable;
the source does not derive them from inclusion alone. The physical and gunk
arguments in §2 lie outside the materialized witness and are not assessed here.

On the same explanatory question, Schaffer's basic whole grounds derivative
material parts, while Aquinas q.44 proposes an essential giver for received
esse. The former's restricted material basicness does not answer why the cosmos
exists or establish an all-being source; the latter must justify actual
reception, causal scope and uniqueness. Neither a mathematical greatest set
nor its empty-priority assignment refutes the substantive dependence account.
Conversely, Schaffer's priority premise does not instantiate the Lean model's
empty relation or establish Aquinas's efficient-cause bridge. These boundaries
leave both actual application and any comparison of explanatory sufficiency open.

## Symmetric comparison on the same why-question

| Account | Proposed answer for why the relevant beings exist | Remaining burden |
| --- | --- | --- |
| Classical theistic participation | Nonreceived subsistent esse gives esse to dependent recipients; finite perfections preexist eminently, not as spatial parts | Defend reception, actual giver/dependence, scope, essential identity and uniqueness; a top or infinity label supplies none. |
| Naturalistic spatial whole | A physically actual whole with laws/constraints accounts for local regions, objects or processes | Defend that actual structure and the explanatory relation. Inclusion is not production; a brute whole is a different stopping account from explained constraints. |
| Schaffer’s priority monism (§§1.1–1.4, pp. 33–44) | Actual material parts depend on a basic material cosmos under the stated priority and tiling framework | Defend foundationalism, completeness, recombinability and economy; its material domain and grounding do not establish an efficient producer or explain cosmic existence. |
| Plural or brute foundations | Independent natures or a brute arrangement stop the explanation at another place | Defend coexistence, application and stopping policy by the same criteria asked of a single giver. Their lack of this bridge is not itself a contradiction. |

These are explicit competing proposals, not new source-attributed claims or a
ranking. The same questions of actual instantiation, dependence and adequate
explanation apply symmetrically. No mathematical spatial model establishes a
worldview, a necessary being, first cause, or identity with God.

## Premise/type and verification boundaries

Intended and actual root-premise change: none. No designated root argument or
premise is replaced. The new closed certificate has no ordinary philosophical
hypotheses. Every claim above matches its scope: exact real-coordinate extent,
region inclusion, restricted-family maximality, bounded open interval and
formal empty priority. The imported Bool/Nat certificates retain their original
full-background scope. The new source audit supplies interpretations and gaps,
not new attributed statements or defended premises.

The Challenge was frozen before solution work: SHA256
`f6374d1e658c8e75cfb1c63e314921a0651d61defd4cabb2612e6e0376d75d1c`.
Shared development checked the combined new definitions/solution plus `rfl`
compatibility of the old maximum/no-top names at clean preview
`9a3bacd5060f16671a8638d792d58c96df0ac9ce`, session `master-20261029`, path
`Scratch/issue696/Combined.lean`, version2; exact content SHA256
`16343445ad5293f725606a0591de5460a990fb073094209a47537cebaf2f648d`.
Only axiom-report diagnostics remained: `propext`, `Classical.choice`,
`Quot.sound`, the permitted Mathlib set. The first edit lacked the existing
`CharZero.infinite` import; adding `Mathlib.Algebra.CharZero.Infinite` fixed
instance resolution without changing the frozen type. No new external package.
A corpus-related query/dossiers used canonical records. Warm request1.722s
(service1.704s; negligible lease wait), identical CLI1.455s under the shared
lease: this sample favors CLI and establishes no throughput gain. Retain the
service's persistent goals/binding convenience and CLI fallback; final delivered
CI owns canonical build, binding, Comparator and NanoDa. Reproduce after build:
`scripts/verify-result.sh INFINITE-GREATEST-WHOLE-CONTROL`.
