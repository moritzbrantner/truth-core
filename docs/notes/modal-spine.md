# Modal spine to "God exists"

Owner direction, 2026-11-09: until it closes, the working root is **God exists**
(`STMT-GOD-EXISTS`, stage 1), not `STMT-CATHOLICISM-TRUE`. The first spine is a
modal contingency argument. Stages 3 to 6 of the Catholic case are deferred, and
their historical premises will later be argued by inference to the best explanation.

Report against the working root with
`python3 scripts/corpus.py frontier --routes --root STMT-GOD-EXISTS`.

Work counts as spine progress when it changes the status of a premise named
below, or records or tests a rival to one.
Other routes (First Way, Fourth Way, the Gödel and Scott material, other senses
of "necessary") stay where they are and are pulled in when a spine rival needs them.

Nothing in this note is established. "Open" means not established under the
closure rules. Every theorem named here is verified; it certifies consequence only.

## Stage one: a necessary concrete being exists

Conclusion (`STMT-NECESSARY-CONCRETE-AT`): one and the same concrete individual
exists at the actual world and at every world accessible from it.

There are two verified arrivals. They share the two frame premises.

| | Premise | Status | Rival |
|---|---|---|---|
| F1 | The actual world is accessible from itself. `STMT-ACTUAL-MODAL-REFLEXIVITY` | open | recorded; see the rival table |
| F2 | Any two worlds accessible from a world are accessible from each other (Euclidean). `STMT-EUCLIDEAN-FRAME` | open | recorded; see the rival table |

**Arrival A, temporal** (`InertEmptiness.necessaryConcrete`, spec `specs/modal-spine-inert-emptiness.toml`):

| | Premise | Status | Rival |
|---|---|---|---|
| A1 | Whatever is present at some time of a history exists in that history. `STMT-COUNT-TEMPORAL-HISTORY-PRESENCE-ACTUAL` | open | recorded; see the rival table |
| A2 | Inert emptiness: a moment with nothing concrete present is followed only by such moments. | open | recorded: a beginning out of nothing |
| A3 | Possibly, contingent concrete things are absent at a moment and present at a later one. | open | recorded: the initial-state view, on which contingent things are present from the earliest moment of every possible history |

A3 is itself derived (`ContingentComingToBe.possibleContingentFreePast`,
spec `specs/modal-spine-coming-to-be.toml`) from one open possibility premise:

| | Premise | Status | Rival |
|---|---|---|---|
| A3′ | Possibly, every contingent concrete thing comes to be (was absent at some earlier moment) in a history with a founded past (no endless descent of moments). | open | recorded: the initial-state view, now incompatible with it by a checked theorem |

So a holder of the initial-state view who denies a necessary concrete being is
committed to this: in every possible history, either some contingent concrete
thing was never preceded by its own absence, or no populated moment has a
founded past. The controls show the view survives in exactly those two ways.
This is valid where the Third Way's quantifier shift is not, because it
requires an *earlier* absence and a founded past.

No causal, grounding or explanatory relation occurs in this arrival. The
controls show that A1, A2 and A3 are each needed and that the bundle is
satisfiable. Omission of F1 and F2 is not tested there.

**Arrival B, possible cause** (`LocalFramePossibleExternalCause.necessaryConcrete`):

| | Premise | Status | Rival |
|---|---|---|---|
| B1 | Possibly, contingent concrete reality begins. `STMT-SCENARIO-POSSIBLY-BEGINS` | open | recorded; see the rival table |
| B2 | If so, possibly it begins with an existing concrete cause outside all contingent things. `STMT-SCENARIO-CAUSAL-OPPORTUNITY` | open | recorded; see the rival table |

`ExternalCandidateNecessity` shows that "a concrete thing outside all contingent
things" is equivalent to "a necessary concrete thing": the causal relation in B2
does no logical work, so B2 already contains the possibility of the conclusion.
Arrival A was built to avoid that. It does not discharge B2.

**Known weak points of stage one**

- A2 is a claim about every possible history, and it is silent about a first
  state that has no earlier moment. The initial-state view accepts A2 and denies A3.
- Ruling out an empty world is not enough for the conclusion: "necessarily
  something exists" does not give "something exists necessarily"
  (`NecessaryIndividual.Alternating`, `SharedRootBridge`).
- If a world with nothing concrete is possible, the conclusion is false under F1 and F2.

## Stage two: that being is God

Stage one gives no uniqueness, causal role or attribute.

`NecessaryClassicalGodRoot.derive` (verified) takes one actual, necessary,
ungrounded root to: first being, pure act, simple, perfect, good, one, infinite,
immutable, eternal, intellect and will, and the name "God". It has 25 premises.

**The join.** Necessity alone does not make the stage-one individual ungrounded.
The verified `NecessaryConcreteUnderived` argument supplies the step from
`STMT-NECESSARY-CONCRETE-AT` to a necessary concrete individual with no actual
supporter of its being, under F1, excluded middle and two further open premises:

| | Premise | Status | Rival |
|---|---|---|---|
| J1 | Whatever concrete thing supports the being of a necessary concrete thing is itself necessary. | open | recorded; see the rival table |
| J2 | Support of being among necessary concrete things is well-founded: no endless descent. | open; derived (`NecessarySupportCoverage.unionWFOfNoNovel`) from F1, actual well-founded grounding and the open one-way no-novel-edge premise, and bypassed by two coverage routes (below) | recorded; see the rival table |

J2 is a global condition on support across all worlds. The batch
`specs/necessary-support-coverage.toml` replaces it with **coverage**, an open
premise about support itself: a necessary concrete thing supported by something
at some world is supported by something actual (possibly something else).
`underivedOfCoverage` reaches the join's conclusion from the regress premises
(population, actual well-founded grounding, every contingent thing grounded,
excluded middle) and coverage, without J1, J2 or F1. In the proof its witness
is the actual necessary root; the theorem states only existence.
`underivedFromNecessityOfCoverage` reaches it from
`STMT-NECESSARY-CONCRETE-AT`, actual well-founded grounding, J1 and coverage,
without J2 or F1. Coverage follows from either existing bridge (F1 + J1 +
no-novel-edge, or same-supporter presence `STMT-NECESSARY-SUPPORT-IS-PRESENT`),
and is strictly weaker than both. J1 and J2 together do not imply it. All
premises remain open. See the
[J2 attempt](../../corpus/attempts/b8eb98b1-4425-455d-9333-9fa2b6397974.json).

Through that argument stage one already reaches `STMT-GOD-EXISTS` in the
computed frontier. It reaches it by the necessary-concrete routes with 15 bare
premises each, which is where the stage-two work lies.

The ungrounded individual of the join is the stage-two root (checked
2026-11-11). `UnderivedRootPerfection`, `PerfectRootPositiveIntellectWill` and
`ClassicalGodFromPositiveRoot` already chain `STMT-NECESSARY-CONCRETE-UNDERIVED-AT`
to `STMT-NECESSARY-CLASSICAL-GOD-ROOT` at the statement level. The Lean theorem
`NecessaryClassicalGodRootFromUnderived.derive` composes the three on one model,
world, profile and dictionary. Internally the proof carries one witness
through all three steps, but the registered type states `∃ b` in the premise
and `∃ n` in the conclusion and does not certify `b = n`; the identity is an
immediate corollary of uniqueness among actual roots at `w`, not part of the
result. The theorem needs only the
underived individual, excluded middle and the 21 act-of-being, attribute and
naming premises of `NecessaryClassicalGodRoot.derive`. The attribute steps do
not use population, whole-roster nontrapping or contingent grounding; those
premises only produce the root. No extra premise is needed. The join's support
exclusion is used at the actual world only.

The composition is now a registered result (2026-11-11): result
`57213a13-fda3-4d8d-86ec-7f4462a3e7a1`, argument
`8f956c81-3887-4567-a25d-22a66486e30b`, theorem
`NecessaryClassicalGodRootFromUnderived.Registration.derive`. Registration first
needed a sense-link cleanup, because `STMT-NECESSARY-CLASSICAL-GOD-ROOT` and two
reused premises linked senses that their Lean types do not use. The rule applied:
for each conflicting term, a statement keeps only the senses whose declaration its
bound type reaches (`scripts/BindTypes.lean` sense reachability, checked by hand
for structure types such as `Modal.Frame`). The endpoint keeps NECESSARY_2
(`NecessaryAt`), GOD_4 (`Signature.IsGod`), MAXIMAL_1 (`IsMaximumIn`) and
WELL_FOUNDEDNESS_2 (`ActualRoot`). It drops 14 links that no part of its type
uses, among them per se necessity, the frame vocabulary, the nominal God, the q.3
a.4 cause-of-esse forks, the nonnecessary and contingent root rivals, de dicto
necessity and adopted potency (its `InPotency` is a free parameter). The underived statement now links world-relative existence (the
`Ontic` it uses) instead of `PresentEsseSupport`: its type uses `m.grounds`
directly, so the underived premise and the act-of-being bridges now read the
same `m.grounds` with the same world-relative existence. `STMT-SIMPLY-PRIOR-IS-ACTUAL-CONCRETE-GROUND` now links the
`ActualConcreteGround` edge that it uses, not the thinker-ancestry and root
senses.

Two conflicts were real and are handled by existing records, not new bridges. The
naming premise is the declared GOD_1 to GOD_4 sense bridge, as in the existing
maxime-ens routes. For potency, the act-priority record links adopted potency
(POTENCY_1), while the non-overlap record and this theorem use the free
`InPotency` parameter (POTENCY_2). Following the #1278 registration, the
registered theorem binds act priority through the transparent wrapper
`IndependentPriority` (statement `3b2d2d46-baa6-4772-a2db-bb3daeb092fc`) and
delegates to the unchanged frozen composition. Registering it changes no root
premise (computed `frontier-diff`: no change), since the statement route already
existed. Attempt `a062ed2b-028c-40b3-928b-12925a28a261` records the links removed
and why.

Today the stage-two chain obtains its root from two regress premises instead:
every contingent concrete thing has an actual concrete ground, and the whole
actual roster is not a borrowing trap. With an actual concrete individual and
excluded middle, those two premises yield a necessary
root without any modal step, so the corpus reaches the node a third way. The
regress results are also the tool against the "endless chain explains itself"
reply to A3 and B1.

## Rival table (run of 2026-11-10)

Every open premise of the spine now has a recorded rival with a replacement
account and one Lean-verified test. "Survives" means: one finite interpretation
satisfies the rival together with the other premises of the named consuming
theorem while that theorem's conclusion fails. It shows the premise is needed
there and that the rest does not exclude the rival. It refutes nothing, and it
does not test the rival against the whole route. "Excluded" names a checked
incompatibility. No rival is refuted and no premise is established.

Batches: stage one in `specs/modal-spine-inert-emptiness.toml`,
`specs/modal-spine-coming-to-be.toml` and `specs/spine-rivals-stage-one.toml`;
the join and the root and act-of-being premises in
`specs/spine-rivals-root-esse.toml`; the attribute premises in
`specs/spine-rivals-attributes.toml`.

### Stage one and the join

| Premise | Rival (replacement account) | Result | Tested against |
|---|---|---|---|
| F1 actual reflexivity | Accessibility is "what lies ahead" or "what would be ideal": serial, and the actual world does not see itself | survives | `InertEmptiness.necessaryConcrete` |
| F2 Euclidean frame | Possibility is relative and not transitive: reflexive, but two possibilities need not see each other | survives | `InertEmptiness.necessaryConcrete` |
| F2′ Euclidean at the actual world (`1b1462e6`, weaker than F2 by `euclideanAtOfEuclidean`) | Symmetric reflexive non-Euclidean access at the actual world (`ToleranceOriginRival`; structural surrogate for origin tolerance) | The structural omission model survives. `OriginToleranceIdentity` supplies a nonvacuous 5-world, 2-individual countermodel for its encoded origin commitments; the separate restored 3-offset assignment satisfies the conclusion. Metaphysical applicability remains OPEN; deletion scopes are distinguished below. | `ActualEuclidean.inertNecessaryConcrete` |
| A1 presence gives existence | Presentism: to exist is to be present now, and something earlier has ceased | survives | `InertEmptiness.necessaryConcrete` |
| A2 inert emptiness | A beginning out of nothing | survives | `InertEmptiness.necessaryConcrete` |
| A3 possible contingent-free past (derived) | Initial-state view: no possible history has contingent things absent, then present | survives | `InertEmptiness.necessaryConcrete` |
| A3′ possible founded coming-to-be | The same initial-state view | **excluded** by `ContingentComingToBe.possibleContingentFreePast`; survives only with an endless past or a never-generated contingent thing | the premise itself |
| B1 possible beginning | Contingent reality is beginningless in every possible history | survives | `LocalFramePossibleExternalCause.necessaryConcrete` |
| B2 causal opportunity | Beginnings are possible and always brute | survives | `LocalFramePossibleExternalCause.necessaryConcrete` |
| J1 supporters of the necessary are necessary | A necessary thing is supported somewhere by a contingent thing | survives | `NecessaryConcreteUnderived.checks` |
| J2 support among necessary things is well-founded | Two necessary things support each other. Two shapes: support in both directions within one world, or a direction that varies between worlds (contingent grounding facts about necessary beings) | survives against `checks`; **excluded** with F1 and actual well-founded grounding by the no-novel-edge premise (`mutualSupportExcluded`). Compatible with the join's conclusion (`Control.rootedPair`), so it defeats that conclusion only when the actual necessary root is itself supported elsewhere, which denies coverage. The weaker discriminators (well-founded support at every world, no reversed pair) fail (`Control.rotatingTriangle`) | `NecessaryConcreteUnderived.checks`; `NecessarySupportCoverage` |

#### Scope of the actual-world Euclidean comparison

`ActualOnlyEuclidean.euclideanOnSuccessors` proves that F2′ and local
transitivity at `w` give Euclidean access at every successor of `w`, without a
reflexivity premise. `Control.appendix` satisfies both local conditions while
global F2 fails at unreachable `far`. Thus F2′ with failure of F2 does not
force local transitivity to fail. The finite-forward-reachability corollary is
prose only, not a registered Lean result. Changes confined to unreachable
worlds leave ordinary forward-modal formulas at `w` unchanged when the
reachable frame and valuation are fixed; globally quantified spine premises
are outside that scope. See the [frame attempt](../../corpus/attempts/ca49ceb8-a02e-4f49-8dd8-12704afb1220.json).

For deletion, let `D(v)` mean that each concrete individual existing at `v`
is absent at some world accessible from `v`. `OriginDeletion.deletionControls`
(result `70d098fe`) certifies `D(actual)` in the five-world model: `a` is absent
from `bMinus` and `b` from `aMinus`. Yet `b` is necessary at `plus`, which cannot
access `aMinus`, so `D(plus)` fails. `OriginDeletion.accessibleDeletionExcluded`
(result `18aadc0d`) composes `InertEmptiness.earlierNecessary`: A1–A3 at `w`
exclude deletion at every world accessible from `w`, hence also worldwise
deletion. Neither actual reflexivity nor Euclidean access is used. This is an
incompatibility of an added premise; it does not make the original countermodel
vacuous or establish worldwise deletion from origins.

The four encoded origin commitments admit worldwise deletion in `withEmpty`
and its failure in `faithful`/`restored`. They do not settle deletion, although
`OriginPlenitude` and `VariedOriginAt` impose existence conditions.
`OriginDeletion.emptyWorldArrivalInconsistent` (result `ba68692e`) adds
`OriginDeterminesAccess` to A1–A3 and excludes a world with no individuals at
all, including non-concrete individuals. Here `EmptyWorld` concerns existence
at a world; `ConcreteEmptyAt` concerns concrete presence at one time.
Joint deletion of a roster remains a further, untested requirement;
near-origin plenitude preserves the selected individual. See the
[origin attempt](../../corpus/attempts/f2b3c229-43cb-4dd5-939e-bce66655fa78.json)
and [deletion attempt](../../corpus/attempts/b28aad0f-f64d-4eda-aaa9-2799472dd773.json).

Provisional assessment (2026-11-10): the formal weakening is strict and the
encoded origin countermodel survives. Warrant for the access biconditional,
rigid identity, absences and temporal profile remains open. The bounded
candidate survey is an unverified analyst assessment; it establishes neither
coverage of serious rivals nor that the weakening lacks dialectical value.
A defended rival interpretation or independently warranted persistence/deletion
bridge would reopen this assessment. No premise is established by it.

### Stage two: the root and the act of being

| Premise | Rival (replacement account) | Result | Tested against |
|---|---|---|---|
| Something concrete exists | Only non-concrete things exist | survives | `NecessaryRootFork.necessaryRootTrilemma` |
| The whole roster is not a borrowing trap | Every concrete thing has a concrete ground, without end | survives | `WholeRosterFoundation.necessaryConcrete` |
| Every contingent concrete thing has a ground | Some contingent concrete thing is ungrounded (a brute fact) | survives | `ActualRootNecessityUpgrade.upgrade` |
| The maximum in being causes all other being | The maximum is idle: a third thing causes another's being | survives | `TermSenseForks3.maximeEnsCausesAllMaximal` |
| What exists is in act as to being | Thin existence: something exists with no act of being | survives | `Round2ExistenceAct.intellectualExerciseRequiresActFromExistence` |
| A cause of a thing's being is its concrete ground | A non-concrete cause of being (a law or abstract object) | survives | `Round2Grounding.contingentGroundedViaParticipation` |
| Grades of being imply a maximum | Unbounded grades: everything is exceeded | survives | `SelectedAncestryUnique.uniqueRoot` |
| A universal cause of being causes the effect's perfections | Mere conservation: a secondary cause supplies a perfection | survives | `CausalPerfectionTransfer.reconstruction` |
| What is simply prior is a concrete ground | Something non-concrete is simply prior to a concrete thing | survives | `NecessaryFirstBeing.necessaryFirst` |
| Whatever is God is maximal in being | A god exceeded in being by something not God | survives | `StageTwo.GodIsSimple.godIsSimple` |

### Stage two: the attributes and the name

All fourteen tests are conjuncts of `SpineRivalsAttributes.controls`.

| Premise | Rival (replacement account) | Result | Tested against |
|---|---|---|---|
| Nothing has actuality except insofar as it is | Actuality without being (Meinongian) | survives | `existingInActAtFromSomeAct` |
| An effect's perfections preexist in its cause | Strong emergence | survives | `causeOfBeingHasWhatItGives` |
| Goodness is actuality | Actuality is not sufficient for goodness | survives | `godIsSupremelyGood` |
| Every composite has a uniting cause | Uncaused composition | survives | `godIsSimple` |
| Matter-form and essence-existence differences are compositions | A real difference without composition | survives | `firstMoverSimple` |
| No component is the first being | A first being that is a component of something | survives | `attributesFromFirst` |
| The immaterial is intellectual | Intellect only in material composites | survives | `godHasIntellect` |
| Will follows intellect | Intellect without will | survives | `godHasWill` |
| Act is simply prior to potency | Potency prior to act | survives | `firstBeingNoPotency` |
| Nothing is in act and potency in the same respect | Act and potency in the same respect | survives | `firstBeingNoPotency` |
| Subsistent being is infinite | A finite subsistent being | survives | `firstMoverPerfectionFromInfinity` |
| The immutable is eternal | Immutable without eternity | survives | `godIsEternal` |
| "God" names the fully described principle | The full nominal naming fails | survives | `properDescriptionExcluded` |
| The nine attributes suffice for the classical attributes | The nine attributes fall short | survives | `ClassicalAttributes.godHasClassicalAttributes` |

Four attribute rivals (will, infinity, eternity, sufficiency) are bare negations
in Lean, with the replacement account in prose only: the premise's carrier has
no predicate in which to state it.

### Foundational-warrant targets

These premises have no source claim and no derivation in the corpus. They are
targets for investigating foundational warrant, not established premises or
choices the owner must settle before research can proceed:

- F1 actual reflexivity. Fix the intended sense of possibility and test whether each recorded rival contests that claim or instead uses another accessibility relation.
- A1 presence gives existence. Compare the proposed non-presentist reading of existence with the presentist rival and test its applicability to the intended histories.
- Something concrete exists at the actual world. Make the intended sense of concrete explicit and assess its support and strongest objections.

The other unsupported premises (F2, A2, A3′, B1, B2, J1, J2, and the root and
act-of-being bridges) remain contested positions to investigate under explicit
assumptions. For each selected target, record the exact scope and applicability,
support, strongest objections and replies, and a reasoned provisional judgment
under the [systematic research loop](../systematic-corpus-loop.md). Such a judgment
can guide priorities and qualified reports without changing computed closure;
personal assent is not philosophical warrant.

## Next investigations

Select the next discriminating question using the current evidence and
provisional assessment. Foundational-warrant work is available alongside these
conditional investigations, not a mandatory first gate:

1. The two horns left to the initial-state view under A3′: test "some contingent
   thing never came to be" against the brute-foundation results, and "every
   possible past is endless" against the causal-finitism and Grim Reaper results.
2. For the rows marked "survives", look for commitments the rival's holder
   accepts that conflict with it. The join models depend on the support relation
   reversing direction between worlds, so an invariance premise is the first
   discriminator for J1 and J2.
   For J2 this is done (`specs/necessary-support-coverage.toml`). One-way
   invariance (no novel edge) excludes the mutual-support rival. Coverage is
   weaker and is enough for the join's conclusion without J2. A holder of the
   rival must deny coverage to block that conclusion. Coverage follows from an
   essence-based account of dependence between necessary beings (which gives no
   novel edge) together with F1 and J1. Contingent grounding edges alone do not deny it: in `Control.rootedPair`
   the edges change between worlds and coverage holds. It is denied only by an
   account that lets a necessary concrete thing lack every actual concrete
   supporter while having one elsewhere. Next: the warrant for coverage against
   that account. Also: whether J1 can be
   weakened to its selected-world instance, which is the only instance the
   coverage route from necessity uses.
3. Done: the ungrounded individual of the join is the stage-two root (see "The
   join"). Done: the sense links were cleaned and the composition registered
   (result `57213a13-fda3-4d8d-86ec-7f4462a3e7a1`). The underived premise and the
   act-of-being bridges now read the same `m.grounds` over the same world-relative `ExistsAt`.
   Open: the four older arguments to the endpoint keep legacy allowlist entries,
   because their intermediate statements and the act-priority record (POTENCY_1
   on a generic `InPotency` parameter) still link several senses. Cleaning those
   records, or splitting the compound disambiguations, would clear more of them.
