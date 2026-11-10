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
| J2 | Support of being among necessary concrete things is well-founded: no endless descent. | open | recorded; see the rival table |

Through that argument stage one already reaches `STMT-GOD-EXISTS` in the
computed frontier. It reaches it by the necessary-concrete routes with 15 bare
premises each, which is where the stage-two work lies. Whether the ungrounded
individual it yields is the root that `NecessaryClassicalGodRoot.derive` starts
from is not yet checked.

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
| A1 presence gives existence | Presentism: to exist is to be present now, and something earlier has ceased | survives | `InertEmptiness.necessaryConcrete` |
| A2 inert emptiness | A beginning out of nothing | survives | `InertEmptiness.necessaryConcrete` |
| A3 possible contingent-free past (derived) | Initial-state view: no possible history has contingent things absent, then present | survives | `InertEmptiness.necessaryConcrete` |
| A3′ possible founded coming-to-be | The same initial-state view | **excluded** by `ContingentComingToBe.possibleContingentFreePast`; survives only with an endless past or a never-generated contingent thing | the premise itself |
| B1 possible beginning | Contingent reality is beginningless in every possible history | survives | `LocalFramePossibleExternalCause.necessaryConcrete` |
| B2 causal opportunity | Beginnings are possible and always brute | survives | `LocalFramePossibleExternalCause.necessaryConcrete` |
| J1 supporters of the necessary are necessary | A necessary thing is supported somewhere by a contingent thing | survives | `NecessaryConcreteUnderived.checks` |
| J2 support among necessary things is well-founded | Two necessary things support each other | survives | `NecessaryConcreteUnderived.checks` |

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
3. Check whether the ungrounded individual of the join is the root the stage-two chain starts from.
