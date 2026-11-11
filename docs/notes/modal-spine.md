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
| A3′w (weak version, use this one) | The same, with a past that has a *beginning* (some moment at or before the populated one has nothing earlier) in place of a founded past. `6d71688e` | open | the same initial-state view, also excluded by a checked theorem |

The derivation of A3 used foundedness only to reach a moment with nothing
earlier, so the weak version suffices
(`BegunComingToBe.possibleContingentFreePast`, spec
`specs/modal-spine-begun-coming-to-be.toml`). A3′ strictly strengthens A3′w
(`possiblyBegunOfFounded`, registered `strengthens` relation). The difference
matters: continuous time with a first moment gives every later moment a begun
past but not a founded one (`t, t/2, t/4, …` descend endlessly; checked for
non-negative rationals in `BegunComingToBe.controls`). So A3′ conflicts with
every possible populated history having continuous time with a beginning, the
standard picture of a universe with a beginning, and A3′w does not. Under A3′w
the rival's second horn is a genuinely beginningless past. The control
`BegunComingToBe.Control.zeno` (times `WithBot ℤ`: a first moment with no
earliest moment after it) also shows that begun coming-to-be, together with an
existing, earlier-present predecessor ground for every contingent thing, does
not entail a necessary individual at any world: an endless descent of
contingent grounds fits between the empty first moment and any later one. In
the spine's existing route, necessity is supplied by inert emptiness (A2)
together with the route's other premises. This indicates, but does not yet
certify, that #1463's earlier-grounds support route loses its entailment of a
possible necessary being once restated over begun pasts.

So a holder of the initial-state view who denies a necessary concrete being is
committed to this: in every possible history, either some contingent concrete
thing was never preceded by its own absence, or no populated moment has a
founded past. The controls show the view survives in exactly those two ways.
This is valid where the Third Way's quantifier shift is not, because it
requires an *earlier* absence and a founded past.

A3′ now has a second, optional support option (spec
`specs/modal-spine-coming-to-be-horns.toml`), which prices both horns.
`ComingToBeHorns.possiblyFoundedOfEarlierGrounds` derives A3′ from two premises:

| | Premise | Status | Rival |
|---|---|---|---|
| A3′a | In every possible history, each moment with a contingent concrete thing present has a founded past (`fce4ac74`). It denies horn H2 wherever a contingent thing is present. | open; one derivation, below | H2, a non-well-founded populated past: a beginningless succession, each contingent thing preceded and even grounded by an earlier one (control 3); or a dense past with a first moment (control 8) |
| A3′b | Possibly, contingent concrete things exist in a history where each has an existing concrete ground present at some moment *before* each moment of its presence (`6dd276f0`). It prices horn H1. | open | H1 with a ground that has no earlier presence: simultaneous (controls 4 and 5) or only later (control 7) |

**H2 is wider than an endless past.** "Founded" is `Acc` of the strict order
of moments. On non-negative rational times every moment after 0 has
`t, t/2, t/4, …` below it. So A3′a forbids a contingent concrete thing to be
present at any non-initial moment of dense time in any possible history. That
anti-continuum commitment is paid by this side. A3′ itself has the same
founded-past condition. Control 8 satisfies A3, inert emptiness and universal
coming-to-be on dense time with a first moment, while H2 holds, the Reaper
bridge fails, and no state-causation relation satisfies finitism and the
precedence bridge together. Each of those two bridges, and the earlier-grounded
possibility premise, can still hold there on its own. Moving foundedness from moments to discrete events is an untested
alternative.

A3′a has one derivation with independent content, plus one equivalent
reformulation:

| | Premises | Theorem | Status |
|---|---|---|---|
| Causal finitism | Modal state-causal finitism: momentary states have finitely many causal ancestors (`9c314355`); and every earlier state is a causal ancestor of a populated later state (`20e6c7df`) | `populatedPastsFoundedOfStateFinitism` | derivation. H2 must reject finitism or the bridge from mere precedence to causation. Each survives alone (controls 1 and 2) |
| Grim Reaper | Reaper assembly (`f63cd425`) | `populatedPastsFoundedOfReaper` | declared near-transcription. The bridge's consequent is a closed claim about `Nat` station systems that never mentions the descent or the history, and `IndexedSignalReaper.impossible` refutes it, so the bridge just restates A3′a. A real patchwork premise would need a vocabulary for assembling worlds, which the corpus lacks |

So H2 is excluded only under the open bridges `9c314355` and `20e6c7df`.

Under A3′a, an H1 thing would be present at a moment with nothing earlier, so
no ground of it can have been present before it. Rejecting A3′b's "before"
means only that some ground is not earlier: it may be simultaneous, later
(control 7, with no grounding edge between simultaneously present things) or
never present. The grounding relation has no temporal-presence constraint, so
this is not a choice of simultaneous grounding. A sustaining ground present at
all times satisfies "before" only for a grounded thing never present at a moment
with nothing earlier (control 4). Without a necessary concrete being, a rival who
keeps every contingent thing grounded needs grounding that is not
well-founded (controls 5 and 7). That is the horn
`BruteFoundationBoundary.bruteRootOrNonWellFounded` already forces; with
well-founded grounding the rival gets a brute contingent root.

**A3′a and A3′b together already contain the possibility of the target.**
`possiblyNecessaryOfEarlierGrounds` proves that they entail "possibly a
necessary concrete individual exists" (`d2d7cf61`). The proof descends along
earlier grounds through a founded past until it reaches a non-contingent
concrete ground. Under F1 and F2 that gives the stage-one conclusion. A rival
who denies that a necessary concrete being is possible therefore rejects A3′b
(or A3′a) outright. This support option does not discriminate against that
rival; it is still a correct conditional support option. See the
[horns attempt](../../corpus/attempts/3cae291a-3ec4-44db-9113-93104140bc8f.json).

No causal, grounding or explanatory relation occurs in the A3 derivation or in
the first support option for A3′; the second support option uses them. The
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
| A3′ possible founded coming-to-be | The same initial-state view | **excluded** by `ContingentComingToBe.possibleContingentFreePast`; survives only with a non-well-founded (endless or dense) populated past (H2) or a never-generated contingent thing (H1) | the premise itself |
| A3′a founded populated pasts (H2 denied) | A beginningless succession of contingent things, each preceded and grounded by an earlier one; or a dense past with a first moment | **excluded under the open bridges** `9c314355` (state-causal finitism) and `20e6c7df` (precedence to causation), by `populatedPastsFoundedOfStateFinitism`. The Reaper form is a declared near-transcription. Survives finitism alone, the precedence bridge alone, and earlier grounding; dense time with a first moment survives the Reaper bridge and the joint finitism/precedence bundle, though each of those two bridges can hold there alone (`ComingToBeHorns.controls` 1–3, 8) | `populatedPastsFoundedOfStateFinitism` |
| A3′b possible earlier-grounded history (H1 priced) | A never-generated contingent thing whose ground has no earlier presence | **excluded under the open premise A3′a** by `possiblyFoundedOfEarlierGrounds`. Survives when some ground is not earlier: simultaneous with a necessary ground; without a necessary being, only under non-well-founded grounding, whether simultaneous or later (`ComingToBeHorns.controls` 4, 5, 7). A3′a with A3′b already entails possible necessary being (`possiblyNecessaryOfEarlierGrounds`) | `possiblyFoundedOfEarlierGrounds` |
| A3′w possible begun coming-to-be (weak version) | The same initial-state view | **excluded** by `BegunComingToBe.possibleContingentFreePast`; survives only if every accessible history containing a present contingent thing has a never-generated contingent thing or a beginningless past at every populated moment (histories without contingent things satisfy the rival trivially) | the premise itself |
| B1 possible beginning | Contingent reality is beginningless in every possible history | survives | `LocalFramePossibleExternalCause.necessaryConcrete` |
| B2 causal opportunity | Beginnings are possible and always brute | survives | `LocalFramePossibleExternalCause.necessaryConcrete` |
| J1 supporters of the necessary are necessary | A necessary thing is supported somewhere by a contingent thing | survives | `NecessaryConcreteUnderived.checks` |
| J2 support among necessary things is well-founded | Two necessary things support each other | survives | `NecessaryConcreteUnderived.checks` |

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

### Stage-one warrant audit: temporal emptiness and absolute possibility (2026-11-12)

This is an analyst interpretation/warrant audit of A2 (`395cb0f6`) and F2
(`62b4a40a`), with the weaker F2′ (`1b1462e6`) kept separate. It changes no
Lean theorem, statement, source attribution or computed status. The existing
`InertEmptiness.earlierNecessary`, `necessaryConcrete` and
`ActualEuclidean.inertNecessaryConcrete` results remain valid conditionals.

**A2's exact positive content.** `EmptinessStaysEmpty` says that for *every*
history and every `s < t`, concrete absence at `s` entails concrete absence at
`t`. Classically, the contrapositive says that if *any* concrete thing is
temporally present at `t`, *something* concrete must have been temporally
present at **each** earlier `s`. This is the precise feature the stage-one
proof uses: A3 supplies an earlier moment free of contingent concreta; A2
supplies a concrete occupant there; presence-to-existence makes that occupant
existent in the accessible history `v`, and its noncontingency there follows
from A3's universal absence condition. F1 and F2 (or F2′) then transport the
same individual's existence to the designated actual world `w`.
No occurrence of `Causes`, `grounds` or an adequacy relation connects that
occupant to the later thing. The result is therefore a backward temporal
population principle, not a demonstrated account of efficient production.

**A precise interpretation mismatch, not an objection by mere possibility.**
`History.IsAt w x t` is a distinct primitive from `ExistsAt w x`, with only
`IsAt -> ExistsAt` required. Thus *no concrete thing temporally present* does
not mean *no actual concrete being available as a cause*. One stipulated
two-world interpretation makes the distinction exact:

| Coordinate | `actual` world | `other` world |
| --- | --- | --- |
| `ExistsAt(source)` | true | true |
| `IsAt(source, 0)` and `IsAt(source, 1)` | false | false |
| `ExistsAt(creature)` | true | false |
| `IsAt(creature, 0)` / `IsAt(creature, 1)` | false / true | false / false |

Take universal accessibility, both individuals concrete, and the complete
two-point time carrier `{0, 1}` ordered by `0 < 1`, with `now = 1`.
Presence-to-existence holds; the creature is contingent and A3 holds at
`actual`; F1 and F2 hold. A2 fails because the history is concrete-empty at
`0` and populated at `1`. Yet `source` is a necessary concrete individual.
One may *add* a primitive edge by which that existing but non-present source
causes the creature: the history's causal field permits it, but the field has
no independently defended causal semantics or verified realization here.
This is an **unregistered, hand-inspected finite assignment**, not a new Lean
certificate or evidence that atemporal creation actually occurs. It shows the
specific modeling gap: the A2 formula forbids this assignment independently
of whether the creature's origin is causeless, and the original control's
`rooted` witness instead makes its necessary source present at *every* time.

The distinction matters especially for a theory with an atemporal concrete
source, but the general issue is broader: simultaneity, time-indexed
presence, atemporal existence and existential production are different
relations. Calling a concrete-empty instant **absolute nothing** begs the
missing presence/existence bridge. This is not a counterexample to the
verified A2-conditional theorem, and it does not show A2 metaphysically false.

**A2's strongest warrant route.** A positive defense can argue that a new
concrete occurrence requires an actual producer, and that an earlier
concrete-empty moment contains no producer. The inference to A2 nevertheless
needs an extra principle: every producer capable of a later concrete onset
must be **temporally present in that history at each earlier moment**. A more
elaborate causal-temporal closure account could instead attempt to exclude
outside-time producers, simultaneous or newly appearing producers, and
nonproductive arrivals; excluding outside-time producers *alone* does not
entail A2. None of these requirements follows from the mere claim that
nonexistents cannot act. A defender may motivate a strictly immanent,
causally closed history, but the spine quantifies over every history,
including ones whose sources could lie outside its time coordinate. An
alternative cause-based premise allowing an existing atemporal or simultaneous
producer would be weaker in this respect and would require a distinct proof
to the root; replacing A2 by it in the existing theorem is unjustified.

**F2's strongest positive interpretation.** If metaphysical possibility means
the ways *total reality* might have been, and admissibility of a complete
world-description is not indexed to which such description obtains, then the
same space of complete alternatives is available from each admissible world.
On that substantive interpretation `R(w,v)` amounts to admissibility of `v`
in one world-independent space; actual reflexivity and Euclidean access
follow. This provides a positive reason for F1 and F2, not merely the observation
that modal system S5 is mathematically convenient. Crucially, its warrant
depends on **world-independent admissibility** and the identity policy for
individuals across descriptions. Defining `R` this way proves a theorem about
the chosen semantics; it does not independently demonstrate that those are
the correct metaphysical semantics.

The strongest recorded alternative is the origin-tolerance profile: a thing
can have nearby but not arbitrarily different origins under a fixed
cross-world identity policy. The five-world certificate shows that the
resulting *modeled* access can fail F2′ while A1–A3 hold. To make this a
philosophical challenge to absolute metaphysical possibility, the profile
must explain why an origin outside the tolerance is **impossible for the
same individual**, not merely more distant, less similar or excluded by a
restricted counterfactual question; it must also justify the symmetric
access criterion for jointly present individuals. The existing attempt
`f2b3c229` leaves precisely these application burdens open. Conversely, a
defender of the absolute profile must justify the cross-world identity and
admissibility claims rather than dismiss origin constraints by the name S5.
The **stage-one conclusion** also has separately verified arrival variants
using only F2′ (`ActualEuclidean.inertNecessaryConcrete` and
`externalNecessaryConcrete`). The original `InertEmptiness.necessaryConcrete`
and `LocalFramePossibleExternalCause.necessaryConcrete` theorems retain global
F2 in their literal hypotheses. Thus the *conclusion* need not pay the global
frame premise, without changing the original theorem signatures.

**Provisional assessment.** F1 has a strong, direct interpretation under
absolute metaphysical possibility: the actual complete reality is one of the
possibilities. F2/F2′ have a substantive positive case under world-independent
admissibility, but its application remains **OPEN**; neither the tolerance
countermodel nor the positive semantics establishes a metaphysical verdict.
A2 has a real temporal-population role in its exact proof, but its slogan
“from nothing, nothing comes” is too weak to warrant the formal universal:
non-presence is not nonexistence, and the producer's time-relation is unstated.
I would not treat A2 as philosophically established without that bridge.

**Next discriminating tests.** For A2, register and Lean-check the finite
non-present necessary-source interpretation, then specify a genuine
cause/production interface and test the weakest *source-availability*
principle sufficient for a revised arrival. Preserve the original conditional
as a distinct stronger route. For F2′, compare the strongest independently
motivated account of world-independent compossibility with an origin-sensitive
identity account on the same two-world possibility question; assess the
identity/admissibility evidence before adding another frame theorem. Neither
test requires a new modal engine, and neither makes a root premise closed by
stipulation. Existing attempts and conditional result IDs are indexed in
`corpus/attempts/bc674a0b-433f-4893-913c-57ac9f68eb9c.json`.

## Next investigations

Select the next discriminating question using the current evidence and
provisional assessment. Foundational-warrant work is available alongside these
conditional investigations, not a mandatory first gate:

1. The two horns left to the initial-state view under A3′ now have prices
   (2026-11-11, see A3′a and A3′b above). Next: move foundedness from moments
   to discrete events, so that a dense past with a first moment is not
   excluded, and compare with A3′. Build a patchwork vocabulary over accessible
   worlds, so that a Reaper bridge has content of its own. Weaken the precedence
   bridge to "some earlier state". Find an H1 price that does not already
   entail possible necessary being. Try `BoundedPastResource.noUniformGrowth`
   as an independent price on H2.
2. For the rows marked "survives", look for commitments the rival's holder
   accepts that conflict with it. The join models depend on the support relation
   reversing direction between worlds, so an invariance premise is the first
   discriminator for J1 and J2.
3. Done: the ungrounded individual of the join is the stage-two root (see "The
   join"). Done: the sense links were cleaned and the composition registered
   (result `57213a13-fda3-4d8d-86ec-7f4462a3e7a1`). The underived premise and the
   act-of-being bridges now read the same `m.grounds` over the same world-relative `ExistsAt`.
   Open: the four older arguments to the endpoint keep legacy allowlist entries,
   because their intermediate statements and the act-priority record (POTENCY_1
   on a generic `InPotency` parameter) still link several senses. Cleaning those
   records, or splitting the compound disambiguations, would clear more of them.
