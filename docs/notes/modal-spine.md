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
every possible populated history having continuous time with a first moment,
and A3′w does not. Under A3′w the rival's second horn is a genuinely
beginningless past (in the order sense). Note that standard FLRW Big Bang
cosmology has no first moment (time is open below; the initial singularity is
not a moment), so it is a beginningless populated past in that sense: neither
A3′ nor A3′w is supported by it as such, though, being possibility premises,
neither is contradicted by its possibility either. The control
`BegunComingToBe.Control.zeno` (times `WithBot ℤ`: a first moment with no
earliest moment after it) also shows that begun coming-to-be, together with an
existing, earlier-present predecessor ground for every contingent thing, does
not entail a necessary individual at any world: an endless descent of
contingent grounds fits between the empty first moment and any later one. In
the spine's existing route, necessity is supplied by inert emptiness (A2)
together with the route's other premises. #1463's earlier-grounds support
route, restated over begun pasts (`GrimReaperPatchwork.possiblyBegunOfEarlierGrounds`),
indeed loses its entailment of a possible necessary being: `zeno` satisfies
both of its premises with no necessary individual (`GrimReaperPatchwork.controls` 3).

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
coming-to-be on dense time with a first moment, while H2 holds, the old Reaper
assembly bridge fails, and no state-causation relation satisfies finitism and the
precedence bridge together. Each of those two bridges, and the earlier-grounded
possibility premise, can still hold there on its own. Moving foundedness from moments to discrete events is an untested
alternative.

A3′a has two derivations with independent content, plus one superseded
reformulation:

| | Premises | Theorem | Status |
|---|---|---|---|
| Causal finitism | Modal state-causal finitism: momentary states have finitely many causal ancestors (`9c314355`); and every earlier state is a causal ancestor of a populated later state (`20e6c7df`) | `populatedPastsFoundedOfStateFinitism` | derivation. H2 must reject finitism or the bridge from mere precedence to causation. Each survives alone (controls 1 and 2) |
| Grim Reaper patchwork | Along every descent below a populated moment, adjacent Reaper pieces are co-possible (`ReaperPiecesPossible`); co-possible adjacent pieces glue into one possible world (`ReaperPatchwork`) | `GrimReaperPatchwork.populatedPastsFoundedOfPatchwork` | derivation (2026-11-12). Stations sit at the moments of the descent in worlds of the history; a glued world's registers are read as a `Nat` signal and refuted by `IndexedSignalReaper.impossible`. Each premise holds without the other in a beginningless history (`GrimReaperPatchwork.controls` 1, 2). Because both range over every descent, they also exclude dense time with a first moment (with `ComingToBeHorns.controls` 8; on a `WithBot ℤ` analogue, control 3) |
| Grim Reaper assembly | Reaper assembly (`f63cd425`) | `populatedPastsFoundedOfReaper` | declared near-transcription, superseded by the row above. Its consequent is a closed claim about `Nat` station systems that never mentions the descent |

So H2 is excluded only under open premises: `9c314355` with `20e6c7df`, or
the two Reaper premises.

**The Grim Reaper route to A3′w** (spec
`specs/modal-spine-grim-reaper-patchwork.toml`, attempt
[`ac336333`](../../corpus/attempts/ac336333-edfe-4599-b35e-1e78b81047e5.json)).
The Reaper argument is naturally an argument for a *begun* past, not a founded
one: in the reconstruction of Koons's argument (#367 audit) the stations fill successive non-overlapping regions of an alleged infinite past, back through the whole of it. The
coinitial premises restrict both Reaper premises to descents that run below
every earlier moment of the populated one; they are implied by the unrestricted
ones and are silent about pasts with a beginning. Coinitiality is purely
order-theoretic: `(0, t]` and `(-∞, t]` are order-isomorphic, so a coinitial
descent may accumulate metrically and the typed premises cover a metrically
finite past with no first moment exactly as they cover an infinite one.

| | Premises | Theorem | Status |
|---|---|---|---|
| Begun populated pasts | Coinitial local pieces, coinitial patchwork, and countable coinitiality of beginningless populated pasts (checked for integer times; the full rational or real line by `t - n`, an open-below half-line by `t / 2 ^ n`) | `populatedPastsBegunOfPatchwork` | derivation; all three OPEN |
| A3′w | Begun populated pasts and A3′b (`6dd276f0`) | `possiblyBegunOfEarlierGrounds` | derivation. Unlike the founded version, this bundle does **not** carry the possibility of a necessary being: `BegunComingToBe.Control.zeno` satisfies it, the coinitial Reaper premises and countable coinitiality with no necessary individual (`GrimReaperPatchwork.controls` 3) |

Founded populated pasts strictly strengthen begun ones (`populatedPastsBegunOfFounded`,
converse fails in `zeno`).

**The metric Reaper** (spec `specs/modal-spine-metric-grim-reaper.toml`,
attempt [`5f4e157a`](../../corpus/attempts/5f4e157a-c495-4cf8-ae58-dcd321a3b5a6.json)).
A real time clock (strictly increasing along the order) measures durations;
*spaced* descents have every slot at least some fixed `δ > 0` long, and exist
(in linear time) exactly below metrically infinite pasts.

| | Premises | Theorem | Status |
|---|---|---|---|
| Metrically finite populated pasts | Spaced local pieces, spaced patchwork (linear time, one real clock for the frame) | `MetricGrimReaper.populatedPastsMetricallyFiniteOfPatchwork` | derivation; both OPEN. No countable-coinitiality premise: a metrically infinite past has a spaced descent by a theorem. The spaced premises are strictly weaker than the coinitial ones, and the conclusion strictly weaker than begun populated pasts (`spacedPiecesOfCoinitial`, `spacedPatchworkOfCoinitial`, `populatedPastsMetricallyFiniteOfBegun`; strictness by `MetricGrimReaper.controls` 2) |

Reach: the conclusion is *no populated past is metrically infinite*, not *every
populated past is begun*. For every register frame the spaced premises hold in a
populated open-below finite past (positive real times, the FLRW shape) and in
continuous time with a first moment (`MetricGrimReaper.controls` 2, 3), so the
FLRW and Benardete objections have no target in them. In control 2, metric
finiteness and A3′b hold while A3′w fails, so the metric version reaches A3′w
only through a further open bridge (below).

**Objection audit (Substantive Objection Standard).** What would have to differ
for the Reaper not to reach an arbitrary beginningless populated past? By the
theorem, one of three things: (a) the past has no coinitial descent, which
needs time of uncountable coinitiality; no model of physical time known to the
corpus has it, so this is a formal escape, not an objection; (b) adjacent Reaper
pieces cannot be placed at consecutive members of any coinitial descent; or
(c) gluing fails along it. Two objections to the typed premises are kept,
both concerning *metrically finite* beginningless pasts (open below, like
`(0, t]`), which the order-theoretic premises cannot distinguish from infinite
ones:

- **FLRW.** Standard FLRW Big Bang cosmology has time open below (the initial
  singularity is not a moment). A populated FLRW history has no begun moment,
  and countable coinitiality holds there (`t / 2 ^ n`), so by the theorem the
  coinitial local-pieces or patchwork premise fails if such a history is
  accessible; accepted physical theory treats these models as possible. This
  is a cost of the necessity premises (and of begun populated pasts), not of
  the possibility premise A3′w.
- **Benardete parity, given a separate commitment C** (populated continuous
  time with a first moment is possible; A3′w permits C but does not assert it).
  A coinitial descent in `(0, t]` accumulates toward the missing endpoint, slot
  for slot like `t, t/2, t/4, …` in `[0, t]`; the two differ only at an instant
  hosting no piece, and that is where the admissibility clause (no code from a
  source outside the descent) bites. Given C, local pieces or gluing fail for
  the first-moment arrangement, and by parity for the open-below one, so the
  typed coinitial premises are doubtful there. The parity step is an analyst
  argument, not checked.

The pieces must also be read as stations with their rules, not as register
contents: adjacent-pair witnesses cannot agree on their shared registers
(`overlapAgreeingWitnessesImpossible`), so a patchwork that glues only
value-agreeing patches gives the Reaper no start. Given the theorem, the typed
patchwork premise is equivalent to "adjacent pieces are not all co-possible
along any populated descent", so its warrant must come from the general
recombination principle it instantiates; the registers carry no existential
import, and the bridge from recombining concrete stations to the typed
premises is not built. The earlier description of the Reaper as "one special
case" that might not generalize named no difference and is withdrawn. Both
Reaper premises remain OPEN: the pieces' possibility and their gluing are the
disputed metaphysics, the arrangement's impossibility is mathematics. See
[the Grim Reaper note](../causal-regress-and-grim-reapers.md#objection-audit-for-the-temporal-reaper-2026-11-12).

**Objection audit of the metric (spaced) premises.** FLRW and the Benardete
parity have no target (controls 2, 3). No undercutting objection is identified:
the parity transfers to a metrically infinite past only under the diagnosis
that gluing fails for every infinite descending arrangement, for which no
independent reason is recorded; the global-compatibility reply of the #367
audit is the same fork as before (on the value-agreement reading the argument
does not start; on the duplication reading no acyclic gluing failure along a
non-accumulating descent is recorded); the unsatisfiable-pair diagnosis has no
recorded mechanism. One *rebutting* objection is recorded: accepted theories
have populated solutions with a metrically infinite past (the Einstein static
universe; eternal Newtonian motion), so if every solution of accepted laws is a
possible history, the conclusion fails. It rests on the same principle as the
FLRW row, names no failing piece or gluing step, and sets law-consistency as a
guide to possibility directly against recombination, since an infinite past is
the Reaper's intended target. No independent warrant for spaced patchwork is on
file beyond the general recombination principle it instantiates. See
[the metric Reaper](../causal-regress-and-grim-reapers.md#the-metric-reaper-2026-11-12).

**Connection of the metric Reaper to the arrival (open).** Two plans, neither
built: (1) a named bridge, *in every possible history a populated moment with a
metrically finite past has a begun past*, which with the metric conclusion
gives begun populated pasts and so A3′w with A3′b; this bridge is exactly what
the FLRW objection denies, so the FLRW cost is isolated there rather than
removed; (2) a metric arrival replacing the empty-moment step (A2 with A3) by a
premise about histories whose populated past has finite duration; blocked
because an open-below finite populated past has no empty moment, and no such
premise has been formulated.

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
| J2 | Support of being among necessary concrete things is well-founded: no endless descent. | open; derived (`NecessarySupportCoverage.unionWFOfNoNovel`) from F1, actual well-founded grounding and the open one-way no-novel-edge premise, and bypassed by two coverage routes (below) | recorded; see the rival table |

J2 is a global condition on support across all worlds. The batch
`specs/necessary-support-coverage.toml` offers an alternative, **coverage**, an
open premise that is also cross-world: a necessary concrete thing supported by
something at any carrier world (accessible from the actual world or not) is
supported by something actual (possibly something else). Coverage and J2 are
incomparable in strength. Given the regress premises, coverage carries the whole
modal step, and its contrapositive is close to the endpoint's cross-world clause.
`underivedOfCoverage` reaches the join's conclusion from the regress premises
(population, actual well-founded grounding, every contingent thing grounded,
excluded middle) and coverage, without J1, J2 or F1. In the proof its witness
is the actual necessary root; the theorem states only existence.
`underivedFromNecessityOfCoverage` reaches it from
`STMT-NECESSARY-CONCRETE-AT`, actual well-founded grounding, J1 and coverage,
without J2 or F1. Coverage follows from either existing bridge (F1 + J1 +
no-novel-edge, or same-supporter presence `STMT-NECESSARY-SUPPORT-IS-PRESENT`),
and is strictly weaker than both. J1 and J2 together do not imply it. On the
`checks` route, the J2 derivation's new leaf, no-novel-edge, is strictly
stronger than J2 given F1 and actual well-founded grounding, so that route's
demand did not weaken. All premises remain open. See the
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
| A3′ possible founded coming-to-be | The same initial-state view | **excluded** by `ContingentComingToBe.possibleContingentFreePast`; survives only with a non-well-founded (endless or dense) populated past (H2) or a never-generated contingent thing (H1) | the premise itself |
| A3′a founded populated pasts (H2 denied) | A beginningless succession of contingent things, each preceded and grounded by an earlier one; or a dense past with a first moment | **excluded under the open bridges** `9c314355` (state-causal finitism) and `20e6c7df` (precedence to causation), by `populatedPastsFoundedOfStateFinitism`; and **excluded under the open Reaper premises** (local pieces, patchwork) by `GrimReaperPatchwork.populatedPastsFoundedOfPatchwork`. Survives finitism alone, the precedence bridge alone, earlier grounding, Reaper patchwork alone and Reaper pieces alone (`ComingToBeHorns.controls` 1–3, `GrimReaperPatchwork.controls` 1–2). Dense time with a first moment survives the old Reaper assembly bridge and the joint finitism/precedence bundle, and is excluded by the two unrestricted Reaper premises together (`ComingToBeHorns.controls` 8, `GrimReaperPatchwork.controls` 3): that exclusion is a cost of the unrestricted premises, avoided by the coinitial ones | `populatedPastsFoundedOfStateFinitism`, `populatedPastsFoundedOfPatchwork` |
| A3′b possible earlier-grounded history (H1 priced) | A never-generated contingent thing whose ground has no earlier presence | **excluded under the open premise A3′a** by `possiblyFoundedOfEarlierGrounds`. Survives when some ground is not earlier: simultaneous with a necessary ground; without a necessary being, only under non-well-founded grounding, whether simultaneous or later (`ComingToBeHorns.controls` 4, 5, 7). A3′a with A3′b already entails possible necessary being (`possiblyNecessaryOfEarlierGrounds`) | `possiblyFoundedOfEarlierGrounds` |
| A3′w possible begun coming-to-be (weak version) | The same initial-state view | **excluded** by `BegunComingToBe.possibleContingentFreePast`; survives only if every accessible history containing a present contingent thing has a never-generated contingent thing or a beginningless past at every populated moment (histories without contingent things satisfy the rival trivially) | the premise itself |
| Begun populated pasts (begun H2 denied) | A beginningless past at every populated moment: metrically infinite (endless days), or metrically finite and open below (no first moment, like `(0, t]`), as in standard FLRW cosmology; also empty beginningless time before a first event | **excluded under the open premises** coinitial Reaper pieces, coinitial Reaper patchwork and countable coinitiality, by `GrimReaperPatchwork.populatedPastsBegunOfPatchwork`; with A3′b this gives A3′w (`possiblyBegunOfEarlierGrounds`) without carrying the possibility of a necessary being (`GrimReaperPatchwork.controls` 3). Kept objections to the typed premises (order-theoretic, so blind to metric finitude): a populated FLRW history, which physical theory treats as possible, is excluded by them (a cost of these necessity claims, not of A3′w); and given the possibility of populated continuous time with a first moment, the Benardete parity makes them doubtful for open-below finite pasts. The metric case alone (an endless succession of days) is **excluded under the open spaced Reaper premises** by `MetricGrimReaper.populatedPastsMetricallyFiniteOfPatchwork`, which leave open-below finite pasts and continuous time with a first moment untouched (`MetricGrimReaper.controls` 2, 3); no undercutting objection to them is identified, and one rebutting objection is recorded (law-consistent populated models with an infinite past, resting on the same principle as the FLRW row). Metric finiteness reaches A3′w only through the open bridge from metrically finite to begun pasts, which FLRW denies. All premises remain OPEN | `populatedPastsBegunOfPatchwork`, `populatedPastsMetricallyFiniteOfPatchwork` |
| B1 possible beginning | Contingent reality is beginningless in every possible history | survives | `LocalFramePossibleExternalCause.necessaryConcrete` |
| B2 causal opportunity | Beginnings are possible and always brute | survives | `LocalFramePossibleExternalCause.necessaryConcrete` |
| J1 supporters of the necessary are necessary | A necessary thing is supported somewhere by a contingent thing | survives | `NecessaryConcreteUnderived.checks` |
| J2 support among necessary things is well-founded | Two necessary things support each other. Two shapes: support in both directions within one world, or a direction that varies between worlds. A formal alternative only: no independent justification for its mechanism is recorded, so it is not a substantive objection (see Next investigations, item 2) | model survives against `checks` (shows J2 is needed there, not that J2 is doubtful); **excluded** with F1 and actual well-founded grounding by the no-novel-edge premise (`mutualSupportExcluded`). Compatible with the join's conclusion (`Control.rootedPair`), so, given the regress premises, it defeats that conclusion only when the actual necessary root is itself supported elsewhere, which denies coverage (a holder may instead reject a regress premise). The weaker discriminators (well-founded support at every world, no reversed pair) fail (`Control.rotatingTriangle`) | `NecessaryConcreteUnderived.checks`; `NecessarySupportCoverage` |

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

1. The two horns left to the initial-state view under A3′ now have prices
   (2026-11-11, see A3′a and A3′b above). Next: move foundedness from moments
   to discrete events, so that a dense past with a first moment is not
   excluded, and compare with A3′. Weaken the precedence
   bridge to "some earlier state". Done (2026-11-12): a patchwork vocabulary
   over accessible worlds (`GrimReaperPatchwork`) gives the Reaper genuine
   derivations of founded and begun populated pasts, and an H1 price for A3′w
   that does not entail possible necessary being. Done (2026-11-12): the metric
   version (`MetricGrimReaper`) separates metrically infinite pasts from
   open-below finite ones; it concludes metric finiteness, not begun pasts.
   Next for the Reaper: weigh the bridge from metrically finite to begun
   populated pasts against the FLRW objection, or formulate a metric arrival
   that needs no empty moment; compare the warrant of law-consistency as a
   guide to possibility with recombination (the recorded rebutting objection);
   a begun-past counterpart of state-causal finitism. Try
   `BoundedPastResource.noUniformGrowth` as an independent price on H2.
2. For the rows marked "survives", look for commitments the rival's holder
   accepts that conflict with it. The join models depend on the support relation
   reversing direction between worlds, so an invariance premise is the first
   discriminator for J1 and J2.
   For J2 this is done (`specs/necessary-support-coverage.toml`). One-way
   invariance (no novel edge) excludes the mutual-support rival. Coverage is
   incomparable with J2 in strength and is enough for the join's conclusion
   without J2. Coverage quantifies over every carrier world, and its
   contrapositive is close to the endpoint's own cross-world clause: it is the
   weakest sufficient premise found so far, and its warrant has not been compared
   with J2's. Given the regress premises (population, actual well-founded
   grounding, every contingent concretum grounded, excluded middle), a holder of
   the rival must deny coverage to block that conclusion; a holder can instead
   reject one of those premises. Contingent grounding edges alone do not deny
   coverage: in `Control.rootedPair` the edges change between worlds and coverage
   holds. Its formal denial is a necessary concrete thing with no actual concrete
   supporter that has one elsewhere. Unformalised analyst sketch: an
   essence-based account of dependence between necessary beings might give no
   novel edge (as sketched it is a two-way invariance, stronger than no novel
   edge), and with F1 and J1 coverage; the rival's world-varying shape simply
   denies such an account.
   Objection status (substantive objection standard, 2026-11-12): no substantive
   objection to J2, to no-novel-edge or to coverage is recorded, and no
   independent warrant for coverage or no-novel-edge is recorded either; their
   motivation is open. The
   mutual-support rival names J2 and a definite mechanism (a cross-world cycle in
   the union of support edges), but the corpus supplies no independent
   justification that support between necessary concrete beings ever runs in a
   circle or reverses between worlds; "interdependence" is a label, not an
   argument, and no source is read. The models (`mutualPair`, `rootedPair`,
   `rotatingTriangle`) are finite formal interpretations: they show which
   premise a theorem needs, not that the premise is doubtful. The denial of
   coverage likewise has no recorded independent motivation. Next: whether
   grounding-contingentism (candidate leads Leuenberger 2014 and Skiles 2015,
   from memory and unread; read before citing) independently motivates the
   world-varying shape, and so a denial of coverage; if no such account is
   found, record that plainly. Also: whether J1
   can be weakened to its selected-world instance, which is the only instance
   the coverage route from necessity uses.
3. Done: the ungrounded individual of the join is the stage-two root (see "The
   join"). Done: the sense links were cleaned and the composition registered
   (result `57213a13-fda3-4d8d-86ec-7f4462a3e7a1`). The underived premise and the
   act-of-being bridges now read the same `m.grounds` over the same world-relative `ExistsAt`.
   Open: the four older arguments to the endpoint keep legacy allowlist entries,
   because their intermediate statements and the act-priority record (POTENCY_1
   on a generic `InPotency` parameter) still link several senses. Cleaning those
   records, or splitting the compound disambiguations, would clear more of them.
