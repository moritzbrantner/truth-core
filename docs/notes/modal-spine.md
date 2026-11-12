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
| Metrically finite populated pasts | Spaced local pieces, spaced patchwork (linear time, one real clock for the frame) | `MetricGrimReaper.populatedPastsMetricallyFiniteOfPatchwork` | derivation; both OPEN. No separate countable-coinitiality premise: given a real clock (whose existence absorbs countable coinitiality), a metrically infinite past has a spaced descent by a theorem. Read with the privileged clock CLOCK_1. The spaced premises are weaker than the coinitial ones (strictly for local pieces and for the two premises jointly; patchwork alone not checked), and the conclusion strictly weaker than begun populated pasts (`spacedPiecesOfCoinitial`, `spacedPatchworkOfCoinitial`, `populatedPastsMetricallyFiniteOfBegun`; strictness by `MetricGrimReaper.controls` 2) |

Reach: the conclusion is *no populated past is metrically infinite*, not *every
populated past is begun*. For every register frame the spaced premises hold in a
populated open-below finite past (positive real times, the FLRW shape) and in
continuous time with a first moment (`MetricGrimReaper.controls` 2, 3), so, read
with CLOCK_1, the FLRW and Benardete objections have no target in them; their
warrant is a separate question (below). In control 2, metric
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

**Objection audit of the metric (spaced) premises.** Metric finiteness depends
on the clock: `arctan` makes integer pasts finite, `ln t` makes FLRW pasts
infinite. The disambiguation `CLOCK` (`725f3417`) separates CLOCK_1 (the
physically privileged duration, cosmic or proper time) from CLOCK_2 (any
order-preserving coordinate). The theorems hold for every clock, and the
statements and verdicts are read with CLOCK_1. A real clock exists only for
orders embedding in `ℝ`, so countable coinitiality is absorbed into the clock's
existence, not eliminated.

- **FLRW and the Benardete parity: no target, read with CLOCK_1** (controls 2,
  3). The typed premises' scope excludes metrically finite pasts.
- **Undercutting objection to the warrant of spaced patchwork: kept,
  conditional on L or C.** Here L is the principle that solutions of accepted
  laws are metaphysically possible. The only warrant on file is recombination,
  and recombination is blind to durations: spaced and accumulating descents hold
  the same pieces in order-isomorphic positions. So it warrants the coinitial
  and unrestricted instances equally, and those exclude a populated FLRW past
  and, given C, first-moment continua. The objection is answered only by a
  duration-sensitive principle: recombination of duplicates of one possible
  patch, room permitting, the spatiotemporal route of the #367 audit. That
  principle warrants spaced arrangements only, and only in proper time. Its
  countable generalization is not derived, and its bridge to the typed premise
  is not built.
- **Misner-type logarithmic time: kept as an objection to the clock choice,
  open.** It is a lead recorded from memory, not read. Under `ln t` the FLRW
  objection returns. The reply is that proper time is what the duplication route
  needs.
- **Rebutting objection: kept, conditional on L.** Accepted theories have
  populated solutions with a metrically infinite past (the Einstein static
  universe; eternal Newtonian motion). It is labelled like the FLRW row, which
  rests on the same principle. It names no failing piece or gluing step.
- **Unchanged:** the global-compatibility fork, the unsatisfiable-pair
  diagnosis (no mechanism), and the parity's transfer to infinite pasts (an
  unsupported suggestion).

See [the metric Reaper](../causal-regress-and-grim-reapers.md#the-metric-reaper-2026-11-12).

**Connection of the metric Reaper to the arrivals.** To Arrival A, two plans,
neither built: (1) a named bridge, *in every possible history a populated moment with a
metrically finite past has a begun past*, which with the metric conclusion
gives begun populated pasts and so A3′w with A3′b; this bridge is exactly what
the FLRW objection denies, so the FLRW cost is isolated there rather than
removed; (2) a metric arrival replacing the empty-moment step (A2 with A3) by a
premise about histories whose populated past has finite duration; blocked
because an open-below finite populated past has no empty moment, and no such
premise has been formulated. To Arrival B the connection is built (2026-11-12),
through B1 in the finite-duration sense BEGINS_2; see Arrival B below. It is
the only route by which the metric Reaper reaches the root, and there the
decisive premise is B2.

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

**What "begins" means in B1** (spec
`specs/modal-spine-metric-beginning-arrival.toml`, attempt
[`9d141c6c`](../../corpus/attempts/9d141c6c-7979-4d8b-a1b4-7b35ebc9fb21.json)).
As typed, B1 and B2 fix no sense of beginning: the Scenario has no times, and
its `beginsContingency` is an uninterpreted world predicate, which the existing
controls set to `True`. The arrival holds for every predicate. Before this
work, Arrival B concluded the Scenario statement `679eb3f7`, not
`STMT-NECESSARY-CONCRETE-AT`, so B1 and B2 did not reach the root. The
disambiguation BEGINS (`dc40914a`) records three typed senses and names a
fourth:

- BEGINS_1: the time before every populated moment of the history has a first
  moment.
- BEGINS_2: that time is of finite duration on the supplied clock, CLOCK_1
  intended. An open-below FLRW-shaped past satisfies it and not BEGINS_1; with a
  bounded clock it reduces to population.
- BEGINS_3: a schematic placeholder that fixes no sense, the Scenario predicate
  B1 and B2 use as typed.
- Not formalized: a first populated moment after emptiness, related to A3.

BEGINS_1 and BEGINS_2 constrain *time*, not when contingent reality began.
Integer time empty before 0 and populated from 0 on has contingent reality
beginning a finite time ago, yet satisfies neither. Non-negative real time
empty at 0 and populated after it satisfies BEGINS_1 with no first populated
moment.

| | Premises | Theorem | Status |
|---|---|---|---|
| B1 in sense BEGINS_2 (`951a2235`) | Metrically finite populated pasts (`4365c3c5`, the metric Reaper conclusion) and possible population (`faa1ff28`: some accessible history has a contingent concrete thing present at some moment) | `MetricBeginningArrival.possiblyBeginsFiniteDurationOfMetricallyFinite` (result `22dbb73a`) | derivation; the possibility premise is OPEN and alone does not suffice (control 1) |
| Stage-one conclusion | Euclidean access at the actual world (`1b1462e6`), F1, B1 and B2 in sense BEGINS_2 (`256b5bab`) | `necessaryConcreteOfFiniteDurationBeginning` (`8f77abb0`) | instantiation of `ActualEuclidean.externalNecessaryConcrete` at the Scenario whose predicate is BEGINS_2; B2 is needed (control 2: the frame premises and B1 hold, B2 and the conclusion fail); the bundle is satisfiable (control 3) |
| Possibly a necessary concrete being (`d2d7cf61`) | B1 and B2 in sense BEGINS_2 | `possiblyNecessaryOfFiniteDurationOpportunity` (`54bf1664`) | instantiation of `ExternalCandidateNecessity`; no frame premise |

Controls: `controls` (`ebf324e3`); strength order: `8da13191`. B2's
totality-cause relation is an unconstrained parameter. B2 for any relation
gives B2 for the relation that always holds (`trivialCauseOpportunity`), and the
arrival uses only that. So the content B2 adds to B1 is "possibly a BEGINS_2
history contains an existing concrete individual outside the contingent
totality". That is close to stipulating the possibility of the target. The
label of `256b5bab` therefore names no cause.

B1 in sense BEGINS_1 (`b58d1aac`) strengthens B1 in sense BEGINS_2 in linear
time (`possiblyFiniteDurationOfFirstMoment`; strict by control 2). That is the
only passage between the senses.

What the connection buys. The metric Reaper now reaches the root (the spaced
premises, possible population and B2 in sense BEGINS_2 are root-reaching
premises), but only through Arrival B, and the decisive premise there is B2,
which with B1 contains the possibility of a necessary concrete being. A rival
who denies that possibility rejects B2 in sense BEGINS_2 outright; the arrival
does not discriminate against that rival. B1 in sense BEGINS_2 is the cheap
premise. Given the metric conclusion, every accessible populated history is a
BEGINS_2 history (an analyst observation from the definitions, not
registered). Under L, which the FLRW objection to begun pasts itself uses, a
possible populated FLRW history gives B1 in sense BEGINS_2 with no Reaper
premise (not formalized). The Reaper's contribution is interpretive. It makes
the possible populated histories BEGINS_2 histories, the sense in which a
causal-opportunity principle for beginnings would apply to them if one were
granted for BEGINS_2 histories. No warrant for such a principle is on file.

Objection and warrant audit (Substantive Objection Standard):

- **B1 in sense BEGINS_2.** No substantive objection identified: no recorded
  argument says that in every possible populated history the time before some
  populated moment is metrically infinite. The open Misner-type objection
  targets the clock choice (CLOCK_1), not this step. The Reaper route inherits
  the undercutting objection to spaced patchwork.
- **Possible population.** No substantive objection identified.
- **B2 in sense BEGINS_2.** No positive warrant is on file. The reviewed
  2026-11-11 audit of the parameter-sense premise applies unchanged
  ([positive modal causal opportunity](causal-temporal-rival-coverage.md#positive-modal-causal-opportunity-independent-warrant-audit-2026-11-11),
  attempt `169b007b`):
  - *Causal marker and beginning predicate do no work.* By
    ExternalCandidateNecessity, calling the external candidate a cause supplies
    no reason why it is possible. Here the cause relation is an unconstrained
    parameter (`trivialCauseOpportunity`).
  - *Source-availability defeater against the warrant.* Causal uniformity from
    ordinary caused beginnings preserves the effect's intrinsic character, but
    not a producer, once every contingent producer is removed from the
    prehistory. A necessary producer would solve this, but its admissibility is
    the question at issue.
  - *Contingent-natural restriction rival, with motivation.* Ordinary causal
    generalization is restricted to histories where bearers and conditions are
    available. That restriction is motivated by the difference between
    producing within an inventory and producing the first inventory. Its price
    is an explanatory stop at an initial contingent inventory, or an intrinsic
    account of it still to be specified.
  - *First-instant objection to the warrant* (Grünbaum-type, analyst
    formulation, not read from a source). An open-below finite past has no
    instant at which contingent reality comes to be. A uniformity argument from
    ordinary beginnings, which come to be at an instant after an earlier state,
    therefore has no matching instance among BEGINS_2 histories that are open
    below. This targets B2's warrant, not the typed premise, whose cause
    relation has no temporal constraint.

  The brute-beginning rival survives as a model (control 2). That shows B2 is
  needed, not that it is false.

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
| J1 | Whatever concrete thing supports the being of a necessary concrete thing is itself necessary. | open; strengthens its selected-world instance J1@w (`84751fc2`, only actual supporters and actual support edges), strictly (`NecessarySupportActualScope`). J1@w suffices on the coverage route from necessity; it does not suffice on `checks`, its from-necessity assembly or the coverage bridge from no-novel-edge (below), and whether an intermediate scope does is untested | recorded; see the rival table |
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

J1 quantifies over every carrier world: a concrete thing that supports a
necessary concrete thing at any world, accessible or not, is necessary. Its
selected-world instance J1@w constrains only supporters existing at the actual
world and support there; it is the existing `STMT-ACTUAL-NO-CONTINGENT` on the
concrete subtype. `NecessarySupportActualScope.actualOfNoContingent` registers
the strength order; `Control.offWorldContingent` makes it strict.
`underivedFromNecessityOfActualCoverage` reaches the join's conclusion from
`STMT-NECESSARY-CONCRETE-AT`, actual well-founded grounding, J1@w, coverage and
excluded middle, composing the existing `actual_source_not_not` (an actual
necessary concretum with no actual concrete supporter) with coverage; so the
coverage route from necessity no longer needs J1. J1@w cannot replace J1 on the
other routes: in `Control.lateSupport` J1@w holds with every other premise of
`checks`, of its from-necessity assembly and of `coverageOfNoContingentNoNovel`,
while J1, coverage and the conclusion fail (each of those arguments now records
`strong_version_needed`). This shows the selected-world instance does not
suffice there, not that J1's full all-world scope is needed: an intermediate
scope (supporters at accessible or admitted worlds only) is untested.
`underivedOfCoverage` uses no form of J1. See the
[J1 attempt](../../corpus/attempts/b7e250b6-39f2-4e16-8da4-0a1f7a21d83a.json).

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

Every open premise of the spine now has a recorded rival and one Lean-verified
test. "Survives" means **needed in a model**: one finite interpretation
satisfies the rival together with the other premises of the named consuming
theorem while that theorem's conclusion fails. It shows the premise is needed
there and that the rest does not exclude the rival. It is an established fact
about one formal interpretation, not a judgment that the premise is doubtful
and not evidence against it (substantive objection standard, AGENTS.md). It
refutes nothing, and it does not test the rival against the whole route.
"Excluded" names a checked incompatibility. No rival is refuted and no premise
is established. Whether a rival is a substantive objection is a separate
question, recorded for stage two in its own column below.

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
| Begun populated pasts (begun H2 denied) | A beginningless past at every populated moment: metrically infinite (endless days), or metrically finite and open below (no first moment, like `(0, t]`), as in standard FLRW cosmology; also empty beginningless time before a first event | **excluded under the open premises** coinitial Reaper pieces, coinitial Reaper patchwork and countable coinitiality, by `GrimReaperPatchwork.populatedPastsBegunOfPatchwork`; with A3′b this gives A3′w (`possiblyBegunOfEarlierGrounds`) without carrying the possibility of a necessary being (`GrimReaperPatchwork.controls` 3). Kept objections to the typed premises (order-theoretic, so blind to metric finitude): a populated FLRW history, which physical theory treats as possible, is excluded by them (a cost of these necessity claims, not of A3′w); and given the possibility of populated continuous time with a first moment, the Benardete parity makes them doubtful for open-below finite pasts. The metric case alone (an endless succession of days) is **excluded under the open spaced Reaper premises** by `MetricGrimReaper.populatedPastsMetricallyFiniteOfPatchwork`, which leave open-below finite pasts and continuous time with a first moment untouched (`MetricGrimReaper.controls` 2, 3); read with the privileged clock CLOCK_1; kept against them: an undercutting objection to their warrant (duration-blind recombination supports the refuted coinitial and unrestricted instances equally; answered only by duplication recombination, room permitting), the open Misner-type objection to the clock choice, and a rebutting objection conditional on L (law-consistent populated models with an infinite past, like the FLRW row). Metric finiteness reaches A3′w only through the open bridge from metrically finite to begun pasts, which FLRW denies. All premises remain OPEN | `populatedPastsBegunOfPatchwork`, `populatedPastsMetricallyFiniteOfPatchwork` |
| B1 possible beginning | Contingent reality is beginningless in every possible history | survives in the typed sense, where "begins" is the schematic placeholder BEGINS_3. BEGINS_1 and BEGINS_2 concern the time before populated moments, not the beginning of contingent reality, so the rival as stated is not their negation: a history empty for infinitely long and then populated has a beginningless time but not beginningless contingent reality. The negation of B1 in sense BEGINS_2 is: in every possible populated history the time before some populated moment is metrically infinite (CLOCK_1). That is **excluded under** the open spaced Reaper premises and possible population, by `MetricBeginningArrival.possiblyBeginsFiniteDurationOfMetricallyFinite` with `populatedPastsMetricallyFiniteOfPatchwork`. An open-below finite past (FLRW) satisfies BEGINS_2 and fails BEGINS_1. The sense "first populated moment after emptiness" is not formalized | `LocalFramePossibleExternalCause.necessaryConcrete`, `necessaryConcreteOfFiniteDurationBeginning` |
| B2 causal opportunity | Beginnings are possible and always brute | survives, in every sense of "begins": in sense BEGINS_2 it is satisfied by the FLRW-shaped `MetricBeginningArrival.controls` 2. B2 with B1 contains the possibility of a necessary concrete being (`possiblyNecessaryOfFiniteDurationOpportunity`). No positive warrant is on file | `LocalFramePossibleExternalCause.necessaryConcrete`, `necessaryConcreteOfFiniteDurationBeginning` |
| J1 supporters of the necessary are necessary | A necessary thing is supported somewhere by a contingent thing (replaceable support: a necessary whole sustained by constituents that might not have existed). The recorded models (sustained whole, `NecessaryWholeReplacement`) put the contingent support at the actual world. Two shapes: a necessary whole whose numerical identity survives replacement of its sustaining constituents, or a necessary concretum with a fixed essential supporter plus additional contingent (partial or redundant) contributors. No independent justification is recorded for either shape (`underived-essence-identity.md`, Replaceable support, items 2–3), so it is not a substantive objection | model survives against `checks` (shows J1 is needed there, not that J1 is doubtful). Against J1@w (weak version): compatible when the contingent support is only at other worlds (`Control.offWorldContingent`, with the join's conclusion); conflicts only in its actual-world form | `NecessaryConcreteUnderived.checks`; `NecessarySupportActualScope` |
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

### Stage two: objection audit (2026-11-12)

The stage-two rows predate the substantive objection standard. Each was audited
against it ([audit attempt](../../corpus/attempts/b6384b6b-ef1a-405e-8237-0c2127d86b5f.json))
and then challenged and repaired.
Columns:

- **Model**: the rival survives in the named consuming theorem, so the premise
  is needed there (see the semantics above). Every stage-two row has this.
- **Objection status**: *substantive* when the rival names the premise, gives a
  mechanism and has independent justification on file (a sourced claim or a
  read source), and the mechanism bears on the premise as formalized;
  *partial* when such support is on file but a named bridge between it and the
  premise is open; *formal alternative* when only the model is on file (no
  substantive objection identified); *misdirected* when the motivation cited for
  the rival bears on another sense or another premise. Leads named for formal
  alternatives are unread and carry no weight, and no inference is drawn from
  them. No row is fully substantive, and no row has an established
  counterexample.
- **Warrant on file**: sourced claims stating the premise, and verified
  derivations of it from other premises that are themselves open. A sourced
  claim attributes the premise and its reason to a text; it does not establish
  the premise. No stage-two premise is established.

### Stage two: the root and the act of being

| Premise | Rival | Model (consuming theorem) | Objection status | Warrant on file |
|---|---|---|---|---|
| Something concrete exists | Only non-concrete things exist | `NecessaryRootFork.necessaryRootTrilemma` | Formal alternative. No independent justification on file. Its holder must deny that the bearer of an occurring thought is concrete. | No claim. Seven Cogito derivations from open premises. A foundational-warrant target. |
| The whole roster is not a borrowing trap | Every concrete thing has a concrete ground, without end or in a circle | `WholeRosterFoundation.necessaryConcrete` | Partial. Welchance 2026 (read, passage `WELCHANCE-INFINITISM-1-3`, [note](unique-feedback-explanation-311.md)) argues that an unexplained chain loses no more explanatory value than an unexplained foundation, and claims a uniformity virtue for infinitism. Open bridges: his relata are facts under "in virtue of", not concrete grounds of beings, and he concludes parity, not truth or possibility. | No claim. Three derivations from open premises. |
| Every contingent concrete thing has a ground | Some contingent concrete thing is ungrounded (a brute fact) | `ActualRootNecessityUpgrade.upgrade` | Partial. Schmid's existential inertia (read, [eternity note](../eternity-dependence-connection.md)) gives a mechanism: a thing's persistence is explained by its earlier existence and the absence of a destroying cause, with no concurrent sustainer. Open bridge: whether grounding under `m.grounds` is concurrent sustenance by a distinct ground; if an earlier existent can be the ground, Schmid does not contest the premise. Hume (claim `HUME-TREATISE-I-3-3-NARROW-A`) argues only that the causal maxim is not demonstrable from ideas: a limit on one kind of warrant, not evidence of an ungrounded thing. Oppy 2020 (read) is support neither way: every possible world shares the actual initial history (claim `OPPY-2020-SHARED-LAWS-INITIAL-HISTORY`), but the claim and `DEF-OPPY-CAUSAL-MODAL-COMPARISON` withhold numerical identity of one bearer across worlds, so whether his uncaused initial state is a necessary individual (allowed by the premise) or a contingent ungrounded one (the rival) is an unresolved bearer-identity bridge. | No claim. Three derivations from open premises. |
| The maximum in being causes all other being | The maximum is idle: a third thing causes another's being | `TermSenseForks3.maximeEnsCausesAllMaximal` | Formal alternative. Lead, unread for this purpose: a first mover that is a final cause only (Aristotle, Met. XII.7). | No claim. Four derivations from open premises. |
| What exists is in act as to being | Thin existence: something exists with no act of being | `Round2ExistenceAct.intellectualExerciseRequiresActFromExistence` | Formal alternative. The rival's sense is fixed by its definition (`f5345c9c`, thin existence: things exist, but existing is not an actuality they have). The stage-two bundle shares one `InAct` and one esse respect, so a thin theorist contests the bundle of existence-to-act, perfection transfer and infinity together, not another sense. No sourced justification for the thin view is on file. | No claim. Three derivations from open premises, two through the sourced q.4 a.1 ad 3 premise. |
| A cause of a thing's being is its concrete ground | A non-concrete cause of being (a law or abstract object) | `Round2Grounding.contingentGroundedViaParticipation` | Partial, on an analyst construction. Phaedo 100d–e (claim `PLATO-PHAEDO-100D-PARTICIPATION-EXPLANATORY`) makes a Form explain a thing's being so; explaining being so is not shown to be causing esse. Rosen reports, without endorsing, that on Lewis's account events are sets (claim `SEP-ABSTRACT-OBJECTS-32-LEWIS-EVENTS-ARE-SETS`); two stacked bridges are open: causing events is not causing esse, and impure sets are not shown non-concrete in the adopted sense ([boundary note](causal-concrete-rival-boundary.md)). Only the analyst's construction connects Lewis to the premise. Aristotle's sourced critique (Met. I.9) is on file against the Phaedo account. | No claim. One derivation from four open premises. |
| Grades of being imply a maximum | Unbounded grades: everything is exceeded | `SelectedAncestryUnique.uniqueRoot` | Formal alternative. Comparatives without a maximum are established (the natural numbers under <), but they bear only on a general rule for "more and less", which nothing on the route uses: both derivations are specific to being. They show that a general more-and-less warrant would not suffice. No case of unbounded grades of being is on file. | No claim. Two derivations from open premises (no infinite ascent; approach to a primary). |
| A universal cause of being causes the effect's perfections | Mere conservation: a secondary cause supplies a perfection | `CausalPerfectionTransfer.reconstruction` | Formal alternative. Lead, unread: medieval mere conservationism (Durandus). | No claim. Two derivations from open premises. |
| What is simply prior is a concrete ground | Something non-concrete is simply prior to a concrete thing | `NecessaryFirstBeing.necessaryFirst` | Formal alternative. The Phaedo claim says nothing about priority; reading its explanation of being so as simple priority would be an unsupported bridge. | No claim. Two derivations from open premises. |
| Whatever is God is maximal in being | A god exceeded in being by something not God | `StageTwo.GodIsSimple.godIsSimple` | Misdirected. Finite and demiurgic gods use another sense of "god". GOD_4 is a primitive field (`DEF-GOD-OF-CLASSICAL-THEISM`) whose content is fixed only by open premises, here the attribute premise `STMT-GOD-HAS-CLASSICAL-DIVINE-ATTRIBUTES` (infinite, perfect); the misdirection holds only given that premise. Which being deserves the name is the naming premise's question. | No claim. Two derivations from open premises. |

### Stage two: the attributes and the name

All fourteen models are conjuncts of `SpineRivalsAttributes.controls`.

| Premise | Rival | Model (consuming theorem) | Objection status | Warrant on file |
|---|---|---|---|---|
| Nothing has actuality except insofar as it is | Actuality without being (Meinongian) | `existingInActAtFromSomeAct` | Formal alternative. Lead: Meinong's independence of so-being from being (candidate `MEINONG-GEGENSTANDSTHEORIE-3`, unread); reading "in act in a respect" as so-being would be an analyst bridge. The recorded conditional refutation rests on two open premises. | Aquinas q.3 a.4, q.4 a.1 ad 3. Two derivations. |
| An effect's perfections preexist in its cause | Strong emergence | `causeOfBeingHasWhatItGives` | Formal alternative. Lead: Broad 1925 (candidate `BROAD-MIND-AND-ITS-PLACE-CH2`, unpinned). Relevance depends on `DISAMB-IN-ACT`: the premise allows eminent possession. | Aquinas q.4 a.2. One derivation. |
| Goodness is actuality | Actuality is not sufficient for goodness | `godIsSupremelyGood` | Formal alternative. Leads, unread: Hume's is/ought and Moore's open question (the rival's cited motivation), and positive-evil objections to privation theory. Whether the first two concern GOOD_1 at all is not checked. | Aquinas q.5 a.1. Two derivations. |
| Every composite has a uniting cause | Uncaused composition | `godIsSimple` | Partial, against the premise's reason. Schaffer (claim `SCHAFFER-14-BASIC-WHOLE`, read) makes the cosmos a basic composite whose parts depend on it, so no prior diverse parts are brought together. Open bridge: basic means ungrounded, not without an efficient cause of being; Schaffer offers no explanation of cosmic existence. | Aquinas q.3 a.7. Five derivations from open premises. |
| Matter-form and essence-existence differences are compositions | A real difference without composition | `firstMoverSimple` | Formal alternative. Lead, unread and unverified: Scotus's formal distinction. | Aquinas q.3 a.7. One derivation. |
| No component is the first being | A first being that is a component of something (world-soul) | `attributesFromFirst` | Formal alternative. The positions are attested only through Aquinas's own report in q.3 a.8; their reasons are not on file. Lead: Spinoza (source registered, no claim). | Aquinas q.3 a.8. One derivation. |
| The immaterial is intellectual | Intellect only in material composites, and something altogether immaterial | `godHasIntellect` | Partial. The recorded rival has two conjuncts. Papineau (claim `PAPINEAU-RISE-CAUSAL-POWERS-PHYSICAL`) supports at most the first, that intellect requires the physical; the bridge from physical to composed of matter and form is open, and nothing on file supports the second, that some altogether immaterial thing exists without intellect. A further partial objection on file is not the recorded rival: Plotinus V.4.2 (claim `PLOTINUS-V4-INTELLECT-NOT-FIRST`, read) argues that intellect is two, thinking and intelligible, so the absolutely simple first is not intellect. Open sense bridge: the claim's intellect is the Plotinian thinking/intelligible structure (`DISAMB-PLOTINIAN-PRIORITY-UNITY`, `DEF-PLOTINIAN-INTELLECT-DUALITY`), which the corpus distinguishes from every account of cognition; nothing shows that stage two's primitive `HasIntellect` entails that duality or a composition in stage two's sense. Only with that bridge would it bear on the joint simplicity and intellect conclusions. It is an argument, not an established case. | Aquinas q.14 a.1. Four derivations. |
| Will follows intellect | Intellect without will | `godHasWill` | Formal alternative. No independent justification on file. Leads, unread: Aristotle's self-thinking first mover (Met. XII.9); Plotinian procession by necessity. | Aquinas q.19 a.1. One derivation. |
| Act is simply prior to potency | Potency prior to act | `firstBeingNoPotency` | Partial. Aristotle states the aporia (claim `ARIST-MET-1071B-POTENCY-PRIOR-A`): whatever acts is able, but not whatever is able acts. Its grounds constrain only ability and act, not simple priority (`ATTEMPT-NIGHT-COSMOGONY-BUNDLE-ELIMINATION`); the claim reaches simple priority only through an analyst reading step, so the bridge from ability to simple priority is open. The Night-generation bundle is excluded by a zero-axiom core Γ of three open premises, without the target; the bare rival survives that core in `MODEL-NIGHT-COSMOGONY-RESIDUAL`. Aristotle rejects the aporia in the same passage. | Aquinas q.3 a.1, q.4 a.1 ad 2; SCG I.16. Four derivations. |
| Nothing is in act and potency in the same respect | Act and potency in the same respect | `firstBeingNoPotency` | Formal alternative. Lead: Scotus, Quaest. Metaph. IX q.14 (candidate `SCOTUS-QQ-METAPH-IX-Q14`, no witness): virtual act with formal potency. On the virtual reading of `DISAMB-IN-ACT` it dissolves rather than rivals (`ATTEMPT-RIVAL-TRIAGE-497`). | Aristotle, Phys. III.1; Aquinas q.2 a.3. Two derivations. |
| Subsistent being is infinite | A finite subsistent being | `firstMoverPerfectionFromInfinity` | Formal alternative. No justification on file. The dispute lies upstream, at `STMT-ESSE-LIMITED-ONLY-THROUGH-RECEPTION`, which both derivations use. | Aquinas q.7 a.1. Two derivations. |
| The immutable is eternal | Immutable without eternity | `godIsEternal` | Formal alternative. Leads, unread and unverified: Shoemaker on time without change; the everlasting-God view (Wolterstorff). | Aquinas q.10 a.2. One derivation. |
| "God" names the fully described principle | The full nominal naming fails | `properDescriptionExcluded` | Partial. The rival is derived (verified, argument `a9b8530b`) from the practice-use thesis WF-P1 plus two further open premises (proper application preserved by practice reference; a satisfier of the full description exists). WF-P1 is an unattributed reconstruction that Phillips's reported remark supports but does not state (claim `SEP-RELIGIOUS-LANGUAGE-4-1-PHILLIPS-NO-OBJECT-A`, secondhand). | No claim. Four arguments: one from the reduced-description premise alone, two through GOD_2 and GOD_3 bridges, and a GOD_1 transcription. |
| The nine attributes suffice for the classical attributes | The nine attributes fall short | `ClassicalAttributes.godHasClassicalAttributes` | No substantive objection identified, to the premise or to the bridges that now derive it (one interpretation dependence, below). Since 2026-11-12 the premise has a derivation. The primitive field stays undefined; what is defined is `DeiFiliusAttributes`, a typed reading of the Dei Filius ch. 1 list (see [the Dei Filius attributes](#stage-two-the-dei-filius-attributes)). The premise follows from the field interpretation (a stipulation about the primitive on its full-list reading) plus seven named bridges. On the nine-reading that `Root.lean` documents, the premise is close to analytic instead. | No claim states it or any of its bridges; motivated by Dei Filius ch. 1 (claim `VATICAN-I-DEI-FILIUS-CH1-ONE-TRUE-LIVING-GOD`). One derivation (`classicalAttributesSufficeOfDeiFilius`) from open premises. |

**Where stage two is contested.** Of the 24 rows, none has a fully substantive
objection. Seven have partial support on file, each with a named open bridge:
whole-roster nontrapping (Welchance), contingent grounding (Schmid), the
esse-cause bridge (Phaedo, Lewis), the uniting cause (Schaffer), the
immaterial-intellect premise (Papineau; Plotinus through a rival not yet
recorded as such), act's priority (Aristotle's aporia) and naming (Phillips).
One is misdirected (God's maximality, given the attribute premise). Sixteen are
formal alternatives with no substantive objection identified; for sufficiency
the open question is warrant, not objection. The Plotinian objection would be
the most consequential if its sense bridge held, since it would then target the
joint conclusion of simplicity and intellect, not one bridge. On the warrant
side, no root or act-of-being premise is stated by a sourced claim. Twelve of
the fourteen attribute premises are, and every stage-two premise has at least
one derivation from other open premises (sufficiency since 2026-11-12).

The four bare-negation rivals (will, infinity, eternity, sufficiency) get no
typed vocabulary. For will, infinity and eternity no replacement account with
independent justification is on file, so typing one would add a placeholder.
For sufficiency the gap was the undefined field. The field stays undefined, but
the full Dei Filius list is now a defined predicate (below), and on that reading
of the field the rival "the nine fall short" becomes, conjunct by conjunct, the
denial of one named bridge.

### Stage two: the Dei Filius attributes

`TruthCore/Causality/DeiFiliusAttributeField.lean` defines `DeiFiliusAttributes`,
one field per attribute that Dei Filius ch. 1 confesses (DS 3001; goodness from
DS 3002), as recorded in claim `VATICAN-I-DEI-FILIUS-CH1-ONE-TRUE-LIVING-GOD`,
in the typed reading of definition `edcfac86`. The primitive
`Signature.HasClassicalAttributes` stays undefined (the skeleton is frozen).

**The field's content is a fork** (disambiguation `2cbf40b4`, CLASSICAL_FIELD).
`Root.lean` documents the field as "intended to group simplicity, perfection,
goodness, infinity, immutability, eternity, unity, intellect and will": exactly
the nine (CLASSICAL_FIELD_1). The Dei Filius motivation is in
`ClassicalAttributesSuffice`'s docstring, `DEF-CLASSICAL-ATTRIBUTES-BUNDLE` and
the claim (CLASSICAL_FIELD_2, the full typed list). The open **field
interpretation** `FieldFromDeiFilius` (whatever has every typed Dei Filius
attribute has the field) is stated on the full-list reading. On the
nine-reading the old premise is close to analytic, the field interpretation
follows at once and the bridges below do no work for sufficiency. The field
interpretation is strictly weaker than the old premise: `fieldOfSuffice` is
lake-checked but deliberately not registered (as an argument it would close a
support cycle), so that direction is not Comparator-verified; strictness is
registered in `Control.Controls`. Analyst readings, attribution deferred.
*Verus* is not an attribute: it is the `IsGod` predicate (GOD_4) of which the
attributes are confessed.

| Dei Filius | Typed as | At any being with the nine (`nineGiveDeiFilius`) | At the spine's root (`deiFiliusRoot`) |
|---|---|---|---|
| unus, una singularis | `IsTheOneGod` | one of the nine | one of the nine |
| vivus | primitive `Lives` (LIVING_1, timeless) | open bridge: whatever has intellect lives (q.18 a.3) | same bridge; or (second route) from the root's pure act through LIVING_2 and a restricted sense bridge (below) |
| creator caeli et terrae | `IsCreatorOfAll`: causes the being of everything else (weaker: no creation from nothing) | contained by definition in the goodness conjunct | same |
| Dominus | primitive `IsLord` | open bridge: creator of all is lord (q.13 a.7) | same bridge |
| omnipotens | `IsAlmighty` (active power; no clash with immutability, which excludes passive potency) | from infinity by the existing `STMT-INFINITE-ACT-HAS-INFINITE-POWER` (itself derived from three open premises) | same |
| aeternus | `Eternal` | one of the nine | one of the nine |
| immensus | primitive `Immense` | open bridge: creator of all is immense (q.8 a.1-2) | same bridge |
| incomprehensibilis | primitive `Incomprehensible` | open bridge: the infinite is incomprehensible (q.12 a.7) | same bridge |
| intellectu ac voluntate omnique perfectione infinitus | `HasIntellect`, `HasWill`, `IsPerfect`, `Infinite` (weaker: infinity of intellect and will as such untyped) | four of the nine | four of the nine |
| simplex omnino, incommutabilis | `IsSimple`, `IsImmutable` | two of the nine | two of the nine |
| substantia spiritualis | `IsSpiritual`: not matter-form composed (weaker: substance untyped; alone it fits prime matter or an accident) | derived: simplicity and the q.3 a.7 matter-form clause | derived: the root excludes matter-form composition |
| re et essentia a mundo distinctus | DIFFERENT reading: `RemoteFromAll`; incomparable with the text, whose anti-pantheist content (DS 3001, canons DS 3023–3024) is untyped; a Spinozist God satisfies `RemoteFromAll` | open bridge: creator of all is a component of nothing (q.3 a.8) | derived: the root is remote from all |
| beatissimus | primitive `MostBlessed` | open bridge: the perfect intellectual is most blessed (q.26 a.1) | same bridge |
| super omnia excelsus | `IsMaximumIn` at being (weaker: not exceeded, rather than exceeding all) | goodness-is-actuality plus open bridge: excess in being is excess in act (q.4 a.2) | derived: the root is maximal in being |
| bonitate sua (DS 3002) | STRONGER: `IsSupremelyGood`, which also includes causing every perfection of everything else; DS 3002 names goodness as the motive of creation | one of the nine | one of the nine |

For *vivus* the corpus already has a typed, time-indexed route
(`SelfOperationLife`, result `PURE-ACT-LIVES-FROM-SELF-OPERATION`: life as
self-operation, derived for pure act as life present at some time of a duration
frame). It is recorded as the sibling reading LIVING_2 (`LivesSomeTime`,
disambiguation `1f2d3b9b`). The attribute structure keeps the timeless LIVING_1,
and the two senses are not identified.

Since 2026-11-12 a second route gives the root LIVING_1 from its pure act
(`DeiFiliusLivingSelfOperation`, `deiFiliusRootLivingFromPureAct`, spec
`specs/dei-filius-living-self-operation.toml`, attempt `6683acc4`). It composes
`deiFiliusRoot` without the intellect bridge and takes pure act from the root's
`immutable` conjunct. It then applies `STMT-PURE-ACT-LIVES` (LIVING_2, itself
derived from three open premises) and crosses to LIVING_1 by one explicit sense
bridge restricted to pure act (`ad49ea00`: whatever is in potency in no respect
and lives at some time lives). The restriction carries the motivation: without
potency, life can neither begin nor end (q.9 a.1,
`STMT-LIFE-BOUNDARY-REQUIRES-POTENCY`). The unrestricted bridge can fail for a
being that lived once. The controls show that without the bridge a pure act can
be LIVING_2 and not LIVING_1, and that the new route does not presuppose the
intellect bridge.

The route does not reduce the open premises: one bare bridge (intellect gives
life) is replaced by one bare sense bridge plus `STMT-PURE-ACT-LIVES`, which the
eternity routes already use. What changes is the connection: living now rests on
the root's derived pure act and q.18 a.3's account of life, not on an unanalysed
step from intellect.

Objection audit for this route: no substantive objection identified to the
instances used at the root. One scope point bears on the universal
`STMT-PURE-ACT-OPERATES`: an immutable, causally inert being (an abstract
object, if the domain has one) would have no potency and no operation. It does
not reach the root, whose witness is actual and concrete; a concrete-restricted
premise would suffice. Plotinus (the One as source of life, *Enn.* VI.7) is an
unread lead that would need a sense bridge like the one for intellect. No claim
states any premise of the route; q.18 a.3 supports three of them by relations.

On the full-list reading the warrant gap of the sufficiency premise is an exact
list. In general it is the field interpretation, seven new bridges and the
existing infinite-power premise (goodness-is-actuality and the q.3 a.7 premise
are already on the route). At the root it is five new bridges and the
infinite-power premise, where `classicalRootOfDeiFiliusRoot` recovers the old
endpoint from the new one and the field interpretation. On the nine-reading the
gap is the near-analytic old premise itself. The controls show each of nine
premises of `nineGiveDeiFilius` is needed there.

Objection audit: none of the bridges or the field interpretation has a
substantive objection on file.

- **The no-component bridge.** Q.3 a.8 itself (passage `AQUINAS-ST-I-Q3-A8`)
  reports three contrary positions: God as world-soul (via Augustine, *De civ.
  Dei* VII), God as the formal principle of all things (the Amalricians) and God
  as prime matter (David of Dinant). Its obj. 1 cites Dionysius: "the being of
  all is the deity", and the being of all enters each composite. The
  Amalrician position and obj. 1 have a clear target and mechanism: they can
  grant that God gives being to all and deny the consequent, since on them God
  gives being by being the things' formal being. Aquinas replies:
  - the efficient cause is not numerically one with the form of what it makes;
  - the first agent acts primarily and per se, which no component does;
  - no component is simply first;
  - (ad 1) deity is the being of all effectively and exemplarily, not by
    essence.

  No independent justification is on file: these positions are attested only
  through Aquinas's report. So this is a named formal alternative with a stated
  mechanism, not a substantive objection. Spinoza remains an unread lead and
  satisfies `RemoteFromAll` anyway.
- **The excess-in-act bridge.** It has an interpretation dependence from the
  quarta via's own picture of more and less in one perfection: with a binary
  `InAct` it holds only if respects separate grades. That bears on its reading,
  not its truth, and the bridge is not used at the root.

Warrant audit: no claim states any bridge; each cites the Summa article giving
its reason, unread into a pinned claim. The field interpretation is a
stipulation about an undefined primitive, on one reading of it. See the
[attempt](../../corpus/attempts/b93ce632-5793-4bdf-a79f-b52fa1abc907.json).

### Foundational-warrant targets

These premises have no source claim, and no derivation from premises that are
not themselves open (the concrete-population premise has seven Cogito
derivations, all from open premises). They are targets for investigating
foundational warrant, not established premises or choices the owner must settle
before research can proceed:

- F1 actual reflexivity. Fix the intended sense of possibility and test whether each recorded rival contests that claim or instead uses another accessibility relation.
- A1 presence gives existence. Compare the proposed non-presentist reading of existence with the presentist rival and test its applicability to the intended histories.
- Something concrete exists at the actual world. Make the intended sense of concrete explicit and assess its support and strongest objections.

The other unsupported premises (F2, A2, A3′, B1, B2, J1, J2, and the root and
act-of-being bridges) remain open positions to investigate under explicit
assumptions; for stage two, the objection audit above records which of them a
substantive objection on file actually contests. For each selected target, record the exact scope and applicability,
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
   Done (2026-11-12): the metric conclusion reaches the root through Arrival B
   with B1 in the finite-duration sense BEGINS_2 (`MetricBeginningArrival`);
   there B2 carries the possibility of a necessary being.
   Next for the Reaper: read and record the duplication (room-permitting) recombination principle and Misner's logarithmic-time argument; weigh the bridge from metrically finite to begun
   populated pasts against the FLRW objection, or formulate a metric
   counterpart of Arrival A's inert-emptiness step that needs no empty moment;
   look for a causal-opportunity principle for BEGINS_2 beginnings whose warrant
   does not already contain possible necessary being; compare the warrant of law-consistency as a
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
   found, record that plainly.
   J1 is done for its scope (`specs/necessary-support-actual-scope.toml`): the
   coverage route from necessity needs only J1@w, the selected-world instance;
   on the J2 routes and the coverage bridge from no-novel-edge J1@w does not
   suffice (`Control.lateSupport`); whether an intermediate scope suffices is
   untested. Objection status (substantive objection standard):
   the replaceable-support rival names J1@w and a mechanism (bottom-up support
   of a necessary whole by contingent actual constituents), but no independent
   justification is recorded that any concrete whole exists necessarily while
   its actual sustaining constituents are contingent; its recorded models fix a
   carrier label, not a defended identity criterion. No substantive objection to
   J1@w is on file. No independent warrant for J1@w is on file either: the
   strongest positive argument recorded (fixed indispensable existential
   dependence) covers particular essential supporters, not every actual
   supporter, and the 2026-11-11 assessment of J1 applies unchanged to J1@w,
   since its controls already place the contingent support at the actual world.
   Next: an independent identity criterion for a candidate necessary whole, or
   an argument that actual support of a necessary thing entails the supporter's
   indispensability, would discriminate.
3. Done: the ungrounded individual of the join is the stage-two root (see "The
   join"). Done: the sense links were cleaned and the composition registered
   (result `57213a13-fda3-4d8d-86ec-7f4462a3e7a1`). The underived premise and the
   act-of-being bridges now read the same `m.grounds` over the same world-relative `ExistsAt`.
   Open: the four older arguments to the endpoint keep legacy allowlist entries,
   because their intermediate statements and the act-priority record (POTENCY_1
   on a generic `InPotency` parameter) still link several senses. Cleaning those
   records, or splitting the compound disambiguations, would clear more of them.
4. Stage-two warrant work, ordered by the objection audit (2026-11-12). First,
   state the sense bridge between the Plotinian intellect
   (`DEF-PLOTINIAN-INTELLECT-DUALITY`) and stage two's `HasIntellect`, or record
   that none is warranted; only if it holds, record the Plotinian objection as a
   typed rival of the immaterial-intellect premise, tested jointly against the
   simplicity and intellect conclusions. Second, the bridges that decide
   whether the read sources bear on their premises: facts and grounds of beings
   (Welchance), ungrounded and uncaused (Schaffer), concurrent sustenance and
   `m.grounds` (Schmid), and ability and simple priority (Aristotle's aporia).
   Third, define the classical-attributes field from Dei Filius ch. 1, so that
   sufficiency has a warrant beyond stipulation or can fail by derivation. Done
   (2026-11-12, [the Dei Filius attributes](#stage-two-the-dei-filius-attributes)):
   the full Dei Filius list is a defined predicate (the primitive field stays
   undefined), and sufficiency is derived from the field interpretation and
   seven named bridges (five at the root) plus existing premises. That
   warrant gap holds on the full-list reading of the field; on the nine-reading
   that `Root.lean` documents, the premise is close to analytic. Next for it:
   typed content for the five primitives (life without change, under which the
   restricted bridge from LIVING_2, attempt `6683acc4`, could be derived or
   fail; dominion; presence and place; created intellects
   and knowability; beatitude); a world term for non-identity with the world
   (the anti-pantheist content); and whether the respects of `InAct` separate
   grades of being. The
   sixteen formal-alternative rows need a read source before they carry any
   weight; until then they show only where each premise is needed.
