# Event actualization: direction fork and its consumed consequence

This is #700's investigation on the First Way/regress route, especially
`STMT-NO-INFINITE-PER-SE-MOVER-SERIES`. It composes the existing
`CONSECUTIVE-MOVER-RESPECTS` (#591), `TEMPORAL-EVENT-CAUSAL-CONTROLS`, and
`successorChainNotWellFounded`; it does not replace their vocabulary or claims.
The actualization of potency is a claim about real change. The constructions
below are candidate interpretations only. The truth of their mathematical
certificates does not supply actual events, genuine causal edges or an adequate
explanation of their activity.

## Primary-witness audit before formalization

The existing immutable manifests were materialized and read in full for:

- `ARIST-PHYS-VII-1`, Greek *Physics* VII.1, especially 242a15–242b30/243a2.
  The local moved-mover regress concerns local motion. At 242a20–30 the moving
  of mover and moved is simultaneous; numerical identity of a movement involves
  its numerically same time. The first aggregate reductio is explicitly rejected
  at 242b19–24: many things may move simultaneously. The repaired reductio adds
  contact/continuity and an aggregate. **Rejected:** assigning every edge of that
  simultaneous dependency chain strictly earlier exercise times as though VII.1
  asserted that ordering. The current strict-forward profile is an analyst
  alternative for causal event production, not Aristotle's universal doctrine.
- `ARIST-PHYS-VIII-5`, Greek *Physics* VIII.5, especially 256a/256b (instrument
  and agent), 257a (same/different kinds of motion and recurrence), and
  257b–258b (parts of a self-mover). The stick/hand example requires the agent
  for instrumental movement; the discussion of unlike motion and recurrence
  adds reasoning beyond the four local predicates. **Rejected:** treating #591's
  alternating-respect control as a refutation of this entire chapter, or treating
  a pair of bare mover edges as proof of a real reciprocal actualization.
- `ARIST-PHYS-IV-11`, Greek *Physics* IV.11, 218b–220a, including 219a–219b:
  time is not motion but is connected with motion/change and number with respect
  to before and after; awareness of change and distinguishing earlier/later
  matters. **Rejected:** inferring presentism, eternalism, an objectively moving
  present, a common linear physical clock for every causal domain, or a ban on
  backward causation from this witness alone. The model's linear clock is explicit
  mathematical background, not a claim extracted from these sentences.
- `AQUINAS-ST-I-Q2-A3`, Latin *ST* I q.2 a.3, whole article, especially co.
  prima via: actual/potential non-coincidence is **simul** and **secundum idem**;
  potency is reduced to act by something actual; the stick/hand dependency is
  not stated as a temporal first-event argument. **Rejected:** dropping the same
  time/same respect restrictions, requiring the cause's completed process to be
  earlier than its effect's ongoing exercise, or reading the regress exclusion as
  a denial of every simultaneous interaction. The second way's prior-to-itself
  argument must not silently identify priority with an earlier clock time.

Exact edition/revision/path/blob and CTS identities remain in the existing
`corpus/passages/aristotle-physics.json` and
`corpus/passages/aquinas-summa-theologiae.json`. No source manifest, historical
claim or attributed Lean type changes. These are interpretive findings, not
source-integrity check conclusions. No copied translation is used as evidence.

## Common semantic profile and open bridges

One fixed world/profile is investigated; alternative modal worlds are not clock
instants. Beings, respects, particular event tokens and times are different type
parameters. A supplied `bearer`, `respect`, `onset`, `exercise`, and `attained`
map individuates the tokens. `Staged` explicitly requires potency at an earlier
onset, exercise no later than attained actuality, and actuality at attainment.
It says nothing about the cause token's attainment preceding its effect's
exercise. The finite staged control has onset −1, exercise 0, attainment 3:
causal exercise can overlap the effect while attainment is later.

`MotionProjection` is an **unattributed open** bridge from an event edge to the
existing canonical `MovesIn` predicate, sliced at the target exercise time and
respect. Four explicit time-slice premises lift the existing located-motion,
potency, actual-mover and non-coincidence conditions. Their use at an actual
world requires independently warranted event individuation, real causal meaning,
clock interpretation and physical/general-reduction scope. The Lean carrier
alone is not a population of real beings/events. `SustainsEvent` is not silently
identified with temporal production: the control uses a separately quantified
relation, equal to its circle only by stipulation, to test local activity.

### Reality-facing meaning and its limits (#690)

For an intended actualization application, an edge must concern **this** exercise
of a mover bringing about **this** change in the target, in an independently
identified respect. An ordinary candidate example is one match's ignition
initiating a nearby flame, which later burns another part of that same match:
being-level feedback does not identify the ignition token with its later burning.
An ongoing hand/stick interaction is an illustrative sustaining case in the
source audit; it need not finish before the stick acts. These examples orient the
interpretation, rather than certify a physical causal model or a universal law.
A clock tick preceding a spatially remote unrelated tick is a counterexample to
identifying temporal precedence with causation. Two recorded correlations alone
also fail to establish the particular actualization edge required here.

The finite-control edges are openly stipulated approximations of these intended
roles; their carrier inhabitants are not claimed to be real events. An adequate
realization bridge would need evidence of the particular occurrences, a causal
account distinguishing production/support from sequence/correlation, and reasons
that the target respects are genuinely the same or different. Event-production,
Humean regularity/counterfactual approaches, and simultaneous instrumental-power
accounts can disagree about which edges count or which time is relevant. No
universal structural property of actual causation is inferred from an example.
The proof assumes linearity only of the supplied clock order. It assumes no
transitivity, asymmetry, source existence or well-foundedness of `C`; strictness
and anti-retrocausation are independently open alternative profiles. It does not
generalize observed local causal direction to all metaphysical dependence.

## Certified fork, separate exclusivity, and actual use

`TEMPORAL-DIRECTION-FRAMEWORK` / `Framework.framework` quantifies over the SAME
`E`, linearly ordered `T`, `clock : E → T` and `C : E → E → Prop`:

1. `StrictForward`: every edge strictly increases its exercise clock;
2. `NoBackward ∧ HasSimultaneous`: no edge reverses time and some edge is simultaneous;
3. `HasBackward`: an explicit reversing edge.

Coverage uses classical quantifier negation and linear order, not an enum or a
list of historical positions. `DirectionExclusive` is proved separately.
The first horn includes `EventAcyclic`: Mathlib `Relation.TransGen C e e` is
impossible, so every finite nonempty event cycle is ruled out. No well-founded
clock, finite event carrier, nonempty population or physical realization is
assumed. The first horn can hold on an empty event carrier. The other horns
supply actual mathematical edges; controls witness all three on nonempty carriers.
Passage, presentism/eternalism/growing-block/moving-spotlight labels remain an
**incomplete, unclassified dimension**. This semantic fork is exhaustive only
under its stated common linear-clock background, not an exhaustive ontology.

The use is mechanically in `Reciprocal.consume`, result/argument
`RECIPROCAL-EVENT-RESPECT-CONSTRAINT`, inference
`INF-TEMPORAL-RECIPROCAL-FORK-USE` (`disjunction_elimination`). Its argument includes
the original zero-input framework inference, so the established coverage is
imported rather than restated as an ordinary premise. All six ordinary premises
remain in the bound theorem. The derived consequence is:

`C e f → C f e → clock e = clock f ∧ respect e ≠ respect f`.

The proof **case-splits imported coverage**. A reciprocal event walk conflicts
with the strict horn's acyclicity. `NoBackward` conflicts with the third horn's
witness. In the second horn, the two edges plus linear order force equal clock
values. Only then does the proof instantiate exact
`TruthCore.Results.Alternatives.RespectSwitch.consecutiveRespects` at that shared
time with the projected edges. It concludes unequal respects; it never equates
states at different times. This consumes the fork on the #591/#310/#440 route and
excludes the family of same-respect reciprocal event configurations under the six
open premises. It does not exclude every finite cycle or every alternating cycle.
The generated result view's case-split marker follows the existing inference
inputs to their registered producing result and displays use/consequence and
premises. No fork registry or manually synchronized graph is introduced.

## Survivors and discriminators

| Control / provisional profile | Certified consequence | Still open in a real application |
| --- | --- | --- |
| Strictly forward A₀→B₁→A₂ | Event graph acyclic, projected entity graph has A↔B | Token identity and genuine forward causal interpretation |
| Non-backward simultaneous alternating-respect circle | Reciprocal event edges, no backward edge, all four canonical local premises and projection jointly hold; distinct respects satisfy the derived constraint | Real possibility and explanatory adequacy of reciprocal borrowed power |
| Same circle with exercise clocks 0/1 | HasBackward; strict and non-backward profiles fail | Whether such backward causation is actually possible, not settled by this model |
| Nat successor-as-cause, clock n = −n in Int | Strictly forward and finite-cycle-free, not well-founded | Actual infinite causal instantiation and regress/explanation bridge |
| Existing reflected Zeno/event controls | First instant and bounded duration need not give a first event; unbounded temporal order need not be causal regress | Physical limit admission, event population and real causal edges |

The circle has a predecessor for every token. Its separately supplied sustaining
relation satisfies local availability for both all-on and all-off assignments.
These are consistency solutions, not initiation, conservation or a sufficient
explanation. This is #310/#311's local-versus-global boundary in a finite
simultaneous control. A defender of real per se priority may add a substantive
independently defended acyclic or source-grounded sustaining constraint. An
infinitist/holist may deny that the local relation demands a distinct initiation
or whole-series explanation. Neither reply is refuted by naming its relation.
The source-free model is the strongest surviving structural rival here; no real
metaphysical possibility is inferred from its Lean witness.

A same-respect simultaneous reciprocal pair is incompatible with the advertised
local act/potency premises and event bridge. An alternating-respect one is not;
this directly preserves #591's scope boundary. Forwardness excludes finite event
circles but not infinite upstream descent, so it cannot discharge
`STMT-NO-INFINITE-PER-SE-MOVER-SERIES`. The independent real-world discriminators
are the actual time-direction law, real mover/event bridge, relevant respect
identity and substantive sustaining/explanation principles, not finite graph
satisfiability or the absence of a modeled rival.

## Premise and verification comparison

Intended and actual root-route/open-premise delta: **zero**. Existing First Way,
regress, causal adequacy and attribute premises are retained; none is defended,
strengthened, removed or discharged. The six new temporal application premises
are explicit open analyst statements, not inserted into a root proof. A
conditional elimination under them is not root closure. Before/after frontier
reports are compared at the delivered batch; final CI owns build, binding,
Comparator and NanoDa, including the frozen Challenges.

Development evidence and rejected proof attempts are persisted in
`ATTEMPT-TEMPORAL-ACTUALIZATION-FORK`; source findings above are not temporary logs.

Focused development evidence: corrected combined definitions and all three
Solutions accepted at preview `db603d3140e92c4b1ca653ab2098a0189a70653f`,
shared session `master-20261029` version 1, SHA256
`191e3d1403adf0dba17368a77408b5843915bb0ec90c8925d2fc93dfb1e19987`.
Only permitted Mathlib axioms were printed; no errors, warnings or `sorry`.
The first failed development edit and dependency refresh are retained in the
attempt. One corrected CLI comparison took 9.288 s against service 2.500 s
(HTTP 2.518 s, lease 28 μs). These are single-run development observations;
retain the service with dependency readiness/cold-timeout handling, without a
proof-throughput claim. They do not certify the final canonical revision.

## First Way route consumption (#718)

`FIRST-WAY-SLICE-ROUTE` applies the exact `primaVia` theorem at each clock time and
case-splits the imported direction fork, in one semantics: the prima via module
reads its time-free vocabulary *simul*, and a clock slice is one analyst
instantiation of that. Nothing below is a source reading. The witnesses audited
above (`AQUINAS-ST-I-Q2-A3`, `ARIST-PHYS-VII-1`) were re-materialized; no claim
was added.

| Horn | Regress hypothesis at each slice | Other consequence | Survivor |
| --- | --- | --- | --- |
| `StrictForward` | Derived: the open link bridge leaves no per se link | Each mover of another at t is unmoved at t; no finite event cycle (imported) | Feedback A₀→B₁→A₂; successor chain with non-well-founded events |
| `NoBackward ∧ HasSimultaneous` | Supplied by open `RegressIfSimultaneous` | The regress premise excludes every closed event walk | With the premise: chain 0→1→2. Without it: the alternating circle, where the slice conclusion fails |
| `HasBackward` | Not reached | Rejected by open `NoBackward` | None under the theorem's premises; the #700 control still witnesses the horn without them |

The three test structures of #718: entity feedback over distinct successive events
is the first survivor; same-time reciprocal power in different respects is the
circle; a time-decreasing loop is the rejected third horn.

**How much the fork does.** Coverage is elementary. The slice first-mover conjunct
also follows from the bridge by cases on `HasSimultaneous` alone. Coverage is what
yields `StrictForward` in the outcome's first disjunct, and that disjunct is what
carries the discriminating consequence.

**What the strict horn's discharge is worth.** The regress hypothesis holds there
because the slice relation is empty, not because a series stops. A successor chain
has a first mover at each event's clock value and a cause for every event, so the event-level
regress obligation is untouched. Do not read this as progress on
`STMT-NO-INFINITE-PER-SE-MOVER-SERIES`.

**Constraint found.** `StrictForward`, the link bridge and the strong per se premise
at a time jointly exclude a mover of another that is moved in any respect at that
time. That excludes the hand moved while moving the stick, and a mover moved in an
irrelevant respect. So whoever takes the hand/stick case as a real instance must
deny `StrictForward`, the bridge or the strong sliced premise. Adding the slice
pure-act premise (`StrictPureActConflict`) yields that no mover of another has any
potency at its time. In the feedback model the slice instance of
`STMT-FIRST-UNMOVED-MOVER-IS-PURE-ACT` fails: A, the first mover at t = 1, has
potency there for its later respect.

**Meaning of the link bridge.** In ordinary language: when the stick moves the stone
only as moved, the stick's token and the stone's token are exercised at the same
time, as in the hand/stick case. Counterexamples to neighbouring relations: a father's
begetting and his son's later begetting are successive, per accidens, and no link; a
remote clock tick precedes another with no edge. It differs from `C`, which holds on
edges that are not links, and from temporal precedence. No transitivity, asymmetry or
well-foundedness is assumed of it. No generalization from these examples to all
causation is made. Rivals: a strict-production account can deny the bridge, or keep it
and accept that no time has a link; a regularity account can reject token production;
an infinitist can keep the bridge and deny the regress premise. None is refuted here.

**Missing bridge and root delta.** To reach the root route, the slice conclusion
needs a defended premise that some slice first mover is unmoved at every time, or
a reading on which the time-free vocabulary is not a clock slice. The feedback
model shows the first does not follow from these premises. Root-route delta is
zero; `DISAMB-UNMOVED-AT-A-TIME` keeps the two senses apart.
