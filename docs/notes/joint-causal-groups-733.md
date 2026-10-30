# Joint causal groups and causal order (#733)

This is an analyst-defined vertical slice for #613/#311 and a reusable input
for #734/#735. It does not deliver those later investigations or establish an
actual complete ground. The premise delta is zero.

## Meaning, real examples, and limits

`Groups Event Group` records an admitted group, its contributor and enabling
condition events, and its effect event. `Group` indexes a record; it is not a
substance, fusion, additional bearer, or a cause over and above the members.
There can be several records for one effect, no record for a source, and even
an empty record. Contributors and enablers are separate fields: their
classification must be independently defended for an application, and the
interface does not impose their disjointness. Events have their own type;
`Exercise.bearer` maps them to a separate bearer type without asserting that
different events have different bearers or that a group has a bearer.

The owner illustrations are explicitly represented by `ignition`: supply plus
air availability precedes a spark occurrence; spark plus air and fuel
availability precedes a fire occurrence. Supply, availability and ignition
are events; supply device, air body, fuel body, discharge and flame are bearer
labels. In these partial records air is classified as an enabler. That choice
is not a general claim that oxygen is never a material contributor. Neither
record asserts sufficiency or actual exercise. Electricity and air alone omit
voltage, gap, dielectric conditions and discharge geometry; the fire example
omits temperature, concentration, chemical compatibility and propagation
conditions. Air can be present without a spark, and a spark can occur without
sustained fire. These are ordinary scope tests, not sourced empirical laws or
independently verified laboratory cases. A claim about any particular chemical
system would need its own evidence and appropriately restricted conditions.

An electrical AND arrangement offers the more modest conceptual illustration:
two closed switches in series can both be needed for a load response with a
functioning supply and circuit held fixed. A parallel branch can introduce an
alternative route, and a further closed switch can become redundant relative
to the chosen response. A dead supply is a near miss despite both switches
being closed. These examples motivate distinctions; the formal fixture below
is a stipulated truth table, not a verified physical circuit model. A Humean
regularity reading, an interventionist account, a productive-powers account,
and existential support need not agree that the same scenario table or
projected membership expresses their causal relation.

## Sufficiency, exercise, and completeness

`Exercise.suffices A e` quantifies over **all supplied allowed scenarios**:
if all antecedents in A occur, e occurs. `jointlySufficient g` uses the whole
contributor/enabler union, never a disjunction of individual causes. Its
strength depends on the independently chosen scenario space and background.
It alone does not express production, causal direction, counterfactual
robustness under every intervention, or a sufficient explanation. An empty
allowed space would trivialize it; `fixture` instead allows all 16 Boolean
input scenarios and has a coherent allowed actual scenario with every event
occurring. The certificate does not infer applicability from satisfiability.

Actual exercise is a separate `exercised` predicate. Coherence requires
admission, actual occurrence of every member and of the effect, and an allowed
actual scenario. These are necessary bookkeeping conditions, not a criterion
that makes a group genuinely productive. `exercisedGroups` filters the
membership graph by both admission and exercise, and `Exercise.actualGraph`
further restricts endpoints to occurring events through the existing
`WorldSourceRegress.Actual` and `actualGraph` adapter. Its synthetic Ontic
`ExistsAt` means event occurrence here, not substantial existence or esse.
Sufficiency and actual occurrence do not create an exercise witness. The same
fixture with no exercised records stays coherent and sufficient while having
no exercised group. Conversely, the interface does not demand that every
admitted or exercised record be sufficient: incomplete cause descriptions
are representable, and a full-ground interpretation owes that further check.

`indispensable g e` is relative to this particular group: e is a contributor,
and removing e while retaining every other member fails sufficiency.
`redundant g e` retains sufficiency after that deletion. These notions do not
say that e is necessary under all alternative causal routes. The finite
fixture has outcome `a ∧ (b ∨ c) ∧ enabled`. Both `{a,b,enabled}` and
`{a,c,enabled}` suffice; neither a nor b suffices even with the enabler retained; a and b are separately
indispensable relative to the first group; c is redundant in
`{a,b,c,enabled}`. The two sufficient alternatives are simultaneously admitted
and exercised at the all-on actual scenario. This is formal overdetermination
of the response relative to the table, not a metaphysical theory of
preemption or causal attribution. Omitting the enabling condition defeats
the claimed sufficiency of `{a,b}`.

Explanatory completeness remains a further obligation, not an opaque Boolean
field certified by the same truth table. A full-ground claim must independently
show that its conditions capture the relevant production/explanation of this
same effect, not merely copy its occurrence. It must address why the scenario
law, actual obtaining arrangement and group exercise obtain. This is exactly
the missing #734 exercise/intrinsic-supply and #735 adequacy work; neither is
settled by a group index, source count, least element or membership arrow.

## Order, minimality, and leastness

`Groups.graph` projects admitted membership to the existing `Graph.edge`.
One edge says that an event is one member of a group for an effect; it says
nothing about that member being sufficient alone. `ancestry` is Mathlib's
nonempty `Relation.TransGen`, not a second graph engine. Transitivity follows
from closure composition, not from an assumption that **immediate** production
is transitive. `NoCycles` gives irreflexivity, and together these give Mathlib's
`IsStrictOrder`. Asymmetry follows structurally from transitivity and
irreflexivity. Actual causal acyclicity is still an independently defended
OPEN applicability commitment. Quotienting strongly connected components into
a DAG would not establish that real events have no causal cycles. A one-event
loop is representable and fails the strict-order condition.

Well-foundedness is a separate OPEN commitment. Under WF, the existing
`Graph.controls_of_wellFounded` gives every supplied actual event a finite
upstream path to a source. A source has no incoming nonempty ancestry path,
so it is a minimal ancestor. A supplied event already populates that cone;
global source existence separately requires `Nonempty (Actual m.ontic ())`.
An inhabited candidate Event carrier with no occurring event does not supply
it. No uniqueness follows. The unchanged #707 theorem
`TruthCore.Results.Causality.PluralRootConfluence.control` retains its full
original joint model certificate and has two distinct globally minimal
sources with a shared downstream effect. That older `jointControl` is a
conjunction of commitments, not cooperative causal sufficiency.

`least K s` means finite reflexive ancestry from s to **every** node. Under
acyclicity it is equivalent to s being a source and every node having the
existing finite upstream path to s. This is stronger than unique sourcehood.
Connectivity plus upstream confluence and a source is one independently
conditional sufficient route, already proved by
`TruthCore.Results.Causality.SourceWitness.rooted_from_source`; no new unity
principle is inferred here. The plural-source control has no least element.
The least characterization uses no WF: reaching every node along one finite
path need not terminate every other upstream branch.

## Exact source-with-infinite-branch control

`recorded K` is a representation adapter for any existing graph: a record
exists exactly at targets with an incoming edge; its contributors are exactly
that target's old predecessors, and its enabler set is empty. Its graph is
proved **equal** to K, not just similar. Records for the same effect are equal
by subtype identity. No record is forced for an uncaused target; the interface
therefore needs no total choice of causes for every event.

For the unchanged #634 actual overlap graph, `none` is S, and `some n` is x_n.
Its complete recorded predecessor set is exactly `C(S)=∅` and
`C(x_n)={S,x_(n+1)}` for **every n**. The certificate gives the universal latter
set equality and the equality of the entire projected graph with the old
graph; the former follows from the literal link's false incoming relation at
none (so no source record is assigned). It imports the exact theorem
`TruthCore.Results.Causality.SourceWitness.overlap_control` unchanged. The
same graph is acyclic, connected, confluent and rooted at a unique source with
finite paths to it, while the same actual some0 anchors an injective infinite
upstream branch, is inaccessible, and refutes WF. One complete recorded set
per effect therefore does not eliminate regress. This adapter asserts exact
membership completeness relative to the recorded graph, **not** causal or
explanatory sufficiency of those sets. It does not establish that every branch
is essential, that the source supplies the whole exercise, or that the graph
is physically or metaphysically realized.

An admitted empty record adds no membership edge. `absentEmpty` retains such a
record while no event occurs; the certificate proves its actual domain empty.
Thus an empty record cannot establish uncaused existence. A graph source is
absence of incoming edges on a specified domain, not a positive explanation
of substantial existence.

## Reuse and source/prose/type audit

The seed related search and dossiers were read for
`STMT-CONFLUENT-SOURCE-REGRESS-OVERLAP` and
`STMT-PLURAL-ROOT-CONFLUENCE-CONTROL`, including existing attempts.
`Logic.RegressDomains.GeneratedWarrant` already uses full premise sets, but
its epistemic interpretation does not coincide with causal exercise and was
not renamed into causation. Canonical Graph, Actual, finite paths, closure and
order are reused. #310/#311 fixed-point/finite-grounding results do not supply
joint sufficiency; existential one-predecessor transmission is a different
notion. #691's recorded support audit leaves direct existential interpretation,
structural constraints and the physical-to-existential abstraction OPEN.
No new source-derived claim is made, and no pinned passage is broadened or
silently reinterpreted. Historical readings and their witness authority remain
in the existing linked records and `docs/power-existence-scope-boundary.md`.
The present examples and scenario semantics are explicitly analyst stipulations.
The related #712 locator correction from the retired #735 branch is included:
`TargetCopyExpansion.checks`, not the nonexistent `.certificate`.

`certificate : Certificate` binds the unconditional conjunction of conditional
schemas and fixed controls. Its universally quantified WF/acyclicity inputs
remain inside those schemas; it is not an assumption-free proof of actual WF
or actual sufficiency. The actual carrier is the occurrence subtype, all
scenarios are checked for the finite sufficiency control, and the imported
#634/#707 witnesses retain their original interpretations. No existential
witness transports incidental properties between those distinct models. This
is a derived structural/countermodel package, not a transcription of an opaque
bridge. It does not compare all five #735 rivals on one explanandum or claim
an exhaustive metaphysical fork.

The strongest surviving rival grants a genuine source and all finite source
paths yet retains the exact infinite branch; another grants plural jointly
sufficient groups without a common upstream cause. Against them, a defender
must independently justify actual full-group exercise, its existential
abstraction, actual acyclicity/WF where used, and any confluence/least-ground
or completeness demand. Scenario truth and record membership cannot supply
those commitments.

Intended and actual root-frontier premise delta: zero added, zero removed,
zero discharged; all ten route costs remain 31,32,36,38,39,39,39,40,40,41. No
configuration is registered or eliminated; the package certifies only the
conditional consequences and the stated surviving structural interpretations.

## Shared-service development evidence

The canonical clone submits combined full edits through `agent_lean.py` to
`Scratch/issue733/JointGroups.lean`, preview
`20b120233ddb791d983d193c252ce2c07fe09014`, session
`workloop-20261030`, the coordinator's loopback service and shared lease.
The final combined edit SHA256 is
`608c6c1a986836fd21d03776ed13d0c3f68418d186d94fc8047c748633f775b7`;
it returned no diagnostics. Earlier attempts exposed an incorrectly
unqualified recursive graph adapter, a closure API mismatch, and predicate
lambdas that prevented set-membership simplification; these were corrected
without weakening any advertised conclusion. The final helper response bound
clean preview HEAD, session, unique path and exact full content; canonical
build/Comparator/NanoDa evidence remains the final authority. Warm repeated
edits returned useful diagnostics without new import preparation; retain the
service for iterative proof edits. This observation is not a throughput
benchmark or evidence about final-head verification.
