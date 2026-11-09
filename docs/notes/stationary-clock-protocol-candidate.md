# Stationary local clock protocol candidate

Analyst formulation; attribution deferred. This does not complete original
FRAME_CLOCK_SIMULTANEITY_GEOMETRIC_ORDER_4. Its allowance remains, and
privileged presence (sense 3) is unchanged.

`StationaryClockProtocol.System` has arbitrary event, instrument and location
domains. An event has a location and real chart parameter. Each instrument has
a position at every parameter and a real indication. `At` requires that the
instrument occupies the event location at its parameter: reading a remote
instrument is not the local event timestamp. `Stationary` requires an actually
constant position function for every instrument, rather than a stationarity flag.

The light-exchange relation is an explicit primitive: physical emission at r,
reflection at c and return to r at three indicated chart parameters. No signal
law follows from its name. `Coverage` supplies an ordered round trip at every
parameter for every instrument pair; `Midpoint` demands that the reflecting
instrument reads the arithmetic midpoint of the sending instrument's emission
and reception indications. `Calibrated` separately requires stationary
trajectories, coverage, reference-based midpoint agreement and a common positive
affine rate and origin relative to the supplied chart. This is an explicit
conditional profile, stronger than isolated midpoint calibration, not an
assertion that arbitrary physical clocks obey it. Common calibration yields
readout agreement (hence symmetry/transitivity of equality). Reference change
requires midpoint calibration relative to the replacement reference.

The unrestricted real-indexed diagnostic family has unit chart travel times
for all pairs, including co-located ones. It is deliberately an abstract
protocol control, not a model of physical distance-dependent light propagation.
Zero offsets give a populated calibrated witness; disagreeing offsets defeat
midpoint calibration. Reference replacement changes the demanded offset.
Unequal rates fail at later reflections even if an origin test passes. Empty
exchanges defeat coverage; moving trajectories defeat stationarity; a remote
instrument is not at the event even if its indication happens to agree. Equal
coordinate times do not imply equal unsynchronized local readings. These
controls neither refute physical special relativity nor infer an ontology.

## Root connection and exact remaining blocker

Target: physical-clock → selected temporal history → STMT-PAST-IS-FINITE.
`HistoryDictionary` explicitly identifies selected real history labels with
local readings at events. `selected_order` transports strict comparisons only
under that dictionary and instrument-at-event evidence. It neither supplies a
History nor identifies events, worlds and beings. Existing `TemporalHistory.History`
requires an ontic interpretation, IsAt and now, which are not clock indications.
Existing strict/inclusive past definitions still concern their selected domain
and order. A dictionary and a domain/coverage map must be selected before that
consumer can be instantiated. No initial time or finiteness follows from a
clock protocol.

Original completion remains blocked on selecting a physical scope: which
stationary system/space and admissible exchanges are intended, how propagation
and rates support consistent remote calibration there, and which events admit
local clock coverage. The all-pairs/all-parameters idealization and common
chart calibration above must not be silently advertised as the full original
meaning. Coordinator decision: retain this bounded profile or select a richer
physical admissibility/coverage specification before binding sense 4. The
candidate is useful independently for testing synchronization omissions.
No geometry, causal edges, privileged present, presentism or eternalism is
inferred. No new source claim or original sense declaration is introduced.
