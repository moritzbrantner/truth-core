# Finite ancestry, histories and per se regress (#367)

This batch supplies a conditional mathematical route, not a defense of causal
finitism. All three new premises remain unattributed and open. It leaves #367
open for the paradox structures, the abductive defense, and the stronger
first-cause/necessary-existence arguments.

## Verified primary evidence and reading limits

The author-hosted manuscript *The Grim Reaper Kalam Argument*, Robert C. Koons,
is pinned in `corpus/passages/koons-grim-reaper-kalam.json`. Two live fetches and
two fixed 2026-03-30 Wayback fetches returned identical PDF bytes. Materialized
and read:

- `KOONS-GRIM-REAPER-KALAM-4-5`: printed and physical PDF pp. 4–5. P1 describes
  finite event histories through absence of loops and infinite regresses. P2
  concerns coming into existence; P3 concerns temporal things beginning. Koons
  explicitly denies that P1 gives a finite universal past under relativity:
  individual past light cones could be finite without a uniform bound. His
  further SILPS argument concerns infinitely extended initial states. None of
  those temporal or modal claims follows merely from the theorem here.
- `KOONS-GRIM-REAPER-KALAM-17-18`: printed and physical PDF pp. 17–18. The
  conclusion is restricted to causal-power histories; PP1.1 excludes infinite
  descending chains and PP1.2 separately excludes loops in every world. PP2.1,
  PP2.2 and P3 then enter the eternal-cause argument. The passage also makes
  explicit a dependence of the preceding patchwork argument on intrinsicality
  of selected powers. That argument is not reconstructed in this batch.
- `AQUINAS-ST-I-Q46-A2`: the pinned Latin was materialized and read with ad 7.
  Aquinas excludes per se regress while not regarding accidentally multiplied
  efficient causes as an impossible infinite regress (fathers/hammers). The
  existing corpus readings are retained. A broad finitism covering such
  accidental ancestry would be stronger and conflict with that permission;
  it is an alternative defense of the restricted premise, not an identification
  of the two philosophical positions.

The exact Pruss finite-history formulation remains a source gap. The publisher
book and chapter abstracts orient the search but do not settle the relevant
causal relation, relata, modality or the meaning of finiteness. The author
lecture PDF at
`https://www.alexanderpruss.com/classes/theism/causal-finitism-class.pdf`
(and the host without `www`) failed TLS hostname validation on 2026-10-26.
No unlicensed book copy was used. The candidate
`PRUSS-CAUSAL-FINITISM-FINITE-HISTORY` preserves the remaining search.

Rejected identification: Koons's lack of infinite descending histories is not
silently formalized as finiteness of the set of distinct ancestors. An accessible
node can have infinitely many independent immediate ancestors. Conversely, a
finite distinct-ancestor set permits a cycle with repeated visits. These are
separate mathematical conditions. No source claim was created for the three
analyst hypotheses merely because the manuscript was read.

## Exact conditional result

`FiniteDistinctAncestry cause` is `∀ x, Set.Finite {y | TransGen cause y x}`.
`TransGen` uses one or more finite edges; both direct and indirect ancestors
count, and set membership counts each relatum once. There is no uniform bound,
possible-world quantifier or bound on elapsed time. `NoCausalLoops cause`
excludes a nonempty finite return path. Together these make the transitive
closure a strict order. Mathlib's `Set.Finite.wellFoundedOn` and
`Set.WellFoundedOn.acc_iff_wellFoundedOn` yield accessibility at each point.
`PerSeLinksIncluded cause perSe` then transfers accessibility by subrelation.

The main theorem concludes the existing
`STMT-NO-INFINITE-PER-SE-EFFICIENT-CAUSE-SERIES`, without changing its type.
The companion theorem imports the earlier regress-to-finite-grounding proof
and the exact `finiteGroundingHasSource` theorem. It obtains the existing finite
path conclusion. It does not restate the finite-grounding theorem as an open
premise. Classical logic is permitted because these proofs use Mathlib.

All relations have the same carrier. This is an explicit application boundary,
not an event/being map: Koons speaks of events and causal powers, whereas the
Aquinas statement uses beings and the per se efficient-cause link. An application
must defend the carrier interpretation and inclusion premise. No such map is
assumed for actual reality. The finite path can be zero steps and its endpoint
is uncaused only relative to that per se relation; nothing establishes uniqueness,
necessary existence, a temporal beginning, or God.

## Omission controls and frontier

Comparator checks a finite self-loop without loop exclusion, strict reverse
natural order without finite ancestry, and an empty cause relation with an
unrelated per se self-loop without inclusion. Each retains the other two
hypotheses while falsifying the main conclusion. They show logical necessity
within this encoding, not metaphysical possibility or premise truth.

The intended premise change is a conditional route from three explicit open
hypotheses, with no claimed discharge. Because the new hypotheses are bare,
this is not a sourced relocation and does not count as philosophical frontier
progress. The existing sourced no-regress premise is retained. Per-route counts
and exact gate evidence belong in the PR, rather than being inferred from a
successful attempt record. The abductive explanation of paradoxes remains open.

## Renewed defense audit: the patchwork bridge (2026-10-28)

This audit addresses the independent defense of actual existential-support
well-foundedness, not another theorem conditional on it. Read the materialized
`KOONS-GRIM-REAPER-KALAM-6-16` and
`KOONS-GRIM-REAPER-KALAM-18-22`, from the same pinned PDF bytes as above.
Printed and physical PDF pagination agree. These prose source findings are not
new attributed statement/claim records or a mechanically certified argument.
The earlier note's statement that the middle argument was not reconstructed
applies to the original batch; the following reconstruction supplies that work.

### What the source's reductio needs

- **Paradox specification, pp.7–9:** each Placer acts just when none of the
  earlier Placers has issued the relevant warrant. The particle version also
  preserves an issued warrant. The contradiction depends on these firing and
  persistence laws, not merely on the presence of infinitely many causal
  predecessors. An arbitrary infinite power-transmission history has no such
  contradiction merely by sharing its order.
- **Spatial/temporal assembly, pp.9–13:** a possible isolated Placer (PGR),
  suitable nonoverlapping regions in an alleged infinite past (HIP), infinitary
  spatiotemporal patchwork (PInfSP), and intrinsicality of the specified powers
  (PDIn) jointly provide the alleged world containing all Placers. Binary
  patchwork is motivated by ordinary recombination as a basis for modal
  knowledge (p.10). Its countable generalization is presented as plausible
  (p.11), rather than derived from binary recombination. The hypothesis also
  needs regions large enough for the mechanism; it is not simply unbounded
  elapsed time, independent of such realizability conditions.
- **Causal replacement, pp.14–16:** Koons proposes Causal Power Network
  Patchwork (CPNPP). Start with a graph already realized in one possible world.
  Supply replacement event patches such that, for each node, a possible world
  realizes that patch together with exact duplicates of its predecessor and
  successor patches. CPNPP supplies a *single* possible world realizing all
  the patches with the specified causal-power graph. The edge interpretation
  is an entity's power to influence another event, not direct esse support of
  the bearer of that power. The final edge formula on p.15 repeats its target
  index where its preceding prose requires a source index; this transcription
  defect is not treated as a refutation of the intended principle.
- **Application, pp.16–17:** a possible infinite descending causal-power chain,
  a possible Placer Trio (PPT), CPNPP, and intrinsicality of the relevant powers
  yield the alleged impossible infinite Placer world. The Trio supplies the
  local predecessor/successor pattern. Applying this to every indexed Placer
  also requires faithful duplicate/relabeling of the required index-dependent
  positions, signals and conditional responses; three named devices alone
  are not a proof of this uniform realizability. Even granting this step,
  local feasibility and global assembly remain distinct premises.
- **Scope of conclusion, p.17:** PP1.1 excludes infinite descending
  causal-power histories in every world. PP1.2 separately excludes loops,
  invoking a time-travel grandfather argument. The read range does not provide
  a developed loop proof. No-loop exclusion must therefore remain separate;
  a defense of PP1.1 alone does not establish the full Lean `WellFounded` claim.

The proposal is a substantive strategy: transfer a known inconsistent firing
pattern onto any alleged infinite causal order. It avoids merely defining
borrowed power by finite generation. Its load-bearing modal permission is,
however, CPNPP, together with the availability and preservation of the specified
power patches. The source introduces causal patchwork by analogy with
spatiotemporal patchwork and as a plausible construction principle (pp.14–15).
It does not independently establish that every collection of locally realizable
neighborhoods has a jointly realizable countable network. This audit therefore
accepts the intended conditional strategy, while withholding its universal
metaphysical application and any claim of a newly checked consequence.

### The best defense and the strongest compatibility reply

The best stated defense is not just absence of a discovered contradiction:
actual modal knowledge commonly permits rearranging independent local material,
and intrinsic causal capacities appear explanatorily prior to their particular
manifestations. Koons explicitly argues against reversing that dependence in
his neo-Humeanism response (pp.18–19). If the required capacities really are
intrinsic, exact duplicates retain them. This answers one reason to deny that
powers survive duplication.

It does not answer a distinct reason to deny the *existence of the joint
duplicate*. The strongest reply can accept intrinsic powers, possible isolated
Placers, every stipulated finite neighborhood, and the impossibility of the
complete firing pattern. It holds that globally compatible manifestations,
causal connections and boundary conditions constrain which collections of
intrinsic bearers can coexist. Intrinsic properties are preserved **if** exact
duplicates exist; that conditional does not supply the duplicate world's
existence. This reply need not adopt a Humean reduction of powers to a whole
history. An anti-Humean can instead regard capacities as real while denying
unrestricted joint realizability of independently possible capacity-bearers.
It must defend a positive compatibility account rather than infer possibility
of a benign infinite history from consistency of local equations alone.

The positive case deserves a defeasible assessment, not a demand that every
metaphysical premise first have a kernel proof. Recombination has explanatory
value: it makes unfamiliar possibilities accessible from independently
understood mechanisms rather than requiring a separate modal intuition for
every arrangement. On the intrinsic-power view, adding remote independent
bearers should not simply erase a mechanism's capacity. CPNPP also preserves
an already possible causal framework and asks for realizable adjacent
interfaces; this is a more motivated restriction than arbitrary juxtaposition
of causally disconnected fragments. If these restrictions exhaust genuine
constraints, a special prohibition on infinite assembly would need a reason.
The paradox then offers an abductive reason to blame the infinite framework
rather than familiar local capacities. These are substantive, disputed reasons
for patchwork, rather than a wholly unmotivated stipulation.

The comparison turns on which independence is defended. Independence of
*possession* of a capacity from remote manifestations supports duplication;
independence of *joint realizability* from global boundary requirements is
stronger. Ordinary finite recombination gives the former case some support,
but supplies less discrimination about the latter infinite limit. A restricted
gluing principle that demands compatible boundary data is independently
motivated by preserving the powers' very causal interfaces; its restriction
need not mention infinity. On that profile, the impossible Placer pattern
fails the compatibility test while some other infinite histories might pass.
This rival pays for its global constraint and must explain its operation. The
finitist pays for the stronger universal assembly permission and must explain
why no additional global constraint is relevant. Neither side wins merely
because one principle is called intrinsic or the other is called holistic.
The manuscript offers a defeasible philosophical defense of the patchwork
strategy, with this particular independence question still insufficiently
settled for a root-premise discharge; it is not refuted by lacking a formal
proof of premise truth.

This is a principled reply to the reductio: reject the assembly permission
where the assembled response requirements conflict. Its cost is a restriction
on modal recombination; its explanatory burden is to specify why compatible
finite neighborhoods need not suffice and how the admitted global histories
are selected. Koons's pp.20–21 already recognize that patchwork can conflict
with necessary causal constraints. He lists defeasible patchwork and a causal
proviso among the responses. Preserving the original network's edges answers
his particular missing-cause objection to causal patchwork; it does not by
itself answer every global compatibility objection. Calling the new proviso
ad hoc without an independent independence principle does not settle this
remaining dispute. Conversely, the paradox alone does not prove that the
compatibility restriction is the correct metaphysics.

The signal revision (pp.19–20) addresses a different issue: particles might
vanish between placements. Koons replaces their persistence with intrinsic
active/passive capacities to send and receive a predecessor signal, and uses
adjoining nonoverlapping regions. This usefully isolates signal preservation
and interface compatibility. It relocates, rather than eliminates, the need
to show that all such interfaces and conditional responses can coexist in the
proposed infinite network. The contradiction remains specific to that global
response specification, not to the word *power*.

### Existing certificates constrain this inference already

No new Bool/Nat regress model is needed. The finite-cover/amalgamation laws
and controls (`FINITE-POPULATION-COVER-LAWS`,
`FINITE-POPULATION-COVER-CONTROLS`, and
`POPULATION-CLOSURE-SEPARATION`; see `finite-population-cover-533.md`) already
distinguish individual modal availability, joint absence, and finite versus
unbounded populations under explicit semantics. They do not prove or refute
CPNPP: absence amalgamation is not event-patch assembly. Their relevant lesson
is a checked scope boundary, not a cross-domain theorem. Finite induction on
combinations does not supply one countably assembled world by itself.

`unique-feedback-explanation-311.md` already certifies that global equations
can have one satisfying state; solution multiplicity is not a universal
objection to global structure. It establishes neither metaphysical possibility
nor explanatory sufficiency of the compatibility reply. The existing
`GroundingRegress.GroundingWithoutUniqueCauseAllowsRegress` and
`GroundingWithUniqueCauseYieldsRegressReading` make a second relevant
boundary precise: a finite path to some intrinsic source does not exclude an
infinite branch running alongside it. Hence even an independent defense of
some source for every exercise would not automatically give well-foundedness
of **all** direct supporters. The earlier finite-ancestry/no-loops/inclusion
result remains a conditional and supplies none of these premises' truth.

### From power histories to direct existential support: a further open map

Let E be events/power-exercises in one fixed world and C the upstream
causal-power relation covered by the source argument. Let B be actual bearers
and R their direct existential-support relation in that same world. To transfer
well-foundedness by a bearer-to-event map f, one would at least need a suitable
f for every relevant bearer and an edge condition
`R c b → C (f c) (f b)` (or an explicitly justified nonempty finite C-path
version). Neither the existence of f nor this inclusion follows from a
physical example of a bearer exercising a particular capacity. Mapping many
bearers to one event is not harmless: an R edge whose endpoints collapse would
require a forbidden C self-edge/path. Mapping each edge to a separately chosen
event also fails to ensure coherent composition along a whole bearer chain.
These are application obligations, not new assumptions silently adopted here.

The stronger universal scope must include every relevant bearer, every direct
esse-support edge, and non-temporal conservation if the target includes it.
Aquinas's q.104 conservation need not be an earlier temporal episode. An event
of beginning to exist, a history of a signal's reception, and the present
support of a substance's existence therefore cannot be identified without an
argument. A defense applying only to physical causal exercises would justify
at most a correspondingly restricted application, not unrestricted being-as-
such dependence. The ordinary-meaning/abstraction investigation remains in
`docs/power-existence-scope-boundary.md` and `DEF-PRESENT-ESSE-SUPPORT`.

All of this concerns a **world-local** relation. Restricting an already
well-founded R to necessary bearers preserves well-foundedness conditionally;
it neither establishes R nor yields the cross-world union's well-foundedness.
The existing rotating-support controls distinguish that union from each local
relation. No edge is drawn from an event in one world to an event in another.
Temporal-past finitude, finite distinct ancestry, absence of infinite power
histories, and universal existential-support well-foundedness remain separate.

### Actual premise comparison and next discriminating question

No root premise is added, removed, sourced as a new claim, or discharged. The
existing no-infinite-per-se-series and actual-support well-foundedness targets
remain open; the original Pruss precise-reading witness gap also remains.
The new source result is the identified modal premise bundle and Koons's
actual defense/objection responses, with its strongest non-Humean compatibility
rival. The decisive next inquiry is whether intrinsic powers plus independently
justified interface/independence constraints license **countable causal-network
assembly**, and whether those constraints apply to direct esse support. A
formal theorem assuming CPNPP or well-foundedness would not resolve it.
