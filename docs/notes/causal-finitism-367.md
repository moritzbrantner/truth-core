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
