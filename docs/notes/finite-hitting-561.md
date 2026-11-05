# Finite hitting and the infinite-tail survivor (#561)

Analyst formulations; attribution deferred. The owner lifted the original
research-only restriction in issue comment 6600966383 (2026-11-03). This note
records mathematical findings and interpretive boundaries; the issue holds the
current delivery handoff.

The question is whether necessary population can force one and the same
necessary concrete individual without a finite *global* population roster.
The strongest positive case supplies an absence-amalgamation policy together
with finite hitting, one finite possible population, or topological compactness.
The strongest negative case accepts necessary population and amalgamation but
keeps every population infinite and withholds compact admissibility. Neither
mathematical branch independently establishes its metaphysical inputs.

## Exact semantic background and reuse

Worlds represent complete admissible possible histories in one universal-access
component; an explicit designated actual world inhabits the carrier. Candidates
form one fixed rigid type. `present x v` denotes concrete existence of the same
`x` at `v`, by stipulation. It is not counterpart matching, a temporal transition,
abstract exemplification, a Scott essence predicate, or a causal relation.
No claim identifies a necessary concretum with God, a unique being, an underived
ground, or a causal source. Applicability of this interpretation remains OPEN.

Reuse is literal: the existing `DeDicto`, `DeRe`, `AbsenceAmalgamation`,
`FinitePopulationCover`, `finiteCoverTailPresent`, and `finiteCoverTailFrame`.
`FinitePopulationCoverLaws.checks.1` supplies finite omission induction;
`FinitePopulationCoverControls.checks` supplies the tail properties. The
existing `PopulationClosureSeparation.checks` supplies strict A-versus-exact-meet
separation; its three populations are abc, bcd, b. No duplicate relation/model
is introduced. The #495/#607 prior attempt records that no prior #495 topological
theorem was implemented. #486/#1043 now supplies exact product-topological
`tail_tendsto` and `false_not_tail`, consumed rather than reproved here.

Dossiers and related bundles were inspected for the finite-cover laws/controls,
limit-admission package, necessary population, de re necessity and amalgamation.
The previous #533 attempt proves full-cover omission, not the hitting theorem.
The #607 closure-separation attempt already settles strictness of the policies.
The #486 attempt settles tail convergence/excluded limit, not compact-subcover
extraction. No source acquisition or attribution task was selected.

## Three sufficient routes

Let P mean every admissible world has a concrete bearer, A the existing binary
subset-of-intersection amalgamation, N the existing rigid de re necessity,
H a finite list hitting every world, O one Mathlib-finite population, and K
Mathlib `IsCompact S` for admissible profiles `S : Set (I → Bool)` with the
product of discrete Bool topologies. World nonemptiness/universal accessibility
are fixed background, and classical logic is explicit through Mathlib's standard
approved axioms.

* **A: H + A implies N.** Under not-N, classical logic gives an absence witness
  for each fixed candidate. Reuse certified finite omission on the hitting list.
  Its final world's H-member contradicts its omission. H already entails P.
* **B: P + A + O implies H, hence N.** Choose the finite population of `u`.
  Amalgamate `u` with each `v`. P supplies a bearer in the amalgam, and A places
  that same bearer in both `u` and `v`. Thus the finite population hits all worlds.
* **C: P + A + K implies N.** Each cylinder `U_x = {v | v x = true}` is open
  (indeed clopen). P covers S by these cylinders. Mathlib
  `IsCompact.elim_finite_subcover` yields an actual finite subcover/list H.
  Apply A. K is not finite-description consistency or an assumed possible limit.

The proof can fail when an input is removed; it does not merely apply a supplied
P-and-A-to-N bridge. A finite type of worlds also yields a finite hitting list:
choose one bearer per world, then apply A. This proves the finite-world-count
bound without supposing that any population is finite.

## Strict comparisons and controls

A full finite population cover implies O even without P or A: take the actual
population, a subset of the covering list. In the other direction, W=Bool,
I=Nat with populations `{0}` and all Nat has P, A, O and H but no finite global
cover. This is the issue's exact strict weakening of #533.

With populations all Nat and `{n | 1 ≤ n}`, P and A hold and `[1]` hits both,
but neither population is finite. Thus H is strictly weaker than O under P+A.
The implication O-to-H uses P+A; no unconditional converse is asserted.
A-versus-exact-meet strictness reuses the existing abc/bcd/b model unchanged.
An amalgam may contain less than the intersection. It need not realize the
intersection, omit just one individual, or preserve every jointly present one.

All single-member deletions of the three cores are checked:

| Core (fixed inhabited universal component) | Delete finiteness/compactness | Delete A | Delete P | Delete not-N |
| --- | --- | --- | --- | --- |
| H, A, not-N | Exact infinite tails | Alternating singleton profiles | P follows H | Singleton positive profile |
| P, A, O, not-N | Exact infinite tails | Alternating singleton profiles | Empty-profile control; additionally the finite registry has `{a}`/empty | Singleton positive profile |
| P, A, K, not-N | Exact infinite tails in Boolean profile arena | Compact alternating singleton profiles | Compact singleton empty profile | Compact singleton positive profile |

These are inclusion-minimal cores relative to the explicit background, not a
claim that no differently formulated smaller core exists. The empty-population
deletions are honest logical controls, not advertised populated rivals. The
positive model jointly satisfies all sufficient backgrounds, excluding an
inconsistent-background victory. Alternating profiles retain nonempty worlds
and populated extensions while specifically refusing A. Universal access is
stronger than disconnected S5, so the registry includes the existing `Universal`
predicate as an explicit background premise rather than silently assuming it.

## The surviving no-necessary-bearer interpretation

From P+A+not-N the checked survivor theorem derives **all** of:

1. No finite hitting list.
2. Every world's population is Mathlib-infinite (not finite).
3. An infinite world carrier/component.
4. Joint absence of every finite list, but no world jointly omitting all candidates.
5. In the Boolean product-profile arena, noncompactness by contrapositive of C.

The exact old Nat-tail interpretation has W=I=Nat, `present n w` iff `w ≤ n`.
It is populated at every w, every fixed n is absent at n+1, and max(u,v) even
realizes the exact meet. Finite omission is compatible with P because no single
admissible tail is empty. The theorem also transports these facts into the
S=range(tailProfile) subtype with the same rigid candidate roster. This gives
one simultaneous witness for all survivor properties in C's semantic arena,
not a collage of incompatible interpretations.

For noncompactness, reuse #1043's actual Mathlib convergence to the excluded
all-false profile. If the tail set were compact, Hausdorff product topology
would make it closed, hence contain that limit. `false_not_tail` contradicts
this. No convergence proof, possible-limit axiom, external topology package,
or second proof-status registry is introduced. Noncompactness is a coherent
mathematical possibility, not contradiction, absurdity, or proof of metaphysical
possibility. Rejecting A (alternation) or K (tails) remains a serious rival.

The metaphysical bridge from complete histories/Boolean extensions to actual
modal possibilities remains OPEN. Ordinary population overlaps are examples
of sets, not independent evidence that arbitrary modal subintersections can be
realized. The mathematical relation has no transitivity, asymmetry, causation
or well-foundedness interpretation; A itself states exactly the closure assumed.
Topology does not defend a metaphysical similarity relation or license inference
from unrefuted finite descriptions to genuine possibility.

## Registry and certification boundaries

`FINITE-HITTING` freezes and verifies the full universal law/control package.
`FINITE-HITTING-CORE` and `FINITE-HITTING-FINITE-WORLD-CORE` expose exact premise
heads and `ConfigurationFalse`; the registered profile prunes their supersets
only in the same semantic arena. U is explicit common background. Three finite
registrations certify H/P/A/not-N/U as supported by the existing zero-axiom
registry. Their world/individual enumerations and evaluations use no axioms.

Mathlib finite-set O proofs use standard approved axioms; K/profile subtypes and
infinite tails are outside that registry's supported zero-axiom finite roles.
They remain exact Lean statement/result/attempt witnesses, with Comparator and
NanoDa, rather than being relabeled finite or provoking a tooling expansion.
Consequently missing registry evaluations/witnesses remain unresolved *there*,
even when the separate Lean package settles the particular deletion or survivor.
No false finite-registry completeness or global minimality is claimed.

Claim/type self-sweep: statement paraphrases, theorem types, result descriptions
and model evaluations all refer to their exact supplied carriers. Conditional
consequences do not establish H/A/O/K or actual-domain applicability. No source,
passage or claim is added; no existing challenge is weakened; no premise truth
or Catholicism root closure is asserted. The actual root/frontier comparison
is recorded with delivered-head verification evidence. Shared convention
`sourceRevision`: `625cb04ca568aebc8d45c90033e107a05e9bd2a0`.
