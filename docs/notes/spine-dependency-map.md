# Critical-spine dependency map (2026-11-12)

Linked from [the modal spine handoff](modal-spine.md). Working root:
`STMT-GOD-EXISTS` (8626f8a5). Nothing here establishes a premise; it records
which verified arguments need which premises.

## Method and its boundary

Graph: every corpus argument with a result record, as an AND/OR graph (an
argument is an AND over its premises; the arguments concluding one statement
are its OR alternatives). Two readings of "P is unavailable":

- **Strict expansion.** Only statements with no verified derivation may be
  accepted as leaves; every other statement must be derived. Derivability is
  the least fixpoint over verified arguments (the graph has cycles, so only
  well-founded derivations count). Removing a set S of statements means no
  member of S is a leaf or derivable. This answers "which derivations need P".
- **Lenient.** Any statement may be accepted as an open premise. P removed
  blocks only arguments that list P directly; the derivations behind other
  premises are irrelevant.

Under either reading, a derivation that runs through P is *support lost* for
its conclusion, not a refutation of it. Removing P neither establishes ¬P nor
refutes P's consequences, and no row below is a claim that P is false. Shared usage and
node degree are not indispensability: the tables count surviving OR-alternatives.

## Stage-one join: AND/OR structure

`STMT-NECESSARY-CONCRETE-UNDERIVED-AT` (0bdcf366), five verified arguments:

| Argument | Premises (AND) | Uses actual WF grounding? |
|---|---|---|
| df542c04 `checks` route | population, AGWF, contingent grounding, F1, J1, J2, EM | yes |
| d45dba04 from necessity | NCAT, F1, J1, J2, EM | only through J2's derivation |
| 36c6b111 | NCAT, AGWF, J1@w (84751fc2), coverage (df42581f), EM | yes |
| 9de79a41 | NCAT, AGWF, J1, coverage, EM | yes |
| 9d8798ea | population, AGWF, contingent grounding, coverage, EM | yes |

- AGWF = `STMT-ACTUAL-GROUNDING-WF` (82cfaf26). J2 = `STMT-CONCRETE-NECESSARY-UNION-WF`
  (d149d238); its only derivation (fe4b5ec7) is F1 + AGWF + no-novel-edge (bd983df2).
- AGWF has two derivations, from finite rank (47e323f2) and from borrowing
  escape (e27ea8e3), and borrowing escape itself derives only from finite rank,
  whose only derivation is the uncalibrated potential bundle (5adb2dc9,
  516c4fee, 838f7cca; `ActualGroundingPotentialRank`, no real-world calibration).
- Strict expansion: the single indispensable premises of the join are AGWF,
  finite rank, the three potential-bundle leaves and excluded middle
  (`STMT-EXCLUDED-MIDDLE`). J1, J2, coverage, F1 and no-novel-edge are each bypassable.
- Minimal two-premise cuts of the join without AGWF or finite rank (strict
  expansion): {F1, coverage}, {F1, same-supporter presence}, {J1, coverage},
  {J1, same-supporter presence}, {J2, coverage}, {no-novel-edge, coverage},
  {no-novel-edge, same-supporter presence}, {J1, contingent grounding},
  {J1, population}, {NCAT, contingent grounding}, {NCAT, population}.
  ({J2, same-supporter presence} is not a cut: coverage keeps its derivation
  from F1, J1 and no-novel-edge.) Under the lenient reading no-novel-edge drops out
  (no join argument lists it), and AGWF alone is not a cut, because d45dba04
  avoids it when J2 is accepted as a leaf. So J2 is an alternative to AGWF
  only for a holder who gives J2 its own warrant: its one recorded derivation
  consumes AGWF.
- Coverage replaces J1, J2 and F1 given AGWF. It does not replace AGWF.

## Direct actual-grounding routes

The arguments db2dead0 and c63f3afa reach `STMT-NECESSARY-CLASSICAL-GOD-ROOT`
without the join, J1, J2, coverage or F1, and several derivations of
`STMT-UNIQUE-NECESSARY-ACTUAL-ROOT` (91b085c4) do the same. db2dead0 uses
grounding asymmetry (39f7c63d). That premise has four derivations, one of them
from AGWF (16539528). c63f3afa uses asymmetry at a maximal target (bcf79e03),
derived from 39f7c63d or from ground-is-more-in-esse (d96105fb). Both obtain the root from
`STMT-GRADES-TO-MAXIMUM-AT-BEING` (e4e6b0cd). One derivation of that premise
(f52deeb7) is from `STMT-NO-INFINITE-ASCENT-IN-BEING` (7dfa068a); the other
(8eab5889) is from approach-to-a-primary grading. On the first,
well-foundedness re-enters as no infinite ascent in being. Other derivations
of 91b085c4 use pure-determination premises (c84c4a2a, 688e42fc) or a
necessary root ancestor (6d64bcad, via 177b9b54, which is lost with AGWF).
Whether both foundation commitments rest on one (a well-founded grade of being
that grounding ascends) is under investigation.

## Connection gap found and closed

On main at 8d5004fe8, `STMT-NECESSARY-CLASSICAL-GOD-ROOT` (the endpoint of the
act-of-being, perfection and attribute composition, result 57213a13) did not
reach `STMT-GOD-EXISTS`. It fed only `STMT-UNIQUE-GOD-WITH-CLASSICAL-ATTRIBUTES-EXISTS`,
which no argument consumes. The join reached the root only through
`STMT-DIRECT-ESSE-ROOT-PERFECTION` → `STMT-MAXIME-ENS-CAUSES-BEING-OF-ALL` →
the quarta via naming step (678ff65f). The assembly
`NecessaryClassicalGodRootGodExists.godExists` (spec
`specs/necessary-classical-god-root-god-exists.toml`) projects `σ.IsGod` from
the classical root. It closes nothing by itself (invariant 16). The new route
(92ab7c94) costs 37 (13 bare); the cheapest route is unchanged.

## Route impact at the working root (strict expansion)

Root arguments: prima via ed7c588a; quarta via 678ff65f, 661ce61d; mixed
routes consuming prima via premises fd1f7e75 (full description), beec1dc1
(maxime ens); cogito/roster routes 0a639ec4, 1c154f2f, 72391d4d, 5e8e6054;
classical root 92ab7c94. Fifteen statements are indispensable to every route:
excluded middle and fourteen in the shared act/potency/efficient-cause/priority
core (for example
`STMT-NOTHING-IN-ACT-AND-POTENCY-IN-SAME-RESPECT`,
`STMT-EFFECT-DEPENDS-FOR-BEING-ON-EFFICIENT-CAUSE`,
`STMT-DISTINCT-BEINGS-NOT-MUTUALLY-DEPENDENT`).

Abbreviations: F1 `STMT-ACTUAL-MODAL-REFLEXIVITY`, F2 `STMT-EUCLIDEAN-FRAME`,
NCAT `STMT-NECESSARY-CONCRETE-AT`, population `STMT-COGITO-INHABITED-CONCRETE-WORLD`,
contingent grounding `STMT-EVERY-CONTINGENT-GROUNDED-AT`. "Derivations lost"
lists only the named spine nodes in this table and the join section that lose
every verified derivation. Other statements lose derivations too.

| Removed premise | Root routes surviving | Derivations lost (named spine nodes) |
|---|---|---|
| F1, F2, J1, J2, no-novel-edge, coverage, NCAT, join | 10/10 | F1, no-novel-edge: J2 |
| AGWF | 10/10 | J2, join |
| finite rank | 10/10 | AGWF, borrowing escape, J2, join |
| grounding asymmetry, classical-attributes sufficiency | 10/10 | none |
| grades to maximum at being, maximum in being causes all, unreceived esse is own being, immaterial is intellectual, the classical root | 9/10 (classical-root route lost) | classical root |
| esse cause is actual concrete ground | 7/10 | classical root |
| contingent grounding | 7/10 | none |
| population, whole roster not trapped | 6/10 (cogito/roster routes lost) | none |
| act simply prior to potency, God names the fully described principle | 2/10 (ed7c588a, beec1dc1) | classical root |
| `STMT-CAUSE-HAS-WHAT-IT-GIVES` (376d6a5a) | 1/10 (prima via only) | classical root |

Reading (structural only): the disputed modal premises and the join are
bypassable for the working root. Removing all of them together (F1, F2, J1,
J1@w, J2, no-novel-edge, coverage, same-supporter presence, NCAT, join, AGWF and
finite rank) still leaves all ten root arguments. Perfection transfer ("nothing
gives what it does not have"), act-priority and the naming premise are
structurally indispensable on most routes outside the prima via. The bypassing
routes carry their own open premises, so this ranks where support concentrates,
not which premises are philosophically weakest.

## Workloop state (coordinator handoff, updated 2026-11-12)

Merged on main:
- #1514: the classical-root projection to `STMT-GOD-EXISTS` and this map.
- #1515: graded foundation. Actual well-founded grounding and J2 follow from support ascending a rigid `MoreIn esse` grade together with no infinite ascent. With a freely chosen grade this is equivalent to AGWF and J2, so it relocates the regress question and does not shrink it. See "Graded foundation" in [the spine note](modal-spine.md).
- #1516: esse-cause bridge. The strength ladder runs `376d6a5a` ⇒ `d0fc96b7` ⇒ `4ccb319f` ⇒ `4a5a43a5`. The Platonist rival is relocated downstream, not defeated.

Open:
- #1518: preexistence without transfer.
  - The bottleneck behind `376d6a5a` is "more such" (`d5a94eb1`), which is interderivable with distinct-cause transfer. Granting it restores all ten routes.
  - A new root route (`5d2b7c6e`) survives removal of `376d6a5a`, through `cffad050`.
  - Granting distinct-cause transfer (`2c0b9bd7`), which is strictly weaker than `376d6a5a`, restores all 11 routes. It is the smallest sufficient commitment found at this bottleneck. Granting the cause-of-being restriction `d0fc96b7` adds route 92ab7c94.
  - Follow-ups: #1517 (preexistence consumers) and #1519 (consumers of `d5a94eb1`, and re-routing the four CONCRETE_6 routes through grades-at-being).
- Act priority over potency (`a4d3261a`; only 2/10 routes survive its removal): in progress in a separate PR.

Next bridges, by computed impact:
1. Re-route the CONCRETE_6 routes through grades-at-being (#1519).
2. Act priority (`a4d3261a`) and the naming premise (`STMT-GOD-NAMES-THE-FULLY-DESCRIBED-PRINCIPLE`), each 2/10.
3. A root-restricted ground for `d0fc96b7`, which would lift route 92ab7c94.
4. #310: the independent warrant for no infinite ascent along grounding chains, on which the graded foundation rests.
