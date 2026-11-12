# Critical-spine dependency map (2026-11-12)

Linked from [the modal spine handoff](modal-spine.md). Working root:
`STMT-GOD-EXISTS` (8626f8a5). Nothing here establishes a premise; it records
which verified arguments need which premises.

## Method and its boundary

Graph: every corpus argument with a result record, as an AND/OR graph (an
argument is an AND over its premises; the arguments concluding one statement
are its OR alternatives). Two readings of "P is unavailable":

- **Strict expansion.** Only statements with no verified derivation may be
  accepted as leaves; every other statement must be derived. P removed means P
  is neither a leaf nor derivable. This answers "which derivations need P".
- **Lenient.** Any statement may be accepted as an open premise. P removed
  blocks only arguments that list P directly; the derivations behind other
  premises are irrelevant.

Under the lenient reading, a derivation that runs through P is *support lost*
for its conclusion, not a refutation of it. Removing P never proves ¬P's
consequences, and no row below is a claim that P is false. Shared usage and
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
- Strict expansion: AGWF and finite rank are the only indispensable spine
  premises of the join. J1, J2, coverage, F1, no-novel-edge are each bypassable.
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

The routes through `STMT-UNIQUE-NECESSARY-ACTUAL-ROOT` (91b085c4) and the
asymmetric-grounding arguments to `STMT-NECESSARY-CLASSICAL-GOD-ROOT` (db2dead0,
c63f3afa) bypass the join, J1, J2, coverage and F1. They use grounding
*asymmetry* (39f7c63d, four derivations) and obtain a root from
`STMT-GRADES-TO-MAXIMUM-AT-BEING` (e4e6b0cd), which derives from
`STMT-NO-INFINITE-ASCENT-IN-BEING` (7dfa068a) or from approach-to-a-primary
grading. Well-foundedness therefore re-enters as no infinite ascent in being.
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

Root arguments: prima via ed7c588a; quarta via 678ff65f, 661ce61d, fd1f7e75,
beec1dc1; cogito/roster routes 0a639ec4, 1c154f2f, 72391d4d, 5e8e6054; classical
root 92ab7c94. Fifteen statements are indispensable to every route, all in the
shared act/potency/efficient-cause/priority core (for example
`STMT-NOTHING-IN-ACT-AND-POTENCY-IN-SAME-RESPECT`,
`STMT-EFFECT-DEPENDS-FOR-BEING-ON-EFFICIENT-CAUSE`,
`STMT-DISTINCT-BEINGS-NOT-MUTUALLY-DEPENDENT`).

| Removed premise | Root routes surviving | Derivations lost |
|---|---|---|
| F1, F2, J1, J2, no-novel-edge, coverage, NCAT, join | 10/10 | F1, no-novel-edge: J2 |
| AGWF | 10/10 | J2, join |
| finite rank | 10/10 | AGWF, J2, join |
| grounding asymmetry, classical-attributes sufficiency | 10/10 | none |
| grades to maximum at being, maximum in being causes all, unreceived esse is own being, immaterial is intellectual, the classical root | 9/10 (classical-root route lost) | classical root |
| esse cause is actual concrete ground | 7/10 | classical root |
| contingent grounding | 7/10 | none |
| population, whole roster not trapped | 6/10 (cogito/roster routes lost) | none |
| act simply prior to potency, God names the fully described principle | 2/10 (prima via, maxime ens) | classical root |
| `STMT-CAUSE-HAS-WHAT-IT-GIVES` (376d6a5a) | 1/10 (prima via only) | classical root |

Reading: the disputed modal premises (F1, F2, J1, J2, coverage) and the join
are bypassable for the working root. The consequential bridges are in stage
two and the naming step: perfection transfer ("nothing gives what it does not
have"), act-priority and the naming premise. These are AND-premises of almost
every route outside the prima via. No single modal premise and no small set of
them blocks the root, because the prima via and quarta via routes do not use
the modal spine.
