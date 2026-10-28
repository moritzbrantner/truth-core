# Unique feedback and whole-chain explanation (#311)

The state equations `a = !b`, `b = a && b` have one satisfying
Boolean pair, `(true,false)`. Their gates are nonconstant: negation
changes across its two inputs; conjunction changes when either input varies
with the other held true. These are logical constraints. They are not
world-local causal edges, temporal evolution, pure copying of plans, or
borrowed instrumental powers. Sensitivity is a truth-table property, not
an assertion that each single-bit perturbation at the solution changes
both outputs.

| a | b | First equation | Second equation |
|---|---|---|---|
| false | false | fails | holds |
| false | true | holds | fails |
| true | false | holds | holds |
| true | true | fails | holds |

`UniqueFeedback.Controls` certifies sensitivity, the satisfying witness,
and equality of every consistent state with it. The proof does not select
an observed boundary value or assume uniqueness. It eliminates the other
three states. This is a nonvacuous satisfiability/uniqueness control; no
explanation predicate is present.

## Reuse and nonduplication

- Merged #299's `EssentialPowerUnderdetermined.essentialPowerUnderdetermined`
  gives all-on/off solutions and cut responses. Its local rule is preserved.
- `LocalObservationSelectsSolution.localObservationSelectsSolution` supplies
  determinacy only after fixing an observation. This control needs none.
- `RegressDomains.CycleAndConverseBoundary` admits equal least/greatest fixed
  points on an intrinsic self-loop. That supplied intrinsic predicate is not
  used here; neither fixed-point selection convention is used.
- Pending #619 owns complete-presence-history contrasts and differing reason
  assignments on the same memberwise structure. It is comparison evidence,
  with no dependency on its unmerged declarations. Those assignments are not
  repeated here.

No existing philosophical conclusion is imported as a fresh premise.
The previous theorems are comparison evidence; the new result proves only
its own distinct finite control.

## Surviving explanation question

Mathematical solution multiplicity cannot be the entire objection to logical
feedback: the constraints here are satisfied and have no second solution.
This does not prove an adequate ontological explanation or prove its absence.
The strongest rival says that the intrinsic global structural fact explains
the satisfying state. A brute global fact and a non-well-founded grounding
account are distinct further answers. None is eliminated by this table.

To reject the structural answer, one must specify which obtaining fact needs
explanation, what counts as sufficient explanation of it, and why satisfying
these global constraints does not meet that norm. A whole-series PSR or a
contrastive requirement must enter explicitly; neither automatically implies
externality or rules out explanatory circularity. No notion of explanation
is defined to prohibit loops. Conversely, uniqueness alone supplies no
independent defense of those norms or of the global structural answer.

The issue's original plans bootstrap still requires a richer interpretation:
these gates are not an inventor-free copying history. No inference from lack
of an inventor to impossibility, from consistency to metaphysical possibility,
or from explanatory dissatisfaction to an original causal source is made.
EXP-SCOPE, EXP-LOCAL-TO-GLOBAL, EXP-NONCIRCULAR and EXP-ULTIMATE remain open.
Source attribution remains paused; no historical claim is added.

## Premises, verification and service evidence

Intended and actual root-path open-premise delta: zero. The closed certificate
has no ordinary premises and no new root connection. All root philosophical
premises are retained; none is discharged.

The Challenge was frozen before proof work, SHA256
`80249ef71f3aa529bc97d4343b15e5af74788f8de1b0b631226a2b897a91325d`.
The shared persistent service accepted repeated full-content edits without
mutating its checkout/imports, at workspace
`/home/brantner/privat/truth-core-sprint-proof`, head
`75192b1c3efdf19f25601e52a06116e706420f11`, session `causal-harvest`,
path `Scratch/issue311.lean`. HTTP 200, final content SHA256
`d9a641f7007215a7884b0ec70d00651952546916e250d2df5e99cb870ae8c949`;
no errors and `#print axioms` reports no axioms. Initial implicit unfolding
failed; explicit unfolding and direct Boolean contradiction proofs fixed it.
Lease wait was 0.000010s, first request 0.836s, corrected warm request 0.230s.
Retain the warm serialized service for small edits; no second session or
benchmark rerun was needed. These are interactive diagnostics, not final
Comparator verification.

Canonical final CI owns build, binding, Comparator and NanoDa. After build,
reproduce the result gate with
`python3 scripts/worker_env.py -- scripts/verify-result.sh UNIQUE-FEEDBACK-CONTROL`.
The attempt record retains rejected interpretations and precise evidence.
