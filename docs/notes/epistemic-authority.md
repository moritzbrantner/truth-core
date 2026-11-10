# Evidential merit versus preference-independent authority (#930)

Question: does warranted evidence give someone a pro tanto reason to correct a
factual belief even when they are indifferent to accuracy? Target:
STMT-THERE-ARE-PREFERENCE-INDEPENDENT-EPISTEMIC-REASONS (`2ca463c2`), under
its exact paraphrase (pro tanto, not overriding; no agent-neutrality or
factivity). Analyst formulations; attribution deferred. Spec:
`specs/epistemic-authority.toml`; Lean: `TruthCore/Logic/EpistemicAuthority.lean`,
`TruthCore/Results/Logic/EpistemicAuthority/Solution.lean`.

The batch retains six theorem declarations and four corpus result registrations.
The two lemmas concluding the target remain in Lean with their frozen types;
their direct graph registrations are deferred because their sense-bridge
annotations were invalid. The four registered results concern the goal-relative
exclusion, the concession for aiming subjects, the inconsistent bundle and the
finite controls. Direct support for the target is not added to the corpus graph.

## What the existing results already give, and where the rival escapes

- `Boundary` (`goalRelative` frame) already shows thin F6, consideration
  presentation and the ordinary-role definition jointly satisfiable with no
  preference-independent reason. The existing premises do not exclude the
  goal-relative rival; only the bare `PreferenceIndependentDefinition`
  (a transcription route, `EP-ROLE-INDEPENDENT-FROM-THIN`) does.
- The accuracy certificates (`EpistemicAccuracy`, `Statewise.dominance`) are
  algebra over a chosen score. They show that a distortion has an avoidable
  accuracy cost, even statewise for incoherent pairs. They bind only a subject
  for whom that cost is a reason; the goal-relative rival accepts every
  identity and denies the normative step. Accuracy dominance therefore does
  not by itself bind an accuracy-indifferent profile.
- The nihilism retorsion bites assertion and argument, i.e. agents already
  taking a correctness aim. An indifferent subject who neither argues nor
  asserts about the question is untouched; and a goal-relativist who argues
  for goal-relativism concedes reasons only relative to their own aim.

## Formal structure and registration boundary

- `authorityFromAnswerability` (retained lemma; direct registration deferred):
  `ActualForceConcession f`,
  `BeliefAnswerability f` ⊢ `SomePreferenceIndependentReason f`. The rival
  grants the concession (an accuracy-valuing subject with favoring evidence)
  and denies answerability (`concessionFromGoalRelative` checks the grant:
  goal-relative force plus an ordinary belief reason of a subject whose actual
  preference has the aim yields the concession). Within this vocabulary and
  given the concession, the dispute sits in that bridge; the
  `PreferenceIndependentDefinition` route and reflective or disjunctive
  goal-relative accounts remain open.
- `goalRelativeExcludesAuthority`: `GoalRelativeForce f aims`,
  `IndifferenceAvailable f aims` ⊢ `NoPreferenceIndependentReason f`. With the
  previous theorem, `authorityRivalBundleInconsistent` checks that concession,
  answerability, the goal-relative account and an indifference alternative
  cannot all hold in one frame; it does not settle which member to reject.
- `constitutiveAimAuthority` (retained lemma; direct registration deferred):
  F6, presentation, ordinary definition (composed
  through the existing `ordinaryFromThin`), `GoalRelativeForce f aims`,
  `ConstitutiveAim f aims` ⊢ target. In Lean `ConstitutiveAim` is only
  `∀ d, aims d`; neither its constitutive origin nor a distinction from desire
  is encoded. It secures the target by excluding indifferent profiles from the
  comparison class, not by giving an indifferent subject a reason, so it is no support for
  the indifference case. The dispute moves to whether indifference profiles
  belong to believers.
- `controls`: `goalRelative` satisfies F6, presentation, ordinary definition,
  concession, goal-relative force and indifference without answerability or
  the target; `indifferentAgent` (same evidence, actual preference comfort)
  has an ordinary reason with no actual force; `forceless` has answerability
  without concession; `independent` has both and the target; `independent`
  with the accuracy aim and with `allAim` are omission controls for the two
  premises of `goalRelativeExcludesAuthority`, the latter also a nonvacuity
  witness for the constitutive-aim argument.

`BeliefAnswerability` is a universal-conditional form of the target's
invariance clause: low inferential distance, and stronger than needed, since it
also covers non-ordinary considerations. The encoding can still fail (the
`goalRelative` and `forceless` controls). The structural finding is the
location of the dispute, not a new support for the target.

## Warrant for the answerability bridge

For: (1) transparency of doxastic deliberation: deliberating whether to
believe p gives way to whether p, and desire for accuracy does not enter as a
further premise; (2) the wrong-kind-of-reasons distinction: incentives to
believe p seem reasons to want or cause the belief, not reasons for it, and an
instrumentalist must explain why accuracy-incentives are of the right kind
while comfort-incentives are not; (3) Kelly-style anti-instrumentalism: a
subject indifferent to a trivial question (the tile count) still believes
against the evidence irrationally, and the criticism does not wait on their
goals; (4) the reversal test in the #930 note: evidence's direction does not
flip with wishes.

Against: (1) the instrumentalist reply that the criticism in (3) is
attributive (bad as a belief) without being a reason for the subject: a
standard of correctness is not thereby authority (the knife/chess point);
(2) deliberative transparency is psychological, compatible with reasons that
only exist given an aim; (3) the constitutive-aim reply is either too weak
(an aim compatible with indifference to particular questions) or restates the
norm; (4) "indifferent believer" cases may simply be agents without the
relevant reasons, which the rival accepts as the cost.

## Provisional judgment (coordinator grade)

`2ca463c2` under its exact paraphrase: **underdetermined**. No checked result
discriminates answerability from goal-relative force; the controls show the
frame cannot. Thin, contested considerations in favor: the wrong-kind-of-
reasons distinction and indifferent-believer criticism. Standard instrumentalist
replies: wrong-kind reasons are those that do not serve the aim, and the
criticism of an indifferent believer is attributive (bad as a belief) without
being a reason for that subject. Strongest surviving objection: that
attributive-versus-reason-giving distinction. Strengthen: an argument that the
rival cannot draw the right-kind/wrong-kind boundary without a
preference-independent standard of what belief answers to. Weaken or reverse:
a goal-relative account (reflective or disjunctive aims) that explains
wrong-kind reasons and indifferent-believer criticism without
preference-independent authority. The constitutive-aim argument does not count
as support for the indifference case.

## Connection plan (unconnected)

None of these results reaches the root. Proposed bridge: the case's premise
assessments, its acceptance or rejection of a root-route premise, are governed
by the same evidential considerations as factual belief; if those
considerations carry preference-independent pro tanto force, the assessments
are not mere preference. Missing record: a statement linking belief-answerable
reasons to the acceptance attitude used by the case's premise-assessment
policy. Blocker: no root-route statement currently represents the assessment
attitude or its normative status, and acceptance in the case may be a
practical commitment rather than a belief; the bridge must not become an ontic
principle of sufficient reason (#756) or an inference to God.

Next discriminating step: formalize the right-kind/wrong-kind boundary
(incentive versus evidence) as frame data and test whether a goal-relative
account can classify comfort incentives as wrong-kind without answerability.

## Deferred target registrations (PR #1374 review)

Restoration is tracked in [#1376](https://github.com/moritzbrantner/truth-core/issues/1376).

At head `6aac309f`, the two target arguments declared their conclusion as sense
bridges. Their conclusion is an existential of `IndependentInstance`, not a
proposition relating the registered senses, so those annotations were not
justified by the proofs. The two arguments, their inference/result records
and their Comparator configurations are deferred. Their owning spec entries
are removed; all six Lean theorem declarations, proof bodies and frozen types,
all nine new statements and all three new definitions remain.

The retained lemmas are
`TruthCore.Results.Logic.EpistemicAuthority.authorityFromAnswerability` and
`TruthCore.Results.Logic.EpistemicAuthority.constitutiveAimAuthority` in
`TruthCore/Results/Logic/EpistemicAuthority/Solution.lean`, with their frozen
types in `TruthCore/Results/Logic/EpistemicAuthority/Challenge.lean`.
`authorityRivalBundleInconsistent` and the controls still reuse the first lemma
as a Lean dependency. The direct target registrations are not required for
those compositions.

These identities are reserved for restoring the deferred registrations:

| Route | Argument | Inference | Result |
|---|---|---|---|
| Actual force and answerability | `a6997c59-a25b-4fbd-ac03-f9648aa6837e` | `ec7430c3-43bb-4707-9c8f-d0d901b96f23` | `d3edec46-831e-49df-a4e0-7a77436d478b` |
| Universal aim satisfaction | `1ce421e8-2e2b-4e3a-9272-aee4ab43b7e7` | `b05690f0-0d4d-4ab7-9b8d-13db50776ab9` | `a18b54bf-3a52-48ba-b605-1e1160ddd8f9` |

Their former Comparator paths are
`results/d3edec46-831e-49df-a4e0-7a77436d478b/comparator.json` and
`results/a18b54bf-3a52-48ba-b605-1e1160ddd8f9/comparator.json`.
The argument, inference and result records use the corresponding UUID-named
JSON paths under `corpus/arguments/`, `corpus/inferences/` and `corpus/results/`.

The shared registration problem remains open: the target links the comparison
`Frame`, ordinary role and independent role as senses 1, 2 and 3 of
disambiguation `339c6bf8`. Keeping only the target's independent-role link still
leaves sense 1 in the premises, since `Frame` is their shared vocabulary.
Definition dependencies must distinguish that common vocabulary from asserted
sense relations. No checker change, new assumption, substitute bridge
annotation or stable-sense change has been applied here.

At reviewed head `6aac309f`, the profile definition is directly linked by 12
arguments and 22 statements; only this disambiguation registers it as a sense.
Apart from the disambiguation and the two new annotations, the sense-1 UUID
occurs only in the legacy allowlist entries for `EP-ROLE-INDEPENDENT-FROM-THIN`,
`EP-ROLE-INDEPENDENT-STRENGTHENS-ORDINARY`,
`EP-ROLE-NAMED-DEFINITION-ELIMINATION` and `EP-ROLE-ORDINARY-FROM-THIN`.
No argument declares sense 1 through `term_senses`. The current schema has no
sense-retirement field, so removing or repurposing the stable sense would
require a separate repair decision.

Reopen the direct registrations when the shared vocabulary/sense boundary is
repaired without hiding genuine ordinary-to-independent or thin-to-independent
transfers. Represent any needed transfer as an explicit conditional relation,
preserving the actual-force/answerability and goal-relative/universal-aim
assumptions. Restore the reserved records through the owning batch spec, then
check corpus references, exact theorem binding, Comparator and NanoDa evidence,
the computed premise delta and independent semantic review before treating
either route as registered target support.

The review also corrected the constitutive-aim paraphrase and theorem comments:
the type requires universal aim satisfaction but does not encode why the aim
belongs to belief or whether it is a desire. The frozen theorem types and
proof bodies are unchanged.
