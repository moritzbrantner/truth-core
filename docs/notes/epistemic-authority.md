# Evidential merit versus preference-independent authority (#930)

Question: does warranted evidence give someone a pro tanto reason to correct a
factual belief even when they are indifferent to accuracy? Target:
STMT-THERE-ARE-PREFERENCE-INDEPENDENT-EPISTEMIC-REASONS (`2ca463c2`), under
its exact paraphrase (pro tanto, not overriding; no agent-neutrality or
factivity). Analyst formulations; attribution deferred. Spec:
`specs/epistemic-authority.toml`; Lean: `TruthCore/Logic/EpistemicAuthority.lean`,
`TruthCore/Results/Logic/EpistemicAuthority/Solution.lean`.

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

## New checked structure

- `authorityFromAnswerability`: `ActualForceConcession f`,
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
- `constitutiveAimAuthority`: F6, presentation, ordinary definition (composed
  through the existing `ordinaryFromThin`), `GoalRelativeForce f aims`,
  `ConstitutiveAim f aims` ⊢ target. In Lean `ConstitutiveAim` is only
  `∀ d, aims d`, indistinguishable from universal desire for accuracy. It
  secures the target by excluding indifferent profiles from the comparison
  class, not by giving an indifferent subject a reason, so it is no support for
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
