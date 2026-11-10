module

public import TruthCore.Logic.EpistemicReasonDefinitionFork

/-!
# Evidential merit versus preference-independent authority (#930)

Analyst formulations; attribution deferred. The question: does evidence that
favors a factual belief give a pro tanto reason to the subject even under a
preference profile indifferent to accuracy? The existing `Frame` already keeps
favoring (evidential merit under the selected standard) apart from `force`
(pro tanto normative authority at a supplied preference). This module adds
three explicit, independently failing inputs:

* `ActualForceConcession`: some ordinary-role reason for a belief has force at
  its subject's actual preference. The goal-relative rival grants this for an
  accuracy-valuing subject whose evidence favors the belief.
* `BeliefAnswerability`: for belief attitudes, force does not vary with the
  supplied preference coordinate (subject, consideration and content fixed).
  This is the contested bridge: belief answers to its subject matter, not to
  the believer's desires. It is restricted to belief; it says nothing about
  practical attitudes and is not an ontic sufficient-reason principle (#756).
* `GoalRelativeForce aims`: the instrumentalist rival. Force at a preference
  obtains iff the consideration plays the ordinary epistemic role and that
  preference includes the accuracy aim `aims`.

`ConstitutiveAim aims` says every supplied preference alternative includes the
aim, as the constitutive-aim reply to indifference cases holds for believers.
These are framework inputs; no theorem here establishes any of them. -/

@[expose] public section

namespace TruthCore.Logic.EpistemicAuthority

open TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.EpistemicReasonDefinitionFork

/-- Some ordinary-role reason for a belief has force for its subject at that
subject's actual preference. Rival-neutral: accepted by the goal-relative
account whenever an accuracy-valuing subject has favoring evidence. -/
def ActualForceConcession (f : Frame) : Prop :=
  ∃ a r p, OrdinaryInstance f a r (f.believe p) ∧
    f.force a r (f.believe p) (f.actualPreference a)

/-- Answerability bridge, restricted to belief: a consideration's force for a
belief at one supplied preference carries over to every supplied preference,
other coordinates fixed. It can fail (see `goalRelative`). -/
def BeliefAnswerability (f : Frame) : Prop :=
  ∀ a r p d d', f.force a r (f.believe p) d → f.force a r (f.believe p) d'

/-- The goal-relative (instrumentalist) account of epistemic force, with the
accuracy aim as an explicit predicate on supplied preferences. -/
def GoalRelativeForce (f : Frame) (aims : f.Preference → Prop) : Prop :=
  ∀ a r t d, f.force a r t d ↔ (EpistemicRole f a r t ∧ aims d)

/-- Some supplied preference alternative lacks the accuracy aim. -/
def IndifferenceAvailable (f : Frame) (aims : f.Preference → Prop) : Prop :=
  ∃ d, ¬ aims d

/-- Constitutive-aim reply: every supplied preference alternative of the
compared subjects includes the accuracy aim. -/
def ConstitutiveAim (f : Frame) (aims : f.Preference → Prop) : Prop :=
  ∀ d, aims d

/-- No ordinary-role reason in the frame keeps force across every supplied
preference alternative. Negation of `SomePreferenceIndependentReason`. -/
def NoPreferenceIndependentReason (f : Frame) : Prop :=
  ¬ SomePreferenceIndependentReason f

/-- Some ordinary-role reason for a belief whose subject's actual preference
satisfies the supplied accuracy aim. -/
def AimedOrdinaryBelief (f : Frame) (aims : f.Preference → Prop) : Prop :=
  ∃ a r p, OrdinaryInstance f a r (f.believe p) ∧ aims (f.actualPreference a)

/-- The four-member bundle concession, answerability, goal-relative force and
an indifference alternative is not jointly satisfiable in the frame. -/
def AuthorityRivalBundleInconsistent (f : Frame) (aims : f.Preference → Prop) : Prop :=
  ¬ (ActualForceConcession f ∧ BeliefAnswerability f ∧ GoalRelativeForce f aims ∧
    IndifferenceAvailable f aims)

/-- The `goalRelative` evidence profile with an indifferent actual preference:
the count still favors the even answer but has no force at comfort. -/
def indifferentAgent : Frame :=
  { goalRelative with actualPreference := fun _ => .comfort }

/-- The `goalRelative` evidence profile in which nothing has force anywhere:
preference-insensitive, but with no actual force to carry over. -/
def forceless : Frame :=
  { goalRelative with force := fun _ _ _ _ => False }

/-- The accuracy aim of the finite controls. -/
def accuracyAim : Preference → Prop := fun d => d = .accuracy

/-- An aim met by every supplied preference (constitutive-aim witness). -/
def allAim : Preference → Prop := fun _ => True

/-- Finite controls (analyst interpretations, not actual normative facts):
(1) `goalRelative` satisfies F6, presentation, the ordinary definition, the
concession and the goal-relative account with an indifference alternative,
but not answerability or the conclusion; (2) `indifferentAgent` satisfies F6,
presentation, the ordinary definition and the goal-relative account, while an
ordinary reason of an actually indifferent subject has no actual force;
(3) `forceless` satisfies answerability without the concession or conclusion;
(4) `independent` satisfies the concession, answerability and the conclusion;
(5) `independent` with the accuracy aim has an indifference alternative and the
conclusion but not goal-relative force; (6) `independent` with `allAim` has
goal-relative force, the constitutive aim and the conclusion but no indifference
alternative. (5) and (6) are omission controls for
`goalRelativeExcludesAuthority`; (6) is a nonvacuity witness for the
constitutive-aim argument. -/
def Controls : Prop :=
  (ThereAreEpistemicReasons goalRelative.Reason ∧ ConsiderationPresentation goalRelative ∧
    OrdinaryDefinition goalRelative ∧ ActualForceConcession goalRelative ∧
    GoalRelativeForce goalRelative accuracyAim ∧
    IndifferenceAvailable goalRelative accuracyAim ∧
    ¬ BeliefAnswerability goalRelative ∧ NoPreferenceIndependentReason goalRelative) ∧
  (ThereAreEpistemicReasons indifferentAgent.Reason ∧
    ConsiderationPresentation indifferentAgent ∧ OrdinaryDefinition indifferentAgent ∧
    GoalRelativeForce indifferentAgent accuracyAim ∧
    (∃ a r t, OrdinaryInstance indifferentAgent a r t ∧
      ¬ indifferentAgent.force a r t (indifferentAgent.actualPreference a)) ∧
    ¬ ActualForceConcession indifferentAgent) ∧
  (BeliefAnswerability forceless ∧ OrdinaryDefinition forceless ∧
    ¬ ActualForceConcession forceless ∧ NoPreferenceIndependentReason forceless) ∧
  (ActualForceConcession independent ∧ BeliefAnswerability independent ∧
    SomePreferenceIndependentReason independent) ∧
  (¬ GoalRelativeForce independent accuracyAim ∧
    IndifferenceAvailable independent accuracyAim ∧
    SomePreferenceIndependentReason independent) ∧
  (ThereAreEpistemicReasons independent.Reason ∧ ConsiderationPresentation independent ∧
    OrdinaryDefinition independent ∧ GoalRelativeForce independent allAim ∧
    ConstitutiveAim independent allAim ∧ ¬ IndifferenceAvailable independent allAim ∧
    SomePreferenceIndependentReason independent)

end TruthCore.Logic.EpistemicAuthority
