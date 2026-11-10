import TruthCore.Logic.EpistemicAuthority
import TruthCore.Results.Logic.EpistemicReasonDefinitions.OrdinaryFromThin.Solution

namespace TruthCore.Results.Logic.EpistemicAuthority

open TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.EpistemicReasonDefinitionFork
open TruthCore.Logic.EpistemicAuthority

/-- Concession plus belief answerability give a preference-independent
ordinary reason. Both inputs are open; the goal-relative rival grants the first
and denies the second. -/
theorem authorityFromAnswerability (f : Frame)
    (hConcession : ActualForceConcession f)
    (hAnswer : BeliefAnswerability f) :
    SomePreferenceIndependentReason f := by
  sorry

/-- The goal-relative account with an indifference alternative excludes any
preference-independent reason in the same frame. -/
theorem goalRelativeExcludesAuthority (f : Frame) (aims : f.Preference → Prop)
    (hGoal : GoalRelativeForce f aims)
    (hIndiff : IndifferenceAvailable f aims) :
    NoPreferenceIndependentReason f := by
  sorry

/-- Inside the goal-relative structure, universal aim satisfaction gives
preference independence over the supplied comparison class. The aim's
constitutive or non-preferential origin is not encoded. Composes the existing
`ordinaryFromThin` for the ordinary witness. -/
theorem constitutiveAimAuthority (f : Frame) (aims : f.Preference → Prop)
    (hThin : ThereAreEpistemicReasons f.Reason)
    (hPresentation : ConsiderationPresentation f)
    (hDefinition : OrdinaryDefinition f)
    (hGoal : GoalRelativeForce f aims)
    (hAim : ConstitutiveAim f aims) :
    SomePreferenceIndependentReason f := by
  sorry

/-- The goal-relative account itself grants the concession whenever an
ordinary belief reason belongs to a subject whose actual preference has the aim. -/
theorem concessionFromGoalRelative (f : Frame) (aims : f.Preference → Prop)
    (hGoal : GoalRelativeForce f aims)
    (hAimed : AimedOrdinaryBelief f aims) :
    ActualForceConcession f := by
  sorry

/-- Composition of the answerability and goal-relative exclusion theorems. -/
theorem authorityRivalBundleInconsistent (f : Frame) (aims : f.Preference → Prop) :
    AuthorityRivalBundleInconsistent f aims := by
  sorry

theorem controls : Controls := by
  sorry

end TruthCore.Results.Logic.EpistemicAuthority
