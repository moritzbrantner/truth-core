module

public import TruthCore.Logic.EpistemicAuthority
public import TruthCore.Results.Logic.EpistemicReasonDefinitions.OrdinaryFromThin.Solution

@[expose] public section

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
  obtain ⟨a, r, p, hOrd, hForce⟩ := hConcession
  exact ⟨a, r, f.believe p, hOrd, fun d => hAnswer a r p _ d hForce⟩

/-- The goal-relative account with an indifference alternative excludes any
preference-independent reason in the same frame. -/
theorem goalRelativeExcludesAuthority (f : Frame) (aims : f.Preference → Prop)
    (hGoal : GoalRelativeForce f aims)
    (hIndiff : IndifferenceAvailable f aims) :
    NoPreferenceIndependentReason f := by
  rintro ⟨a, r, t, _, hAll⟩
  obtain ⟨d, hd⟩ := hIndiff
  exact hd ((hGoal a r t d).mp (hAll d)).2

/-- Inside the goal-relative structure, a constitutive (non-preferential)
accuracy aim restores preference independence. Composes the existing
`ordinaryFromThin` for the ordinary witness. -/
theorem constitutiveAimAuthority (f : Frame) (aims : f.Preference → Prop)
    (hThin : ThereAreEpistemicReasons f.Reason)
    (hPresentation : ConsiderationPresentation f)
    (hDefinition : OrdinaryDefinition f)
    (hGoal : GoalRelativeForce f aims)
    (hAim : ConstitutiveAim f aims) :
    SomePreferenceIndependentReason f := by
  obtain ⟨a, r, t, hOrd⟩ :=
    TruthCore.Results.Logic.EpistemicReasonDefinitions.OrdinaryFromThin.ordinaryFromThin
      f hThin hPresentation hDefinition
  exact ⟨a, r, t, hOrd, fun d => (hGoal a r t d).mpr ⟨hOrd.2, hAim d⟩⟩

private theorem goalThin : ThereAreEpistemicReasons goalRelative.Reason :=
  ⟨(), .even, rfl⟩

private theorem goalPresentation : ConsiderationPresentation goalRelative := by
  intro _ p
  constructor
  · intro hp
    exact ⟨.count, rfl, hp⟩
  · rintro ⟨_, _, hp⟩
    exact hp

private theorem goalOrdinary : OrdinaryDefinition goalRelative := by
  intro _ _ _
  exact ⟨fun h => ⟨trivial, trivial, h⟩, fun h => h.2.2⟩

private theorem goalForce : GoalRelativeForce goalRelative accuracyAim := by
  intro _ r t d
  constructor
  · rintro ⟨hr, ht, hd⟩
    exact ⟨⟨trivial, trivial, hr, ht⟩, hd⟩
  · rintro ⟨⟨_, _, hr, ht⟩, hd⟩
    exact ⟨hr, ht, hd⟩

private theorem goalIndiff : IndifferenceAvailable goalRelative accuracyAim :=
  ⟨.comfort, by intro h; cases h⟩

private theorem goalNoAnswer : ¬ BeliefAnswerability goalRelative := by
  intro h
  have := h () .count .even .accuracy .comfort ⟨rfl, rfl, rfl⟩
  cases this.2.2

theorem controls : Controls := by
  refine ⟨⟨goalThin, goalPresentation, goalOrdinary,
      ⟨(), .count, .even, ⟨⟨rfl, rfl⟩, trivial, trivial, rfl, rfl⟩, rfl, rfl, rfl⟩,
      goalForce, goalIndiff, goalNoAnswer,
      goalRelativeExcludesAuthority goalRelative accuracyAim goalForce goalIndiff⟩,
    ⟨goalThin, goalPresentation, goalOrdinary, goalForce,
      ⟨(), .count, .even, ⟨⟨rfl, rfl⟩, trivial, trivial, rfl, rfl⟩,
        fun h => by cases h.2.2⟩, ?_⟩,
    ⟨fun _ _ _ _ _ h => h.elim, goalOrdinary, ?_, ?_⟩,
    ⟨⟨(), .count, .even, ⟨⟨rfl, rfl⟩, trivial, trivial, rfl, rfl⟩, rfl, rfl⟩,
      fun _ _ _ _ _ h => h,
      authorityFromAnswerability independent
        ⟨(), .count, .even, ⟨⟨rfl, rfl⟩, trivial, trivial, rfl, rfl⟩, rfl, rfl⟩
        (fun _ _ _ _ _ h => h)⟩⟩
  · rintro ⟨_, _, _, _, hForce⟩
    cases hForce.2.2
  · rintro ⟨_, _, _, _, hForce⟩
    exact hForce
  · rintro ⟨_, _, _, _, hAll⟩
    exact hAll .accuracy

end TruthCore.Results.Logic.EpistemicAuthority
