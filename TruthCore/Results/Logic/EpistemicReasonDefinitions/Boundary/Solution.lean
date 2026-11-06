module

public import TruthCore.Logic.EpistemicReasonDefinitionFork

@[expose] public section

namespace TruthCore.Results.Logic.EpistemicReasonDefinitions.Boundary

open TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.EpistemicReasonDefinitionFork

private theorem goalPresentation : ConsiderationPresentation goalRelative := by
  intro _ p
  constructor
  · intro hp
    exact ⟨.count, rfl, hp⟩
  · intro h
    obtain ⟨_, _, hp⟩ := h
    exact hp

private theorem goalOrdinary : OrdinaryDefinition goalRelative := by
  intro _ _ _
  exact ⟨fun h => ⟨trivial, trivial, h⟩, fun h => h.2.2⟩

private theorem goalSome : SomeOrdinaryReason goalRelative :=
  ⟨(), .count, .even, ⟨rfl, rfl⟩, trivial, trivial, rfl, rfl⟩

private theorem goalNoIndependent : ¬ SomePreferenceIndependentReason goalRelative := by
  intro h
  obtain ⟨_, _, _, _, hForce⟩ := h
  have hWrong : Preference.comfort = Preference.accuracy := (hForce .comfort).2.2
  cases hWrong

private theorem independentSome : SomePreferenceIndependentReason independent :=
  ⟨(), .count, .even, ⟨⟨rfl, rfl⟩, trivial, trivial, rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩

private theorem independentMeaning : PreferenceIndependentDefinition independent := by
  intro _ _ _
  constructor
  · intro h
    exact ⟨⟨trivial, trivial, h⟩, fun _ => h⟩
  · intro h
    exact h.1.2.2

private theorem productionPresentation : ConsiderationPresentation bareProduction := by
  intro _ p
  constructor
  · intro hp
    exact ⟨.reassurance, rfl, hp⟩
  · intro h
    obtain ⟨_, _, hp⟩ := h
    exact hp

private theorem productionMeaning : ProductionDefinition bareProduction := by
  intro _ _ _
  exact ⟨fun h => ⟨trivial, trivial, h⟩, fun h => h.2.2⟩

private theorem productionNoOrdinary : ¬ SomeOrdinaryReason bareProduction := by
  intro h
  obtain ⟨_, r, _, hCounts, hRole⟩ := h
  have hWrong : Consideration.reassurance = Consideration.count :=
    hCounts.1.symm.trans hRole.2.2.1
  cases hWrong

private theorem compatibleProduction : ProductionDefinition compatible := by
  intro _ _ _
  exact ⟨fun h => ⟨trivial, trivial, h⟩, fun h => h.2.2⟩

private theorem remainingMeanings : RemainingDefinition remaining := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact ((h () .count .even).mp ⟨rfl, rfl⟩).2.2
  · intro h
    exact ((h () .count .even).mp ⟨rfl, rfl⟩).1.2.2
  · intro h
    exact ((h () .count .even).mp ⟨rfl, rfl⟩).2.2
  · intro h
    exact ((h () .count .even).mp ⟨rfl, rfl⟩).2.2

private theorem remainingNoCoverage : ¬ NamedDefinitionCoverage remaining := by
  intro h
  cases h with
  | inl h => exact remainingMeanings.1 h
  | inr h =>
    cases h with
    | inl h => exact remainingMeanings.2.1 h
    | inr h =>
      cases h with
      | inl h => exact remainingMeanings.2.2.1 h
      | inr h => exact remainingMeanings.2.2.2 h

private theorem remainingNoOrdinary : ¬ SomeOrdinaryReason remaining := by
  intro h
  obtain ⟨_, _, _, _, hRole⟩ := h
  exact hRole.2.2

private theorem unpresentedOrdinary : OrdinaryDefinition unpresented := by
  intro _ _ _
  constructor
  · intro h
    exact False.elim h
  · intro h
    exact h.2.2

/-- Explicit finite controls of the definition comparisons; no actual normative
instance, access condition, or empirical interpretation is established. -/
theorem boundary : BoundaryCertificate := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨goalPresentation, goalOrdinary, ⟨(), .even, rfl⟩,
      goalSome, goalNoIndependent, ?_, ?_⟩
    · exact ⟨(), .count, .even, ⟨⟨rfl, rfl⟩, trivial, trivial, rfl, rfl⟩,
        rfl, rfl, rfl⟩
    · refine ⟨(), .count, .even, ⟨⟨rfl, rfl⟩, trivial, trivial, rfl, rfl⟩, ?_, ?_⟩
      · intro h
        have hWrong : Consideration.count = Consideration.reassurance := h.1
        cases hWrong
      · intro h
        have hWrong : Content.even = Content.rain := h
        cases hWrong
  · exact ⟨independentSome, goalOrdinary, independentMeaning⟩
  · exact ⟨productionPresentation, productionMeaning, productionMeaning,
      ⟨(), .even, rfl⟩, productionNoOrdinary⟩
  · exact ⟨goalOrdinary, independentMeaning, compatibleProduction, compatibleProduction⟩
  · exact ⟨goalPresentation, ⟨(), .even, rfl⟩, remainingMeanings,
      remainingNoCoverage, remainingNoOrdinary⟩
  · refine ⟨unpresentedOrdinary, ⟨(), .even, rfl⟩, ?_, ?_⟩
    · intro h
      obtain ⟨_, hCounts⟩ := (h () .even).mp rfl
      exact hCounts
    · intro h
      obtain ⟨_, _, _, hCounts, _⟩ := h
      exact hCounts

end TruthCore.Results.Logic.EpistemicReasonDefinitions.Boundary
