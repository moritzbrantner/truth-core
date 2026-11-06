module

public import TruthCore.Logic.ObjectiveTruthDefinitionFork
public import TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.ProfileToTruth.Solution

@[expose] public section
namespace TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.Controls
open TruthCore.Logic.ObjectiveTruthDefinitionFork

theorem stableTrue : Stable actualStable Content.stableTrue := by
  intro p
  cases p <;> exact Iff.rfl

theorem stableFalse : Stable actualStable Content.stableFalse := by
  intro p
  cases p <;> exact Iff.rfl

theorem variableTrue : ¬ Stable actualStable Content.actualTrueVariable := by
  intro h
  exact (h true).mpr True.intro

theorem variableFalse : ¬ Stable actualStable Content.actualFalseVariable := by
  intro h
  exact (h true).mp True.intro

theorem strongCalibration : ActualStableDefinition actualStable := by
  intro s
  cases s with
  | stableTrue =>
    exact ⟨fun _ => ⟨True.intro, stableTrue⟩, fun _ => rfl⟩
  | stableFalse =>
    constructor
    · intro h; cases h
    · intro h; exact False.elim h.1
  | actualTrueVariable =>
    constructor
    · intro h; cases h
    · intro h; exact False.elim (variableTrue h.2)
  | actualFalseVariable =>
    constructor
    · intro h; cases h
    · intro h; exact False.elim h.1

theorem invariantCalibration : InvariantOnlyDefinition invariantOnly := by
  intro s
  cases s with
  | stableTrue => exact ⟨fun _ => stableTrue, fun _ => Or.inl rfl⟩
  | stableFalse => exact ⟨fun _ => stableFalse, fun _ => Or.inr rfl⟩
  | actualTrueVariable =>
    constructor
    · intro h; cases h with | inl h => cases h | inr h => cases h
    · intro h; exact False.elim (variableTrue h)
  | actualFalseVariable =>
    constructor
    · intro h; cases h with | inl h => cases h | inr h => cases h
    · intro h; exact False.elim (variableFalse h)

theorem actualCalibration : ActualTruthOnlyDefinition actualOnly := by
  intro s
  cases s with
  | stableTrue => exact ⟨fun _ => True.intro, fun _ => Or.inl rfl⟩
  | stableFalse =>
    constructor
    · intro h; cases h with | inl h => cases h | inr h => cases h
    · intro h; exact False.elim h
  | actualTrueVariable => exact ⟨fun _ => True.intro, fun _ => Or.inr rfl⟩
  | actualFalseVariable =>
    constructor
    · intro h; cases h with | inl h => cases h | inr h => cases h
    · intro h; exact False.elim h

theorem notStrongActual : ¬ ActualStableDefinition actualOnly := by
  intro h
  exact variableTrue ((h Content.actualTrueVariable).mp (Or.inr rfl)).2

theorem remainingCalibration : RemainingDefinition remaining := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact variableTrue ((h Content.actualTrueVariable).mp rfl).2
  · intro h
    have hBad := (h Content.stableTrue).mpr stableTrue
    cases hBad
  · intro h
    have hBad := (h Content.stableTrue).mpr True.intro
    cases hBad

theorem remainingTruth : HasTruthComponent remaining := by
  intro s h
  cases h
  exact True.intro

theorem overlapStableTrue : Stable overlap true := by
  intro p
  exact ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩

theorem overlapVariableFalse : ¬ Stable overlap false := by
  intro h
  have hBad := (h true).mp (Or.inr rfl)
  cases hBad with | inl h => cases h | inr h => cases h

theorem overlapStrong : ActualStableDefinition overlap := by
  intro s
  cases s with
  | false =>
    constructor
    · intro h; cases h
    · intro h; cases h.1 with | inl h => cases h | inr h => cases h
  | true => exact ⟨fun _ => ⟨Or.inl rfl, overlapStableTrue⟩, fun _ => rfl⟩

theorem overlapInvariant : InvariantOnlyDefinition overlap := by
  intro s
  cases s with
  | false =>
    constructor
    · intro h; cases h
    · intro h; exact False.elim (overlapVariableFalse h)
  | true => exact ⟨fun _ => overlapStableTrue, fun _ => rfl⟩

theorem overlapActual : ActualTruthOnlyDefinition overlap := by
  intro s
  cases s with
  | false =>
    constructor
    · intro h; cases h
    · intro h; cases h with | inl h => cases h | inr h => cases h
  | true => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩

theorem controls : Controls := by
  refine ⟨⟨strongCalibration, ?_, ?_, ?_⟩, ⟨invariantCalibration, ?_, Or.inr rfl, ?_⟩,
    ⟨actualCalibration, ?_, notStrongActual, Or.inr rfl, variableTrue⟩,
    ⟨remainingCalibration, remainingTruth, rfl, True.intro, ?_⟩,
    ⟨overlapStrong, overlapInvariant, overlapActual, rfl, ?_⟩⟩
  · exact ProfileToTruth.profileToTruth actualStable strongCalibration
  · intro h
    have hBad := (h Content.stableFalse).mpr stableFalse
    cases hBad
  · intro h
    have hBad := (h Content.actualTrueVariable).mpr True.intro
    cases hBad
  · intro h
    exact h Content.stableFalse (Or.inr rfl)
  · intro h
    exact h
  · intro s h
    exact (actualCalibration s).mp h
  · intro h
    cases h with
    | inl h => exact remainingCalibration.1 h
    | inr h =>
      cases h with
      | inl h => exact remainingCalibration.2.1 h
      | inr h => exact remainingCalibration.2.2 h
  · intro h
    cases h with | inl h => cases h | inr h => cases h

end TruthCore.Results.Logic.ObjectiveTruthDefinitionFork.Controls
