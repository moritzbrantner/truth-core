module

public import TruthCore.Case.Catholicism.PrimaViaStrengthBoundaries
public import TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFacts.WeakReadingDoesNotYield.Solution
public import TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaRelative.Solution
public import TruthCore.Results.Aristotle.Physics.Typed.LocalRegressFromPerSeRegress.Solution
public import TruthCore.Results.Aristotle.Physics.Typed.MovedByAnotherRegressFromPerSeRegress.Solution

@[expose] public section
namespace TruthCore.Results.Case.Catholicism.StrengthConsumers.Boundary
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.PrimaViaStrengthBoundaries
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels

private theorem allWeakBeingsMoved : ∀ subject : weakModel.Being, ∃ r, weakModel.MovedIn subject r := by
  intro subject
  cases subject with
  | f => exact ⟨.other, trivial⟩
  | g => exact ⟨.other2, trivial⟩
  | x => exact ⟨.heat, trivial⟩

private theorem noWeakFirst : ¬ ∃ subject, IsFirstUnmovedMover weakModel.MovedIn weakModel.MovesIn subject := by
  rintro ⟨subject, _, hUnmoved⟩
  obtain ⟨r, hr⟩ := allWeakBeingsMoved subject
  exact hUnmoved r hr

/-- Boundary controls for five exact consumer interfaces; EM remains explicit. -/
theorem weakConsumerBoundaries (hEM : TruthCore.Logic.ExcludedMiddle) : WeakConsumerBoundaries := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFacts.WeakReadingDoesNotYield.weakReadingDoesNotYieldUnmovedMover
    intro M ⟨hSense, hPotency, hAct, hReduction, hNotBoth, hPerSe, hRegress⟩
    exact h M hSense hPotency
      (fun x r hr => by obtain ⟨y, hy⟩ := hReduction x r hr; exact ⟨y, hy, hAct y x r hy⟩)
      hNotBoth hPerSe hRegress
  · intro h
    apply TruthCore.Results.Aristotle.Physics.Typed.LocalRegressFromPerSeRegress.premisesNeeded.1
    intro B R isLocal moved moves primary links hRegress
    exact h B R isLocal moved moves primary links (fun _ _ _ _ => False)
      (fun _ _ _ _ _ _ _ hFalse => hFalse.elim) hRegress
  · intro h
    apply TruthCore.Results.Aristotle.Physics.Typed.MovedByAnotherRegressFromPerSeRegress.premisesNeeded.2.1
    intro B R moved moves links hInMoved hRegress
    exact h B R moved moves links (fun _ _ _ _ => False) hInMoved
      (fun _ _ _ _ _ _ _ hFalse => hFalse.elim) hRegress
  · obtain ⟨hSense, hPotency, hAct, hReduction, hNotBoth, hPerSe, hRegress⟩ := weakModel_premises
    refine ⟨weakModel, weakModel_premises, ?_, Or.inr noWeakFirst, ?_, ?_, ?_, ?_⟩
    · exact TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaRelative.primaViaRelative
        weakModel.MovedIn weakModel.MovesIn weakModel.InPotency weakModel.InAct
        weakModel.MovesAsMoved weakModel.RelevantTo hSense hPotency hAct hReduction hNotBoth hPerSe hRegress
    · intro subject other hf _
      exact (noWeakFirst ⟨subject, hf⟩).elim
    · intro subject hf
      exact (noWeakFirst ⟨subject, hf⟩).elim
    · intro subject hf
      exact (noWeakFirst ⟨subject, hf⟩).elim
    · rintro ⟨_, hFalse⟩
      exact hFalse
  · intro h
    obtain ⟨_, hPotency, hAct, hReduction, hNotBoth, hPerSe, hRegress⟩ := weakModel_premises
    have hConclusion := h weakModel.Being weakModel.Respect Unit weakModel.MovedIn weakModel.MovesIn
      weakModel.InPotency weakModel.InAct weakModel.MovesAsMoved weakModel.RelevantTo
      (fun _ => True) (fun _ => False) (fun _ => False) (fun _ _ _ => True)
      hPotency hAct hNotBoth hReduction hPerSe hRegress hEM
      (fun _ _ _ _ _ _ _ _ => trivial)
      (fun subject _ _ _ hUnmoved => by
        obtain ⟨r, hr⟩ := allWeakBeingsMoved subject
        exact (hUnmoved r hr).elim)
    obtain ⟨_, hFalse, _⟩ := hConclusion .x .x () trivial trivial
    exact hFalse
end TruthCore.Results.Case.Catholicism.StrengthConsumers.Boundary
