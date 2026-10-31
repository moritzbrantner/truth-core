import TruthCore.Explanation.EmptyHistoryCountControl
import TruthCore.Results.Causality.CountTemporalControls.Solution
namespace TruthCore.Results.Explanation.EmptyHistoryCountControl
open TruthCore.Explanation.EmptyHistoryCountControl
open TruthCore.Explanation.EmptyHistoryCausalAvailability
open TruthCore.Models.CountTemporalControls
open TruthCore.Explanation.PSRStrength (Contingent)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Logic (ExcludedMiddle)

private theorem noContingents : NoContingentConcreteAt arena Concrete false := by
  intro b _ hCont
  cases b with
  | none =>
    obtain ⟨_, v, _, hAbsent⟩ := hCont
    exact hAbsent trivial
  | some i =>
    have hFalse : false = true := hCont.1
    cases hFalse

private theorem actualContingent : ContingentAt arena.ontic true (some (0 : Fin 5)) := by
  refine ⟨rfl, false, trivial, ?_⟩
  intro h
  cases h

private theorem negativeContingent : Contingent arena false none := by
  refine ⟨noContingents, true, trivial, ?_⟩
  intro h
  exact h (some (0 : Fin 5)) trivial actualContingent

private theorem negativeCaused : ActualCausedFact arena Concrete causeFact false none :=
  ⟨noContingents, none, trivial, trivial, rfl, rfl, rfl⟩

private theorem coverage : WeakActualConcreteCausalAvailabilityAt arena Concrete causeFact false := by
  intro f hCont
  cases f with
  | none => exact ⟨false, trivial, negativeCaused⟩
  | some b =>
    cases b with
    | none =>
      obtain ⟨_, v, _, hAbsent⟩ := hCont
      exact (hAbsent trivial).elim
    | some i =>
      have hFalse : false = true := hCont.1
      cases hFalse

private theorem retained : RetainedInputs := by
  refine ⟨(fun _ _ _ _ _ => trivial), trivial, (fun _ => Iff.rfl),
    ⟨false, trivial, noContingents, coverage⟩, true, trivial, ?_⟩
  exact ⟨some (0 : Fin 5), trivial, rfl⟩

theorem checks (hEM : ExcludedMiddle) : Control := by
  exact ⟨TruthCore.Results.Causality.CountTemporalControls.checks hEM, rfl,
    (fun _ _ => Iff.rfl), retained, negativeContingent, negativeCaused,
    actualContingent, (fun _ => ⟨none, trivial, trivial⟩),
    (fun _ _ _ h => h), (fun _ _ _ h => h)⟩
end TruthCore.Results.Explanation.EmptyHistoryCountControl
