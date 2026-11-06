module

public import TruthCore.Logic.ScopedEmpiricalProofBarrier
public import TruthCore.Results.Logic.ScopedEmpiricalProofBarrier.Scoped.Solution

@[expose] public section
namespace TruthCore.Results.Logic.ScopedEmpiricalProofBarrier.Controls
open TruthCore.Logic.Verificationism
open TruthCore.Logic.ScopedEmpiricalProofBarrier
open TruthCore.Logic.ScopedEmpiricalProofBarrier.Control
open TruthCore.Results.Logic.Verificationism.VerdictSilent
theorem controls : Control.Properties := by
  have hiddenBarrier : ObservationBarrier observableFrame beginning := by
    intro ⟨a, b⟩ h
    refine ⟨(a, false), ?_, ?_⟩
    · intro o ho
      change o (a, b) = true ↔ o (a, false) = true
      have eq := ho a b false
      exact ⟨fun hx => eq ▸ hx, fun hx => eq.symm ▸ hx⟩
    · intro hFalse
      exact Bool.noConfusion hFalse
  have scopedBarrier : ScopedObservationBarrier observableFrame inquiries selected := by
    intro t ht
    cases ht
    exact hiddenBarrier
  have tautologyProof : ConclusivelyVerifiable observableFrame tautology := by
    refine ⟨[], ?_, ⟨(false, false), ?_⟩, ?_⟩
    · intro o ho
      cases ho
    · intro o ho
      cases ho
    · intro w hw
      rfl
  have selectedUnavailable := Scoped.restrictedFromBarrier observableFrame inquiries selected scopedBarrier
  have notSelectedTautology : ¬ selected .theologicalTautology := by
    intro h
    cases h
  refine ⟨?_, scopedBarrier, selectedUnavailable, ?_, ⟨?_, ?_, ?_⟩,
    ?_, ⟨?_, List.Mem.head [], rfl⟩, ⟨rfl, ?_, ?_⟩,
    ⟨?_, ?_, ?_, Barrier.barrier observableFrame beginning hiddenBarrier⟩,
    ⟨rfl, rfl⟩, ?_, ?_⟩
  · intro ⟨a, b⟩
    cases b
    · constructor
      · intro h
        exact False.elim (Bool.noConfusion h)
      · intro ⟨t, _, hNever⟩
        exact False.elim (hNever (t + 1) (Nat.lt_succ_self t))
    · constructor
      · intro h
        exact ⟨0, Or.inl rfl, fun t ht => Nat.not_lt_zero t ht⟩
      · intro h
        rfl
  · intro hGlobal
    exact hGlobal .theologicalTautology tautologyProof
  · intro h
    exact notSelectedTautology ((h .theologicalTautology).mpr rfl)
  · intro h
    exact notSelectedTautology ((h .theologicalTautology).mpr (List.Mem.head []))
  · intro h
    exact notSelectedTautology ((h .theologicalTautology).mpr rfl)
  · intro c
    cases c
    · exact ⟨rfl, tautologyProof⟩
    · exact ⟨List.Mem.head [], tautologyProof⟩
    · exact ⟨rfl, tautologyProof⟩
  · intro h
    cases h
  · intro h
    cases h
  · intro h
    cases h
  · intro h
    cases h
  · intro h
    cases h
  · intro h
    cases h
  · intro w hw
    exact hw beginning (List.Mem.head [])
  · refine ⟨[observable], ?_, ⟨(true, false), ?_⟩, ?_⟩
    · intro o ho
      cases ho with
      | head => exact fun _ _ _ => rfl
      | tail _ h => cases h
    · intro o ho
      cases ho with
      | head => rfl
      | tail _ h => cases h
    · intro w hw
      exact hw observable (List.Mem.head [])
end TruthCore.Results.Logic.ScopedEmpiricalProofBarrier.Controls
