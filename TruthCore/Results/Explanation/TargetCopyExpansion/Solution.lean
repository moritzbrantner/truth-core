import TruthCore.Explanation.TargetCopyExpansion
namespace TruthCore.Results.Explanation.TargetCopyExpansion
open TruthCore.Explanation.TargetCopyExpansion
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.BruteFoundationExplanations
open TruthCore.Explanation.ExistencePSR
open TruthCore.Logic.Regress

/-- Entailment holds because truth was copied, not because an independently
specified explanans determines the target. This works for every old reality. -/
theorem copiedCoverage (m : Profile W B) : EntailingCoverage (copied m) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro w r x ⟨rfl, hc, hx⟩
    exact ⟨⟨hc, hx⟩, hc, hx⟩
  · intro w x hc hx
    exact ⟨.fact x, ⟨hc, hx⟩, rfl, hc, hx⟩
  · rintro w r x ⟨rfl, _, _⟩ v _ h
    exact h.2

theorem controls : ArenaControls := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g w
    exact ⟨⟨0, trivial, trivial⟩, fun _ _ _ => trivial⟩
  · refine ⟨0, ?_, ?_⟩
    · rintro ⟨_, _, h⟩
      exact h rfl
    · intro n hn
      by_cases h : n = 0
      · exact h
      · exact (hn ⟨0, rfl, h⟩).elim
  · rintro ⟨_, _, hn⟩
    omega
  · rintro ⟨_, _, hn⟩
    omega
  · intro n hn
    have hlt : n < 2 := by
      by_contra h
      exact hn ⟨0, by omega, by omega⟩
    omega
  · intro n hn
    exact hn ⟨n + 1, rfl⟩
  · intro hw
    exact TruthCore.Causality.successorChainNotWellFounded hw.apply
  · intro g
    exact copiedCoverage (arena g)
  · rintro g ⟨r, hr⟩
    have h : (ExistenceFact.fact 0 : ExistenceFact Nat) = .fact 1 :=
      (hr 0).1.symm.trans (hr 1).1
    cases h

theorem checks : Certificate := by
  refine ⟨?_, ?_, controls⟩
  · intro W B m
    exact ⟨rfl, copiedCoverage m⟩
  · intro W B P
    constructor
    · intro h m
      exact h (copied m) (copiedCoverage m)
    · intro h e _
      exact h e.reality
end TruthCore.Results.Explanation.TargetCopyExpansion
