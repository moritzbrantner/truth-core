module

public import TruthCore.Logic.TranscendentalPractice
public import TruthCore.Results.Logic.CorrectionCriterion.Solution

@[expose] public section

namespace TruthCore.Results.Logic.TranscendentalPractice.InquiryAccess

open TruthCore.Logic.CorrectionCriterion
open TruthCore.Logic.ReflectiveCoherence
open TruthCore.Logic.TranscendentalPractice

/-- Reuse the certified exact-classifier factorization and its two-state
countermodel; independently witness the truth-directed and non-truth-directed
selection policies on that same semantics. -/
theorem boundary : InquiryAccessBoundary := by
  have hCriterion : CriterionCharacterizationAndControls :=
    TruthCore.Results.Logic.CorrectionCriterion.characterization
  constructor
  · intro World Claim Evidence S observe p hAvailable
    exact (hCriterion.1 World Evidence observe (fun w => S.trueAt w p)).mp hAvailable
  constructor
  · refine ⟨(fun Γ => Γ = emptyWorldview), ?_, rfl, ?_⟩
    · intro Γ hSelected
      change Γ = emptyWorldview at hSelected
      subst Γ
      intro p hAccepted
      exact False.elim hAccepted
    · exact hCriterion.2.2.1
  · constructor
    · exact ⟨(fun w => w = true), fun _ => Iff.rfl⟩
    · intro hTruthDirected
      have hDenier := hTruthDirected deniesDuty rfl
      have hFalse := hDenier false rfl
      change true = false at hFalse
      cases hFalse

end TruthCore.Results.Logic.TranscendentalPractice.InquiryAccess
