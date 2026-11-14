module

public import TruthCore.Explanation.EssenceReasonSeparation

@[expose] public section

namespace TruthCore.Results.Explanation.EssenceReasonSeparation

open TruthCore.Explanation.EssenceReasonSeparation
open TruthCore.Explanation.ExistencePSR
open TruthCore.German.Kant.CosmologicalInference

/-- Finite semantic controls for the two missing nature/explanation bridges.
The models certify only the explicit structural separation in the Challenge;
they do not rule out a substantive metaphysical principle connecting them. -/
theorem checks : SeparationControls := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨natureWithoutReason, ?_, ?_, ?_, ?_, ?_⟩
    · intro w x r h
      exact False.elim h
    · trivial
    · intro v _
      trivial
    · exact ⟨rfl, rfl⟩
    · intro h
      exact h
  · refine ⟨reasonWithoutNature, ?_, ?_, ?_, ?_, ?_⟩
    · intro w x r _
      trivial
    · trivial
    · intro v _
      trivial
    · intro h
      exact h
    · trivial
  · refine ⟨directedNature, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro w x r _
      trivial
    · intro v _
      trivial
    · intro v _
      trivial
    · intro v _ _
      trivial
    · intro v _ _
      trivial
    · exact ⟨rfl, rfl⟩
    · intro h
      cases h.1
    · intro h
      exact h
    · intro h
      exact h

end TruthCore.Results.Explanation.EssenceReasonSeparation
