module

public import TruthCore.Logic.Verificationism
public import TruthCore.Results.Logic.Verificationism.Church.Solution

@[expose] public section

namespace TruthCore.Results.Logic.Verificationism.Ayer1946Exclusion
open TruthCore.Logic.Verificationism
/-- No 1946 frame excludes a sentence together with its negation: wherever Church's observation statements exist, no sentence and its negation both fail to be literally meaningful. -/
theorem ayer1946ExclusionFails : Ayer1946ExclusionFails := by
  intro L F ⟨⟨o₁, o₂, o₃, h⟩, m, hm, hnm⟩
  have hnd : ¬ DirectlyVerifiable F (L.neg m) := fun hd => hnm (Or.inr (Or.inl hd))
  exact hm (Or.inr (Or.inr (Church.churchTrivialization L F o₁ o₂ o₃ h m hnd)))
end TruthCore.Results.Logic.Verificationism.Ayer1946Exclusion
