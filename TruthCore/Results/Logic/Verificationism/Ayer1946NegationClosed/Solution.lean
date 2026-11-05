module

public import TruthCore.Logic.Verificationism
public import TruthCore.Results.Logic.Verificationism.Church.Solution

@[expose] public section

namespace TruthCore.Results.Logic.Verificationism.Ayer1946NegationClosed
open TruthCore.Logic.Verificationism
/-- With closure of 1946 meaningfulness under negation and Church's observation statements, no sentence fails to be literally meaningful. -/
theorem ayer1946NegationClosedExcludesNothing : Ayer1946NegationClosedExcludesNothing := by
  intro L F o₁ o₂ o₃ h hClosed s hNot
  have hnd : ¬ DirectlyVerifiable F (L.neg s) :=
    fun hd => hNot (hClosed s (Or.inr (Or.inl hd)))
  exact hNot (Or.inr (Or.inr (Church.churchTrivialization L F o₁ o₂ o₃ h s hnd)))
end TruthCore.Results.Logic.Verificationism.Ayer1946NegationClosed
