module

public import TruthCore.Logic.Verificationism.NegationClosure
public import TruthCore.Results.Logic.Verificationism.Church.Solution

@[expose] public section

namespace TruthCore.Results.Logic.Verificationism.Ayer1946Closure
open TruthCore.Logic.Verificationism

/-- The strengthened 1946 corollary counted: with meaningfulness closed under
negation, the V3 package fails. If ¬y were not meaningful, ¬y would not be
directly verifiable, so by Church y would be indirectly verifiable, hence
meaningful, and by closure ¬y would be meaningful. -/
theorem ayer1946ExcludesANegationFails {L : Language} (F : Frame L)
    (meaningful : L.Sentence → Prop) (hClosed : MeaningClosedUnderNegation L meaningful) :
    Ayer1946ExcludesANegationFails F meaningful := by
  intro ⟨hCrit, ⟨o₁, o₂, o₃, h⟩, y, hny⟩
  have hnd : ¬ DirectlyVerifiable F (L.neg y) :=
    fun hd => hny ((hCrit _).mpr (Or.inr (Or.inl hd)))
  have hy : meaningful y :=
    (hCrit _).mpr (Or.inr (Or.inr (Church.churchTrivialization L F o₁ o₂ o₃ h y hnd)))
  exact hny (hClosed y hy)

end TruthCore.Results.Logic.Verificationism.Ayer1946Closure
