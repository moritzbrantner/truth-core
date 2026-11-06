module
public import TruthCore.Comparison.ProblemOfEvil
@[expose] public section
namespace TruthCore.Results.Comparison.ProblemOfEvil.FromDueDeficiency
open TruthCore.Comparison.ProblemOfEvil
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- The typed privation/deficiency inference uses no motion or God commitment. -/
theorem evilFromDueDeficiency (s : Sig)
    (hPrivation : EvilIsPrivationReading s.Evil s.Due s.Has)
    (hLacks : SomethingFallsShortOfDueGoodReading s.Due s.Has) :
    EvilIsFoundInThingsReading s.Evil := by
  obtain ⟨subject, perfection, hDue, hAbsent⟩ := hLacks
  exact ⟨subject, (hPrivation subject).mpr ⟨perfection, hDue, hAbsent⟩⟩
end TruthCore.Results.Comparison.ProblemOfEvil.FromDueDeficiency
