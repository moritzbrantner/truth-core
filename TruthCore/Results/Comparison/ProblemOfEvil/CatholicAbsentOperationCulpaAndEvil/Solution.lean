import TruthCore.Comparison.ProblemOfEvilCulpa

namespace TruthCore.Results.Comparison.ProblemOfEvil.CatholicAbsentOperationCulpaAndEvil
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Comparison.ProblemOfEvilCulpa

theorem catholicAbsentOperationCulpaAndEvil (s : Sig)
    (hCatholic : CatholicOperationalGrounding s) :
    AbsentVoluntaryOperationIsCulpaAndEvilReading s.Voluntary s.Due s.Performs s.Culpa s.Evil := by
  obtain ⟨hPrivation, hCulpa⟩ := hCatholic
  intro a o hVoluntary hDue hAbsent
  have hFault := hCulpa a o hVoluntary hDue (Or.inl hAbsent)
  have hEvil := (hPrivation a).mpr ⟨o, hDue, hAbsent⟩
  exact ⟨hFault, hEvil⟩
end TruthCore.Results.Comparison.ProblemOfEvil.CatholicAbsentOperationCulpaAndEvil
