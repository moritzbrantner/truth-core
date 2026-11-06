module
public import TruthCore.Metaethics.GoodnessCorrectSupport
@[expose] public section
namespace TruthCore.Results.Metaethics.GoodnessCorrectSupport.CorrectCoverage
open TruthCore.Metaethics.GoodnessFormEnd
open TruthCore.Metaethics.GoodnessCorrectSupport
theorem supportCoverageEquivalence : SupportCoverageEquivalence := by
  intro f s
  constructor
  · intro hSupport e hAdmissible hCorrectE
    obtain ⟨d, _, hCorrectD, hNamed⟩ := hSupport ⟨e, hAdmissible, hCorrectE⟩
    have hSame : Coextensive s e d := fun x p =>
      (hCorrectE x p).symm.trans (hCorrectD x p)
    rcases hNamed with hDue | hOthers
    · exact Or.inl (fun x p => (hSame x p).trans (hDue x p))
    · rcases hOthers with hFeature | hApproval
      · exact Or.inr (Or.inl (fun x p => (hSame x p).trans (hFeature x p)))
      · exact Or.inr (Or.inr (fun x p => (hSame x p).trans (hApproval x p)))
  · intro hAll ⟨d, hAdmissible, hCorrect⟩
    exact ⟨d, hAdmissible, hCorrect, hAll d hAdmissible hCorrect⟩
end TruthCore.Results.Metaethics.GoodnessCorrectSupport.CorrectCoverage
