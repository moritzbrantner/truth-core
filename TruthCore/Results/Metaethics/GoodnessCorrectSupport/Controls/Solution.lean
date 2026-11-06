module
public import TruthCore.Metaethics.GoodnessCorrectSupport
public import TruthCore.Results.Metaethics.GoodnessFormEndBoundary.Solution
@[expose] public section
namespace TruthCore.Results.Metaethics.GoodnessCorrectSupport.Controls
open TruthCore.Metaethics.GoodnessFormEnd
open TruthCore.Metaethics.GoodnessCorrectSupport
theorem strictControl : StrictControl := by
  have hCorrect : CorrectAccount widerSpace .due := fun _ _ => Iff.rfl
  have hNamed : SemanticallyNamed widerSpace .due :=
    Or.inl (fun _ _ => Iff.rfl)
  have hWrong : ¬ CorrectAccount widerSpace .other := by
    intro h
    have bad := (h .knife .existence).mp
      (show (artifactWithGood false).GoodIn .knife .existence from ⟨True.intro, True.intro⟩)
    cases bad.2
  have hUnnamed : ¬ SemanticallyNamed widerSpace .other := by
    rintro (hDue | hOther)
    · exact ((hDue .knife .mass).mp ⟨rfl, rfl⟩).1
    · rcases hOther with hFeature | hApproval
      · have bad := (hFeature .counterweight .mass).mpr True.intro
        cases bad.1
      · have bad := (hApproval .counterweight .mass).mpr ⟨rfl, True.intro, True.intro⟩
        cases bad.1
  refine ⟨⟨.due, True.intro, hCorrect⟩, ?_, ?_, ?_, ?_,
    True.intro, hCorrect, hNamed, True.intro, hWrong, hUnnamed, ?_⟩
  · intro _
    exact ⟨.due, True.intro, hCorrect, hNamed⟩
  · exact TruthCore.Results.Metaethics.GoodnessFormEndBoundary.namedControls.1.2.2.1
  · exact TruthCore.Results.Metaethics.GoodnessFormEndBoundary.namedControls.1.2.2.2
  · intro _ _
    exact Iff.rfl
  · intro hGlobal
    exact hUnnamed (hGlobal .other True.intro)
end TruthCore.Results.Metaethics.GoodnessCorrectSupport.Controls
