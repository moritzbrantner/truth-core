module

public import TruthCore.Metaethics.GoodnessFormEnd

@[expose] public section
namespace TruthCore.Results.Metaethics.GoodnessCoverageStrength
open TruthCore.Metaethics.GoodnessFormEnd

theorem identityCoverageEntailsSemantic (f : Frame) (s : DefinitionSpace f)
    (h : NamedCoverage s) : SemanticNamedCoverage s := by
  intro d hd
  rcases h d hd with hDue | hOther
  · rw [hDue]
    exact Or.inl (fun _ _ => Iff.rfl)
  · rcases hOther with hFeature | hApproval
    · rw [hFeature]
      exact Or.inr (Or.inl (fun _ _ => Iff.rfl))
    · rw [hApproval]
      exact Or.inr (Or.inr (fun _ _ => Iff.rfl))
end TruthCore.Results.Metaethics.GoodnessCoverageStrength
