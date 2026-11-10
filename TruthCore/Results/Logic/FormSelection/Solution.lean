module

public import TruthCore.Logic.FormSelection

@[expose] public section
namespace TruthCore.Results.Logic.FormSelection
open TruthCore.Logic.FormSelection
open TruthCore.Latin.Aquinas.SummaTheologiae.FormReception

theorem selection : Selection := by
  intro C S F p ha hi c d hs
  exact (ha c).symm.trans ((congrArg (p.decode c) hs).trans ((hi c d (p.state d)).trans (ha d)))

theorem controls : Controls := by
  exact ⟨⟨false, True.intro, .withoutMatter, rfl⟩,
    (fun _ => ⟨True.intro, rfl⟩), (fun h => h), (fun _ => rfl), rfl,
    Bool.noConfusion, (fun _ => rfl), Bool.noConfusion⟩

theorem referenceControls : ReferenceControls := by
  exact ⟨rfl, Bool.noConfusion, rfl, rfl, Bool.noConfusion⟩

end TruthCore.Results.Logic.FormSelection
