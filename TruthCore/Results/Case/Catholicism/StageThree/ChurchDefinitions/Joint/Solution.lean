module

public import TruthCore.Case.Catholicism.StageThree.ChurchDefinitions

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageThree.ChurchDefinitions.Joint

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.ChurchDefinitions

/-- Exact selected-criterion consequence; no source reading or history is established. -/
theorem jointCriterionSuppliesStageFive (σ : Signature) (church spiritual : σ.Society → Prop)
    (hCriterion : JointAspectCriterion σ church spiritual)
    (hFounded : ChristFoundedSelectedChurch σ church) : ChristFoundedVisibleChurch σ := by
  obtain ⟨c, hFoundedC, hChurch⟩ := hFounded
  exact ⟨c, hFoundedC, ((hCriterion c).1 hChurch).1⟩

end TruthCore.Results.Case.Catholicism.StageThree.ChurchDefinitions.Joint
