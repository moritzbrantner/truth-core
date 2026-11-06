module

public import TruthCore.Case.Catholicism.StageThree.ChurchDefinitions

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageThree.ChurchDefinitions.Visible

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.ChurchDefinitions

/-- Exact selected-criterion consequence; no source reading or history is established. -/
theorem visibleCriterionSuppliesStageFive (σ : Signature) (church : σ.Society → Prop)
    (hCriterion : VisibleCriterion σ church)
    (hFounded : ChristFoundedSelectedChurch σ church) : ChristFoundedVisibleChurch σ := by
  obtain ⟨c, hFoundedC, hChurch⟩ := hFounded
  exact ⟨c, hFoundedC, (hCriterion c).1 hChurch⟩

end TruthCore.Results.Case.Catholicism.StageThree.ChurchDefinitions.Visible
