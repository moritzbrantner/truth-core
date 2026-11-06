module

public import TruthCore.Case.Catholicism.StageThree.ChurchDefinitions
public import TruthCore.Results.Case.Catholicism.StageThree.ChurchDefinitions.Visible.Solution
public import TruthCore.Results.Case.Catholicism.StageThree.ChurchDefinitions.Joint.Solution

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageThree.ChurchDefinitions.Elimination

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.ChurchDefinitions

/-- Exact selected-criterion consequence; no source reading or history is established. -/
theorem namedEliminationSuppliesStageFive (σ : Signature) (church spiritual : σ.Society → Prop)
    (hCoverage : NamedChurchCoverage σ church spiritual)
    (hSpiritualFails : SpiritualCriterionFails σ church spiritual)
    (hFounded : ChristFoundedSelectedChurch σ church) : ChristFoundedVisibleChurch σ := by
  cases hCoverage with
  | inl hVisible =>
    exact TruthCore.Results.Case.Catholicism.StageThree.ChurchDefinitions.Visible.visibleCriterionSuppliesStageFive
      σ church hVisible hFounded
  | inr hRest =>
    cases hRest with
    | inl hSpiritual => exact False.elim (hSpiritualFails hSpiritual)
    | inr hJoint =>
      exact TruthCore.Results.Case.Catholicism.StageThree.ChurchDefinitions.Joint.jointCriterionSuppliesStageFive
        σ church spiritual hJoint hFounded

end TruthCore.Results.Case.Catholicism.StageThree.ChurchDefinitions.Elimination
