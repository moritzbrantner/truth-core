module

public import TruthCore.Case.Catholicism.StageThree.CommissionDefinitions

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageThree.CommissionDefinitions.Narrow

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism.StageThree.Commissions
open TruthCore.Case.Catholicism.StageThree.CommissionDefinitions

/-- Exact criterion/bridge scope; no institutional history is inferred from a report alone. -/
theorem narrowCalibration (σ : Signature) (A : Agency σ) (E : Commissioning) (governing : Power → Prop)
    (hCriterion : NarrowGovernanceCriterion governing) :
    NarrowInstitutionCalibration σ A E governing := by
  constructor
  · intro hOld g hm hf hv
    obtain ⟨hFound, hTeach⟩ := hOld g hm hf hv
    exact ⟨fun p hp hg => hFound p ((hCriterion p).1 hp) hg, hTeach⟩
  · intro hNew g hm hf hv
    obtain ⟨hFound, hTeach⟩ := hNew g hm hf hv
    exact ⟨fun p hp hg => hFound p ((hCriterion p).2 hp) hg, hTeach⟩

end TruthCore.Results.Case.Catholicism.StageThree.CommissionDefinitions.Narrow
