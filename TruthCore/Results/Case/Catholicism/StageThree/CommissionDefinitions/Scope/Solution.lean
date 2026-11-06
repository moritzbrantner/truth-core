module

public import TruthCore.Case.Catholicism.StageThree.CommissionDefinitions

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageThree.CommissionDefinitions.Scope

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism.StageThree.Commissions
open TruthCore.Case.Catholicism.StageThree.CommissionDefinitions

/-- Exact criterion/bridge scope; no institutional history is inferred from a report alone. -/
theorem matthew28AndTeachingCriterionSupplyScope (σ : Signature) (A : Agency σ) (E : Commissioning) (governing : Power → Prop)
    (hMatthew : Matthew28GoesBack E)
    (hCriterion : TeachingInclusiveGovernanceCriterion governing)
    (hLink : InstitutionLinkFor σ A E governing) : MandatedFoundingOfCatholicChurch σ A := by
  have hGaveTeach : E.Gave .teach := hMatthew .teach (.tail _ (.tail _ (.head _)))
  intro g hm hf hv
  obtain ⟨hFound, hTeach⟩ := hLink g hm hf hv
  exact ⟨hFound .teach ((hCriterion .teach).2 (Or.inr rfl)) hGaveTeach, hTeach hGaveTeach⟩

end TruthCore.Results.Case.Catholicism.StageThree.CommissionDefinitions.Scope
