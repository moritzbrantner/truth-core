module

public import TruthCore.Case.Catholicism.StageThree.CommissionDefinitions

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageThree.CommissionDefinitions.Strength

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.FoundingScope
open TruthCore.Case.Catholicism.StageThree.Commissions
open TruthCore.Case.Catholicism.StageThree.CommissionDefinitions

/-- Exact criterion/bridge scope; no institutional history is inferred from a report alone. -/
theorem teachingLinkSuppliesNarrowLink (σ : Signature) (A : Agency σ) (E : Commissioning)
    (hLink : TeachingInclusiveInstitutionLink σ A E) : ChurchFoundedInCommissionedApostles σ A E := by
  intro g hm hf hv
  obtain ⟨hFound, hTeach⟩ := hLink g hm hf hv
  exact ⟨fun p hp hg => hFound p (Or.inl hp) hg, hTeach⟩

end TruthCore.Results.Case.Catholicism.StageThree.CommissionDefinitions.Strength
