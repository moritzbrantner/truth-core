module
public import TruthCore.Causality.ExistsSenseMeaning

@[expose] public section
namespace TruthCore.Results.Causality.ExistsSenseMeaning
open TruthCore.Causality.ExistsSenseMeaning

theorem controls : Controls := by
  refine ⟨.intro () True.intro, ?_, .intro () True.intro True.intro⟩
  intro h
  cases h with
  | intro x hx _ => exact hx
end TruthCore.Results.Causality.ExistsSenseMeaning
