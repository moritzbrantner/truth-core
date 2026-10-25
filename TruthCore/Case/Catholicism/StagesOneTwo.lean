import TruthCore.Case.Catholicism.StageTwo

namespace TruthCore.Case.Catholicism

/-- A single witness is God, is the only being to which `IsGod` applies, and has
all the skeleton's classical attributes. This is a logical conjunction, not a
new nominal definition: it does not identify maximality with being God. -/
def UniqueClassicalGodExists (σ : Signature) : Prop :=
  ∃ g, σ.IsGod g ∧ IsTheOneGod σ.IsGod g ∧ σ.HasClassicalAttributes g

end TruthCore.Case.Catholicism
