import TruthCore.Comparison.MoralLanguage
namespace TruthCore.Results.Comparison.MoralLanguage.ExpressivismConsistentWithGeachValidity
open TruthCore.Comparison.MoralLanguage

/-- One moral sentence `p = q`, with the same meaning in both kinds of
occurrence. Free-standing it expresses the one attitude, in the antecedent it
expresses none, and the modus ponens is valid. -/
def expressivistModel : Sig where
  Sentence := Unit
  Ctx := Bool
  Meaning := Unit
  Attitude := Unit
  free := true
  antecedent := false
  meaning := fun _ _ => ()
  Expresses := fun _ c _ => c = true
  Moral := fun _ => True
  ValidMP := fun _ _ => True
  p := ()
  q := ()

/-- Constant-meaning expressivism and the shared data are jointly satisfiable. -/
theorem expressivismConsistentWithGeachValidity : ExpressivismConsistentWithGeachValidity :=
  ⟨expressivistModel, fun _ _ _ _ => rfl,
    fun _ _ => ⟨(), rfl⟩, fun _ _ h => Bool.noConfusion h, fun _ _ _ => rfl, trivial, trivial⟩

end TruthCore.Results.Comparison.MoralLanguage.ExpressivismConsistentWithGeachValidity
