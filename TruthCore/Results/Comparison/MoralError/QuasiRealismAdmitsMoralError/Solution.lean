import TruthCore.Comparison.MoralError
namespace TruthCore.Results.Comparison.MoralError.QuasiRealismAdmitsMoralError
open TruthCore.Comparison.MoralError

/-- One person and one moral sentence, minimally but not robustly truth-apt,
not true, and accepted. -/
def quasiRealistModel : Sig where
  Agent := Unit
  Sentence := Unit
  Moral := fun _ => True
  TruthApt := fun _ => True
  RobustlyTruthApt := fun _ => False
  Holds := fun _ => False
  Accepts := fun _ _ => True
  Rejects := fun _ _ => False

/-- Quasi-realism's minimal truth and an actual moral error are jointly
satisfiable. -/
theorem quasiRealismAdmitsMoralError : QuasiRealismAdmitsMoralError :=
  ⟨quasiRealistModel, fun _ _ => ⟨trivial, id⟩, ⟨(), (), trivial, trivial, trivial, id⟩⟩

end TruthCore.Results.Comparison.MoralError.QuasiRealismAdmitsMoralError
