import TruthCore.Greek.Plato.ThirdMan
namespace TruthCore.Results.Greek.Plato.ThirdMan.LikenessRegress
open TruthCore.Greek.Plato.Forms TruthCore.Greek.Plato.ThirdMan
universe u v
variable {E : Type u} {Q : Type v}
/-- Conditional likeness regress, without ordinary self-predication. -/
theorem likenessRegress (s : Vocabulary E Q) (eligible : List E → Prop) (q : Q)
    (hSeed : LikenessSeed s eligible q)
    (hFormation : LikenessFormation s eligible q)
    (hSymmetry : LikenessSymmetry s) (hBridge : ParticipationLikeness s)
    (hNonid : ParticipantNonidentity s) (hIteration : Iteration s eligible) :
    UnboundedForms s := by
  sorry
end TruthCore.Results.Greek.Plato.ThirdMan.LikenessRegress
