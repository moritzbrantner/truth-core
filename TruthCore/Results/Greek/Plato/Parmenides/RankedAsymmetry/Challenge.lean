import TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
namespace TruthCore.Results.Greek.Plato.Parmenides.RankedAsymmetry
open TruthCore.Greek.Plato.Forms
open TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
universe u v w
variable {E : Type u} {Q : Type v} {A : Type w}

theorem rankedAsymmetry (g : Explanation E) (rank : E → Nat)
    (hrank : RankedGround g rank) : AsymmetricGround g := by
  sorry

end TruthCore.Results.Greek.Plato.Parmenides.RankedAsymmetry
