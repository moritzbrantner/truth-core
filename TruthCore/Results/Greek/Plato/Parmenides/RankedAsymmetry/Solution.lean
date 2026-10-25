import TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
namespace TruthCore.Results.Greek.Plato.Parmenides.RankedAsymmetry
open TruthCore.Greek.Plato.Forms
open TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
universe u v w
variable {E : Type u} {Q : Type v} {A : Type w}

theorem rankedAsymmetry (g : Explanation E) (rank : E → Nat)
    (hrank : RankedGround g rank) : AsymmetricGround g := by
  intro f x hfx hxf
  have hforward : rank f < rank x := hrank f x hfx
  have hbackward : rank x < rank f := hrank x f hxf
  exact Nat.lt_irrefl (rank f) (Nat.lt_trans hforward hbackward)

end TruthCore.Results.Greek.Plato.Parmenides.RankedAsymmetry
