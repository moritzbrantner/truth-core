import TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
namespace TruthCore.Results.Greek.Plato.Parmenides.DistanceObjection
open TruthCore.Greek.Plato.Forms
open TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
universe u v w
variable {E : Type u} {Q : Type v} {A : Type w}

theorem distanceObjection (s : Vocabulary E Q) (g : Explanation E)
    (hmany : PropertyInstances s) (hexplains : ExplanatoryParticipation s)
    (houtside : NoninherentForms s g) (hground : ExplanationGrounds s g) :
    NoImmanenceRequirement g := by
  sorry

end TruthCore.Results.Greek.Plato.Parmenides.DistanceObjection
