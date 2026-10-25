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
  obtain ⟨x, _, q, _, hx, _, hq, hxq, _⟩ := hmany
  obtain ⟨f, hf, _, hex⟩ := hexplains q hq x hx hxq
  intro hrequires
  have hgrounds : g.Ground f x := hground f x q hex
  have hinheres : g.Inheres f x := hrequires f x hgrounds
  exact houtside q hq f x hf hx hinheres

end TruthCore.Results.Greek.Plato.Parmenides.DistanceObjection
