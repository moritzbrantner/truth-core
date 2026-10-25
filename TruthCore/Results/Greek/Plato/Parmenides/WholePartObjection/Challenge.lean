import TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
namespace TruthCore.Results.Greek.Plato.Parmenides.WholePartObjection
open TruthCore.Greek.Plato.Forms
open TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
universe u v w
variable {E : Type u} {Q : Type v} {A : Type w}

theorem wholePartObjection (s : Vocabulary E Q) (m : Mereology E)
    (hmany : PropertyInstances s) (hone : OneOverMany s)
    (hexclusive : WholeExclusive m) (hindivisible : IndivisibleForms s m) :
    NoSpatialDilemma s m := by
  sorry

end TruthCore.Results.Greek.Plato.Parmenides.WholePartObjection
