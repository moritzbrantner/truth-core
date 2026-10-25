import TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
namespace TruthCore.Results.Greek.Plato.Parmenides.EpistemicObjection
open TruthCore.Greek.Plato.Forms
open TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
universe u v w
variable {E : Type u} {Q : Type v} {A : Type w}

theorem epistemicObjection (s : Vocabulary E Q) (k : Cognition E A)
    (hclosure : KnowledgeRealmClosure s k) (hhuman : HumanOutside k)
    (hdivine : DivineInside k) : CrossRealmIgnorance s k := by
  sorry

end TruthCore.Results.Greek.Plato.Parmenides.EpistemicObjection
