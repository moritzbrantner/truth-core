import TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
namespace TruthCore.Results.Greek.Plato.Parmenides.EpistemicObjection
open TruthCore.Greek.Plato.Forms
open TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
universe u v w
variable {E : Type u} {Q : Type v} {A : Type w}

theorem epistemicObjection (s : Vocabulary E Q) (k : Cognition E A)
    (hclosure : KnowledgeRealmClosure s k) (hhuman : HumanOutside k)
    (hdivine : DivineInside k) : CrossRealmIgnorance s k := by
  constructor
  · intro a ha f hf hknows
    have hin : k.IntelligibleAgent a := (hclosure a f hknows).mpr hf
    exact hhuman a ha hin
  · intro a ha x hx hknows
    have hin : k.IntelligibleAgent a := hdivine a ha
    have hobject : s.Intelligible x := (hclosure a x hknows).mp hin
    exact hx hobject

end TruthCore.Results.Greek.Plato.Parmenides.EpistemicObjection
