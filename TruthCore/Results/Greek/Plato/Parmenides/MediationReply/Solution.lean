import TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
namespace TruthCore.Results.Greek.Plato.Parmenides.MediationReply
open TruthCore.Greek.Plato.Forms
open TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
universe u v w
variable {E : Type u} {Q : Type v} {A : Type w}

theorem mediationReply (s : Vocabulary E Q) (k : Cognition E A)
    (hhuman : HumanOutside k) (htransfer : MediatedTransfer k)
    (hroute : HumanRoute s k) : NoKnowledgeRealmClosure s k := by
  obtain ⟨a, r, f, ha, hf, hdirect, hpresents⟩ := hroute
  have hknows : k.Knows a f := htransfer a r f hdirect hpresents
  intro hclosure
  have hin : k.IntelligibleAgent a := (hclosure a f hknows).mpr hf
  exact hhuman a ha hin

end TruthCore.Results.Greek.Plato.Parmenides.MediationReply
