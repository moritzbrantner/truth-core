import TruthCore.Greek.Plato.Parmenides.ReplyModels
import TruthCore.Results.Greek.Plato.Parmenides.MediationReply.Solution
namespace TruthCore.Results.Greek.Plato.Parmenides.MediationModel
open TruthCore.Greek.Plato.Forms
open TruthCore.Greek.Plato.Parmenides.ParticipationChallenges

theorem mediationModel : MediationPossible := by
  have hhuman : HumanOutside replyCognition := by
    intro a ha hi
    exact Bool.noConfusion (ha.symm.trans hi)
  have htransfer : MediatedTransfer replyCognition := by
    intro a r f hdirect hpresents
    intro heq
    exact hpresents (hdirect.symm.trans heq)
  have hroute : HumanRoute replyForms replyCognition :=
    ⟨false, false, true, rfl, rfl, rfl, fun h => Bool.noConfusion h⟩
  refine ⟨replyForms, replyCognition, hhuman, ?_, htransfer, hroute, ?_, ?_⟩
  · intro a ha
    exact ha
  · exact TruthCore.Results.Greek.Plato.Parmenides.MediationReply.mediationReply
      replyForms replyCognition hhuman htransfer hroute
  · exact ⟨true, false, rfl, fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩

end TruthCore.Results.Greek.Plato.Parmenides.MediationModel
