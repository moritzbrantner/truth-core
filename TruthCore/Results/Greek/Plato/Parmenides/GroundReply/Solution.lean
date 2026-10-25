import TruthCore.Greek.Plato.Parmenides.ReplyModels
import TruthCore.Results.Greek.Plato.Parmenides.RankedAsymmetry.Solution
namespace TruthCore.Results.Greek.Plato.Parmenides.GroundReply
open TruthCore.Greek.Plato.Forms
open TruthCore.Greek.Plato.Parmenides.ParticipationChallenges

theorem groundReply : GroundReplyPossible := by
  refine ⟨replyForms, replyGround, replyRank, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q _ f hf
    exact hf
  · intro q _ f x hf hx _ heq
    exact Bool.noConfusion (hf.symm.trans (heq.trans hx))
  · intro q _ x hx _
    exact ⟨true, rfl, ⟨hx, rfl⟩, rfl, hx⟩
  · intro f x q h
    exact h
  · intro q _ f x _ _ h
    exact h
  · intro f x h
    obtain ⟨hf, hx⟩ := h
    subst f
    subst x
    exact Nat.zero_lt_succ 0
  · apply TruthCore.Results.Greek.Plato.Parmenides.RankedAsymmetry.rankedAsymmetry
      replyGround replyRank
    intro f x h
    obtain ⟨hf, hx⟩ := h
    subst f
    subst x
    exact Nat.zero_lt_succ 0
  · intro h
    exact h true false ⟨rfl, rfl⟩
  · exact ⟨true, false, (), rfl, rfl, rfl, rfl⟩
  · intro f x h
    exact h

end TruthCore.Results.Greek.Plato.Parmenides.GroundReply
