module
public import TruthCore.Explanation.EmptyTruthmakerReplies
@[expose] public section
namespace TruthCore.Results.Explanation.EmptyTruthmaker.Replies
open TruthCore.Explanation.PSRStrength TruthCore.Explanation.TruthmakerTheories
open TruthCore.Explanation.EmptyTruthmakerReplies

 theorem concreteEmpty : ConcreteEmptyFact replyArena concrete .negative := by
  intro w
  cases w with
  | false => exact ⟨fun h => Bool.noConfusion h, fun h => (h .object ⟨rfl, rfl⟩).elim⟩
  | true => exact ⟨fun _ _ h => Bool.noConfusion h.1, fun _ => rfl⟩

 theorem bearerSound (b : Bearer) : TruthSound replyArena (byBearer b) := by
  rintro _ _ _ ⟨rfl, _, rfl⟩; rfl

 theorem bearerCoverage (b : Bearer) : NeedsMakerAt replyArena (byBearer b) true .negative :=
  fun _ => ⟨b, rfl, rfl, rfl⟩

 theorem bearerNonconcrete (b : Bearer) : ¬ ConcreteMaker (byBearer b) concrete := by
  intro h; exact Bool.noConfusion (h true b .negative ⟨rfl, rfl, rfl⟩).1

 theorem replies : RepliesMap := by
  refine ⟨concreteEmpty, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ _ ⟨rfl, rfl⟩; rfl
  · exact ⟨bearerSound _, by rintro _ _ _ ⟨rfl, rfl, _⟩; trivial,
      bearerCoverage _, bearerNonconcrete _, by
        intro h; exact Bool.noConfusion (h true .abstractObject .negative ⟨rfl, rfl, rfl⟩ false trivial trivial)⟩
  · exact ⟨⟨fun _ => Iff.rfl, concreteEmpty⟩, bearerSound _,
      by rintro _ _ _ ⟨rfl, rfl, _⟩; rfl,
      bearerCoverage _, bearerNonconcrete _, by
        rintro _ _ _ ⟨rfl, rfl, rfl⟩ v _ hv; exact hv⟩
  · refine ⟨⟨?_, ?_, ?_, ⟨rfl, rfl⟩⟩, bearerSound _, ?_, bearerCoverage _, bearerNonconcrete _, ?_⟩
    · intro w; cases w with
      | false =>
        constructor
        · intro h; cases h
        · intro h; have hn := ((h .object).1 ⟨rfl, rfl⟩).1; cases hn
      | true =>
        constructor
        · intro _ b; constructor
          · intro h; cases h.1
          · intro h; cases h.1
        · intro _; rfl
    · intro w; cases w with
      | false => exact ⟨fun _ _ => ⟨fun h => ⟨rfl, h.2⟩, fun h => ⟨rfl, h.2⟩⟩, fun _ => rfl⟩
      | true =>
        constructor
        · intro h; cases h
        · intro h; have hn := ((h .object).2 ⟨rfl, rfl⟩).1; cases hn
    · intro b h; cases h.1
    · rintro _ _ _ ⟨rfl, rfl, _⟩; rfl
    · rintro _ _ _ ⟨rfl, rfl, rfl⟩ v _ hv; exact hv
  · exact ⟨⟨rfl, Bool.noConfusion, trivial, rfl, rfl, rfl⟩, bearerSound _, bearerCoverage _,
      fun h => Bool.noConfusion (h true .external .negative ⟨rfl, rfl, rfl⟩), bearerNonconcrete _, by
        intro h; exact Bool.noConfusion (h true .external .negative ⟨rfl, rfl, rfl⟩ false trivial rfl)⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _; exact ⟨fun _ _ h => h, fun _ => trivial⟩
    · intro _ _ _ _; trivial
    · intro _ _ _ _; trivial
    · intro _ _ _ _ _ _ _; trivial
    · intro _ _; exact ⟨(), rfl⟩
    · intro _; trivial
    · intro _; trivial
    · intro _; exact Iff.rfl
    · intro h; exact h true () .negative rfl
    · intro h; obtain ⟨_, hb⟩ := h trivial; exact hb
  · intro h; exact Bool.noConfusion (h false trivial)
end TruthCore.Results.Explanation.EmptyTruthmaker.Replies
