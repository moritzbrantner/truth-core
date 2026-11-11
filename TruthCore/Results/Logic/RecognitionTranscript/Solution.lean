module
public import TruthCore.Logic.RecognitionTranscript
public import Mathlib.Data.List.Basic

@[expose] public section
namespace TruthCore.Results.Logic.RecognitionTranscript
open TruthCore.Logic.RecognitionTranscript

theorem attribution : Attribution := by
  intro g c h responds integrity fresh disciplined exclusive
  have token : h.originToken = c.token := integrity.symm.trans (congrArg Message.token responds)
  constructor
  · exact exclusive h.origin (token ▸ disciplined)
  · intro earlier
    exact fresh earlier token

private theorem exclusiveGenuine : Exclusive 0 challenge genuine := by
  intro p hp
  by_cases he : p = 0
  · exact he
  · simp [he] at hp

private theorem exclusiveInsertion : Exclusive 0 challenge insertion := by
  intro p hp
  by_cases he : p = 0
  · exact he
  · simp [he] at hp

theorem controls : Controls := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨rfl, rfl, by dsimp [Fresh, Disciplined, Integrity, AuthoredNow]; decide, by dsimp [Fresh, Disciplined, Integrity, AuthoredNow]; decide, exclusiveGenuine, rfl, by dsimp [Fresh, Disciplined, Integrity, AuthoredNow]; decide⟩
  · exact ⟨rfl, rfl, by dsimp [Fresh, Disciplined, Integrity, AuthoredNow]; decide, by dsimp [Fresh, Disciplined, Integrity, AuthoredNow]; decide, (by
      intro h
      have bad := h 1 (by dsimp [Disciplined]; decide)
      cases bad), by dsimp [Fresh, Disciplined, Integrity, AuthoredNow]; decide⟩
  · exact ⟨rfl, rfl, by dsimp [Fresh, Disciplined, Integrity, AuthoredNow]; decide, exclusiveGenuine, by dsimp [Fresh, Disciplined, Integrity, AuthoredNow]; decide, by dsimp [Fresh, Disciplined, Integrity, AuthoredNow]; decide⟩
  · exact ⟨rfl, by dsimp [Fresh, Disciplined, Integrity, AuthoredNow]; decide, by dsimp [Fresh, Disciplined, Integrity, AuthoredNow]; decide, exclusiveInsertion, by dsimp [Fresh, Disciplined, Integrity, AuthoredNow]; decide, by dsimp [Fresh, Disciplined, Integrity, AuthoredNow]; decide⟩
  · exact ⟨rfl, rfl, by dsimp [Fresh, Disciplined, Integrity, AuthoredNow]; decide, exclusiveGenuine, by dsimp [Fresh, Disciplined, Integrity, AuthoredNow]; decide, by dsimp [Fresh, Disciplined, Integrity, AuthoredNow]; decide⟩

end TruthCore.Results.Logic.RecognitionTranscript
