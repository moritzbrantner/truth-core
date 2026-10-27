import TruthCore.Logic.ActBearer
namespace TruthCore.Results.Logic.ActBearer
open TruthCore.Logic.ActBearer

theorem bearerInference : BearerInference := by
  intro Act Being Actual Bears hAct hBearer
  obtain ⟨a, ha⟩ := hAct
  obtain ⟨b, hb⟩ := hBearer a ha
  exact ⟨b, a, ha, hb⟩

theorem substanceInference : SubstanceInference := by
  intro Act Being Actual Bears Substance hAct hBearer hSubstance
  obtain ⟨b, a, ha, hb⟩ := bearerInference Act Being Actual Bears hAct hBearer
  exact ⟨b, a, ha, hb, hSubstance b a ha hb⟩

theorem nonSubstantialBearerModel : NonSubstantialBearerModel := by
  refine ⟨fun _ => True, fun _ _ => True, fun _ => False,
    ⟨(), trivial⟩, ?_, ?_⟩
  · intro _ _
    exact ⟨(), trivial⟩
  · intro ⟨_, _, _, _, hSubstance⟩
    exact hSubstance

theorem bearerlessActModel : BearerlessActModel := by
  refine ⟨fun _ => True, fun _ _ => False, ⟨(), trivial⟩, ?_⟩
  intro ⟨_, _, _, hb⟩
  exact hb

end TruthCore.Results.Logic.ActBearer
