import TruthCore.Mereology.ProcessTurnover
namespace TruthCore.Results.Mereology.ProcessTurnover
open TruthCore.Mereology.ProcessTurnover TruthCore.Mereology.Vitalism
 theorem certificate : Boundary := by
  refine ⟨?_, ?_, ?_⟩
  · intro P carrier parts persist
    exact turnover_excludes_fixed_extension _ carrier parts
      (scenario_has_turnover False False) persist
  · exact ⟨fun _ => (), fun p _ c => (scenario False False).MemberAt p c,
      fun _ _ _ => rfl, fun _ _ => Iff.rfl⟩
  · refine ⟨id, (scenario False False).MemberAt, fun _ _ => Iff.rfl, ?_⟩
    intro persist
    have impossible := persist .early .late (Or.inl ⟨rfl, rfl⟩)
    cases impossible
end TruthCore.Results.Mereology.ProcessTurnover
