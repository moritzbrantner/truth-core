import TruthCore.Mereology.Vitalism

namespace TruthCore.Results.Mereology.SoulUnityIndependence
open TruthCore.Mereology.Vitalism

/-- Two positive rival scenarios share the entire observable history but
disagree about what, if anything, confers substantial unity. -/
theorem soulUnityIndependence : SoulUnityIndependence := by
  constructor
  · refine ⟨scenario True True, scenario False False, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact scenario_has_turnover _ _
    · exact scenario_has_turnover _ _
    · exact scenario_same_profile _ _ _ _
    all_goals simp [scenario]
  · refine ⟨scenario True True, scenario True False, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact scenario_has_turnover _ _
    · exact scenario_has_turnover _ _
    · exact scenario_same_profile _ _ _ _
    all_goals simp [scenario]

end TruthCore.Results.Mereology.SoulUnityIndependence
