import TruthCore.Mereology.Vitalism

namespace TruthCore.Results.Mereology.SoulUnityIndependence
open TruthCore.Mereology.Vitalism

/-- Two positive rival scenarios share the entire observable history but
disagree about what, if anything, confers substantial unity. -/
theorem soulUnityIndependence : SoulUnityIndependence :=
  ⟨⟨scenario True True, scenario False False,
      scenario_has_turnover _ _, scenario_has_turnover _ _,
      scenario_same_profile _ _ _ _, trivial, trivial, id, id⟩,
    ⟨scenario True True, scenario True False,
      scenario_has_turnover _ _, scenario_has_turnover _ _,
      scenario_same_profile _ _ _ _, trivial, trivial, trivial, id⟩⟩

end TruthCore.Results.Mereology.SoulUnityIndependence
