import TruthCore.Causality.AccidentalFeatureOrigin

namespace TruthCore.Results.Causality.AccidentalFeatureOrigin
open TruthCore.Causality.AccidentalFeatureOrigin

/-- Eliminate internal essential production for one distinguishing accidental
feature. This partial case says nothing about existential dependence or unity. -/
theorem externalOrigin {B P F : Type} (s : RoleSchema B P F)
    (essenceOf : B → P) (x y : B) (f : F)
    (hAccidental : Accidental s x f) (hDifference : Distinguishes s x y f)
    (hOrigin : OriginFork s essenceOf x f)
    (hShared : SharedProduction s essenceOf x y f)
    (hRealized : Realization s essenceOf y f) : ExternalOriginExists s x f := by
  sorry

end TruthCore.Results.Causality.AccidentalFeatureOrigin
