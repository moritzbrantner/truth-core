import TruthCore.Greek.Aristotle.Physics.BookII.Chapter7

namespace TruthCore.Results.Aristotle.Physics.PhysicalFourCauses

open TruthCore.Greek.Aristotle.Physics

/-- Exhaustive causal modes establish the physicist's four-cause explanatory scope. -/
theorem physicistKnowsAllFourCauses
    {Cause Effect : Type}
    (IsCause Material Formal SourceOfChange Final : Cause → Effect → Prop)
    (PhysicistMustKnowAllFourCauses : Prop)
    (hFour : FourCauseExhaustiveReading IsCause Material Formal SourceOfChange Final)
    (hScope :
      FourCauseExhaustivenessImpliesPhysicalScopeReading
        (FourCauseExhaustiveReading IsCause Material Formal SourceOfChange Final)
        PhysicistMustKnowAllFourCauses) :
    PhysicistKnowsAllFourCausesReading PhysicistMustKnowAllFourCauses := by
  exact hScope hFour

end TruthCore.Results.Aristotle.Physics.PhysicalFourCauses
