import TruthCore.Logic.ThoughtChangeSubject

namespace TruthCore.Results.Logic.ThoughtChangeSubject
open TruthCore.Logic.ThoughtChangeSubject
open TruthCore.Greek.Aristotle.Physics

/-- Conditional composition; the three premises are not independently proved. -/
theorem thoughtChangeHasSubject {Episode Subject : Type}
    (Thought Change : Episode → Prop) (Potential : Subject → Prop)
    (QuaPotentialActuality : Episode → Subject → Prop)
    (hThought : ActualThought Thought)
    (hBridge : ThoughtChangeBridge Thought Change)
    (hPhysics : ChangeAsActualityOfPotentialReading Change Potential QuaPotentialActuality) :
    ThoughtChangeHasPotentialSubject Thought Change Potential QuaPotentialActuality := by
  sorry

/-- Three models show that none of the three premises may simply be dropped. -/
theorem omissionControls : OmissionControls := by
  sorry

end TruthCore.Results.Logic.ThoughtChangeSubject
