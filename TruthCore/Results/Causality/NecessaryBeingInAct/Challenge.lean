import TruthCore.Causality.NecessaryBeingInAct

namespace TruthCore.Results.Causality.NecessaryBeingInAct
open TruthCore.Causality.NecessaryBeingInAct
open TruthCore.Latin.Aquinas.InMetaphysicam (IncorruptibleIsInActReading)
open TruthCore.Case.Catholicism (NecessaryBeingHasBeing)

/-- A necessary being cannot fail to be in substance (by the bridge), so it is
simply incorruptible and therefore in act as to being. Conditional on two OPEN
premises. -/
theorem necessaryBeingInAct {B T R : Type} (Possible : (T → Prop) → Prop)
    (IsAt : B → T → Prop) (InAct CanFailToBe : B → R → Prop) (esse : R)
    (hBridge : CanFailToBeIsPossiblyNot Possible IsAt CanFailToBe esse)
    (hIncorruptible : IncorruptibleIsInActReading InAct CanFailToBe esse) :
    NecessaryBeingHasBeing Possible IsAt InAct esse := by
  sorry

theorem controls : TruthCore.Causality.NecessaryBeingInAct.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.NecessaryBeingInAct
