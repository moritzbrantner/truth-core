module

public import TruthCore.Causality.NecessaryBeingInAct

@[expose] public section

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
    NecessaryBeingHasBeing Possible IsAt InAct esse :=
  fun x hNecessary => hIncorruptible x (fun hFail => hNecessary (hBridge x hFail))

open TruthCore.Causality.NecessaryBeingInAct.Control in
theorem controls : Certificate :=
  ⟨⟨fun h => h () trivial, fun _ h => (h trivial).elim, fun h => h () (fun h => h)⟩,
    ⟨fun _ h => h.elim, fun h => h () (fun h => h), fun h => h () (fun h => h)⟩,
    ⟨fun _ h => h.elim, fun _ _ => trivial, fun _ _ => trivial⟩⟩

end TruthCore.Results.Causality.NecessaryBeingInAct
