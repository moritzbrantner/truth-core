module

public import TruthCore.Causality.AristotelianRivalRefutations

@[expose] public section

namespace TruthCore.Results.Causality.AristotelianRivalRefutations
open TruthCore.Causality.AristotelianRivalRefutations
open TruthCore.Greek.Aristotle.Metaphysics (PotencyIsUnactualizedCapacityReading)
open TruthCore.Greek.Aristotle.Physics (BeingMovedIsActualizationOfPotencyReading)

/-- What is in potency in a respect is not in act in it. -/
theorem noActAndPotencyInSameRespect {B R : Type} (InAct InPotency CanBe : B → R → Prop)
    (hAnalysis : PotencyIsUnactualizedCapacityReading InAct InPotency CanBe) :
    NoActAndPotencyInSameRespect InAct InPotency :=
  fun ⟨x, r, hAct, hPot⟩ => ((hAnalysis x r).mp hPot).2 hAct

/-- What is being moved in a respect is in potency in it. -/
theorem noMovedWithoutPotency {B R : Type} (MovedIn InPotency Actualized : B → R → Prop)
    (hAnalysis : BeingMovedIsActualizationOfPotencyReading MovedIn InPotency Actualized) :
    NoMovedWithoutPotency MovedIn InPotency :=
  fun ⟨x, r, hMoved, hNot⟩ => hNot ((hAnalysis x r).mp hMoved).1

open TruthCore.Causality.AristotelianRivalRefutations.Control in
theorem controls : Certificate :=
  ⟨⟨fun h => ((h () ()).mp trivial).2 trivial, ⟨(), (), trivial, trivial⟩⟩,
    ⟨fun h => ((h () ()).mp trivial).1, ⟨(), (), trivial, fun h => h⟩⟩,
    ⟨fun _ _ => ⟨fun h => h.elim, fun h => (h.2 trivial).elim⟩,
      fun _ _ => ⟨fun h => h.elim, fun h => h.1.elim⟩⟩⟩

end TruthCore.Results.Causality.AristotelianRivalRefutations
