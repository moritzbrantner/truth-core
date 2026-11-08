module

public import TruthCore.Causality.SelfOperationLife

@[expose] public section

namespace TruthCore.Results.Causality.SelfOperationLife
open TruthCore.Causality.SelfOperationLife
open TruthCore.Latin.Aquinas.SummaTheologiae (PureActLivesReading MovedOnlyAsInPotencyReading)

/-- A pure act operates from itself; being in potency in no respect, it is moved
in no respect; so it lives. Conditional on three OPEN premises. -/
theorem pureActLives {B R T : Type} (InPotency MovedIn : B → R → Prop)
    (Operates : B → Prop) (LivesAt : B → T → Prop)
    (hOperates : PureActOperates InPotency Operates)
    (hLife : SelfOperatingUnmovedLives Operates MovedIn LivesAt)
    (hMoved : MovedOnlyAsInPotencyReading MovedIn InPotency) :
    PureActLivesReading InPotency LivesAt :=
  fun x hPure => hLife x (hOperates x hPure) (fun r hr => hPure r (hMoved x r hr))

open TruthCore.Causality.SelfOperationLife.Control in
theorem controls : Certificate :=
  ⟨⟨fun h => h () (fun _ h => h), fun _ h => h.elim, fun _ _ h => h,
      fun h => (h () (fun _ h => h)).elim (fun _ h => h)⟩,
    ⟨fun _ _ => trivial, fun h => (h () trivial (fun _ h => h)).elim (fun _ h => h),
      fun _ _ h => h, fun h => (h () (fun _ h => h)).elim (fun _ h => h)⟩,
    ⟨fun _ _ => trivial, fun _ _ hNot => (hNot () trivial).elim, fun h => h () () trivial,
      fun h => (h () (fun _ h => h)).elim (fun _ h => h)⟩,
    ⟨fun _ _ => trivial, fun _ _ _ => ⟨(), trivial⟩, fun _ _ h => h,
      fun _ _ => ⟨(), trivial⟩⟩⟩

end TruthCore.Results.Causality.SelfOperationLife
