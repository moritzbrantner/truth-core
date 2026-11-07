module

public import TruthCore.Causality.LifeBoundaryPotency

@[expose] public section

namespace TruthCore.Results.Causality.LifeBoundaryPotency
open TruthCore.Causality.LifeBoundaryPotency
open TruthCore.Latin.Aquinas.SummaTheologiae (LifeBoundaryRequiresPotencyReading)
open TruthCore.Logic (ExcludedMiddle)

/-- Contrapositive of q.10 a.1 under excluded middle. Conditional on two OPEN
premises. -/
theorem lifeBoundaryRequiresPotency {B R T : Type} [LT T] (InPotency : B → R → Prop)
    (LivesAt : B → T → Prop) (hEM : ExcludedMiddle)
    (hImmutable : ImmutableHasNoLifeBoundary InPotency LivesAt) :
    LifeBoundaryRequiresPotencyReading InPotency LivesAt := by
  intro x hBoundary
  rcases hEM (∃ r, InPotency x r) with h | h
  · exact h
  · exact (hImmutable x (fun r hr => h ⟨r, hr⟩) hBoundary).elim

open TruthCore.Causality.LifeBoundaryPotency.Control in
theorem begins : TruthCore.Latin.Aquinas.SummaTheologiae.LifeBeginsOrEnds livesLater () :=
  ⟨false, true, rfl, fun h => Bool.noConfusion (h.mpr rfl)⟩

open TruthCore.Causality.LifeBoundaryPotency.Control in
theorem controls : Certificate :=
  ⟨⟨fun h => h () (fun _ h => h) begins, fun h => (h () begins).elim (fun _ h => h)⟩,
    ⟨fun _ _ ⟨_, _, _, h⟩ => h ⟨fun _ => trivial, fun _ => trivial⟩,
      fun _ ⟨_, _, _, h⟩ => (h ⟨fun _ => trivial, fun _ => trivial⟩).elim⟩⟩

end TruthCore.Results.Causality.LifeBoundaryPotency
