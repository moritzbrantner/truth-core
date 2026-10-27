import TruthCore.Models.FiniteSupport
import TruthCore.Alternatives.NightCosmogony

/-! Named finite interpretations and closed certificates for the Night
cosmogony elimination (#497). Beings are `Bool`, the one respect is `Unit`.
Registration tests formal consequence only; it does not establish metaphysical
possibility.

* `NoReduction`: `false` is in potency, posterior to nothing, and moved by
  nothing.
* `SelfMover`: `false` is in potency and in act in the respect and moves itself.
* `OtherMover`: `true`, in act, moves `false`, in potency, without being simply
  prior to it.
* `Residual`: `false` is in potency, posterior to nothing, and nothing is moved:
  the bare rival survives the elimination core. -/
namespace TruthCore.Models.NightCosmogony
open TruthCore.Models.FiniteSupport

structure Model where
  InAct : Bool → Unit → Prop
  InPotency : Bool → Unit → Prop
  MovedIn : Bool → Unit → Prop
  MovesIn : Bool → Bool → Unit → Prop
  PriorSimply : Bool → Bool → Prop

namespace NoReduction
def model : Model where
  InAct := fun _ _ => False
  InPotency := fun x _ => x = false
  MovedIn := fun x _ => x = false
  MovesIn := fun _ _ _ => False
  PriorSimply := fun _ _ => False

theorem evaluation0 : @TruthCore.Alternatives.NightCosmogony.UnprecededPotencyActualizedReading Bool Unit model.InAct model.InPotency model.MovedIn model.PriorSimply :=
  ⟨false, (), ⟨rfl, fun _ h => h.elim⟩, rfl⟩

theorem evaluation1 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByABeingInActReading Bool Unit model.MovedIn model.MovesIn model.InAct) := by
  intro h
  obtain ⟨_, hMoves, _⟩ := h false () rfl
  exact hMoves

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.NothingMovesItselfInSameRespectReading Bool Unit model.MovedIn model.MovesIn :=
  fun _ _ _ h => h

theorem evaluation3 : @TruthCore.Alternatives.NightCosmogony.ActualMoverIsSimplyPriorReading Bool Unit model.InAct model.InPotency model.MovesIn model.PriorSimply :=
  fun _ _ _ _ h _ _ => h.elim

theorem evaluation4 : @TruthCore.Alternatives.ActPotencyRegress.PotencyPriorToActReading Bool Unit model.InAct model.InPotency model.PriorSimply :=
  ⟨false, (), rfl, fun _ h => h.elim⟩

theorem evaluation5 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.ActSimplyPriorToPotencyReading Bool Unit model.InAct model.InPotency model.PriorSimply) := by
  intro h
  obtain ⟨_, hAct, _⟩ := h false () rfl
  exact hAct
end NoReduction

namespace SelfMover
def model : Model where
  InAct := fun x _ => x = false
  InPotency := fun x _ => x = false
  MovedIn := fun x _ => x = false
  MovesIn := fun y x _ => y = false ∧ x = false
  PriorSimply := fun _ _ => False

theorem evaluation0 : @TruthCore.Alternatives.NightCosmogony.UnprecededPotencyActualizedReading Bool Unit model.InAct model.InPotency model.MovedIn model.PriorSimply :=
  ⟨false, (), ⟨rfl, fun _ _ h => h⟩, rfl⟩

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByABeingInActReading Bool Unit model.MovedIn model.MovesIn model.InAct :=
  fun _ _ h => ⟨false, ⟨rfl, h⟩, rfl⟩

theorem evaluation2 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.NothingMovesItselfInSameRespectReading Bool Unit model.MovedIn model.MovesIn) :=
  fun h => h false () rfl ⟨rfl, rfl⟩

theorem evaluation3 : @TruthCore.Alternatives.NightCosmogony.ActualMoverIsSimplyPriorReading Bool Unit model.InAct model.InPotency model.MovesIn model.PriorSimply := by
  intro y x _ _ hMoves _ hne
  obtain ⟨hy, hx⟩ := hMoves
  exact (hne (hy.trans hx.symm)).elim

theorem evaluation4 : @TruthCore.Alternatives.ActPotencyRegress.PotencyPriorToActReading Bool Unit model.InAct model.InPotency model.PriorSimply :=
  ⟨false, (), rfl, fun _ _ h => h⟩

theorem evaluation5 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.ActSimplyPriorToPotencyReading Bool Unit model.InAct model.InPotency model.PriorSimply) := by
  intro h
  obtain ⟨_, _, hPrior⟩ := h false () rfl
  exact hPrior
end SelfMover

namespace OtherMover
def model : Model where
  InAct := fun x _ => x = true
  InPotency := fun x _ => x = false
  MovedIn := fun x _ => x = false
  MovesIn := fun y x _ => y = true ∧ x = false
  PriorSimply := fun _ _ => False

theorem evaluation0 : @TruthCore.Alternatives.NightCosmogony.UnprecededPotencyActualizedReading Bool Unit model.InAct model.InPotency model.MovedIn model.PriorSimply :=
  ⟨false, (), ⟨rfl, fun _ _ h => h⟩, rfl⟩

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByABeingInActReading Bool Unit model.MovedIn model.MovesIn model.InAct :=
  fun _ _ h => ⟨true, ⟨rfl, h⟩, rfl⟩

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.NothingMovesItselfInSameRespectReading Bool Unit model.MovedIn model.MovesIn := by
  intro x _ hMoved hMoves
  obtain ⟨hy, _⟩ := hMoves
  exact Bool.noConfusion (hMoved.symm.trans hy)

theorem evaluation3 : ¬ (@TruthCore.Alternatives.NightCosmogony.ActualMoverIsSimplyPriorReading Bool Unit model.InAct model.InPotency model.MovesIn model.PriorSimply) :=
  fun h => h true false () rfl ⟨rfl, rfl⟩ rfl Bool.noConfusion

theorem evaluation4 : @TruthCore.Alternatives.ActPotencyRegress.PotencyPriorToActReading Bool Unit model.InAct model.InPotency model.PriorSimply :=
  ⟨false, (), rfl, fun _ _ h => h⟩

theorem evaluation5 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.ActSimplyPriorToPotencyReading Bool Unit model.InAct model.InPotency model.PriorSimply) := by
  intro h
  obtain ⟨_, _, hPrior⟩ := h false () rfl
  exact hPrior
end OtherMover

namespace Residual
def model : Model where
  InAct := fun _ _ => False
  InPotency := fun x _ => x = false
  MovedIn := fun _ _ => False
  MovesIn := fun _ _ _ => False
  PriorSimply := fun _ _ => False

theorem evaluation0 : ¬ (@TruthCore.Alternatives.NightCosmogony.UnprecededPotencyActualizedReading Bool Unit model.InAct model.InPotency model.MovedIn model.PriorSimply) := by
  intro h
  obtain ⟨_, _, _, hMoved⟩ := h
  exact hMoved

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByABeingInActReading Bool Unit model.MovedIn model.MovesIn model.InAct :=
  fun _ _ h => h.elim

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.NothingMovesItselfInSameRespectReading Bool Unit model.MovedIn model.MovesIn :=
  fun _ _ h => h.elim

theorem evaluation3 : @TruthCore.Alternatives.NightCosmogony.ActualMoverIsSimplyPriorReading Bool Unit model.InAct model.InPotency model.MovesIn model.PriorSimply :=
  fun _ _ _ _ h _ _ => h.elim

theorem evaluation4 : @TruthCore.Alternatives.ActPotencyRegress.PotencyPriorToActReading Bool Unit model.InAct model.InPotency model.PriorSimply :=
  ⟨false, (), rfl, fun _ h => h.elim⟩

theorem evaluation5 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.ActSimplyPriorToPotencyReading Bool Unit model.InAct model.InPotency model.PriorSimply) := by
  intro h
  obtain ⟨_, hAct, _⟩ := h false () rfl
  exact hAct
end Residual

end TruthCore.Models.NightCosmogony
