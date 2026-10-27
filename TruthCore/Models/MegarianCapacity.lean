import TruthCore.Models.FiniteSupport
import TruthCore.Alternatives.ActPotencyRegress

/-! Named finite interpretations for the Megarian capacity core (#576,
`MEGARIAN-CAPACITY-MOTION-INCOMPATIBLE`). Beings and respects are `Unit`. Each
model drops exactly one of the four core members and satisfies the other
three, so every maximal proper subset of the core is model witnessed under the
shared vocabulary `MovedIn`, `InAct`, `CanBe`. Registration tests formal
satisfiability of the encoding only; it does not establish metaphysical
possibility or close any premise.

* `UnactualizedAbility`: the one being is moved, able to be the respect and not
  actually it. Present motion, motion's incompleteness and the ability of what
  is moved hold; the Megarian thesis fails.
* `NothingMoved`: nothing is moved, able or actual. The Megarian thesis holds
  vacuously and so do the two conditionals on motion; present motion fails.
* `MovedAlreadyActual`: the being is moved toward a respect it already actually
  has and is able to have. The Megarian thesis, present motion and ability hold;
  motion's incompleteness fails.
* `MovedWithoutAbility`: the being is moved, not actual and not able. The
  Megarian thesis holds vacuously; the ability of what is moved fails. -/
namespace TruthCore.Models.MegarianCapacity
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Alternatives.ActPotencyRegress

structure Model where
  MovedIn : Unit → Unit → Prop
  InAct : Unit → Unit → Prop
  CanBe : Unit → Unit → Prop

namespace UnactualizedAbility
def model : Model where
  MovedIn := fun _ _ => True
  InAct := fun _ _ => False
  CanBe := fun _ _ => True

theorem evaluation0 : ¬ (@MegarianAbilityOnlyWhenActingReading Unit Unit model.InAct model.CanBe) :=
  fun h => h () () trivial

theorem evaluation1 : @SomethingIsMovedReading Unit Unit model.MovedIn :=
  ⟨(), (), trivial⟩

theorem evaluation2 : @MovedNotYetInActReading Unit Unit model.MovedIn model.InAct :=
  fun _ _ _ h => h

theorem evaluation3 : @MovedIsAbleToBeReading Unit Unit model.MovedIn model.CanBe :=
  fun _ _ _ => trivial
end UnactualizedAbility

namespace NothingMoved
def model : Model where
  MovedIn := fun _ _ => False
  InAct := fun _ _ => False
  CanBe := fun _ _ => False

theorem evaluation0 : @MegarianAbilityOnlyWhenActingReading Unit Unit model.InAct model.CanBe :=
  fun _ _ h => h

theorem evaluation1 : ¬ (@SomethingIsMovedReading Unit Unit model.MovedIn) :=
  fun ⟨_, _, h⟩ => h

theorem evaluation2 : @MovedNotYetInActReading Unit Unit model.MovedIn model.InAct :=
  fun _ _ h => h.elim

theorem evaluation3 : @MovedIsAbleToBeReading Unit Unit model.MovedIn model.CanBe :=
  fun _ _ h => h
end NothingMoved

namespace MovedAlreadyActual
def model : Model where
  MovedIn := fun _ _ => True
  InAct := fun _ _ => True
  CanBe := fun _ _ => True

theorem evaluation0 : @MegarianAbilityOnlyWhenActingReading Unit Unit model.InAct model.CanBe :=
  fun _ _ _ => trivial

theorem evaluation1 : @SomethingIsMovedReading Unit Unit model.MovedIn :=
  ⟨(), (), trivial⟩

theorem evaluation2 : ¬ (@MovedNotYetInActReading Unit Unit model.MovedIn model.InAct) :=
  fun h => h () () trivial trivial

theorem evaluation3 : @MovedIsAbleToBeReading Unit Unit model.MovedIn model.CanBe :=
  fun _ _ _ => trivial
end MovedAlreadyActual

namespace MovedWithoutAbility
def model : Model where
  MovedIn := fun _ _ => True
  InAct := fun _ _ => False
  CanBe := fun _ _ => False

theorem evaluation0 : @MegarianAbilityOnlyWhenActingReading Unit Unit model.InAct model.CanBe :=
  fun _ _ h => h

theorem evaluation1 : @SomethingIsMovedReading Unit Unit model.MovedIn :=
  ⟨(), (), trivial⟩

theorem evaluation2 : @MovedNotYetInActReading Unit Unit model.MovedIn model.InAct :=
  fun _ _ _ h => h

theorem evaluation3 : ¬ (@MovedIsAbleToBeReading Unit Unit model.MovedIn model.CanBe) :=
  fun h => h () () trivial
end MovedWithoutAbility

end TruthCore.Models.MegarianCapacity
