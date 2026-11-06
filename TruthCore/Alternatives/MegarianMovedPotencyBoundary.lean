module

public import TruthCore.Models.MegarianCapacity
public import TruthCore.Greek.Aristotle.MetaphysicsIX
public import TruthCore.Logic.ExcludedMiddle

/-!
# When the Megarian thesis actually opposes moved-in-potency

Reuse the exact original MovedIn/InAct/InPotency/CanBe dictionaries. The
Megarian capacity principle is not automatically a denial of moved-in-potency:
a real moved witness and the SAME-sense unactualized-capacity analysis are
needed. Only its forward direction at moved tuples is used. This weaker
interpretation is a separate proposition, not a changed Aristotle claim.
The controls extend the old finite Megarian models only with an independent
potency field; the old model fields/evaluations remain unchanged.
-/

@[expose] public section
namespace TruthCore.Alternatives.MegarianMovedPotencyBoundary
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Greek.Aristotle.Metaphysics

/-- Weak scope actually needed: only moved tuples and only potency-to-capacity
and nonactuality. No converse or constraint on idle potency is included. -/
def AnalysisOnMoved {B R : Type} (MovedIn InAct InPotency CanBe : B → R → Prop) : Prop :=
  ∀ x r, MovedIn x r → InPotency x r → CanBe x r ∧ ¬ InAct x r

/-- Exact analyst countertuple, without the historical re-creation story that
the existing occasionalist candidate adds in its prose. -/
def Countertuple {B R : Type} (MovedIn InPotency : B → R → Prop) : Prop :=
  MovedWithoutPotencyReading MovedIn InPotency

def MovedPotencyFork {B R : Type} (MovedIn InPotency : B → R → Prop) : Prop :=
  MovedOnlyAsInPotencyReading MovedIn InPotency ∨ Countertuple MovedIn InPotency

def MovedPotencyFails {B R : Type} (MovedIn InPotency : B → R → Prop) : Prop :=
  ¬ MovedOnlyAsInPotencyReading MovedIn InPotency

open TruthCore.Models.MegarianCapacity

def noPotency : Unit → Unit → Prop := fun _ _ => False
def fullPotency : Unit → Unit → Prop := fun _ _ => True

def NoMovedControl : Prop :=
  MegarianAbilityOnlyWhenActingReading NothingMoved.model.InAct NothingMoved.model.CanBe ∧
  PotencyIsUnactualizedCapacityReading NothingMoved.model.InAct noPotency NothingMoved.model.CanBe ∧
  MovedOnlyAsInPotencyReading NothingMoved.model.MovedIn noPotency ∧
  ¬ SomethingIsMovedReading NothingMoved.model.MovedIn

def UncalibratedControl : Prop :=
  MegarianAbilityOnlyWhenActingReading MovedAlreadyActual.model.InAct MovedAlreadyActual.model.CanBe ∧
  SomethingIsMovedReading MovedAlreadyActual.model.MovedIn ∧
  MovedOnlyAsInPotencyReading MovedAlreadyActual.model.MovedIn fullPotency ∧
  ¬ AnalysisOnMoved MovedAlreadyActual.model.MovedIn MovedAlreadyActual.model.InAct fullPotency MovedAlreadyActual.model.CanBe

def GuardedControl : Prop :=
  MegarianAbilityOnlyWhenActingReading MovedWithoutAbility.model.InAct MovedWithoutAbility.model.CanBe ∧
  SomethingIsMovedReading MovedWithoutAbility.model.MovedIn ∧
  PotencyIsUnactualizedCapacityReading MovedWithoutAbility.model.InAct noPotency MovedWithoutAbility.model.CanBe ∧
  MovedWithoutPotencyReading MovedWithoutAbility.model.MovedIn noPotency

def StrictnessControl : Prop :=
  AnalysisOnMoved NothingMoved.model.MovedIn NothingMoved.model.InAct fullPotency NothingMoved.model.CanBe ∧
  ¬ PotencyIsUnactualizedCapacityReading NothingMoved.model.InAct fullPotency NothingMoved.model.CanBe

def Controls : Prop := NoMovedControl ∧ UncalibratedControl ∧ GuardedControl ∧ StrictnessControl

end TruthCore.Alternatives.MegarianMovedPotencyBoundary
