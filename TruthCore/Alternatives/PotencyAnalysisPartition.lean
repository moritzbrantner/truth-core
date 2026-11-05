import TruthCore.Greek.Aristotle.MetaphysicsIX
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3

/-!
The owner's worldview-level argument for F7 (#1007), as a partition by the
shared question, not a hand-picked list of worldviews.

Shared question Q-F7: is a being in potency in a respect exactly when it is
able to be so and is not actually so (`PotencyIsUnactualizedCapacityReading`,
*Metaphysics* IX.6, 1048a30-35)? Every worldview, as far as Q-F7 goes, either
answers yes (the F7 cell) or lies in one of three ¬F7 cells, by the way the
biconditional fails for some being and respect:

* (a) potency together with act in the same respect (Scotus' virtual act and
  formal potency; Hegel's moving body, here and not here);
* (b) potency without the capacity (potency read as something other than an
  ability);
* (c) an unexercised capacity that is no potency.

Exhaustiveness follows from excluded middle alone (`STMT-EXCLUDED-MIDDLE`,
supplied as a hypothesis, never as an axiom). F7 is equivalent to the
conjunction of the three constraints that exclude the cells one by one, so a
floor that defeats every ¬F7 cell has to entail F7 itself.
-/

namespace TruthCore.Alternatives.PotencyAnalysisPartition

open TruthCore.Greek.Aristotle.Metaphysics
open TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

variable {Being : Sort u} {Respect : Sort v}

/-- Cell (a): something is in potency and in act in the same respect. -/
def PotencyWithActCell (InAct InPotency : Being → Respect → Prop) : Prop :=
  ∃ x r, InPotency x r ∧ InAct x r

/-- Cell (b): something is in potency in a respect without being able to be so. -/
def PotencyWithoutCapacityCell (InPotency CanBe : Being → Respect → Prop) : Prop :=
  ∃ x r, InPotency x r ∧ ¬ CanBe x r

/-- Cell (c): something is able to be so in a respect, is not actually so, and
is not in potency in that respect. -/
def UnexercisedCapacityWithoutPotencyCell (InAct InPotency CanBe : Being → Respect → Prop) : Prop :=
  ∃ x r, CanBe x r ∧ ¬ InAct x r ∧ ¬ InPotency x r

/-- The partition of Q-F7: F7, or one of the three ¬F7 cells. -/
def PotencyAnalysisPartition (InAct InPotency CanBe : Being → Respect → Prop) : Prop :=
  PotencyIsUnactualizedCapacityReading InAct InPotency CanBe ∨
    PotencyWithActCell InAct InPotency ∨ PotencyWithoutCapacityCell InPotency CanBe ∨
      UnexercisedCapacityWithoutPotencyCell InAct InPotency CanBe

/-- The constraint that excludes cell (b): whatever is in potency is able to be so. -/
def PotencyImpliesCapacity (InPotency CanBe : Being → Respect → Prop) : Prop :=
  ∀ x r, InPotency x r → CanBe x r

/-- The constraint that excludes cell (c): an unexercised capacity is a potency. -/
def UnexercisedCapacityIsPotency (InAct InPotency CanBe : Being → Respect → Prop) : Prop :=
  ∀ x r, CanBe x r ∧ ¬ InAct x r → InPotency x r

/-- Each ¬F7 cell survives the approved floor items that constrain these
predicates at all: there is an interpretation of the cell in which something
is moved (F4). F1 (non-contradiction for the case predicates) holds in every
interpretation, being a theorem; F3 and F6 use vocabulary (`Changes`, epistemic
`Reason`) that does not occur here, so they extend any interpretation. -/
def CellsSurviveFloor : Prop :=
  (∃ (B R : Type) (InAct InPotency : B → R → Prop) (MovedIn : B → R → Prop),
      PotencyWithActCell InAct InPotency ∧ SomethingIsMovedReading MovedIn) ∧
    (∃ (B R : Type) (InPotency CanBe : B → R → Prop) (MovedIn : B → R → Prop),
      PotencyWithoutCapacityCell InPotency CanBe ∧ SomethingIsMovedReading MovedIn) ∧
    (∃ (B R : Type) (InAct InPotency CanBe : B → R → Prop) (MovedIn : B → R → Prop),
      UnexercisedCapacityWithoutPotencyCell InAct InPotency CanBe ∧ SomethingIsMovedReading MovedIn)

end TruthCore.Alternatives.PotencyAnalysisPartition
