import TruthCore.Alternatives.NightCosmogony
import TruthCore.Logic.ExcludedMiddle

/-!
The alternatives for the *same* unpreceded moved potency in the existing Night
reading. These are compound predicates over the shared act/potency vocabulary,
not a new interpretation of motion, act, potency or priority. The coverage
theorem takes excluded middle explicitly; no source is attributed with this
classification. The self-mover and other-mover branches can overlap.
-/
namespace TruthCore.Alternatives.NightActualizationFork

/-- No mover in act in the given respect moves this being. This does not deny
that a mover not in act in the respect moves it. -/
def NoActualMoverAt {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) (x : Being) (r : Respect) : Prop :=
  ¬ ∃ y, MovesIn y x r ∧ InAct y r

/-- This being moves itself and is in act in the very same respect. -/
def ActualSelfMoverAt {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop) (x : Being) (r : Respect) : Prop :=
  MovesIn x x r ∧ InAct x r

/-- A distinct mover in act in the respect moves this being without being
simply prior to it. This is not a denial of priority in time. -/
def NonpriorOtherActualMoverAt {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop) (x : Being) (r : Respect) : Prop :=
  ∃ y, y ≠ x ∧ MovesIn y x r ∧ InAct y r ∧ ¬ PriorSimply y x

/-- Some unpreceded moved potency, in the exact sense of the existing Night
reading, has no actual mover, is an actual self-mover, or has a distinct actual
mover lacking simple priority. All alternatives concern the selected x and r.
Coverage does not assert that the alternatives are exclusive or establish the
Night background. In particular, the last two may hold jointly. -/
def NightActualizationFork {Being Respect : Type}
    (InAct InPotency MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop) : Prop :=
  ∃ x r, (InPotency x r ∧ ∀ y, InAct y r → ¬ PriorSimply y x) ∧
    MovedIn x r ∧
    (NoActualMoverAt InAct MovesIn x r ∨
      ActualSelfMoverAt InAct MovesIn x r ∨
      NonpriorOtherActualMoverAt InAct MovesIn PriorSimply x r)

/-- Some unpreceded moved potency has a distinct mover in act in its respect
that is not simply prior to it. This retains the Night witness and does not
claim that the mover is an efficient cause or that no temporal priority holds.
It is the forced third branch under the existing root mover premises. -/
def NightNonpriorOtherActualMover {Being Respect : Type}
    (InAct InPotency MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop) : Prop :=
  ∃ x r, (InPotency x r ∧ ∀ y, InAct y r → ¬ PriorSimply y x) ∧
    MovedIn x r ∧ NonpriorOtherActualMoverAt InAct MovesIn PriorSimply x r

end TruthCore.Alternatives.NightActualizationFork
