module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.BoethianEternity
public import TruthCore.Greek.Aristotle.Physics

/-! Succession requires potency, from motion as actualization of potency
(ST I q.9 a.1; Physics III.1)

`STMT-SUCCESSION-REQUIRES-POTENCY` (q.9 a.1: whatever is changed in any way is in
some way in potency, read for succession of life-states) reaches the root with
no derivation. Physics III.1 defines being moved as the actualization of what is
potential as such (`BeingMovedIsActualizationOfPotencyReading`), so whatever is
being moved in a respect is in potency in it. One explicit bridge links the
two: a life whose state differs between two times at which it lives is being
moved in some respect (`SuccessionIsBeingMoved`). Only the left-to-right half of
the Physics biconditional is used. Generation and corruption (beginning or
ceasing to live) are not covered: they are changes but not motions in Physics V,
so the bridge says nothing about them. -/

@[expose] public section

namespace TruthCore.Causality.SuccessionPotency
open TruthCore.Latin.Aquinas.SummaTheologiae (LifeHasSuccession)

/-- OPEN bridge: a succession of life-states within one living subject is a
being moved in some respect. -/
def SuccessionIsBeingMoved {B R T S : Type} [LT T] (LivesAt : B → T → Prop)
    (lifeStateAt : B → T → S) (MovedIn : B → R → Prop) : Prop :=
  ∀ x, LifeHasSuccession LivesAt lifeStateAt x → ∃ r, MovedIn x r

namespace Control
open TruthCore.Latin.Aquinas.SummaTheologiae (SuccessionRequiresPotencyReading)
open TruthCore.Greek.Aristotle.Physics (BeingMovedIsActualizationOfPotencyReading)

/-- One being living at times `false < true` with different states. -/
def lives (_ : Unit) (_ : Bool) : Prop := True
def state (_ : Unit) (t : Bool) : Bool := t
def moved (_ _ : Unit) : Prop := True
def unmoved (_ _ : Unit) : Prop := False
def potent (_ _ : Unit) : Prop := True
def impotent (_ _ : Unit) : Prop := False

/-- The being's life has succession. Without the bridge it is not moved and has
no potency; without Physics III.1 it is moved without potency; with both it is
in potency. -/
def Certificate : Prop :=
  (¬ SuccessionIsBeingMoved lives state unmoved ∧
    BeingMovedIsActualizationOfPotencyReading unmoved impotent impotent ∧
    ¬ SuccessionRequiresPotencyReading impotent lives state) ∧
  (SuccessionIsBeingMoved lives state moved ∧
    ¬ BeingMovedIsActualizationOfPotencyReading moved impotent impotent ∧
    ¬ SuccessionRequiresPotencyReading impotent lives state) ∧
  (SuccessionIsBeingMoved lives state moved ∧
    BeingMovedIsActualizationOfPotencyReading moved potent potent ∧
    SuccessionRequiresPotencyReading potent lives state)

end Control
end TruthCore.Causality.SuccessionPotency
