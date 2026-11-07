module

public import TruthCore.Latin.Aquinas.InMetaphysicam.BookIX
public import TruthCore.Case.Catholicism.StageOneConvergence

/-! A necessary being has being, from "incorruptibles are in act"
(In Metaph. IX lect. 9; Met. Θ.8 1050b16-18)

`STMT-NECESSARY-BEING-HAS-BEING` is an open bridge between the *tertia via*'s
modal vocabulary and the *quarta via*'s act vocabulary. The Metaphysics IX
reading `IncorruptibleIsInActReading` (a simply incorruptible being is in act in
substance) had no argument consumer. They meet through one explicit bridge:
whatever can fail to be in substance (In Metaph. IX: *corruptibile ... quod
potest non esse secundum substantiam*) possibly is not in the *tertia via*'s
sense (`CanFailToBeIsPossiblyNot`). Then a necessary being cannot fail to be in
substance, so it is incorruptible simply, so it is in act as to being.

Only the direction from "can fail to be" to "possibly not" is assumed. Analyst
bridge; attribution deferred. -/

@[expose] public section

namespace TruthCore.Causality.NecessaryBeingInAct
open TruthCore.Latin.Aquinas.SummaTheologiae (PossibleNotToBe)

/-- OPEN bridge: what can fail to be in substance possibly is not. -/
def CanFailToBeIsPossiblyNot {B T R : Type} (Possible : (T → Prop) → Prop)
    (IsAt : B → T → Prop) (CanFailToBe : B → R → Prop) (esse : R) : Prop :=
  ∀ x, CanFailToBe x esse → PossibleNotToBe Possible IsAt x

namespace Control
open TruthCore.Latin.Aquinas.InMetaphysicam (IncorruptibleIsInActReading)
open TruthCore.Case.Catholicism (NecessaryBeingHasBeing)

/-- One being, always present, nothing possible about absence. -/
def neverPossible (_ : Unit → Prop) : Prop := False
def always (_ _ : Unit) : Prop := True
def canFail (_ _ : Unit) : Prop := True
def cannotFail (_ _ : Unit) : Prop := False
def noAct (_ _ : Unit) : Prop := False
def allAct (_ _ : Unit) : Prop := True

/-- The one being is necessary. Without the bridge it can fail to be in
substance, so incorruptibility gives nothing and it is not in act; without
"incorruptibles are in act" it cannot fail and is still not in act; with both it
is in act. -/
def Certificate : Prop :=
  (¬ CanFailToBeIsPossiblyNot neverPossible always canFail () ∧
    IncorruptibleIsInActReading noAct canFail () ∧
    ¬ NecessaryBeingHasBeing neverPossible always noAct ()) ∧
  (CanFailToBeIsPossiblyNot neverPossible always cannotFail () ∧
    ¬ IncorruptibleIsInActReading noAct cannotFail () ∧
    ¬ NecessaryBeingHasBeing neverPossible always noAct ()) ∧
  (CanFailToBeIsPossiblyNot neverPossible always cannotFail () ∧
    IncorruptibleIsInActReading allAct cannotFail () ∧
    NecessaryBeingHasBeing neverPossible always allAct ())

end Control
end TruthCore.Causality.NecessaryBeingInAct
