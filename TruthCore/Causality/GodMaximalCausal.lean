module

public import TruthCore.Case.Catholicism.StageTwo
public import TruthCore.Greek.Aristotle.Metaphysics
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaAscent
public import TruthCore.Logic.ExcludedMiddle

/-! God is maximal in being, from God's causing the being of all else
(exploration map `explorations/god-is-maximal-in-being.toml`)

An alternative to taking `STMT-GOD-IS-MAXIMAL-IN-BEING` as the bare converse of
the nominal definition: read the same q.2 a.3 naming sentence's causal clause
conversely (whatever is God causes the being of every other being), then use the
route premise that a cause of a quality is more such and the Quarta Via premise
that what is more such has the perfection. Two bridges are explicit and open:
more-in is asymmetric, and something other than God exists. -/

@[expose] public section

namespace TruthCore.Causality.GodMaximalCausal

variable {B R : Type}

/-- Causal converse of the naming sentence: whatever is God causes the being of
every other being. -/
def GodCausesBeingOfAllOthers (IsGod : B → Prop) (CausesIn : B → B → R → Prop) (esse : R) : Prop :=
  ∀ g y, IsGod g → y ≠ g → CausesIn g y esse

/-- OPEN bridge: being more such is asymmetric. -/
def MoreInIsAsymmetric (MoreIn : R → B → B → Prop) : Prop :=
  ∀ r x y, MoreIn r x y → ¬ MoreIn r y x

/-- OPEN bridge: for whatever is God, something other than it exists. -/
def SomethingOtherThanGodExists (IsGod : B → Prop) : Prop :=
  ∀ g, IsGod g → ∃ y, y ≠ g

namespace Control
open TruthCore.Case.Catholicism (GodIsMaximalInBeing)

/-- Two beings, `true` is God; `true` causes the being of `false` and is more in
being than it. -/
def isGod (x : Bool) : Prop := x = true
def causes (c x : Bool) (_ : Unit) : Prop := c = true ∧ x = false
def more (_ : Unit) (x y : Bool) : Prop := x = true ∧ y = false
def inAct (_ : Bool) (_ : Unit) : Prop := True

/-- Positive witness: all premises and the conclusion hold with a God and another
being. -/
def Certificate : Prop :=
  GodCausesBeingOfAllOthers isGod causes () ∧ MoreInIsAsymmetric more ∧
    SomethingOtherThanGodExists isGod ∧
    TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading causes more ∧
    TruthCore.Latin.Aquinas.SummaTheologiae.MoreSuchHasThePerfectionReading inAct more ∧
    GodIsMaximalInBeing isGod inAct more () ∧ isGod true

end Control
end TruthCore.Causality.GodMaximalCausal
