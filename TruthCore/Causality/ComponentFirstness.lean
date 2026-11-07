module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article8
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia

/-! No component is the first being, from ST I q.3 a.8's third reason (#356)

`STMT-NO-COMPONENT-IS-FIRST-BEING` is an underived leaf of 21 root routes. The
third reason of q.3 a.8 says why: no component can be simply first, "neither
matter, because matter is in potency, and potency is simply posterior to act;
nor a form that is part of a composite, because it is a participated form, and
the participated is posterior to what is by essence". Typed here:
* `ComponentIsPotentialOrParticipated`: each component is in potency in some
  respect or has its being by participation (the two kinds the passage
  considers, read as exhaustive);
* `ParticipatedHasOtherCause` (ST I q.44 a.1 ad 1): what has being by
  participation has a cause of its being other than itself;
* the existing route premises that act is simply prior to potency and that
  nothing is in act and in potency in the same respect;
* the existing Secunda Via reading that an efficient cause is prior to its
  effect.

`Participated` is a primitive predicate ("has esse by participation"); no Platonic
participation relation is implied. Analyst composition; the two new readings are
linked to their passages by `supports` relations recording the gaps. -/

@[expose] public section

namespace TruthCore.Causality.ComponentFirstness

variable {B R : Type}

/-- q.3 a.8, third reason, as exhaustive: every component is in potency in some
respect or has its being by participation. -/
def ComponentIsPotentialOrParticipated (ComponentOf : B → B → Prop)
    (InPotency : B → R → Prop) (Participated : B → Prop) : Prop :=
  ∀ p x, ComponentOf p x → (∃ r, InPotency p r) ∨ Participated p

/-- q.44 a.1 ad 1: whatever has being by participation is caused in being by
something other than itself. -/
def ParticipatedHasOtherCause (Participated : B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) : Prop :=
  ∀ x, Participated x → ∃ c, c ≠ x ∧ CausesIn c x esse

namespace Control
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- `false` is a component of `true`. -/
def comp (p x : Bool) : Prop := p = false ∧ x = true
def none2 (_ _ : Bool) : Prop := False
def none1 (_ : Bool) : Prop := False
def isFalse (x : Bool) : Prop := x = false
def potFalse (x : Bool) (_ : Unit) : Prop := x = false
def actNone (_ : Bool) (_ : Unit) : Prop := False
def actAll (_ : Bool) (_ : Unit) : Prop := True
def causesNone (_ _ : Bool) (_ : Unit) : Prop := False
/-- `true` causes the being of `false`. -/
def causesFalse (c x : Bool) (_ : Unit) : Prop := c = true ∧ x = false
/-- Each being is prior only to itself. -/
def priorSelf (y x : Bool) : Prop := y = x
/-- `true` is prior to `false`. -/
def priorFalse (y x : Bool) : Prop := y = true ∧ x = false

/-- The five premises of the derivation, in one bundle per interpretation. -/
def Premises (InAct InPotency : Bool → Unit → Prop) (Participated : Bool → Prop)
    (CausesIn : Bool → Bool → Unit → Prop) (Prior : Bool → Bool → Prop) : Prop :=
  ComponentIsPotentialOrParticipated comp InPotency Participated ∧
  ActSimplyPriorToPotencyReading InAct InPotency Prior ∧
  NotActAndPotencyInSameRespectReading InAct InPotency ∧
  ParticipatedHasOtherCause Participated CausesIn () ∧
  EfficientCauseIsPriorToEffectReading CausesIn Prior

/-- Finite interpretations with `false` a component of `true`. Each omission
keeps the other four premises and makes `false` first in being, so the
conclusion fails:
* disjunction omitted: the component is neither potential nor participated;
* act priority omitted: the component is in potency with nothing prior;
* same-respect exclusion omitted: the component is in act and in potency, so act
  priority is met by itself;
* participation-cause omitted: the component is participated without a cause;
* efficient priority omitted: it is participated and caused, but the cause is not
  prior.
Positive witness: with the cause prior, all five premises and the conclusion
hold. -/
def Certificate : Prop :=
  (¬ ComponentIsPotentialOrParticipated comp actNone none1 ∧
    ActSimplyPriorToPotencyReading actNone actNone none2 ∧
    NotActAndPotencyInSameRespectReading actNone actNone ∧
    ParticipatedHasOtherCause none1 causesNone () ∧
    EfficientCauseIsPriorToEffectReading causesNone none2 ∧
    ¬ NoComponentIsFirstBeingReading comp none2) ∧
  (ComponentIsPotentialOrParticipated comp potFalse none1 ∧
    ¬ ActSimplyPriorToPotencyReading actNone potFalse none2 ∧
    NotActAndPotencyInSameRespectReading actNone potFalse ∧
    ParticipatedHasOtherCause none1 causesNone () ∧
    EfficientCauseIsPriorToEffectReading causesNone none2 ∧
    ¬ NoComponentIsFirstBeingReading comp none2) ∧
  (ComponentIsPotentialOrParticipated comp potFalse none1 ∧
    ActSimplyPriorToPotencyReading actAll potFalse priorSelf ∧
    ¬ NotActAndPotencyInSameRespectReading actAll potFalse ∧
    ParticipatedHasOtherCause none1 causesNone () ∧
    EfficientCauseIsPriorToEffectReading causesNone priorSelf ∧
    ¬ NoComponentIsFirstBeingReading comp priorSelf) ∧
  (ComponentIsPotentialOrParticipated comp actNone isFalse ∧
    ActSimplyPriorToPotencyReading actNone actNone none2 ∧
    NotActAndPotencyInSameRespectReading actNone actNone ∧
    ¬ ParticipatedHasOtherCause isFalse causesNone () ∧
    EfficientCauseIsPriorToEffectReading causesNone none2 ∧
    ¬ NoComponentIsFirstBeingReading comp none2) ∧
  (ComponentIsPotentialOrParticipated comp actNone isFalse ∧
    ActSimplyPriorToPotencyReading actNone actNone none2 ∧
    NotActAndPotencyInSameRespectReading actNone actNone ∧
    ParticipatedHasOtherCause isFalse causesFalse () ∧
    ¬ EfficientCauseIsPriorToEffectReading causesFalse none2 ∧
    ¬ NoComponentIsFirstBeingReading comp none2) ∧
  (Premises actNone actNone isFalse causesFalse priorFalse ∧
    NoComponentIsFirstBeingReading comp priorFalse ∧ comp false true)

end Control
end TruthCore.Causality.ComponentFirstness
