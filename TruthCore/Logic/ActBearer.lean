/-! Act–bearer–substance distinctions. The ontology is parameterized:
no bearer principle or substance thesis is built into the event type. -/
namespace TruthCore.Logic.ActBearer

/-- An actual act occurs. -/
def SomeAct {Act : Type} (Actual : Act → Prop) : Prop :=
  ∃ a, Actual a

/-- Every actual act is borne by something. Open metaphysical premise. -/
def EveryActHasBearer {Act Being : Type}
    (Actual : Act → Prop) (Bears : Being → Act → Prop) : Prop :=
  ∀ a, Actual a → ∃ b, Bears b a

/-- There exists a bearer of an actual act. -/
def ActualBearer {Act Being : Type}
    (Actual : Act → Prop) (Bears : Being → Act → Prop) : Prop :=
  ∃ b a, Actual a ∧ Bears b a

/-- Every bearer of an actual act is a substance. A separate stronger thesis. -/
def EveryActualBearerSubstance {Act Being : Type}
    (Actual : Act → Prop) (Bears : Being → Act → Prop)
    (Substance : Being → Prop) : Prop :=
  ∀ b a, Actual a → Bears b a → Substance b

/-- There is a substance bearing an actual act. -/
def ActualSubstantialBearer {Act Being : Type}
    (Actual : Act → Prop) (Bears : Being → Act → Prop)
    (Substance : Being → Prop) : Prop :=
  ∃ b a, Actual a ∧ Bears b a ∧ Substance b

/-- Occurrence and bearer principle imply a bearer. -/
def BearerInference : Prop :=
  ∀ (Act Being : Type) (Actual : Act → Prop) (Bears : Being → Act → Prop),
    SomeAct Actual → EveryActHasBearer Actual Bears → ActualBearer Actual Bears

/-- The additional substance principle is needed for this stronger inference. -/
def SubstanceInference : Prop :=
  ∀ (Act Being : Type) (Actual : Act → Prop) (Bears : Being → Act → Prop)
    (Substance : Being → Prop),
    SomeAct Actual → EveryActHasBearer Actual Bears →
      EveryActualBearerSubstance Actual Bears Substance →
        ActualSubstantialBearer Actual Bears Substance

/-- A bearer can exist without being classified as a substance. -/
def NonSubstantialBearerModel : Prop :=
  ∃ (Actual : Unit → Prop) (Bears : Unit → Unit → Prop)
    (Substance : Unit → Prop),
    SomeAct Actual ∧ EveryActHasBearer Actual Bears ∧
      ¬ ActualSubstantialBearer Actual Bears Substance

/-- An actual event need not have a bearer in an unconstrained event ontology. -/
def BearerlessActModel : Prop :=
  ∃ (Actual : Unit → Prop) (Bears : Unit → Unit → Prop),
    SomeAct Actual ∧ ¬ ActualBearer Actual Bears

end TruthCore.Logic.ActBearer
