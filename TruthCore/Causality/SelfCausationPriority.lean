module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia

/-! Nothing causes itself, because a cause is prior and nothing is prior to
itself (ST I q.2 a.3, second way; *quia sic esset prius seipso, quod est
impossibile*).

The Secunda Via result proves this step internally; this module states it as
its own derivation of `STMT-NOTHING-IS-EFFICIENT-CAUSE-OF-ITSELF`, which reaches
the root without any recorded derivation. -/

@[expose] public section

namespace TruthCore.Causality.SelfCausationPriority
open TruthCore.Latin.Aquinas.SummaTheologiae

namespace Control

def selfCause (c x : Unit) (_ : Unit) : Prop := c = x
def noPrior (_ _ : Unit) : Prop := False
def allPrior (_ _ : Unit) : Prop := True
def noCause (_ _ _ : Unit) : Prop := False

/-- One being that causes itself: without cause priority, nothing is prior; with
it, the being is prior to itself. With no causation both premises hold. -/
def Certificate : Prop :=
  (¬ EfficientCauseIsPriorToEffectReading selfCause noPrior ∧
    NothingPriorToItselfReading noPrior ∧
    ¬ NothingIsEfficientCauseOfItselfReading selfCause) ∧
  (EfficientCauseIsPriorToEffectReading selfCause allPrior ∧
    ¬ NothingPriorToItselfReading allPrior ∧
    ¬ NothingIsEfficientCauseOfItselfReading selfCause) ∧
  (EfficientCauseIsPriorToEffectReading noCause noPrior ∧
    NothingPriorToItselfReading noPrior ∧
    NothingIsEfficientCauseOfItselfReading noCause)

end Control
end TruthCore.Causality.SelfCausationPriority
