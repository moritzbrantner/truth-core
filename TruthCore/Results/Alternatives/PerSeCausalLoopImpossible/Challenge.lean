import TruthCore.Alternatives.ActPotencyRegress
namespace TruthCore.Results.Alternatives.PerSeCausalLoopImpossible
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Alternatives.ActPotencyRegress

/-- No per se causal loop, from the Second Way's priority premises (*sic esset
prius seipso*): each per se link is an efficient causing, every efficient cause
is simply prior to its effect, and simple priority is transitive, so by
induction along the chain a being on a loop would be prior to itself, which
nothing is. -/
theorem noPerSeCausalLoop {Being Respect : Type}
    (EfficientlyCausesIn : Being → Being → Respect → Prop)
    (CausesAsCaused PriorSimply : Being → Being → Prop)
    (hMiddle : MiddleCauseEfficientlyCausesReading EfficientlyCausesIn CausesAsCaused)
    (hPrior : EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply)
    (hNotSelfPrior : NothingPriorToItselfReading PriorSimply)
    (hTrans : SimplePriorityTransitiveReading PriorSimply) :
    NoPerSeCausalLoop CausesAsCaused := by
  sorry

/-- Transitivity is needed: two beings that cause each other per se, each
simply prior to the other but neither to itself, satisfy the other premises. -/
theorem needsTransitivity :
    ¬ ∀ (Being Respect : Type) (EfficientlyCausesIn : Being → Being → Respect → Prop)
        (CausesAsCaused PriorSimply : Being → Being → Prop),
      MiddleCauseEfficientlyCausesReading EfficientlyCausesIn CausesAsCaused →
      EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply →
      NothingPriorToItselfReading PriorSimply →
        NoPerSeCausalLoop CausesAsCaused := by
  sorry

/-- Irreflexivity of priority is needed: a single self-prior being on a
self-loop satisfies the other premises. -/
theorem needsNothingPriorToItself :
    ¬ ∀ (Being Respect : Type) (EfficientlyCausesIn : Being → Being → Respect → Prop)
        (CausesAsCaused PriorSimply : Being → Being → Prop),
      MiddleCauseEfficientlyCausesReading EfficientlyCausesIn CausesAsCaused →
      EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply →
      SimplePriorityTransitiveReading PriorSimply →
        NoPerSeCausalLoop CausesAsCaused := by
  sorry

/-- Priority of cause over effect is needed: a self-causing loop with no
priority at all satisfies the other premises. -/
theorem needsCausePriorToEffect :
    ¬ ∀ (Being Respect : Type) (EfficientlyCausesIn : Being → Being → Respect → Prop)
        (CausesAsCaused PriorSimply : Being → Being → Prop),
      MiddleCauseEfficientlyCausesReading EfficientlyCausesIn CausesAsCaused →
      NothingPriorToItselfReading PriorSimply →
      SimplePriorityTransitiveReading PriorSimply →
        NoPerSeCausalLoop CausesAsCaused := by
  sorry

/-- The middle-cause premise is needed: a per se loop whose links are no
efficient causings escapes the priority premises. -/
theorem needsMiddleCause :
    ¬ ∀ (Being Respect : Type) (EfficientlyCausesIn : Being → Being → Respect → Prop)
        (CausesAsCaused PriorSimply : Being → Being → Prop),
      EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply →
      NothingPriorToItselfReading PriorSimply →
      SimplePriorityTransitiveReading PriorSimply →
        NoPerSeCausalLoop CausesAsCaused := by
  sorry

end TruthCore.Results.Alternatives.PerSeCausalLoopImpossible
