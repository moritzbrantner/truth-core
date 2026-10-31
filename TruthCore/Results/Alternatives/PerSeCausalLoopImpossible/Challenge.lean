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

/-- A productive act cannot bring its own bearer into existence when the
bearer's existence is prior to the act, the act is prior to the existence it
produces, and priority is transitive and irreflexive. The two `Sum` tags keep
the *existence of a being* distinct from an *act of that being*. This is an
unattributed conditional, not a claim that all causal or explanatory relations
have this priority interpretation. -/
theorem noExistentialSelfActualization {Being Exercise : Type}
    (Occurs : Exercise → Prop) (Bearer : Exercise → Being)
    (ActualizesExistence : Exercise → Being → Prop)
    (Prior : Sum Being Exercise → Sum Being Exercise → Prop)
    (hBearerPrior : ∀ a, Occurs a → Prior (.inl (Bearer a)) (.inr a))
    (hProductPrior : ∀ a x, Occurs a → ActualizesExistence a x →
      Prior (.inr a) (.inl x))
    (hNoSelfPrior : NothingPriorToItselfReading Prior)
    (hTrans : SimplePriorityTransitiveReading Prior) :
    ∀ a, Occurs a → ¬ ActualizesExistence a (Bearer a) := by
  sorry

/-- Without transitivity, a two-token priority cycle can be irreflexive while
allowing the bearer's existence to precede the act and vice versa. -/
theorem existentialSelfActualizationNeedsTransitivity :
    ∃ Prior : Sum Unit Unit → Sum Unit Unit → Prop,
      NothingPriorToItselfReading Prior ∧
      Prior (.inl ()) (.inr ()) ∧ Prior (.inr ()) (.inl ()) := by
  sorry

/-- Without irreflexivity, universal priority permits the same two-token
cycle while remaining transitive. -/
theorem existentialSelfActualizationNeedsIrreflexivity :
    ∃ Prior : Sum Unit Unit → Sum Unit Unit → Prop,
      SimplePriorityTransitiveReading Prior ∧
      Prior (.inl ()) (.inr ()) ∧ Prior (.inr ()) (.inl ()) := by
  sorry

/-- Positive control: an act can still actualize the existence of a being
other than its already-existing bearer, while respecting both priority
interfaces and strict transitive priority. -/
theorem otherBearerCanActualizeExistence :
    ∃ (Occurs : Unit → Prop) (Bearer : Unit → Bool)
        (ActualizesExistence : Unit → Bool → Prop)
        (Prior : Sum Bool Unit → Sum Bool Unit → Prop),
      (∀ a, Occurs a → Prior (.inl (Bearer a)) (.inr a)) ∧
      (∀ a x, Occurs a → ActualizesExistence a x → Prior (.inr a) (.inl x)) ∧
      NothingPriorToItselfReading Prior ∧
      SimplePriorityTransitiveReading Prior ∧
      Occurs () ∧ ActualizesExistence () false := by
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
