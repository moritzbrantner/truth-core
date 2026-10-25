import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3SecundaVia
namespace TruthCore.Results.Aquinas.SummaTheologiae.SecundaVia
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- ST I q.2 a.3 co., the *secunda via*: there is an order of efficient causes;
nothing causes itself, since it would be prior to itself; a caused cause causes
only as caused; and the per se series cannot go to infinity. So a first efficient
cause cannot be lacking. -/
theorem secundaVia {Being : Type} {Respect : Type}
    (EfficientlyCausesIn : Being → Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop)
    (CausesAsCaused : Being → Being → Prop)
    (hOrder : OrderOfEfficientCausesFoundReading EfficientlyCausesIn)
    (hPrior : EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply)
    (hIrrefl : NothingPriorToItselfReading PriorSimply)
    (hPerSe : SecondEfficientCausesCauseOnlyAsCausedReading EfficientlyCausesIn
      CausesAsCaused)
    (hRegress : NoInfinitePerSeEfficientCauseSeriesReading CausesAsCaused) :
    FirstEfficientCauseCannotBeLackingReading EfficientlyCausesIn := by
  sorry

/-- The observation premise is needed: in a world where nothing efficiently causes anything, every other premise holds vacuously and there is no first efficient cause. -/
theorem secundaViaNeedsOrder :
    ¬ ∀ (Being Respect : Type)
      (E : Being → Being → Respect → Prop) (P C : Being → Being → Prop),
      EfficientCauseIsPriorToEffectReading E P →
      NothingPriorToItselfReading P →
      SecondEfficientCausesCauseOnlyAsCausedReading E C →
      NoInfinitePerSeEfficientCauseSeriesReading C →
      FirstEfficientCauseCannotBeLackingReading E := by
  sorry

/-- The premise that a cause is prior to its effect is needed: a single self-causing being, with no priority relation, satisfies every other premise and is caused by itself, so nothing is a first efficient cause. -/
theorem secundaViaNeedsCausePrior :
    ¬ ∀ (Being Respect : Type)
      (E : Being → Being → Respect → Prop) (P C : Being → Being → Prop),
      OrderOfEfficientCausesFoundReading E →
      NothingPriorToItselfReading P →
      SecondEfficientCausesCauseOnlyAsCausedReading E C →
      NoInfinitePerSeEfficientCauseSeriesReading C →
      FirstEfficientCauseCannotBeLackingReading E := by
  sorry

/-- The premise that nothing is prior to itself is needed: a single self-causing being that is prior to itself satisfies every other premise and is caused by itself. -/
theorem secundaViaNeedsNothingPriorToItself :
    ¬ ∀ (Being Respect : Type)
      (E : Being → Being → Respect → Prop) (P C : Being → Being → Prop),
      OrderOfEfficientCausesFoundReading E →
      EfficientCauseIsPriorToEffectReading E P →
      SecondEfficientCausesCauseOnlyAsCausedReading E C →
      NoInfinitePerSeEfficientCauseSeriesReading C →
      FirstEfficientCauseCannotBeLackingReading E := by
  sorry

/-- The per se ordering premise is needed: an infinite series in which each n is caused by n + 1, none of whose links is per se (the per accidens series of ST I q.46 a.2 ad 7), satisfies every other premise and has no first efficient cause. -/
theorem secundaViaNeedsPerSeOrder :
    ¬ ∀ (Being Respect : Type)
      (E : Being → Being → Respect → Prop) (P C : Being → Being → Prop),
      OrderOfEfficientCausesFoundReading E →
      EfficientCauseIsPriorToEffectReading E P →
      NothingPriorToItselfReading P →
      NoInfinitePerSeEfficientCauseSeriesReading C →
      FirstEfficientCauseCannotBeLackingReading E := by
  sorry

/-- The no-regress premise is needed: an infinite per se series in which each n is caused, as a middle cause, by n + 1 satisfies every other premise and has no first efficient cause. -/
theorem secundaViaNeedsNoRegress :
    ¬ ∀ (Being Respect : Type)
      (E : Being → Being → Respect → Prop) (P C : Being → Being → Prop),
      OrderOfEfficientCausesFoundReading E →
      EfficientCauseIsPriorToEffectReading E P →
      NothingPriorToItselfReading P →
      SecondEfficientCausesCauseOnlyAsCausedReading E C →
      FirstEfficientCauseCannotBeLackingReading E := by
  sorry

/-- The premises are jointly satisfiable with a genuine per se link: 2 causes 1
as a first cause, and 1 causes 0 only as caused. -/
theorem premisesJointlySatisfiable :
    ∃ (E : Nat → Nat → Unit → Prop) (P C : Nat → Nat → Prop),
      OrderOfEfficientCausesFoundReading E ∧
      EfficientCauseIsPriorToEffectReading E P ∧
      NothingPriorToItselfReading P ∧
      SecondEfficientCausesCauseOnlyAsCausedReading E C ∧
      NoInfinitePerSeEfficientCauseSeriesReading C ∧
      (∃ y x, C y x) ∧ (∃ f, IsFirstEfficientCause E f) := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.SecundaVia
