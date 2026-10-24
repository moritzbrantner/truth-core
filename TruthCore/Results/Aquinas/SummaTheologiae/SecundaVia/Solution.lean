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
  -- INF-AQUINAS-ST-I-Q2-A3-NOTHING-EFFICIENT-CAUSE-OF-ITSELF: it would be prior to itself
  have hNoSelf : NothingIsEfficientCauseOfItselfReading EfficientlyCausesIn :=
    fun x r hSelf => hIrrefl x (hPrior x x r hSelf)
  -- INF-AQUINAS-ST-I-Q2-A3-FIRST-EFFICIENT-CAUSE: reductio by well-founded induction
  intro hNoFirst
  have hNoEffect : ∀ x, (∃ c r, EfficientlyCausesIn c x r) → False := by
    intro x
    have hAcc := hRegress x
    induction hAcc with
    | intro x _ ih =>
      intro ⟨c, r, hCauses⟩
      -- the cause is another thing, since nothing causes itself
      have hDistinct : c ≠ x := by
        intro hEq
        subst hEq
        exact hNoSelf c r hCauses
      -- if the cause were caused by nothing, it would be a first efficient cause
      have hCaused : ¬ ¬ ∃ d r', EfficientlyCausesIn d c r' := by
        intro hUncaused
        exact hNoFirst ⟨c, ⟨x, r, hCauses⟩, fun d r' h => hUncaused ⟨d, r', h⟩⟩
      -- otherwise it is a middle cause, one step up a well-founded series
      exact hCaused fun hC =>
        ih c (hPerSe c x r hDistinct hCauses hC) hC
  obtain ⟨c, x, r, hCauses⟩ := hOrder
  exact hNoEffect x ⟨c, r, hCauses⟩

/-- The observation premise is needed: in a world where nothing efficiently causes anything, every other premise holds vacuously and there is no first efficient cause. -/
theorem secundaViaNeedsOrder :
    ¬ ∀ (Being Respect : Type)
      (E : Being → Being → Respect → Prop) (P C : Being → Being → Prop),
      EfficientCauseIsPriorToEffectReading E P →
      NothingPriorToItselfReading P →
      SecondEfficientCausesCauseOnlyAsCausedReading E C →
      NoInfinitePerSeEfficientCauseSeriesReading C →
      FirstEfficientCauseCannotBeLackingReading E := by
  intro h
  exact h Unit Unit (fun _ _ _ => False) (fun _ _ => False) (fun _ _ => False)
    (fun _ _ _ h => h) (fun _ h => h) (fun _ _ _ _ h => h.elim) (fun x => Acc.intro x (fun _ h => h.elim))
    (fun ⟨_, ⟨_, _, h⟩, _⟩ => h)

/-- The premise that a cause is prior to its effect is needed: a single self-causing being, with no priority relation, satisfies every other premise and is caused by itself, so nothing is a first efficient cause. -/
theorem secundaViaNeedsCausePrior :
    ¬ ∀ (Being Respect : Type)
      (E : Being → Being → Respect → Prop) (P C : Being → Being → Prop),
      OrderOfEfficientCausesFoundReading E →
      NothingPriorToItselfReading P →
      SecondEfficientCausesCauseOnlyAsCausedReading E C →
      NoInfinitePerSeEfficientCauseSeriesReading C →
      FirstEfficientCauseCannotBeLackingReading E := by
  intro h
  exact h Unit Unit (fun _ _ _ => True) (fun _ _ => False) (fun _ _ => False)
    ⟨(), (), (), trivial⟩ (fun _ h => h) (fun _ _ _ hne _ _ => absurd rfl hne)
    (fun x => Acc.intro x (fun _ h => h.elim))
    (fun ⟨_, _, hNone⟩ => hNone () () trivial)

/-- The premise that nothing is prior to itself is needed: a single self-causing being that is prior to itself satisfies every other premise and is caused by itself. -/
theorem secundaViaNeedsNothingPriorToItself :
    ¬ ∀ (Being Respect : Type)
      (E : Being → Being → Respect → Prop) (P C : Being → Being → Prop),
      OrderOfEfficientCausesFoundReading E →
      EfficientCauseIsPriorToEffectReading E P →
      SecondEfficientCausesCauseOnlyAsCausedReading E C →
      NoInfinitePerSeEfficientCauseSeriesReading C →
      FirstEfficientCauseCannotBeLackingReading E := by
  intro h
  exact h Unit Unit (fun _ _ _ => True) (fun _ _ => True) (fun _ _ => False)
    ⟨(), (), (), trivial⟩ (fun _ _ _ _ => trivial) (fun _ _ _ hne _ _ => absurd rfl hne)
    (fun x => Acc.intro x (fun _ h => h.elim))
    (fun ⟨_, _, hNone⟩ => hNone () () trivial)

/-- The per se ordering premise is needed: an infinite series in which each n is caused by n + 1, none of whose links is per se (the per accidens series of ST I q.46 a.2 ad 7), satisfies every other premise and has no first efficient cause. -/
theorem secundaViaNeedsPerSeOrder :
    ¬ ∀ (Being Respect : Type)
      (E : Being → Being → Respect → Prop) (P C : Being → Being → Prop),
      OrderOfEfficientCausesFoundReading E →
      EfficientCauseIsPriorToEffectReading E P →
      NothingPriorToItselfReading P →
      NoInfinitePerSeEfficientCauseSeriesReading C →
      FirstEfficientCauseCannotBeLackingReading E := by
  intro h
  exact h Nat Unit (fun y x _ => y = x + 1) (fun y x => x < y) (fun _ _ => False)
    ⟨1, 0, (), rfl⟩ (fun c x _ hc => hc ▸ Nat.lt_succ_self x) (fun x hx => Nat.lt_irrefl x hx)
    (fun x => Acc.intro x (fun _ h => h.elim))
    (fun ⟨f, _, hNone⟩ => hNone (f + 1) () rfl)

/-- The no-regress premise is needed: an infinite per se series in which each n is caused, as a middle cause, by n + 1 satisfies every other premise and has no first efficient cause. -/
theorem secundaViaNeedsNoRegress :
    ¬ ∀ (Being Respect : Type)
      (E : Being → Being → Respect → Prop) (P C : Being → Being → Prop),
      OrderOfEfficientCausesFoundReading E →
      EfficientCauseIsPriorToEffectReading E P →
      NothingPriorToItselfReading P →
      SecondEfficientCausesCauseOnlyAsCausedReading E C →
      FirstEfficientCauseCannotBeLackingReading E := by
  intro h
  exact h Nat Unit (fun y x _ => y = x + 1) (fun y x => x < y) (fun y x => y = x + 1)
    ⟨1, 0, (), rfl⟩ (fun c x _ hc => hc ▸ Nat.lt_succ_self x) (fun x hx => Nat.lt_irrefl x hx)
    (fun _ _ _ _ hc _ => hc)
    (fun ⟨f, _, hNone⟩ => hNone (f + 1) () rfl)

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
  have hAcc1 : Acc (fun (y x : Nat) => x < 1 ∧ y = x + 1) 1 :=
    Acc.intro 1 (fun _ h => absurd h.1 (Nat.lt_irrefl 1))
  refine ⟨fun y x _ => x < 2 ∧ y = x + 1, fun y x => x < y, fun y x => x < 1 ∧ y = x + 1,
    ⟨1, 0, (), Nat.zero_lt_two, rfl⟩, ?_, fun x hx => Nat.lt_irrefl x hx, ?_, ?_,
    ⟨1, 0, Nat.zero_lt_one, rfl⟩,
    ⟨2, ⟨1, (), Nat.one_lt_two, rfl⟩, fun _ _ h => Nat.lt_irrefl 2 h.1⟩⟩
  · intro c x _ h
    obtain ⟨_, hc⟩ := h
    subst hc
    exact Nat.lt_succ_self x
  · intro c x _ _ h hCaused
    obtain ⟨_, hc⟩ := h
    obtain ⟨d, _, hd1, _⟩ := hCaused
    subst hc
    exact ⟨Nat.lt_of_succ_lt_succ hd1, rfl⟩
  · intro n
    match n with
    | 0 => exact Acc.intro 0 (fun y h => by obtain ⟨_, hy⟩ := h; subst hy; exact hAcc1)
    | 1 => exact hAcc1
    | k + 2 =>
      exact Acc.intro (k + 2) (fun _ h =>
        absurd (Nat.le_of_lt_succ h.1) (Nat.not_succ_le_zero (k + 1)))

end TruthCore.Results.Aquinas.SummaTheologiae.SecundaVia
