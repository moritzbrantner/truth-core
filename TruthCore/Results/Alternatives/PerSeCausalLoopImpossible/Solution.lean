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
  -- Each per se link is a step of simple priority.
  have hStep : ∀ c x, CausesAsCaused c x → PriorSimply c x := by
    intro c x hLink
    obtain ⟨r, hCauses⟩ := hMiddle c x hLink
    exact hPrior c x r hCauses
  -- Every finite chain of per se links is a step of simple priority.
  have hChain : ∀ a b, Relation.TransGen CausesAsCaused a b → PriorSimply a b := by
    intro a b hPath
    induction hPath with
    | single hLink => exact hStep _ _ hLink
    | tail _ hLink ih => exact hTrans _ _ _ ih (hStep _ _ hLink)
  -- A being on a loop would be prior to itself.
  intro ⟨x, hLoop⟩
  exact hNotSelfPrior x (hChain x x hLoop)

/-- An exercise's actual bearer and the exercise remain different relata.
If its bearer must already exist to exercise it, and the exercise is prior to
the existence it produces, self-origination would create a two-step cycle in
strict existential priority. No temporal order or global well-foundedness is
assumed. These are OPEN metaphysical priority bridges, not stipulative facts
about every coherent causal loop or self-explanatory necessary essence. -/
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
  intro a ha hCreates
  exact hNoSelfPrior (.inl (Bearer a))
    (hTrans (.inl (Bearer a)) (.inr a) (.inl (Bearer a))
      (hBearerPrior a ha) (hProductPrior a (Bearer a) ha hCreates))

/-- A local two-cycle is consistent with irreflexivity alone. In this model,
let the single act occur and actualize its bearer: both priority interfaces
hold, but transitivity is false. This is a semantic omission control, not a
metaphysically productive self-cause. -/
theorem existentialSelfActualizationNeedsTransitivity :
    ∃ Prior : Sum Unit Unit → Sum Unit Unit → Prop,
      NothingPriorToItselfReading Prior ∧
      Prior (.inl ()) (.inr ()) ∧ Prior (.inr ()) (.inl ()) := by
  refine ⟨fun x y => x ≠ y, ?_, ?_, ?_⟩
  · intro x h
    exact h rfl
  · decide
  · decide

/-- Without irreflexivity, universal priority is transitive and admits the
two directions required by self-origination. -/
theorem existentialSelfActualizationNeedsIrreflexivity :
    ∃ Prior : Sum Unit Unit → Sum Unit Unit → Prop,
      SimplePriorityTransitiveReading Prior ∧
      Prior (.inl ()) (.inr ()) ∧ Prior (.inr ()) (.inl ()) := by
  exact ⟨fun _ _ => True, (fun _ _ _ _ _ => True.intro), True.intro, True.intro⟩

/-- Concrete finite external-actualization model: the bearer `true` has rank
zero, the occurring act has rank one, and its distinct product `false` has
rank two. Thus the self-actualization theorem does not prohibit all productive
acts or supply an existence proof for a particular external actualizer. -/
theorem otherBearerCanActualizeExistence :
    ∃ (Occurs : Unit → Prop) (Bearer : Unit → Bool)
        (ActualizesExistence : Unit → Bool → Prop)
        (Prior : Sum Bool Unit → Sum Bool Unit → Prop),
      (∀ a, Occurs a → Prior (.inl (Bearer a)) (.inr a)) ∧
      (∀ a x, Occurs a → ActualizesExistence a x → Prior (.inr a) (.inl x)) ∧
      NothingPriorToItselfReading Prior ∧
      SimplePriorityTransitiveReading Prior ∧
      Occurs () ∧ ActualizesExistence () false := by
  let rank : Sum Bool Unit → Nat
    | .inl true => 0
    | .inr () => 1
    | .inl false => 2
  refine ⟨(fun _ => True), (fun _ => true),
    (fun _ x => x = false), (fun x y => rank x < rank y),
    ?_, ?_, ?_, ?_, True.intro, rfl⟩
  · intro a _
    cases a
    decide
  · intro a x _ hProduct
    cases a
    cases x with
    | false => decide
    | true => cases hProduct
  · intro x hSelf
    exact Nat.lt_irrefl (rank x) hSelf
  · intro x y z hxy hyz
    exact Nat.lt_trans hxy hyz

/-- Transitivity is needed: two beings that cause each other per se, each
simply prior to the other but neither to itself, satisfy the other premises. -/
theorem needsTransitivity :
    ¬ ∀ (Being Respect : Type) (EfficientlyCausesIn : Being → Being → Respect → Prop)
        (CausesAsCaused PriorSimply : Being → Being → Prop),
      MiddleCauseEfficientlyCausesReading EfficientlyCausesIn CausesAsCaused →
      EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply →
      NothingPriorToItselfReading PriorSimply →
        NoPerSeCausalLoop CausesAsCaused := by
  intro h
  apply h Bool Unit (fun c x _ => c ≠ x) (fun c x => c ≠ x) (fun c x => c ≠ x)
    (fun _ _ hLink => ⟨(), hLink⟩) (fun _ _ _ hCauses => hCauses)
    (fun _ hSelf => hSelf rfl)
  exact ⟨true, Relation.TransGen.tail
    (Relation.TransGen.single (show true ≠ false by decide)) (show false ≠ true by decide)⟩

/-- Irreflexivity of priority is needed: a single self-prior being on a
self-loop satisfies the other premises. -/
theorem needsNothingPriorToItself :
    ¬ ∀ (Being Respect : Type) (EfficientlyCausesIn : Being → Being → Respect → Prop)
        (CausesAsCaused PriorSimply : Being → Being → Prop),
      MiddleCauseEfficientlyCausesReading EfficientlyCausesIn CausesAsCaused →
      EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply →
      SimplePriorityTransitiveReading PriorSimply →
        NoPerSeCausalLoop CausesAsCaused := by
  intro h
  exact h Unit Unit (fun _ _ _ => True) (fun _ _ => True) (fun _ _ => True)
    (fun _ _ _ => ⟨(), trivial⟩) (fun _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial)
    ⟨(), Relation.TransGen.single trivial⟩

/-- Priority of cause over effect is needed: a self-causing loop with no
priority at all satisfies the other premises. -/
theorem needsCausePriorToEffect :
    ¬ ∀ (Being Respect : Type) (EfficientlyCausesIn : Being → Being → Respect → Prop)
        (CausesAsCaused PriorSimply : Being → Being → Prop),
      MiddleCauseEfficientlyCausesReading EfficientlyCausesIn CausesAsCaused →
      NothingPriorToItselfReading PriorSimply →
      SimplePriorityTransitiveReading PriorSimply →
        NoPerSeCausalLoop CausesAsCaused := by
  intro h
  exact h Unit Unit (fun _ _ _ => True) (fun _ _ => True) (fun _ _ => False)
    (fun _ _ _ => ⟨(), trivial⟩) (fun _ hSelf => hSelf) (fun _ _ _ hPrior _ => hPrior)
    ⟨(), Relation.TransGen.single trivial⟩

/-- The middle-cause premise is needed: a per se loop whose links are no
efficient causings escapes the priority premises. -/
theorem needsMiddleCause :
    ¬ ∀ (Being Respect : Type) (EfficientlyCausesIn : Being → Being → Respect → Prop)
        (CausesAsCaused PriorSimply : Being → Being → Prop),
      EfficientCauseIsPriorToEffectReading EfficientlyCausesIn PriorSimply →
      NothingPriorToItselfReading PriorSimply →
      SimplePriorityTransitiveReading PriorSimply →
        NoPerSeCausalLoop CausesAsCaused := by
  intro h
  exact h Unit Unit (fun _ _ _ => False) (fun _ _ => True) (fun _ _ => False)
    (fun _ _ _ hCauses => hCauses.elim) (fun _ hSelf => hSelf)
    (fun _ _ _ hPrior _ => hPrior) ⟨(), Relation.TransGen.single trivial⟩

end TruthCore.Results.Alternatives.PerSeCausalLoopImpossible
