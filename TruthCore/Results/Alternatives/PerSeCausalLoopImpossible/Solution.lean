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
