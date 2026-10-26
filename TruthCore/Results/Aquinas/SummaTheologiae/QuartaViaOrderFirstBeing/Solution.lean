import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaOrderFirstBeing
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Countermodel: neither order reading makes the maximum in being the first
being. Two beings on Mathlib's order of `Bool` (`false < true`), which is at
once a homogeneous scale and an order by approach to the primary `true`. Each
being causes the other's being and is simply prior to it. The causal order to
the primary, the broad genus principle and `SimplyPriorIsCauseOfBeing` hold; but
`false` is simply prior to the maximum `true`. What fails is *Metaphysics* II.1
at the primary as effect: `false` causes the primary's being without being more
a being. -/
theorem orderReadingsDoNotYieldFirstBeing : OrderReadingsDoNotYieldFirstBeing := by
  -- INF-QUARTA-VIA-ORDER-READINGS-DO-NOT-YIELD-FIRST-BEING
  intro h
  have hApproach : ApproachToPrimaryReading (fun (_ : Bool) (_ : Unit) => True)
      (fun _ x y => y < x) () id true :=
    ⟨trivial, fun _ _ => Iff.rfl, fun x hx => by
      cases x with
      | false => decide
      | true => exact absurd rfl hx⟩
  have hOrdered : OrderedToPrimaryAsCauseReading (fun (_ : Bool) (_ : Unit) => True)
      (fun c x _ => c ≠ x) () true := fun _ hx _ => fun h => hx h.symm
  have hFirst := h Bool Unit Bool (fun _ _ => True) (fun _ x y => y < x)
    (fun c x _ => c ≠ x) (fun c x => c ≠ x) () id true
    -- one homogeneous scale,
    ⟨fun _ => trivial, fun _ _ => Iff.rfl⟩
    -- an order by approach to `true`,
    hApproach
    -- `true` causes the being of the other,
    hOrdered
    -- the broad genus principle: every maximum is `true`, which causes all,
    (fun r m hm => by
      cases m
      · exact absurd (show false < true by decide) (hm.2 true)
      · exact hOrdered)
    -- what is simply prior to a thing causes its being,
    (fun _ _ hp => hp)
  -- but `false` is simply prior to the maximum `true`.
  exact Bool.noConfusion (hFirst true hApproach.isMaximumIn_primary false (by decide))
end TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaOrderFirstBeing
