import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionUniqueMaximum
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (AtMostOneMaximeEns)

/-- On the reading by attribution, there is at most one maximum in being. If
one thing is more a being than another exactly as it approaches a primary more
nearly, and nothing else reaches the primary (q.3 a.5 ad 2), every maximum in
being is the primary, so any two are the same. Neither the genus principle nor
*Metaphysics* II.1 is used, unlike `AtMostOneMaximeEns.atMostOneMaximeEns`. -/
theorem attributionOrderUniqueMaximum {Being Respect Degree : Type}
    [Preorder Degree]
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect)
    (near : Being → Degree) (p : Being)
    (hApproach : ApproachToPrimaryReading InAct MoreIn esse near p)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    AtMostOneMaximeEns InAct MoreIn esse := by
  intro m m' hm hm'
  -- INF-QUARTA-VIA-ATTRIBUTION-UNIQUE-MAXIMUM: both maxima are the primary
  rw [hApproach.eq_of_isMaximumIn hEM hm, hApproach.eq_of_isMaximumIn hEM hm']

/-- Strict primacy is needed. With all degrees tied (in `Unit`), "every other
thing falls short of the primary" weakens to "no other thing exceeds it"; then
both beings are maximal in being. This is the univocal picture of a homogeneous
scale with two tied top grades (`AtMostOneMaximeEns.TiedMaxima`). -/
theorem withoutStrictPrimacyNotUnique :
    ¬ ∀ (Being Respect Degree : Type) [Preorder Degree]
      (InAct : Being → Respect → Prop)
      (MoreIn : Respect → Being → Being → Prop) (esse : Respect)
      (near : Being → Degree) (p : Being),
      (InAct p esse ∧ (∀ x y, MoreIn esse x y ↔ near y < near x) ∧
        ∀ x, x ≠ p → near x ≤ near p) →
      TruthCore.Logic.ExcludedMiddle →
      AtMostOneMaximeEns InAct MoreIn esse := by
  intro h
  have hU := h Bool Unit Unit (fun _ _ => True) (fun _ _ _ => False) ()
    (fun _ => ()) true
    ⟨trivial, fun _ _ => ⟨False.elim, fun h => (lt_irrefl () h).elim⟩,
      fun _ _ => le_refl ()⟩
    (fun q => Classical.em q)
  exact Bool.noConfusion (hU true false ⟨trivial, fun _ h => h⟩ ⟨trivial, fun _ h => h⟩)
end TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionUniqueMaximum
