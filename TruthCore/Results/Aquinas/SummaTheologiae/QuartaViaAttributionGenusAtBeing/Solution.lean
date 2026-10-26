import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionGenusAtBeing
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- On the reading by attribution, the genus principle holds at being. If one
thing is more a being than another exactly as it approaches a primary more
nearly, and nothing else reaches the primary (q.3 a.5 ad 2), then whatever is
maximal in being is the primary; if every other being is ordered to the primary
as to its cause (q.13 a.5), the maximum causes the being of every other being.
Only the instance at being is derived: the genus principle for other
perfections is not touched. -/
theorem attributionOrderGenusPrincipleAtBeing {Being Respect Degree : Type}
    [Preorder Degree]
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (near : Being → Degree) (p : Being)
    (hApproach : ApproachToPrimaryReading InAct MoreIn esse near p)
    (hOrdered : OrderedToPrimaryAsCauseReading InAct CausesIn esse p)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse := by
  intro m hm
  -- INF-QUARTA-VIA-ATTRIBUTION-GENUS-PRINCIPLE-AT-BEING: the maximum is the primary,
  have hPrimary : m = p := hApproach.eq_of_isMaximumIn hEM hm
  -- and the primary causes the being of every other being (q.13 a.5)
  rw [hPrimary]
  exact hOrdered

/-! ## Omission countermodels

Two beings, `true` and `false`, both having being (one respect, `Unit`). -/

/-- The causal order of q.13 a.5 is needed. `true` approaches itself more
nearly than `false` (degrees in `Bool`, `false < true`), so the order by
approach holds with primary `true`; but nothing causes anything, so the maximum
`true` does not cause the being of `false`. -/
theorem withoutCausalOrderFails :
    ¬ ∀ (Being Respect Degree : Type) [Preorder Degree]
      (InAct : Being → Respect → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
      (near : Being → Degree) (p : Being),
      ApproachToPrimaryReading InAct MoreIn esse near p →
      TruthCore.Logic.ExcludedMiddle →
      MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse := by
  intro h
  have hEM : TruthCore.Logic.ExcludedMiddle := fun q => Classical.em q
  have hApproach : ApproachToPrimaryReading (fun (_ : Bool) (_ : Unit) => True)
      (fun _ x y => y < x) () id true :=
    ⟨trivial, fun _ _ => Iff.rfl, fun x hx => by cases x <;> simp_all⟩
  have hc := h Bool Unit Bool (fun _ _ => True) (fun _ x y => y < x)
    (fun _ _ _ => False) () id true hApproach hEM true hApproach.isMaximumIn_primary
    false (by decide) trivial
  exact hc

/-- Strict primacy is needed. If the other being may be tied with the primary
(all degrees equal, in `Unit`), the clause "every other thing falls short of the
primary" weakens to "no other thing exceeds it". The primary `true` causes the
being of `false`, as q.13 a.5 says; but `false` is maximal too, and causes
nothing. -/
theorem withoutStrictPrimacyFails :
    ¬ ∀ (Being Respect Degree : Type) [Preorder Degree]
      (InAct : Being → Respect → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
      (near : Being → Degree) (p : Being),
      (InAct p esse ∧ (∀ x y, MoreIn esse x y ↔ near y < near x) ∧
        ∀ x, x ≠ p → near x ≤ near p) →
      OrderedToPrimaryAsCauseReading InAct CausesIn esse p →
      TruthCore.Logic.ExcludedMiddle →
      MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse := by
  intro h
  have hEM : TruthCore.Logic.ExcludedMiddle := fun q => Classical.em q
  have hc := h Bool Unit Unit (fun _ _ => True) (fun _ _ _ => False)
    (fun c x _ => c = true ∧ x ≠ true) () (fun _ => ()) true
    ⟨trivial, fun _ _ => ⟨False.elim, fun h => (lt_irrefl () h).elim⟩,
      fun _ _ => le_refl ()⟩
    (fun _ hx _ => ⟨rfl, hx⟩) hEM false ⟨trivial, fun _ h => h⟩ true (by decide) trivial
  exact Bool.noConfusion hc.1
end TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaAttributionGenusAtBeing
