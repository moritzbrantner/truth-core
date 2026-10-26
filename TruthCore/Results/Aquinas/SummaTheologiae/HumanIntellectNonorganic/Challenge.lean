import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question75.OrganOperation

namespace TruthCore.Results.Aquinas.SummaTheologiae.HumanIntellectNonorganic
open TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect

/-- The conditional organ inference of q.75 a.2. All three philosophical
premises remain open; no non-organic exercise is inferred from non-bodyhood. -/
theorem intellectUsesNoBodilyOrgan {Principle Nature : Type}
    (m : Model Principle Nature) (through : Principle → Principle → Prop)
    (intellect : Principle)
    (hScope : UniversalBodilyCognition m intellect)
    (hBodies : BodilyDeterminacy m)
    (hInterference : OrganBodilyInterference m through intellect) :
    IntellectUsesNoBodilyOrgan m through intellect := by
  sorry

/-- Without universal scope, a bodily instrument can satisfy the other two
premises. The omitted premise fails and an instrument is explicitly exhibited. -/
theorem scopeOmission :
    ∃ (m : Model Unit Unit) (through : Unit → Unit → Prop),
      (∃ organ, m.IsBody organ ∧ through () organ) ∧
      ¬ UniversalBodilyCognition m () ∧ BodilyDeterminacy m ∧
      OrganBodilyInterference m through () := by
  sorry

/-- Without bodily determinacy, a bodily instrument and universal scope are
compatible with the organ-interference conditional. -/
theorem determinacyOmission :
    ∃ (m : Model Unit Unit) (through : Unit → Unit → Prop),
      (∃ organ, m.IsBody organ ∧ through () organ) ∧
      UniversalBodilyCognition m () ∧ ¬ BodilyDeterminacy m ∧
      OrganBodilyInterference m through () := by
  sorry

/-- The other organ premises, even with the old non-bodyhood conclusion and
old intellectual-constitution interference, permit a bodily instrument in a
finite formal-schema model. This is not a possible-world or physicalist
realization claim. Intellect and its exhibited organ are distinct Booleans. -/
theorem organInterferenceOmission :
    ∃ (m : Model Bool Unit) (through : Bool → Bool → Prop),
      IntellectIsNotBody m false ∧ NaturalBodilyInterference m false ∧
      UniversalBodilyCognition m false ∧ BodilyDeterminacy m ∧
      (∃ organ, m.IsBody organ ∧ through false organ) ∧
      ¬ OrganBodilyInterference m through false := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.HumanIntellectNonorganic
