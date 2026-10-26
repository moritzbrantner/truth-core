import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question75.Article2

namespace TruthCore.Results.Aquinas.SummaTheologiae.HumanIntellectIncorporeal
open TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect

/-- Q.75 a.2's first inference: a bodily intellect would have a bodily nature;
the open interference premise would then deny the universal capacity asserted
by the cognitive premise. Only consequence from these three premises is proved. -/
theorem intellectIsNotBody {Principle Nature : Type}
    (m : Model Principle Nature) (intellect : Principle)
    (hScope : UniversalBodilyCognition m intellect)
    (hBodies : BodilyDeterminacy m)
    (hInterference : NaturalBodilyInterference m intellect) :
    IntellectIsNotBody m intellect := by
  sorry

/-- Finite schema omission control: without universal cognitive scope, the
other two premises allow a body. The displayed subject is explicitly bodily;
the omitted premise explicitly fails. Not a metaphysically possible-world claim. -/
theorem scopeOmission :
    ∃ m : Model Unit Unit, m.IsBody () ∧
      ¬ UniversalBodilyCognition m () ∧ BodilyDeterminacy m ∧
      NaturalBodilyInterference m () := by
  sorry

/-- Finite schema omission control for bodily determinacy, with an explicitly
bodily subject and explicit failure of the omitted premise. -/
theorem determinacyOmission :
    ∃ m : Model Unit Unit, m.IsBody () ∧
      UniversalBodilyCognition m () ∧ ¬ BodilyDeterminacy m ∧
      NaturalBodilyInterference m () := by
  sorry

/-- Finite schema omission control for interference. A bodily subject with
its own nature can understand every selected nature in this stipulated model.
This challenges entailment from the other two premises; it is not a complete
physicalist theory or an explanation of semantic content. -/
theorem interferenceOmission :
    ∃ m : Model Unit Unit, m.IsBody () ∧
      UniversalBodilyCognition m () ∧ BodilyDeterminacy m ∧
      ¬ NaturalBodilyInterference m () := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.HumanIntellectIncorporeal
