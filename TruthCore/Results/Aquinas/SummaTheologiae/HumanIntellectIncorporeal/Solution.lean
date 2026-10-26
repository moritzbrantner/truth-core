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
  intro hBody
  obtain ⟨n, hNature, hHas⟩ := hBodies intellect hBody
  have hCannot := hInterference n hNature hHas
  exact hCannot hScope

/-- Finite schema omission control: without universal cognitive scope, the
other two premises allow a body. The displayed subject is explicitly bodily;
the omitted premise explicitly fails. Not a metaphysically possible-world claim. -/
theorem scopeOmission :
    ∃ m : Model Unit Unit, m.IsBody () ∧
      ¬ UniversalBodilyCognition m () ∧ BodilyDeterminacy m ∧
      NaturalBodilyInterference m () := by
  refine ⟨⟨(fun _ => True), (fun _ => True), (fun _ _ => True),
    (fun _ _ => False)⟩, trivial, ?_, ?_, ?_⟩
  · exact fun h => h () trivial
  · exact fun _ _ => ⟨(), trivial, trivial⟩
  · exact fun _ _ _ h => h () trivial

/-- Finite schema omission control for bodily determinacy, with an explicitly
bodily subject and explicit failure of the omitted premise. -/
theorem determinacyOmission :
    ∃ m : Model Unit Unit, m.IsBody () ∧
      UniversalBodilyCognition m () ∧ ¬ BodilyDeterminacy m ∧
      NaturalBodilyInterference m () := by
  refine ⟨⟨(fun _ => True), (fun _ => True), (fun _ _ => False),
    (fun _ _ => True)⟩, trivial, ?_, ?_, ?_⟩
  · exact fun _ _ => trivial
  · intro h
    obtain ⟨_, _, hHas⟩ := h () trivial
    exact hHas
  · exact fun _ _ h => h.elim

/-- Finite schema omission control for interference. A bodily subject with
its own nature can understand every selected nature in this stipulated model.
This challenges entailment from the other two premises; it is not a complete
physicalist theory or an explanation of semantic content. -/
theorem interferenceOmission :
    ∃ m : Model Unit Unit, m.IsBody () ∧
      UniversalBodilyCognition m () ∧ BodilyDeterminacy m ∧
      ¬ NaturalBodilyInterference m () := by
  refine ⟨⟨(fun _ => True), (fun _ => True), (fun _ _ => True),
    (fun _ _ => True)⟩, trivial, ?_, ?_, ?_⟩
  · exact fun _ _ => trivial
  · exact fun _ _ => ⟨(), trivial, trivial⟩
  · intro h
    exact h () trivial trivial (fun _ _ => trivial)

end TruthCore.Results.Aquinas.SummaTheologiae.HumanIntellectIncorporeal
