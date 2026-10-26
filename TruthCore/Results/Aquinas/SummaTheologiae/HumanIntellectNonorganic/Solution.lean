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
  intro hOrgan
  obtain ⟨organ, hBody, hThrough⟩ := hOrgan
  obtain ⟨n, hNature, hHas⟩ := hBodies organ hBody
  have hCannot := hInterference organ n hThrough hBody hNature hHas
  exact hCannot hScope

/-- Without universal scope, a bodily instrument can satisfy the other two
premises. The omitted premise fails and an instrument is explicitly exhibited. -/
theorem scopeOmission :
    ∃ (m : Model Unit Unit) (through : Unit → Unit → Prop),
      (∃ organ, m.IsBody organ ∧ through () organ) ∧
      ¬ UniversalBodilyCognition m () ∧ BodilyDeterminacy m ∧
      OrganBodilyInterference m through () := by
  refine ⟨⟨(fun _ => True), (fun _ => True), (fun _ _ => True),
    (fun _ _ => False)⟩, (fun _ _ => True), ⟨(), trivial, trivial⟩, ?_, ?_, ?_⟩
  · exact fun h => h () trivial
  · exact fun _ _ => ⟨(), trivial, trivial⟩
  · exact fun _ _ _ _ _ _ h => h () trivial

/-- Without bodily determinacy, a bodily instrument and universal scope are
compatible with the organ-interference conditional. -/
theorem determinacyOmission :
    ∃ (m : Model Unit Unit) (through : Unit → Unit → Prop),
      (∃ organ, m.IsBody organ ∧ through () organ) ∧
      UniversalBodilyCognition m () ∧ ¬ BodilyDeterminacy m ∧
      OrganBodilyInterference m through () := by
  refine ⟨⟨(fun _ => True), (fun _ => True), (fun _ _ => False),
    (fun _ _ => True)⟩, (fun _ _ => True), ⟨(), trivial, trivial⟩, ?_, ?_, ?_⟩
  · exact fun _ _ => trivial
  · intro h
    obtain ⟨_, _, hHas⟩ := h () trivial
    exact hHas
  · exact fun _ _ _ _ _ hHas => hHas.elim

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
  let m : Model Bool Unit := ⟨(fun b => b = true), (fun _ => True),
    (fun b _ => b = true), (fun _ _ => True)⟩
  let through : Bool → Bool → Prop := fun _ b => b = true
  refine ⟨m, through, ?_, ?_, ?_, ?_, ⟨true, rfl, rfl⟩, ?_⟩
  · exact fun h => Bool.noConfusion h
  · exact fun _ _ hHas => Bool.noConfusion hHas
  · exact fun _ _ => trivial
  · exact fun _ hBody => ⟨(), trivial, hBody⟩
  · intro h
    exact h true () rfl rfl trivial rfl (fun _ _ => trivial)

end TruthCore.Results.Aquinas.SummaTheologiae.HumanIntellectNonorganic
