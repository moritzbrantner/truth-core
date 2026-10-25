import TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
namespace TruthCore.Results.Greek.Plato.Parmenides.WholePartObjection
open TruthCore.Greek.Plato.Forms
open TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
universe u v w
variable {E : Type u} {Q : Type v} {A : Type w}

theorem wholePartObjection (s : Vocabulary E Q) (m : Mereology E)
    (hmany : PropertyInstances s) (hone : OneOverMany s)
    (hexclusive : WholeExclusive m) (hindivisible : IndivisibleForms s m) :
    NoSpatialDilemma s m := by
  obtain ⟨x, y, q, hxy, hx, hy, hq, hxq, hyq⟩ := hmany
  obtain ⟨f, hf, hcommon⟩ := hone q hq
  intro hdilemma
  have hwx : m.WholeAt f x := by
    cases hdilemma x f (hcommon x hx hxq) with
    | inl h => exact h
    | inr h =>
      obtain ⟨p, hp, _⟩ := h
      exact False.elim (hindivisible q hq f hf p hp)
  have hwy : m.WholeAt f y := by
    cases hdilemma y f (hcommon y hy hyq) with
    | inl h => exact h
    | inr h =>
      obtain ⟨p, hp, _⟩ := h
      exact False.elim (hindivisible q hq f hf p hp)
  exact hxy (hexclusive f x y hwx hwy)

end TruthCore.Results.Greek.Plato.Parmenides.WholePartObjection
