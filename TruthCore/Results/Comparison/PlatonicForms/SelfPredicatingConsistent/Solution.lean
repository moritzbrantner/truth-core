import TruthCore.Comparison.PlatonicForms
namespace TruthCore.Results.Comparison.PlatonicForms.SelfPredicatingConsistent
open TruthCore.Greek.Plato.Forms
open TruthCore.Comparison.PlatonicForms

-- Give Fin numerals constructive nonzero evidence directly; the elaborator's
-- automatic arithmetic proof may otherwise introduce propositional extensionality.
private instance : NeZero 3 where
  out h := Nat.noConfusion h

/-- 0 is the Form; 1 and 2 are particulars. The sole quality is admitted.
These extensions interpret predicates rather than asserting their truth of reality. -/
private def finiteModel : Vocabulary (Fin 3) Unit where
  Particular x := x ≠ 0
  Admitted _ := True
  FormOf f _ := f = 0
  Exemplifies _ _ := True
  Participates x f := x ≠ 0 ∧ f = 0
  Independent f := f = 0
  Intelligible f := f = 0
  Unchanging f := f = 0
  Explains f x _ := f = 0 ∧ x ≠ 0
  ModelFor f x := f = 0 ∧ x ≠ 0
  Imitates x f := x ≠ 0 ∧ f = 0
  Like _ _ := False
  Essentially _ _ := False

/-- Formal compatibility of precisely the scoped ten-commitment synthesis. -/
theorem selfPredicatingConsistent : SelfPredicatingConsistent := by
  refine ⟨finiteModel, ?_⟩
  constructor
  · refine ⟨1, 2, (), ?_, ?_, ?_, True.intro, True.intro, True.intro⟩
    · intro h
      exact Nat.noConfusion (Nat.succ.inj (congrArg Fin.val h))
    · intro h
      exact Nat.noConfusion (congrArg Fin.val h)
    · intro h
      exact Nat.noConfusion (congrArg Fin.val h)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro q _
      exact ⟨0, rfl, fun x hx _ => ⟨hx, rfl⟩⟩
    · intro q _ f g hf hg
      exact hf.trans hg.symm
    · intro q _ f x _ _ _
      exact True.intro
    · intro q _ f x hf hx _ hEq
      exact hx (hEq.symm.trans hf)
    · intro q _ f hf
      exact hf
    · intro q _ x hx _
      exact ⟨0, rfl, ⟨hx, rfl⟩, rfl, hx⟩
    · intro q _ x hx _
      exact ⟨0, rfl, ⟨rfl, hx⟩, hx, rfl⟩
    · intro q _ f hf
      exact ⟨hf, hf⟩
    · intro q _ f _
      exact True.intro
end TruthCore.Results.Comparison.PlatonicForms.SelfPredicatingConsistent
