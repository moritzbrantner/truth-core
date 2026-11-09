module
public import TruthCore.Alternatives.PhysicalSpecification

@[expose] public section
namespace TruthCore.Results.Alternatives.PhysicalSpecification
open FirstOrder TruthCore.Alternatives.PhysicalSpecification

theorem naming : namingControl := by
  refine ⟨markedFormula, ?_⟩
  intro y
  rfl

theorem partFree : partFreeControl := ⟨naming, fun h => h⟩

theorem notUniform : noUniformControl := by
  intro h
  obtain ⟨_, p, hp⟩ := h
  let original : Interpretation controlVocabulary Empty Bool := ⟨controlOriginal, Empty.elim⟩
  let transported : Interpretation controlVocabulary Empty Bool := ⟨controlTransported, Empty.elim⟩
  have ht := (hp original trivial true).mpr rfl
  have same := @Language.StrongHomClass.realize_formula
    (ordinaryLanguage controlVocabulary) Bool Bool controlOriginal controlTransported
    _ _ _ _ (@Equiv.inducedStructureEquiv _ Bool Bool controlOriginal swap) p
    (Sum.elim (fun _ => true) (fun a => Empty.elim a.val))
  have eqv : (fun a : Unit ⊕ {a : Empty // False} =>
      swap (Sum.elim (fun _ => true) (fun a => Empty.elim a.val) a)) =
      Sum.elim (fun _ => false) (fun a => Empty.elim a.val) := by
    funext a
    cases a with
    | inl u => rfl
    | inr a => exact Empty.elim a.val
  have hf := same.mpr ht
  change @Language.Formula.Realize _ Bool controlTransported _ p
    (fun a => swap (Sum.elim (fun _ => true) (fun a => Empty.elim a.val) a)) at hf
  rw [eqv] at hf
  have bad := (hp transported trivial false).mp hf
  cases bad

theorem permittedParameter : permittedControl := by
  refine ⟨⟨⟨controlOriginal, fun _ => true⟩, trivial⟩,
    (Language.Term.var (Sum.inl ())).equal (Language.Term.var (Sum.inr ⟨(), trivial⟩)), ?_⟩
  intro i _ x
  rfl

theorem forbiddenParameter : forbiddenControl := by
  rintro ⟨p, _⟩
  exact p.property

end TruthCore.Results.Alternatives.PhysicalSpecification
