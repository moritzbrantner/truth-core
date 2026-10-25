import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question11.Article3Nature
namespace TruthCore.Results.Case.Catholicism.Q11NatureUniqueness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism

theorem godIsOneFromNature {Being : Type} {Principle : Type}
    (IsGod : Being → Prop) (suppositumOf essenceOf : Being → Principle) (deity : Principle)
    (hIndividual : IndividuatingBasisIsIncommunicableReading suppositumOf)
    (hNature : GodSuppositumIsNatureReading IsGod suppositumOf essenceOf)
    (hCommon : ProperGodInstancesHaveCommonNatureReading IsGod essenceOf deity) :
    GodIsOne IsGod := by
  intro g hg other hOther
  apply hIndividual other g
  exact (hNature other hOther).trans ((hCommon other hOther).trans
    ((hCommon g hg).symm.trans (hNature g hg).symm))

theorem withoutIndividuation : UniquenessFailsWithoutIndividuation := by
  refine ⟨(fun _ => false), (fun _ => false), false, ?_, ?_, ?_⟩
  · intro _ _; rfl
  · intro _ _; rfl
  · intro h
    exact Bool.noConfusion (h false True.intro true True.intro)

theorem withoutNatureIdentity : UniquenessFailsWithoutNatureIdentity := by
  refine ⟨(fun x => x), (fun _ => false), false, ?_, ?_, ?_⟩
  · intro _ _ h; exact h
  · intro _ _; rfl
  · intro h
    exact Bool.noConfusion (h false True.intro true True.intro)

theorem withoutCommonNature : UniquenessFailsWithoutCommonNature := by
  refine ⟨(fun x => x), (fun x => x), ?_, ?_, ?_⟩
  · intro _ _ h; exact h
  · intro _ _; rfl
  · intro h
    exact Bool.noConfusion (h false True.intro true True.intro)

/-- Conditional recovery for premise comparison only: a named maximum and
God-uniqueness together imply every God is maximal. Neither the witness nor
uniqueness is produced by a naming definition. No global corpus bridge is closed
by registering this auxiliary theorem. -/
theorem maximalityFromNamedMaximumAndUniqueness {Being : Type} {Respect : Type}
    (IsGod : Being → Prop) (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect) (m : Being)
    (hNamed : IsGod m) (hMax : IsMaximumIn InAct MoreIn esse m)
    (hOne : GodIsOne IsGod) : GodIsMaximalInBeing IsGod InAct MoreIn esse := by
  intro g hg
  exact (hOne m hNamed g hg).symm ▸ hMax
end TruthCore.Results.Case.Catholicism.Q11NatureUniqueness
