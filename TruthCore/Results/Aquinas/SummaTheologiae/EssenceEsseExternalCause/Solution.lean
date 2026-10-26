import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

namespace TruthCore.Results.Aquinas.SummaTheologiae.EssenceEsseExternalCause

open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

/-- q.3 a.4's first proof, as a conditional reconstruction: once causal
exhaustiveness and the no-efficient-self-cause restriction are admitted,
the external cause follows. Neither antecedent is proved here. This is an
explicitly scoped transcription, not a metaphysical discharge. -/
theorem distinctEsseExternalFromExhaustion (p : Profile B P R)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p) :
    DistinctEsseRequiresExternalCauseReading p := by
  intro x hDistinct
  rcases hExhaustive x hDistinct with hEssential | hExternal
  · exact False.elim ((hNoSelfCause x hDistinct) hEssential)
  · exact hExternal

/-- The three models are *nonvacuous*: the subject exists with distinct
essence/esse in every case, and any represented efficient cause has actual
relata. The two omissions are separately satisfiable; so proving only one
of the source's principles cannot establish its external-cause conclusion. -/
theorem premiseOmissionsAndControl : PremiseOmissionsAndControl := by
  -- Explicit proof terms avoid propositional extensionality from simp.
  constructor
  · let p : Profile Bool Bool Unit := {
      InAct := fun x _ => x = false
      CausesIn := fun _ _ _ => False
      essenceOf := fun _ => false
      esseOf := fun _ => true
      essentialPrinciplesAloneSufficeForEsse := fun _ => False
      esse := () }
    have hd : DistinctEsseAt p false := ⟨rfl, Bool.noConfusion⟩
    have hn : ∀ x, ¬HasExternalEsseCause p x := fun _ ⟨_, _, _, h⟩ => h
    exact ⟨p, (fun _ _ h => h.elim), hd, (fun _ _ _ h => h),
      (fun h => h), hn false, (fun _ _ h => h),
      (fun h => (h false hd).elim (fun h => h) (hn false)),
      (fun h => hn false (h false hd))⟩
  constructor
  · let p : Profile Bool Bool Unit := {
      InAct := fun x _ => x = false
      CausesIn := fun _ _ _ => False
      essenceOf := fun _ => false
      esseOf := fun _ => true
      essentialPrinciplesAloneSufficeForEsse := fun x => x = false
      esse := () }
    have hd : DistinctEsseAt p false := ⟨rfl, Bool.noConfusion⟩
    have hn : ∀ x, ¬HasExternalEsseCause p x := fun _ ⟨_, _, _, h⟩ => h
    exact ⟨p, (fun _ _ h => h.elim), hd, rfl, hn false,
      (fun _ h => Or.inl h.1), (fun h => h false hd rfl),
      (fun h => hn false (h false hd))⟩
  · let p : Profile Bool Bool Unit := {
      InAct := fun _ _ => True
      CausesIn := fun y x _ => y = true ∧ x = false
      essenceOf := fun _ => false
      esseOf := Bool.not
      essentialPrinciplesAloneSufficeForEsse := fun _ => False
      esse := () }
    have he : HasExternalEsseCause p false :=
      ⟨true, Bool.noConfusion, True.intro, rfl, rfl⟩
    have hc : DistinctEsseRequiresExternalCauseReading p := by
      intro x h
      cases x with
      | false => exact he
      | true => exact False.elim (h.2 rfl)
    exact ⟨p, (fun _ _ _ => ⟨True.intro, True.intro⟩),
      ⟨True.intro, Bool.noConfusion⟩, he,
      (fun x h => Or.inr (hc x h)), (fun _ _ h => h), hc⟩

end TruthCore.Results.Aquinas.SummaTheologiae.EssenceEsseExternalCause
