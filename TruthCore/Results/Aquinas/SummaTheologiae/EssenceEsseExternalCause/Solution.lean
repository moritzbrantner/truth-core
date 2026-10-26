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
  -- Quantification over Bool is unfolded rather than assuming a general
  -- decidable instance for arbitrary universally quantified propositions.
  constructor
  · let p : Profile Bool Bool Unit := {
      InAct := fun x _ => x = false
      CausesIn := fun _ _ _ => False
      essenceOf := fun _ => false
      esseOf := fun _ => true
      essentialPrinciplesCauseEsse := fun _ => False
      esse := () }
    refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [p, Coherent, DistinctEsseAt, HasExternalEsseCause,
        DistinctEsseCauseDichotomyReading,
        EssentialPrinciplesCannotCauseDistinctEsseReading,
        DistinctEsseRequiresExternalCauseReading]
  constructor
  · let p : Profile Bool Bool Unit := {
      InAct := fun x _ => x = false
      CausesIn := fun _ _ _ => False
      essenceOf := fun _ => false
      esseOf := fun _ => true
      essentialPrinciplesCauseEsse := fun x => x = false
      esse := () }
    refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [p, Coherent, DistinctEsseAt, HasExternalEsseCause,
        DistinctEsseCauseDichotomyReading,
        EssentialPrinciplesCannotCauseDistinctEsseReading,
        DistinctEsseRequiresExternalCauseReading]
  · let p : Profile Bool Bool Unit := {
      InAct := fun _ _ => True
      CausesIn := fun y x _ => y = true ∧ x = false
      essenceOf := fun _ => false
      esseOf := Bool.not
      essentialPrinciplesCauseEsse := fun _ => False
      esse := () }
    refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [p, Coherent, DistinctEsseAt, HasExternalEsseCause,
        DistinctEsseCauseDichotomyReading,
        EssentialPrinciplesCannotCauseDistinctEsseReading,
        DistinctEsseRequiresExternalCauseReading]

end TruthCore.Results.Aquinas.SummaTheologiae.EssenceEsseExternalCause
