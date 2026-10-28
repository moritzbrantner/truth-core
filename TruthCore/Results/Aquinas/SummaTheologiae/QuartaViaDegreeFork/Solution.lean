import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaFork

namespace TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaDegreeFork
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)

/-- On the stipulated homogeneous scale, the existing grades premise supplies
population. Either a maximum is a unique strict top causing being in every
other being and receiving no distinct cause of being, or every being has a
strictly higher being. Excluded middle is explicit. The unrestricted causal
comparative is an open strengthening; no maximum existence or causal chain is
assumed or established unconditionally. -/
theorem coverage {Being Respect : Type} [Preorder Being]
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse bonum verum nobile : Respect)
    (hScale : HomogeneousScaleReading InAct MoreIn esse)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hCause : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    QuartaViaDegreeFork InAct MoreIn CausesIn esse := by
  obtain ⟨a, _, _⟩ := hGrades.1
  refine ⟨⟨a, hScale.1 a⟩, ?_⟩
  rcases hEM (∃ m, IsMaximumIn InAct MoreIn esse m) with hMax | hNoMax
  · obtain ⟨m, hm⟩ := hMax
    have hAllCause : ∀ x, x ≠ m → CausesIn m x esse :=
      fun x hx => hGenus m hm x hx (hScale.1 x)
    have hStrict : ∀ x, x ≠ m → MoreIn esse m x :=
      fun x hx => hCause m x esse (fun heq => hx heq.symm) (hAllCause x hx)
    have hIncoming : ∀ c, c ≠ m → ¬ CausesIn c m esse :=
      (perfectionOrderSystem CausesIn esse).maximal_has_no_distinct_cause
        (hScale.causesRaiseDegree hCause) ((hScale.isMaximumIn_iff_isMax m).mp hm)
    have hUnique : ∀ n, IsMaximumIn InAct MoreIn esse n → n = m := by
      intro n hn
      rcases hEM (n = m) with hSame | hOther
      · exact hSame
      · exact (hn.2 m (hStrict n hOther)).elim
    exact Or.inl ⟨m, hm, hStrict, hAllCause, hIncoming, hUnique⟩
  · apply Or.inr
    intro x
    rcases hEM (∃ y, MoreIn esse y x) with hGreater | hNoGreater
    · exact hGreater
    · exact (hNoMax ⟨x, hScale.1 x, fun y hy => hNoGreater ⟨y, hy⟩⟩).elim

/-- The top and unbounded-degree predicates cannot both hold, since the top's
actual maximality forbids a strictly higher being. No population, order,
causation or classical assumption is needed for this incompatibility. -/
theorem hornsIncompatible {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) :
    ¬ (QuartaViaStrictCausalTop InAct MoreIn CausesIn esse ∧
      QuartaViaUnboundedDegrees MoreIn esse) := by
  rintro ⟨⟨m, hm, _⟩, hUnbounded⟩
  obtain ⟨y, hy⟩ := hUnbounded m
  exact hm.2 y hy

end TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaDegreeFork
