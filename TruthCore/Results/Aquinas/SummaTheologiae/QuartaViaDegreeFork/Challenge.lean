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
  sorry

/-- The top and unbounded-degree predicates cannot both hold, since the top's
actual maximality forbids a strictly higher being. No population, order,
causation or classical assumption is needed for this incompatibility. -/
theorem hornsIncompatible {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) :
    ¬ (QuartaViaStrictCausalTop InAct MoreIn CausesIn esse ∧
      QuartaViaUnboundedDegrees MoreIn esse) := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaDegreeFork
