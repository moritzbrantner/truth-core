import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- ST I q.2 a.3 co., the *quarta via*: things are found more and less true;
more and less are said by approach to a maximum, so something is maximally true;
the maximally true is maximally being; and the maximum in a genus causes all in
that genus. So something maximal in being causes the being of every other being. -/
theorem quartaVia {Being : Type} {Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (bonum verum nobile esse : Respect)
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hTrue : MostTrueIsMostBeingReading InAct MoreIn verum esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn) :
    MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse := by
  sorry

/-- The maximum premise is needed. On the natural numbers ordered by size, with
one perfection that everything has, there are grades but no maximum: the other
three premises hold (vacuously) and the conclusion fails. -/
theorem quartaViaNeedsMaximum :
    ¬ ∀ (Being Respect : Type)
      (InAct : Being → Respect → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop)
      (bonum verum nobile esse : Respect),
      GradesFoundInThingsReading MoreIn bonum verum nobile →
      MostTrueIsMostBeingReading InAct MoreIn verum esse →
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn →
      MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia
