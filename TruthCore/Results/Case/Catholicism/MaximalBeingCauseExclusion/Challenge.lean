import TruthCore.Case.Catholicism.MaximalBeingCauseExclusion
import TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia.Solution
import TruthCore.Greek.Aristotle.Metaphysics
namespace TruthCore.Results.Case.Catholicism.MaximalBeingCauseExclusion
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism

/-- A distinct cause would be more in being, contradicting maximality. -/
theorem maximumHasNoDistinctEsseCause {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn) :
    MaximumHasNoDistinctEsseCause InAct MoreIn CausesIn esse := by
  sorry

/-- The imported fourth-way theorem supplies the very witness to which the
causal-comparison exclusion applies. No maximum-existence premise is added. -/
theorem quartaViaWitness {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (bonum verum nobile esse : Respect)
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hTrue : MostTrueIsMostBeingReading InAct MoreIn verum esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn) :
    MaximalCauseWithNoDistinctEsseCause InAct MoreIn CausesIn esse := by
  sorry

/-- On two beings, with no strict comparisons and every causal pair true, every
being is maximal but each has a distinct cause. This exposes the necessity of
causal comparison; it is not a theological or modal counterworld. -/
theorem maximalityAloneDoesNotExcludeCause :
    ∃ (InAct : Bool → Unit → Prop)
      (MoreIn : Unit → Bool → Bool → Prop)
      (CausesIn : Bool → Bool → Unit → Prop),
      IsMaximumIn InAct MoreIn () false ∧
      CausesIn true false () ∧
      ¬ MaximumHasNoDistinctEsseCause InAct MoreIn CausesIn () := by
  sorry

end TruthCore.Results.Case.Catholicism.MaximalBeingCauseExclusion
