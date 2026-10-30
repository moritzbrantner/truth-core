import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaFork
import TruthCore.Logic.Configuration
import TruthCore.Models.QuartaViaDegreeFork

namespace TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaUnboundedCore
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Models.QuartaViaDegreeFork

/-- The existing grades-to-maximum principle, the existing observation of
some grades, and unbounded degree extension at esse cannot coexist. Grades
supply one carrier witness; extension gives a comparison in esse; the maximum
principle then gives a maximal being contradicted by another extension.
No scale, order class, causation, genus principle or excluded middle is used.
This rejects no preferred member and establishes no philosophical premise. -/
theorem incompatible {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse bonum verum nobile : Respect)
    (hMaximum : GradesByApproachToAMaximumReading InAct MoreIn)
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hUnbounded : QuartaViaUnboundedDegrees MoreIn esse) :
    TruthCore.Logic.ConfigurationFalse := by
  obtain ⟨a, _, _⟩ := hGrades.1
  obtain ⟨b, hb⟩ := hUnbounded a
  obtain ⟨m, hm⟩ := hMaximum esse ⟨b, a, hb⟩
  obtain ⟨c, hc⟩ := hUnbounded m
  exact hm.2 c hc

/-- Dropping unbounded extension leaves a single finite top interpretation of
both existing root commitments, with extension false in that same model. -/
theorem withoutUnbounded :
    GradesByApproachToAMaximumReading FiniteTop.model.InAct FiniteTop.model.MoreIn ∧
    GradesFoundInThingsReading FiniteTop.model.MoreIn FiniteTop.model.esse
      FiniteTop.model.esse FiniteTop.model.esse ∧
    ¬ QuartaViaUnboundedDegrees FiniteTop.model.MoreIn FiniteTop.model.esse := by
  exact ⟨FiniteTop.gradesHaveMaximum, FiniteTop.grades, FiniteTop.notUnbounded⟩

/-- Dropping the maximum principle leaves one infinite Nat interpretation of
observed grades and unbounded extension, with the maximum principle false.
This interpretation is not claimed to be a finite registered model. -/
theorem withoutMaximumPrinciple :
    GradesFoundInThingsReading Unbounded.moreIn Unbounded.esse
      Unbounded.esse Unbounded.esse ∧
    QuartaViaUnboundedDegrees Unbounded.moreIn Unbounded.esse ∧
    ¬ GradesByApproachToAMaximumReading Unbounded.inAct Unbounded.moreIn := by
  exact ⟨Unbounded.grades, Unbounded.unboundedDegrees, Unbounded.violatesGradesHaveMaximum⟩

/-- Dropping observed grades admits the empty carrier: both universal
principles hold vacuously and the grades observation fails. This is an explicit
empty control, not a nonempty witness or an accepted finite-registry entry. -/
theorem withoutGrades :
    GradesByApproachToAMaximumReading EmptyControl.inAct EmptyControl.moreIn ∧
    QuartaViaUnboundedDegrees EmptyControl.moreIn EmptyControl.esse ∧
    ¬ GradesFoundInThingsReading EmptyControl.moreIn EmptyControl.esse
      EmptyControl.esse EmptyControl.esse := by
  exact ⟨EmptyControl.gradesHaveMaximum, EmptyControl.unboundedDegrees,
    EmptyControl.violatesGradesFound⟩

end TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaUnboundedCore
