import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaFork
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
import TruthCore.Logic.Configuration
import TruthCore.Models.QuartaViaDegreeFork
import TruthCore.Models.QuartaViaMaximumControls

namespace TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaMaximumInBeing
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Models.QuartaViaMaximumControls
open TruthCore.Models.QuartaViaDegreeFork

/-- Excluded middle alone splits: some being is maximal in esse, or every being
having esse has some being more such than it. This is the actual-population
form of the degree fork's split; it assumes no scale, order or causation. -/
theorem actualFork {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    (∃ m, IsMaximumIn InAct MoreIn esse m) ∨ QuartaViaUnboundedAmongActual InAct MoreIn esse := by
  sorry

/-- The fork's own unbounded horn implies the actual-population horn. -/
theorem unboundedGivesAmongActual {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect)
    (hUnbounded : QuartaViaUnboundedDegrees MoreIn esse) :
    QuartaViaUnboundedAmongActual InAct MoreIn esse := by
  sorry

/-- The grades-to-maximum principle excludes the actual-population horn once
something has esse: a comparison above that being triggers the principle at
esse, and the resulting maximal being, which has esse, would have a being more
such than it. -/
theorem actualCore {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hActual : ∃ x, InAct x esse)
    (hUnbounded : QuartaViaUnboundedAmongActual InAct MoreIn esse) :
    TruthCore.Logic.ConfigurationFalse := by
  sorry

/-- Some being is maximal in esse and causes esse in every other being having
esse, without the premise that the maximally true is maximally being. The
grades-to-maximum principle at truth gives a being having truth; actuality only
insofar as being gives it esse. Those grades supply only that population; any
respect with grades would do. If some being having esse has a being more such
than it, the principle at esse gives the maximum (`actualFork`, `actualCore`).
Otherwise a being having esse is vacuously maximal and the principle at esse is
not used, so the maximum does not presuppose grades of being (`flatBranch`,
`flatMaximum`). The witness is not shown to be maximally true. Maximality here is the weak `IsMaximumIn`. The truth
bridge is neither refuted nor derived. -/
theorem maximeEnsCausesBeingOfAll {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (bonum verum nobile esse : Respect)
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse := by
  sorry

/-- With no comparison in esse, the genus principle and unrestricted causal
comparative leave at most one being having esse: any other would be caused by
it and so compared with it. -/
theorem flatBranch {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hFlat : ∀ y x, ¬ MoreIn esse y x)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hCause : TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
      CausesIn MoreIn)
    (m : Being) (hm : InAct m esse) :
    ∀ x, x ≠ m → ¬ InAct x esse := by
  sorry

/-- One Boolean interpretation satisfies the theorem's other nonlogical premises
and its conclusion with no comparison in esse, while the fixture's truth compares
a being with one lacking every perfection, so `MoreIn` does not entail `InAct`. -/
theorem flatMaximum :
    GradesFoundInThingsReading FlatEsse.moreIn verum verum verum ∧
    GradesByApproachToAMaximumReading FlatEsse.inAct FlatEsse.moreIn ∧
    MaximumInGenusCausesAllInGenusReading FlatEsse.inAct FlatEsse.moreIn FlatEsse.causesIn ∧
    ActualityOnlyInsofarAsBeingReading FlatEsse.inAct esse ∧
    MaximeEnsCausesBeingOfAllReading FlatEsse.inAct FlatEsse.moreIn FlatEsse.causesIn esse ∧
    (∀ y x, ¬ FlatEsse.moreIn esse y x) ∧
    (FlatEsse.moreIn verum true false ∧ ¬ FlatEsse.inAct false verum) := by
  sorry

/-- The truth bridge is not entailed: one Boolean interpretation satisfies the
other premises and the conclusion while the truth bridge fails. -/
theorem truthBridgeNotEntailed :
    GradesFoundInThingsReading CrossedTops.moreIn verum verum verum ∧
    GradesByApproachToAMaximumReading CrossedTops.inAct CrossedTops.moreIn ∧
    MaximumInGenusCausesAllInGenusReading CrossedTops.inAct CrossedTops.moreIn
      CrossedTops.causesIn ∧
    ActualityOnlyInsofarAsBeingReading CrossedTops.inAct esse ∧
    MaximeEnsCausesBeingOfAllReading CrossedTops.inAct CrossedTops.moreIn
      CrossedTops.causesIn esse ∧
    ¬ MostTrueIsMostBeingReading CrossedTops.inAct CrossedTops.moreIn verum esse := by
  sorry

/-- Deleting actuality only insofar as being: one Boolean interpretation
satisfies the other premises and the conclusion fails. -/
theorem withoutActuality :
    GradesFoundInThingsReading NoEsse.moreIn verum verum verum ∧
    GradesByApproachToAMaximumReading NoEsse.inAct NoEsse.moreIn ∧
    MaximumInGenusCausesAllInGenusReading NoEsse.inAct NoEsse.moreIn NoEsse.causesIn ∧
    ¬ ActualityOnlyInsofarAsBeingReading NoEsse.inAct esse ∧
    ¬ MaximeEnsCausesBeingOfAllReading NoEsse.inAct NoEsse.moreIn NoEsse.causesIn esse := by
  sorry

/-- Deleting the grades-to-maximum principle: the existing Nat interpretation
satisfies the other premises and the conclusion fails. -/
theorem withoutApproach :
    GradesFoundInThingsReading Unbounded.moreIn Unbounded.esse Unbounded.esse Unbounded.esse ∧
    MaximumInGenusCausesAllInGenusReading Unbounded.inAct Unbounded.moreIn Unbounded.causesIn ∧
    ActualityOnlyInsofarAsBeingReading Unbounded.inAct Unbounded.esse ∧
    ¬ GradesByApproachToAMaximumReading Unbounded.inAct Unbounded.moreIn ∧
    ¬ MaximeEnsCausesBeingOfAllReading Unbounded.inAct Unbounded.moreIn Unbounded.causesIn
      Unbounded.esse := by
  sorry

/-- Deleting observed grades: the existing empty-carrier interpretation
satisfies the grades-to-maximum principle and actuality only insofar as being, the grades
observation fails, and nothing is maximal in esse. Empty means an omitted
population assumption, not metaphysical emptiness. -/
theorem withoutGrades :
    GradesByApproachToAMaximumReading EmptyControl.inAct EmptyControl.moreIn ∧
    ActualityOnlyInsofarAsBeingReading EmptyControl.inAct EmptyControl.esse ∧
    ¬ GradesFoundInThingsReading EmptyControl.moreIn EmptyControl.esse
      EmptyControl.esse EmptyControl.esse ∧
    ¬ ∃ m, IsMaximumIn EmptyControl.inAct EmptyControl.moreIn EmptyControl.esse m := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaMaximumInBeing
