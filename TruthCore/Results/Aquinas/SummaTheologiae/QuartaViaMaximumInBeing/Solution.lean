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
  rcases hEM (∃ m, IsMaximumIn InAct MoreIn esse m) with hMax | hNoMax
  · exact Or.inl hMax
  · refine Or.inr fun x hx => ?_
    rcases hEM (∃ y, MoreIn esse y x) with hGreater | hNoGreater
    · exact hGreater
    · exact (hNoMax ⟨x, hx, fun y hy => hNoGreater ⟨y, hy⟩⟩).elim

/-- The fork's own unbounded horn implies the actual-population horn. -/
theorem unboundedGivesAmongActual {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect)
    (hUnbounded : QuartaViaUnboundedDegrees MoreIn esse) :
    QuartaViaUnboundedAmongActual InAct MoreIn esse := by
  exact fun x _ => hUnbounded x

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
  obtain ⟨a, ha⟩ := hActual
  obtain ⟨b, hb⟩ := hUnbounded a ha
  obtain ⟨m, hm⟩ := hApproach esse ⟨b, a, hb⟩
  obtain ⟨c, hc⟩ := hUnbounded m hm.1
  exact hm.2 c hc

/-- Some being is maximal in esse and causes esse in every other being having
esse, without the premise that the maximally true is maximally being. The
grades-to-maximum principle at truth gives a being having truth; actuality only
insofar as being gives it esse; `actualFork` and `actualCore` then give a
maximum in esse. The principle is used at truth and at esse. The witness is not
shown to be maximally true. Maximality here is the weak `IsMaximumIn`. The truth
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
  obtain ⟨_, hVerum, _⟩ := hGrades
  obtain ⟨t, ht⟩ := hApproach verum hVerum
  rcases actualFork InAct MoreIn esse hEM with ⟨m, hm⟩ | hUnbounded
  · exact ⟨m, hm, hGenus esse m hm⟩
  · exact (actualCore InAct MoreIn esse hApproach ⟨t, hBeing t verum ht.1⟩ hUnbounded).elim

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
  exact ⟨CrossedTops.grades, CrossedTops.approach, CrossedTops.genus, CrossedTops.actuality,
    CrossedTops.conclusion, CrossedTops.truthBridgeFails⟩

/-- Deleting actuality only insofar as being: one Boolean interpretation
satisfies the other premises and the conclusion fails. -/
theorem withoutActuality :
    GradesFoundInThingsReading NoEsse.moreIn verum verum verum ∧
    GradesByApproachToAMaximumReading NoEsse.inAct NoEsse.moreIn ∧
    MaximumInGenusCausesAllInGenusReading NoEsse.inAct NoEsse.moreIn NoEsse.causesIn ∧
    ¬ ActualityOnlyInsofarAsBeingReading NoEsse.inAct esse ∧
    ¬ MaximeEnsCausesBeingOfAllReading NoEsse.inAct NoEsse.moreIn NoEsse.causesIn esse := by
  exact ⟨NoEsse.grades, NoEsse.approach, NoEsse.genus, NoEsse.actualityFails,
    NoEsse.conclusionFails⟩

/-- Deleting the grades-to-maximum principle: the existing Nat interpretation
satisfies the other premises and the conclusion fails. -/
theorem withoutApproach :
    GradesFoundInThingsReading Unbounded.moreIn Unbounded.esse Unbounded.esse Unbounded.esse ∧
    MaximumInGenusCausesAllInGenusReading Unbounded.inAct Unbounded.moreIn Unbounded.causesIn ∧
    ActualityOnlyInsofarAsBeingReading Unbounded.inAct Unbounded.esse ∧
    ¬ GradesByApproachToAMaximumReading Unbounded.inAct Unbounded.moreIn ∧
    ¬ MaximeEnsCausesBeingOfAllReading Unbounded.inAct Unbounded.moreIn Unbounded.causesIn
      Unbounded.esse := by
  refine ⟨Unbounded.grades, fun _ m hm => (Unbounded.noMaximum ⟨m, hm⟩).elim,
    fun _ _ _ => trivial, Unbounded.violatesGradesHaveMaximum, ?_⟩
  rintro ⟨m, hm, _⟩
  exact Unbounded.noMaximum ⟨m, hm⟩

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
  exact ⟨EmptyControl.gradesHaveMaximum, fun x => Empty.elim x, EmptyControl.violatesGradesFound,
    fun ⟨m, _⟩ => Empty.elim m⟩

end TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaMaximumInBeing
