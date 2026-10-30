import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1

/-! Two-being Boolean controls for deriving a maximum in esse without the truth
bridge. Respects are Booleans: `false` is the fixture's truth, goodness and
nobility, and `true` is its esse. These are satisfiability fixtures for encoded
premises, not metaphysical possibilities or source readings. -/
namespace TruthCore.Models.QuartaViaMaximumControls
open TruthCore.Latin.Aquinas.SummaTheologiae

abbrev verum : Bool := false
abbrev esse : Bool := true

/-! `true` tops the fixture's truth and `false` tops its esse. Each being has
each perfection, and causation follows the comparison. -/
namespace CrossedTops
def inAct (_ : Bool) (_ : Bool) : Prop := True
def moreIn (r x y : Bool) : Prop := x = !r ∧ y = r
def causesIn (c x r : Bool) : Prop := moreIn r c x

theorem grades : GradesFoundInThingsReading moreIn verum verum verum := by
  dsimp only [GradesFoundInThingsReading, moreIn]; decide
theorem approach : GradesByApproachToAMaximumReading inAct moreIn := by
  dsimp only [GradesByApproachToAMaximumReading, IsMaximumIn, inAct, moreIn]; decide
theorem genus : MaximumInGenusCausesAllInGenusReading inAct moreIn causesIn := by
  dsimp only [MaximumInGenusCausesAllInGenusReading, CausesAllInGenus, IsMaximumIn,
    inAct, causesIn, moreIn]; decide
theorem actuality : ActualityOnlyInsofarAsBeingReading inAct esse :=
  fun _ _ _ => trivial
theorem conclusion : MaximeEnsCausesBeingOfAllReading inAct moreIn causesIn esse := by
  dsimp only [MaximeEnsCausesBeingOfAllReading, CausesAllInGenus, IsMaximumIn,
    inAct, causesIn, moreIn]; decide
theorem truthBridgeFails : ¬ MostTrueIsMostBeingReading inAct moreIn verum esse := by
  dsimp only [MostTrueIsMostBeingReading, IsMaximumIn, inAct, moreIn]; decide
end CrossedTops

/-! Only the fixture's truth is had by anything, so nothing has esse. -/
namespace NoEsse
def inAct (_ : Bool) (r : Bool) : Prop := r = verum
def moreIn (r x y : Bool) : Prop := r = verum ∧ x = true ∧ y = false
def causesIn (c x r : Bool) : Prop := moreIn r c x

theorem grades : GradesFoundInThingsReading moreIn verum verum verum := by
  dsimp only [GradesFoundInThingsReading, moreIn]; decide
theorem approach : GradesByApproachToAMaximumReading inAct moreIn := by
  dsimp only [GradesByApproachToAMaximumReading, IsMaximumIn, inAct, moreIn]; decide
theorem genus : MaximumInGenusCausesAllInGenusReading inAct moreIn causesIn := by
  dsimp only [MaximumInGenusCausesAllInGenusReading, CausesAllInGenus, IsMaximumIn,
    inAct, causesIn, moreIn]; decide
theorem actualityFails : ¬ ActualityOnlyInsofarAsBeingReading inAct esse := by
  dsimp only [ActualityOnlyInsofarAsBeingReading, inAct]; decide
theorem conclusionFails : ¬ MaximeEnsCausesBeingOfAllReading inAct moreIn causesIn esse := by
  rintro ⟨_, ⟨h, _⟩, _⟩
  exact Bool.noConfusion (h : esse = verum)
end NoEsse

/-! Only `true` has any perfection, and the fixture's truth compares it with
`false`, which has no perfection. Nothing is compared in esse. -/
namespace FlatEsse
def inAct (x : Bool) (_ : Bool) : Prop := x = true
def moreIn (r x y : Bool) : Prop := r = verum ∧ x = true ∧ y = false
def causesIn (_ _ _ : Bool) : Prop := False

theorem grades : GradesFoundInThingsReading moreIn verum verum verum := by
  dsimp only [GradesFoundInThingsReading, moreIn]; decide
theorem approach : GradesByApproachToAMaximumReading inAct moreIn := by
  dsimp only [GradesByApproachToAMaximumReading, IsMaximumIn, inAct, moreIn]; decide
theorem genus : MaximumInGenusCausesAllInGenusReading inAct moreIn causesIn := by
  dsimp only [MaximumInGenusCausesAllInGenusReading, CausesAllInGenus, IsMaximumIn,
    inAct, causesIn, moreIn]; decide
theorem actuality : ActualityOnlyInsofarAsBeingReading inAct esse :=
  fun _ _ h => h
theorem conclusion : MaximeEnsCausesBeingOfAllReading inAct moreIn causesIn esse := by
  dsimp only [MaximeEnsCausesBeingOfAllReading, CausesAllInGenus, IsMaximumIn,
    inAct, causesIn, moreIn]; decide
theorem noComparisonInEsse : ∀ y x, ¬ moreIn esse y x := by
  dsimp only [moreIn]; decide
end FlatEsse

end TruthCore.Models.QuartaViaMaximumControls
