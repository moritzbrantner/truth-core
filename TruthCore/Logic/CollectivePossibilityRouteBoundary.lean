module

public import TruthCore.Results.Logic.QuantifierShiftInvalid.Solution
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3TertiaVia
public import TruthCore.Logic.ExcludedMiddle

/-! Analyst scope boundary: an invalid UNIVERSAL proof method is not the
negation of a particular collective-possibility premise. A restricted shift can
hold in a fixed presence profile. Its temporal-realization and possibility
interfaces are separately named; neither a common absence nor its possibility
is assumed by the word possible. No historical interpretation is settled here.
-/

@[expose] public section
namespace TruthCore.Logic.CollectivePossibilityRouteBoundary
open TruthCore.Latin.Aquinas.SummaTheologiae

structure Frame where
  Being : Type
  Time : Type
  IsAt : Being → Time → Prop
  Possible : (Time → Prop) → Prop

/-- Restricted to this SAME presence profile; unlike the invalid global schema
it does not quantify over all being/time domains and presence dictionaries. -/
def LocalShift (f : Frame) : Prop :=
  (∀ x, ∃ t, ¬ f.IsAt x t) → ∃ t, ∀ x, ¬ f.IsAt x t

def RealizedIsPossible (f : Frame) : Prop :=
  ∀ φ, (∃ t, φ t) → f.Possible φ

/-- Weakest realization interface consumed by this route, restricted to the
common-absence condition. It does not assert any actual common absence. -/
def EmptyRealizedIsPossible (f : Frame) : Prop :=
  (∃ t, ∀ x, ¬ f.IsAt x t) → f.Possible (fun t => ∀ x, ¬ f.IsAt x t)

def AllIndividuallyPossible (f : Frame) : Prop :=
  ∀ x, PossibleNotToBe f.Possible f.IsAt x

def JointAbsenceImpossible (f : Frame) : Prop :=
  ¬ f.Possible (fun t => ∀ x, ¬ f.IsAt x t)

def Countercase (f : Frame) : Prop :=
  AllIndividuallyPossible f ∧ JointAbsenceImpossible f

def CollectiveFails (f : Frame) : Prop :=
  ¬ AllCanNotBeThenNothingPossibleReading f.Possible f.IsAt

def CollectiveFork : Prop :=
  ∀ f, AllCanNotBeThenNothingPossibleReading f.Possible f.IsAt ∨ Countercase f

/-- Both beings are absent at false; a local shift can hold despite failure
of the global logical schema. Existence at a supplied time is one MODEL's
possibility interpretation, not a universal source definition. -/
def commonAbsence : Frame where
  Being := Bool
  Time := Bool
  IsAt := fun _ t => t = true
  Possible := fun φ => ∃ t, φ t

/-- Each being is absent somewhere, but there is no common absence. -/
def alternating : Frame where
  Being := Bool
  Time := Bool
  IsAt := fun x t => x = t
  Possible := fun φ => ∃ t, φ t

/-- The common absence at none is realized but excluded from this supplied
possibility domain. At some b, being b is present. This is a formal omission
control, not a metaphysical claim that actual states are impossible. -/
def disallowedCommon : Frame where
  Being := Bool
  Time := Option Bool
  IsAt := fun x t => some x = t
  Possible := fun φ => ∃ b : Bool, φ (some b)

def Controls : Prop :=
  TruthCore.Logic.EachSometimeNotDoesNotEntailSometimeNothing ∧
  (LocalShift commonAbsence ∧
    WhatCanNotBeSometimeIsNotReading commonAbsence.Possible commonAbsence.IsAt ∧
    RealizedIsPossible commonAbsence ∧ AllIndividuallyPossible commonAbsence ∧
    AllCanNotBeThenNothingPossibleReading commonAbsence.Possible commonAbsence.IsAt) ∧
  (¬ LocalShift alternating ∧
    WhatCanNotBeSometimeIsNotReading alternating.Possible alternating.IsAt ∧
    RealizedIsPossible alternating ∧ Countercase alternating) ∧
  (LocalShift disallowedCommon ∧
    WhatCanNotBeSometimeIsNotReading disallowedCommon.Possible disallowedCommon.IsAt ∧
    ¬ EmptyRealizedIsPossible disallowedCommon ∧ Countercase disallowedCommon)

end TruthCore.Logic.CollectivePossibilityRouteBoundary
