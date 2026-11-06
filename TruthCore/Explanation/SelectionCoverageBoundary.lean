module

public import TruthCore.Results.Explanation.OrderingCardinality.TruthfulRival.Solution
public import TruthCore.Logic.ExcludedMiddle

/-!
# Truthfulness and coverage of the arrangement-selection rival

The existing rival requires an accepted candidate TRUE at the actual arrangement
that also leaves an alternative. Generic adequacy judgments can instead accept
false candidates. Reuse the old truthful-rival controls and make the missing
factivity policy explicit. No mathematical information test is identified with
actual explanatory adequacy, and no source account is silently strengthened.
-/
@[expose] public section
namespace TruthCore.Explanation.SelectionCoverageBoundary
open TruthCore.Explanation.OrderingCardinality

/-- OPEN factivity of the supplied acceptance judgment, not warrant or causal
production and not a definition of every complete-explanation standard. -/
def AcceptedAreTrue (a : Arrangement) (adequate : (Arrangement → Prop) → Prop) : Prop :=
  ∀ p, adequate p → p a

def AcceptedFalse (a : Arrangement) (adequate : (Arrangement → Prop) → Prop) : Prop :=
  ∃ p, adequate p ∧ ¬ p a

def FactivityFails (a : Arrangement) (adequate : (Arrangement → Prop) → Prop) : Prop :=
  ¬ AcceptedAreTrue a adequate

def SelectionFails (a : Arrangement) (adequate : (Arrangement → Prop) → Prop) : Prop :=
  ¬ CompleteRequiresSelection a adequate

/-- Coverage only: the two negative branches can overlap when a judgment accepts
both false candidates and truthful nonselecting candidates. -/
def SelectionTrilemma (a : Arrangement) (adequate : (Arrangement → Prop) → Prop) : Prop :=
  CompleteRequiresSelection a adequate ∨ AcceptsUnselected a adequate ∨ AcceptedFalse a adequate

def FactiveSelectionFork (a : Arrangement) (adequate : (Arrangement → Prop) → Prop) : Prop :=
  CompleteRequiresSelection a adequate ∨ AcceptsUnselected a adequate

def falseOnly (a : Arrangement) (p : Arrangement → Prop) : Prop := ¬ p a
def trueOnly (a : Arrangement) (p : Arrangement → Prop) : Prop := p a
def selectsOnly (a : Arrangement) (p : Arrangement → Prop) : Prop := Selects a p

/-- Reuse the original arena/control theorem; the last policy is a deliberately
selection-defined positive calibration, not independent explanatory warrant. -/
def Controls : Prop := ∀ a : Arrangement,
  (AcceptedFalse a (falseOnly a) ∧ SelectionFails a (falseOnly a) ∧
    ¬ AcceptsUnselected a (falseOnly a)) ∧
  (AcceptedAreTrue a (trueOnly a) ∧ AcceptsUnselected a (trueOnly a) ∧
    SelectionFails a (trueOnly a)) ∧
  (CompleteRequiresSelection a (selectsOnly a) ∧ AcceptedAreTrue a (selectsOnly a) ∧
    ∃ p, selectsOnly a p)
end TruthCore.Explanation.SelectionCoverageBoundary
