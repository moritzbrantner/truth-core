module

public import TruthCore.Modal.TemporalHistory
public import Mathlib.Tactic

/-! Owner-selected analyst interpretation siblings for the A5/A3 history
interface. These are history predicates, not situation tokens or causal laws.
`IsAt` means temporal existence; `classified w t b` means that b counts as
contingent at the specified classification world and time. Neither primitive
asserts a modal definition of contingency. No finiteness, persistence, linearity,
well-foundedness, causal exercise or actuality bridge is imposed. -/

@[expose] public section

namespace TruthCore.Modal.A5HistoryScope
open TemporalHistory

variable {W B T : Type}

/-- Full supplied history, with classification frozen at actual a/atime and
roster identity selected once at w. Both inclusion and exclusion are required.
The supplied time carrier need not contain future times; when it does, this
predicate includes them. It must not be called the current-or-past reading
without an explicit restriction of the supplied history. -/
def RigidEverRoster (h : History W B T) (classified : W → T → B → Prop)
    (a : W) (atime : T) (w : W) (roster : B → Prop) : Prop :=
  ∀ b, roster b ↔ classified a atime b ∧ ∃ t, h.IsAt w b t

/-- Evaluation-world/time classification, still over the full supplied history.
This does not freeze a selected actual-world class across evaluations. -/
def EvaluatedEverRoster (h : History W B T) (classified : W → T → B → Prop)
    (w : W) (time : T) (roster : B → Prop) : Prop :=
  ∀ b, roster b ↔ classified w time b ∧ ∃ t, h.IsAt w b t

/-- Current-or-past evaluation: both the contingent class and historical cutoff
vary with the evaluation. This differs from an unrestricted full-history roster. -/
def EvaluatedPastRoster [Preorder T] (h : History W B T)
    (classified : W → T → B → Prop) (w : W) (time : T)
    (roster : B → Prop) : Prop :=
  ∀ b, roster b ↔ classified w time b ∧ ∃ t, t ≤ time ∧ h.IsAt w b t

/-- Rigid selected-history current-or-past roster, with classification fixed at
actual a/atime and a fixed cutoff in the selected history. -/
def RigidPastRoster [Preorder T] (h : History W B T)
    (classified : W → T → B → Prop) (a : W) (atime : T)
    (w : W) (cutoff : T) (roster : B → Prop) : Prop :=
  ∀ b, roster b ↔ classified a atime b ∧ ∃ t, t ≤ cutoff ∧ h.IsAt w b t

/-- Nonrigid population: the existential bearer is inside each time's scope.
The classification is explicitly frozen here, supplied independently of time. -/
def PopulationFirst [Preorder T] (h : History W B T) (contingent : B → Prop)
    (w : W) (t : T) : Prop :=
  (∃ b, contingent b ∧ h.IsAt w b t) ∧
    ∀ s, s < t → ¬ ∃ b, contingent b ∧ h.IsAt w b s

/-- Particular-member first occurrence. Other contingent beings may already
exist. Reuses the exact TemporalHistory.BeginsAt body for this member. -/
def MemberFirst [Preorder T] (h : History W B T) (contingent : B → Prop)
    (w : W) (b : B) (t : T) : Prop :=
  contingent b ∧ BeginsAt h w b t

/-- Immediate predecessor transition: no intervening supplied time. Earlier
population episodes are permitted; this is not a global first occurrence. -/
def PopulationPredecessor [Preorder T] (h : History W B T)
    (contingent : B → Prop) (w : W) (t : T) : Prop :=
  (∃ b, contingent b ∧ h.IsAt w b t) ∧
    ∃ s, s < t ∧ (∀ u, s < u → u < t → False) ∧
      ¬ ∃ b, contingent b ∧ h.IsAt w b s

/-- Particular-member predecessor transition, without excluding other members
or earlier episodes of the same member. -/
def MemberPredecessor [Preorder T] (h : History W B T)
    (contingent : B → Prop) (w : W) (b : B) (t : T) : Prop :=
  contingent b ∧ h.IsAt w b t ∧
    ∃ s, s < t ∧ (∀ u, s < u → u < t → False) ∧ ¬ h.IsAt w b s

/-- Explicit first-moment variant: no earlier supplied time exists. Neither
first-occurrence predicate above requires the time carrier to have a first moment. -/
def PopulationAtFirstMoment [Preorder T] (h : History W B T)
    (contingent : B → Prop) (w : W) (t : T) : Prop :=
  (∃ b, contingent b ∧ h.IsAt w b t) ∧ ∀ s, ¬ s < t

/-- Particular member at a first supplied moment. -/
def MemberAtFirstMoment [Preorder T] (h : History W B T)
    (contingent : B → Prop) (w : W) (b : B) (t : T) : Prop :=
  contingent b ∧ h.IsAt w b t ∧ ∀ s, ¬ s < t

/-- Finite declared menu, not an assertion of exhaustive source interpretation. -/
inductive BeginningReading where
  | populationFirst | memberFirst | populationPredecessor | memberPredecessor
  | populationFirstMoment | memberFirstMoment

def BeginningCase [Preorder T] (h : History W B T) (contingent : B → Prop)
    (w : W) (b : B) (t : T) : BeginningReading → Prop
  | .populationFirst => PopulationFirst h contingent w t
  | .memberFirst => MemberFirst h contingent w b t
  | .populationPredecessor => PopulationPredecessor h contingent w t
  | .memberPredecessor => MemberPredecessor h contingent w b t
  | .populationFirstMoment => PopulationAtFirstMoment h contingent w t
  | .memberFirstMoment => MemberAtFirstMoment h contingent w b t

/-- Coverage/exclusivity means selecting one menu constructor. Whether the menu
covers a historical use remains an OPEN application premise, not a theorem. -/
structure SelectedBeginning [Preorder T] (h : History W B T)
    (contingent : B → Prop) (w : W) (b : B) (t : T) where
  reading : BeginningReading
  condition : BeginningCase h contingent w b t reading

namespace Controls
/-- Full Int/Rat/Nat carriers below are test interpretations only. The general
predicates above quantify over arbitrary supplied time and individual carriers. -/
def history {S : Type} (present : Bool → Bool → S → Prop) (now : S) :
    History Bool Bool S where
  ontic := { frame := { access := fun _ _ => True }
             ExistsAt := fun _ _ => True
             Causes := fun _ _ _ => False }
  IsAt := present
  now := now

def onset : History Bool Bool Int := history (fun _ _ t => 0 ≤ t) 0

def discreteNonvacuity : Prop :=
    PopulationFirst onset (fun _ => True) false 0 ∧
    MemberFirst onset (fun _ => True) false true 0 ∧
    PopulationPredecessor onset (fun _ => True) false 0 ∧
    MemberPredecessor onset (fun _ => True) false true 0

def denseOnset : History Bool Bool Rat := history (fun _ _ t => 0 ≤ t) 0

def denseSeparation : Prop :=
    PopulationFirst denseOnset (fun _ => True) false 0 ∧
    ¬ PopulationPredecessor denseOnset (fun _ => True) false 0

def initial : History Bool Bool Nat := history (fun _ _ _ => True) 0

def firstMomentSeparation : Prop :=
    PopulationAtFirstMoment initial (fun _ => True) false 0 ∧
    MemberAtFirstMoment initial (fun _ => True) false true 0 ∧
    ¬ PopulationPredecessor initial (fun _ => True) false 0

def turnover : History Bool Bool Int :=
  history (fun _ b t => b = false ∨ 0 ≤ t) 0

def memberNotPopulation : Prop :=
    MemberFirst turnover (fun _ => True) false true 0 ∧
    ¬ PopulationFirst turnover (fun _ => True) false 0

def recurrence : History Bool Bool Int :=
  history (fun _ _ t => t = 0 ∨ t = -2) 0

def predecessorNotFirst : Prop :=
    PopulationPredecessor recurrence (fun _ => True) false 0 ∧
    ¬ PopulationFirst recurrence (fun _ => True) false 0

/-- Positive-only membership misses an extra member; an empty roster still
has satisfiable negative content and fails as soon as a member appears. -/
def rosterControls : Prop :=
    RigidEverRoster onset (fun _ _ _ => True) false 0 false (fun _ => True) ∧
    ¬ RigidEverRoster onset (fun _ _ _ => True) false 0 false (fun b => b = false) ∧
    RigidEverRoster onset (fun _ _ _ => False) false 0 false (fun _ => False) ∧
    ¬ RigidEverRoster onset (fun _ _ _ => True) false 0 false (fun _ => False)

/-- Same history, different contingent classification. The disagreement is
not suppressed by conjoining the two readings. -/
def classificationSeparation : Prop :=
    RigidEverRoster onset (fun w _ _ => w = false) false 0 true (fun _ => True) ∧
    ¬ EvaluatedEverRoster onset (fun w _ _ => w = false) true 0 (fun _ => True)

/-- A bearer occurring only tomorrow separates full-history from past membership. -/
def cutoffSeparation : Prop :=
    RigidEverRoster (history (fun _ _ (t : Int) => t = 1) 0)
      (fun _ _ _ => True) false 0 false (fun _ => True) ∧
    ¬ EvaluatedPastRoster (history (fun _ _ (t : Int) => t = 1) 0)
      (fun _ _ _ => True) false 0 (fun _ => True)

end Controls

/-- Joint formal control suite; it establishes no source interpretation. -/
def ControlSuite : Prop :=
  Controls.discreteNonvacuity ∧
  Controls.denseSeparation ∧
  Controls.firstMomentSeparation ∧
  Controls.memberNotPopulation ∧
  Controls.predecessorNotFirst ∧
  Controls.rosterControls ∧
  Controls.classificationSeparation ∧
  Controls.cutoffSeparation
end TruthCore.Modal.A5HistoryScope
