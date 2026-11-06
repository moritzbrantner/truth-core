module

public import TruthCore.Explanation.MechanismInterventionParity
public import TruthCore.Explanation.ExplanatorySymmetry
public import TruthCore.Modal.Kripke

/-!
Analyst comparison for #1085; attribution deferred. The old active AND and idle
lookup equations supply TWO interpretations of explicitly off-normal repairs.
They agree on every normal observation, with source present throughout and a
contingent effect. Repairs are not accessible normal possibilities.

The selector below selects ALL normal antecedent witnesses, then only if there
are none consults the originating context's repair when it satisfies the
antecedent. It has success and normal-first restriction; no centering, closeness,
seriality, full Lewis/Stalnaker theory or real counterpossible truth is claimed.
The antecedent is impossible relative to this declared normal model, not a
logical contradiction. Changing modal accessibility is a separate control.
-/

@[expose] public section

namespace TruthCore.Modal.CounterpossibleConservativity
open TruthCore.Explanation.MechanismInterventionParity
open TruthCore.Explanation.PSRStrength (Arena Access)
open TruthCore.Explanation.ExplanatorySymmetry (Enables)

inductive Mode | active | idle deriving DecidableEq
inductive State | normal (context : Bool) | repair (context : Bool) deriving DecidableEq
inductive Atom | source | cofactor | effect deriving DecidableEq

/-- The old mechanism equation remains intact; only its interpretation in
normal versus source-off settings is new. -/
def run : Mode → TwoState → Setting → Observation
  | .active => pluralRun
  | .idle => idleRun

def sourceOff : Setting := ⟨some false, none⟩

def observation (mode : Mode) : State → Observation
  | .normal u => run mode ⟨true, u⟩ natural
  | .repair u => run mode ⟨true, u⟩ sourceOff

def truth (mode : Mode) (s : State) : Atom → Prop
  | .source => (observation mode s).a = true
  | .cofactor => (observation mode s).b = true
  | .effect => (observation mode s).effect = true

def normalFrame : Frame Bool := ⟨fun _ _ => True⟩
def normalTruth (u : Bool) : Atom → Prop := truth .active (.normal u)

/-- This enlarged frame would admit repairs as possibilities, changing the
modal profile. It is NOT the frame used for normal necessity. -/
def enlargedFrame : Frame State := ⟨fun _ _ => True⟩

def NormalWitness (A : State → Prop) : Prop := ∃ u, A (.normal u)

/-- Universal evaluation on the normal antecedent extension. This is one
explicit selection profile, not material implication evaluated at the origin. -/
def NormalConditional (A Q : State → Prop) : Prop := ∀ u, A (.normal u) → Q (.normal u)

/-- Normal-first, all-witness selection, with at most one source-context repair.
The repair may be absent: no global nonemptiness or seriality is asserted. -/
def Selected (origin : Bool) (A : State → Prop) : State → Prop
  | .normal u => A (.normal u)
  | .repair u => ¬ NormalWitness A ∧ u = origin ∧ A (.repair u)

def SelectedConditional (origin : Bool) (A Q : State → Prop) : Prop :=
  ∀ s, Selected origin A s → Q s

def sourceAbsent (mode : Mode) (s : State) : Prop := ¬ truth mode s .source

def effectPresent (mode : Mode) (s : State) : Prop := truth mode s .effect

/-- Preserve arbitrary predicate interpretations agreeing on every normal
state, provided the antecedent has a normal witness. Off-normal truth is not
constrained by those data. No nested conditional-language completeness claim. -/
def Conservativity : Prop :=
  (∀ origin A Q, NormalWitness A →
    (SelectedConditional origin A Q ↔ NormalConditional A Q)) ∧
  (∀ origin A B Q R, NormalWitness A →
    (∀ u, A (.normal u) ↔ B (.normal u)) →
    (∀ u, Q (.normal u) ↔ R (.normal u)) →
    (SelectedConditional origin A Q ↔ SelectedConditional origin B R))

/-- Carry the EXISTING strict-absence-vacuity theorem without identifying it
with the newly stipulated selected-state conditional. -/
def StrictAbsenceBaseline : Prop :=
  ∀ (W B F : Type) (A : Arena W B F) (a : W) (r f : F),
    (∀ v, Access A a v → A.holds v r) → Enables A a r f

/-- One joint normal/repair comparison. Existing intervention results are
composed, not re-proved. Normal source necessity and effect contingency use
exact Kripke Holds. Logical validity and enlarged accessibility are separated. -/
def Certificate : Prop :=
  (NaturalAgreement ∧ RespondsToEitherInput pluralRun ∧ ¬ RespondsToEitherInput idleRun) ∧
  StrictAbsenceBaseline ∧
  (∀ u, observation .active (.normal u) = observation .idle (.normal u)) ∧
  Holds normalFrame normalTruth true (.box (.atom .source)) ∧
  (Holds normalFrame normalTruth true (.atom .effect) ∧
    Holds normalFrame normalTruth true (.diamond (Formula.neg (.atom .effect)))) ∧
  ¬ Valid normalFrame (.box (.atom Atom.source)) ∧
  (∀ origin A s, Selected origin A s → A s) ∧
  Conservativity ∧
  (∀ mode, ¬ NormalWitness (sourceAbsent mode) ∧
    NormalConditional (sourceAbsent mode) (effectPresent mode) ∧
    NormalConditional (sourceAbsent mode) (fun s => ¬ effectPresent mode s)) ∧
  (∀ mode origin s, Selected origin (sourceAbsent mode) s ↔ s = .repair origin) ∧
  (SelectedConditional true (sourceAbsent .active) (fun s => ¬ effectPresent .active s) ∧
    ¬ SelectedConditional true (sourceAbsent .active) (effectPresent .active) ∧
    SelectedConditional true (sourceAbsent .idle) (effectPresent .idle) ∧
    ¬ SelectedConditional true (sourceAbsent .idle) (fun s => ¬ effectPresent .idle s)) ∧
  (∀ mode, ¬ Holds enlargedFrame (truth mode) (.normal true) (.box (.atom .source)))

end TruthCore.Modal.CounterpossibleConservativity
