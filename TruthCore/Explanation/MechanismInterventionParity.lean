module

public import TruthCore.Explanation.CompleteResponseParity
public import TruthCore.Modern.Hume.Regularity

/-! A bounded response-mechanism experiment following #974.

Unlike the #733 scenario-sufficiency predicate, a supplied `Setting` here
replaces a named public input's equation while the background stays fixed.
The experimental response notion `Changes` is REUSED from Hume.Regularity;
the all-inputs-needed test in #752 instead removes intrinsic `Supply` inputs.
Neither intervention family is independently certified as physically or
metaphysically available. The root of `OneState` explicitly carries TWO bits;
calling it one state or one graph node does not make it simple or underived.
-/

@[expose] public section

namespace TruthCore.Explanation.MechanismInterventionParity

open TruthCore.Modern.Hume.Regularity
open TruthCore.Explanation.CompleteResponseParity

/-- Two independently settable PUBLIC contributors. `none` preserves the
equation; `some v` replaces it with v. No source intervention is asserted. -/
structure Setting where
  setA : Option Bool
  setB : Option Bool
  deriving DecidableEq

def natural : Setting := ⟨none, none⟩

structure Observation where
  a : Bool
  b : Bool
  effect : Bool
  deriving DecidableEq

/-- One graph root's state can still hold two independently readable bits. -/
structure OneState where
  root : Bool × Bool
  deriving DecidableEq

/-- Two independent Boolean root-state slots. Not a thesis about substances. -/
structure TwoState where
  first : Bool
  second : Bool
  deriving DecidableEq

def pack (s : TwoState) : OneState := ⟨(s.first, s.second)⟩
def unpack (s : OneState) : TwoState := ⟨s.root.1, s.root.2⟩

def override (original : Bool) : Option Bool → Bool
  | none => original
  | some replacement => replacement

/-- The two public contributors feed an explicit AND-effect equation. -/
def pluralRun (s : TwoState) (i : Setting) : Observation :=
  let a := override s.first i.setA
  let b := override s.second i.setB
  ⟨a, b, a && b⟩

/-- The SAME mechanism can be factored through one pair-valued root state.
This is representational packing, not an independently productive unit. -/
def singleRun (s : OneState) (i : Setting) : Observation :=
  pluralRun (unpack s) i

/-- A rival with the same natural observations: its effect reads the old
background bits, ignoring PUBLIC surgical changes to a or b. -/
def idleRun (s : TwoState) (i : Setting) : Observation :=
  { pluralRun s i with effect := s.first && s.second }

/-- Hume's existing experimental `Changes`, once for each public input with
the other held on. This is a *test* of the supplied operation, not a theory
that intervention sensitivity alone constitutes metaphysical production. -/
def RespondsToEitherInput (run : TwoState → Setting → Observation) : Prop :=
  Changes (fun background forced =>
    (run ⟨background, true⟩ ⟨some forced, some true⟩).effect) ∧
  Changes (fun background forced =>
    (run ⟨true, background⟩ ⟨some true, some forced⟩).effect)

/-- At neutral settings the new effect mechanisms instantiate the OLD
`completedSingle` observations, without identifying latent state with bearer
or asserting the #974 Exercise record survives public interventions. -/
def NaturalAgreement : Prop :=
  ∀ s : TwoState,
    singleRun (pack s) natural = pluralRun s natural ∧
    pluralRun s natural = idleRun s natural ∧
    ((pluralRun s natural).a = true ↔
      completedSingle.occurs (s.first, s.second) .a) ∧
    ((pluralRun s natural).b = true ↔
      completedSingle.occurs (s.first, s.second) .b) ∧
    ((pluralRun s natural).effect = true ↔
      completedSingle.occurs (s.first, s.second) .t)

/-- Exhausting all input combinations requires at least four distinct
available states. In particular a single one-bit root cannot do it, though a
ONE-OBJECT root may have a four-state (pair-valued) internal capacity. -/
def CoversAllPairs {S : Type} (a b : S → Bool) : Prop :=
  ∀ x y : Bool, ∃ s : S, a s = x ∧ b s = y

def CapacityFork : Prop :=
  CoversAllPairs (fun s : Bool × Bool => s.1) (fun s => s.2) ∧
  ∀ a b : Bool → Bool, ¬ CoversAllPairs a b

/-- A real discrimination is achieved between the supplied AND mechanism
and the idle lookup; ONE versus TWO source *slots* remains equivalent through
every public surgery. Graph root parity is the pre-existing #974 theorem.
No one-source metaphysical unity or productive-explanation premise is added. -/
def Certificate : Prop :=
  (∀ s : TwoState, unpack (pack s) = s) ∧
  (∀ s : OneState, pack (unpack s) = s) ∧
  (∀ s i, singleRun (pack s) i = pluralRun s i) ∧
  NaturalAgreement ∧
  RespondsToEitherInput pluralRun ∧
  RespondsToEitherInput (fun s i => singleRun (pack s) i) ∧
  ¬ RespondsToEitherInput idleRun ∧
  (∃ s i, pluralRun s i ≠ idleRun s i) ∧
  CapacityFork ∧ RootParity

end TruthCore.Explanation.MechanismInterventionParity
