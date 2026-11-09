module
public import TruthCore.Logic.ObjectiveTruthDefinitionFork

/-! Analyst candidates for moral objectivity, attribution deferred.
Profiles hold content and non-attitude circumstances fixed by intended use; admissibility
is explicit input, not all logically describable changes. Coverage of relevant changes
and fidelity of grounding edges remain OPEN. Grounding edges mean immediate constitutive
support, not temporal causation or evidence. E.g. an approval-constituted norm may have
an attitude ancestor even when redundant support keeps its truth stable. No asymmetry,
transitivity of immediate support, or real-world applicability is assumed. Ancestry
below is finite nonempty support paths, not just immediate grounds. -/
@[expose] public section
namespace TruthCore.Logic.MoralAttitudeProfiles

structure Profile where
  truth : ObjectiveTruthDefinitionFork.Frame
  admissible : truth.AttitudeProfile → Prop
  Node : Type
  attitude : Node → Prop
  ground : Node → Node → Prop
  factNode : truth.Sentence → Node
  moralFact : truth.Sentence → Prop
  existsFact : truth.Sentence → Prop

inductive Ancestor {N : Type} (edge : N → N → Prop) : N → N → Prop where
  | direct {a b} : edge a b → Ancestor edge a b
  | step {a b c} : edge a b → Ancestor edge b c → Ancestor edge a c

/-- Truth-status invariance, including stably false contents. -/
def Invariant (p : Profile) (s : p.truth.Sentence) : Prop :=
  ∀ a, p.admissible a → (p.truth.holds a s ↔ p.truth.holds p.truth.actual s)

def NoDirectAttitudeGround (p : Profile) (s : p.truth.Sentence) : Prop :=
  ∀ n, p.ground n (p.factNode s) → ¬ p.attitude n

def NoAttitudeAncestor (p : Profile) (s : p.truth.Sentence) : Prop :=
  ∀ n, Ancestor p.ground n (p.factNode s) → ¬ p.attitude n

def InterventionObject (p : Profile) (s : p.truth.Sentence) : Prop :=
  p.moralFact s ∧ p.existsFact s ∧ p.truth.holds p.truth.actual s ∧ Invariant p s

def GroundingObject (p : Profile) (s : p.truth.Sentence) : Prop :=
  p.moralFact s ∧ p.existsFact s ∧ p.truth.holds p.truth.actual s ∧ NoAttitudeAncestor p s

/-- An explicit bridge, not a consequence of grounding's name. -/
def GroundingStability (p : Profile) : Prop :=
  ∀ s, NoAttitudeAncestor p s → Invariant p s

def GroundingImpliesIntervention (p : Profile) : Prop :=
  ∀ s, GroundingObject p s → InterventionObject p s

def AncestralImpliesDirect : Prop :=
  ∀ p s, NoAttitudeAncestor p s → NoDirectAttitudeGround p s

/-- Calibration to either actual-truth-bearing candidate supplies exactly the
truth component needed by the existing external POE step. No assertion supplies it. -/
def CalibrationTruth : Prop :=
  ∀ p : Profile,
    ((∀ s, p.truth.objective s ↔ InterventionObject p s) ∨
     (∀ s, p.truth.objective s ↔ GroundingObject p s)) →
    ObjectiveTruthDefinitionFork.HasTruthComponent p.truth

/-- Same content/profile carrier across separators. One immediate attitude ground
can coexist with stable truth; no ground can coexist with variable truth. -/
def sample (stable grounded restricted actualTrue : Bool) : Profile where
  truth := {
    Sentence := Unit
    AttitudeProfile := Bool
    actual := false
    holds := fun a _ => actualTrue = true ∧ (stable = true ∨ a = false)
    objective := fun _ => True }
  admissible := fun a => restricted = false ∨ a = false
  Node := Unit
  attitude := fun _ => True
  ground := fun _ _ => grounded = true
  factNode := fun _ => ()
  moralFact := fun _ => True
  existsFact := fun _ => True

/-- Broad admissibility on the two separators; restricted interventions separately
show that local invariance need not cover all profiles. -/
def Controls : Prop :=
  (InterventionObject (sample true true false true) () ∧
    ¬ GroundingObject (sample true true false true) ()) ∧
  (GroundingObject (sample false false false true) () ∧
    ¬ InterventionObject (sample false false false true) ()) ∧
  (InterventionObject (sample true false false true) () ∧
    GroundingObject (sample true false false true) ()) ∧
  (Invariant (sample true false false false) () ∧
    NoAttitudeAncestor (sample true false false false) () ∧
    ¬ InterventionObject (sample true false false false) ()) ∧
  (Invariant (sample false true true true) () ∧
    ¬ ObjectiveTruthDefinitionFork.Stable (sample false true true true).truth ())
end TruthCore.Logic.MoralAttitudeProfiles
