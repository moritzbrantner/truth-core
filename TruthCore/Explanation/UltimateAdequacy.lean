import TruthCore.Causality.DerivativeJointPower
import TruthCore.Explanation.HistorySelection
import TruthCore.Epistemology.UltimateExplanation
import TruthCore.Explanation.TargetCopyExpansion
import TruthCore.Explanation.ConservativeReasonExpansion

/-! Shared exercise comparison for #735. All four configurations use Nat event
and bearer candidates, target2, Bool×Bool scenarios and the actual (true,true)
context. No predicate named adequate is supplied. Intrinsic contribution is not
intrinsic existence; the separate modal overlay tests that distinction. -/
namespace TruthCore.Explanation.UltimateAdequacy
open TruthCore.Causality.JointGroups TruthCore.Causality.DerivativeJointPower
open TruthCore.Logic.Regress
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.TemporalHistory

inductive Kind | single | plural | branch | chain deriving DecidableEq

def groups (k : Kind) : Groups Nat Nat where
  contributors := fun g => {e | match k with
    | .single => e = 0
    | .plural => e = 0 ∨ e = 1
    | .branch => e = 0 ∨ e = g + 2
    | .chain => e = g + 1 ∨ e = g + 2}
  enablers := fun _ => ∅
  effect := fun g => match k with
    | .single | .branch => g + 1
    | .plural => g + 2
    | .chain => g
  admitted := fun _ => True

def intrinsic (k : Kind) (e : Nat) : Prop := match k with
  | .single | .branch => e = 0
  | .plural => e = 0 ∨ e = 1
  | .chain => False

def exercise (k : Kind) : Exercise Nat Nat Nat (Bool × Bool) where
  groups := groups k
  bearer := id
  occurs := fun s e => match k with
    | .single | .chain => s.1 = true
    | .plural => if e = 0 then s.1 = true else if e = 1 then s.2 = true
      else s.1 = true ∧ s.2 = true
    | .branch => e = 0 ∨ s.1 = true
  allowed := fun _ => True
  actual := (true,true)
  exercised := fun _ => True

/-- Same context, nonempty actual population, exercise, scenario sufficiency
and local power. These clauses do not imply productive adequacy. -/
def Background (k : Kind) : Prop :=
  (exercise k).coherent ∧ (∀ g, (exercise k).jointlySufficient g) ∧
  (∀ e, (exercise k).occurs (exercise k).actual e) ∧
  LocalPower (groups k) (intrinsic k) ((exercise k).occurs (exercise k).actual) ∧
  PoweredGroups (groups k) ((exercise k).occurs (exercise k).actual) ∧
  AtContext (groups k) (fun _ => ()) (fun _ => ()) () () ∧
  (∀ y x, (exercise k).ontic.Causes () y x ↔ (groups k).graph.edge y x)

/-- Relabelling of the existing exact Option-Nat #634 actual nodes. -/
def encode (e : TruthCore.Causality.DerivativeJointPower.Node) : Nat :=
  e.val.elim 0 (fun n => n + 1)

def decode (n : Nat) : TruthCore.Causality.DerivativeJointPower.Node :=
  TruthCore.Causality.DerivativeJointPower.node (match n with | 0 => none | n+1 => some n)

/-- The same actual exercise is compatible with necessary or contingent bearer
existence. Modal indices are NOT exercise scenarios. Both overlays keep all
actual events and exactly their actual graph; false is the designated world.
The independent bit b makes ALL candidates necessary when true, and only the
intrinsic-contribution candidates necessary when false. These are semantic
controls, not an account of why any bearer exists. -/
def modal (k : Kind) (b : Bool) : Ontic Bool Nat where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun w e => w = false ∨ b = true ∨ intrinsic k e
  Causes := fun w y x =>
    (w = false ∨ b = true ∨ intrinsic k y) ∧
    (w = false ∨ b = true ∨ intrinsic k x) ∧ (groups k).graph.edge y x

def history (k : Kind) : History Bool Nat Unit where
  ontic := modal k false
  IsAt := fun w e _ => (modal k false).ExistsAt w e
  now := ()

/-- A necessary reason truth may be labelled as explaining the actual target
without necessitating it. Target-copy success is tested separately, never
advertised as an adequate repair. -/
def reasons (k : Kind) : TruthCore.Causality.BruteFoundationExplanations.ExplanationProfile Bool Nat Unit where
  reality := {
    ontic := modal k false
    concrete := fun _ => True
    grounds := fun w y x => (modal k false).Causes w y x }
  reasonPresent := fun _ _ => True
  explains := fun w _ e => e = 2 ∧ (modal k false).ExistsAt w e

/-- The new discriminator: supplying all active productive contributions is
neither necessary nor sufficient for graph leastness. The plural survivor has
TWO indispensable intrinsic contributors to target2, with joint Supply of all
events and no least node. The branch is the exact transported #634 graph and
has a least node but no target Supply. The chain has neither. -/
def Structural : Prop :=
  (∀ k, Background k) ∧
  (∀ e, Supply (groups .single) (intrinsic .single) e) ∧
  TruthCore.Causality.JointGroups.least (groups .single).graph 0 ∧
  (∀ e, Supply (groups .plural) (intrinsic .plural) e) ∧
  (exercise .plural).indispensable 0 0 ∧ (exercise .plural).indispensable 0 1 ∧
  (groups .plural).graph.Source 0 ∧ (groups .plural).graph.Source 1 ∧
  ¬ (∃ s, TruthCore.Causality.JointGroups.least (groups .plural).graph s) ∧
  TruthCore.Causality.JointGroups.least (groups .branch).graph 0 ∧
  ¬ Supply (groups .branch) (intrinsic .branch) 2 ∧
  (exercise .branch).indispensable 1 3 ∧
  (∀ e, ¬ Supply (groups .chain) (intrinsic .chain) e) ∧
  ¬ (∃ s, TruthCore.Causality.JointGroups.least (groups .chain).graph s) ∧
  (∀ e, decode (encode e) = e) ∧ (∀ n, encode (decode n) = n) ∧
  (∀ y x, TruthCore.Causality.DerivativeJointPower.K.edge y x ↔
    (groups .branch).graph.edge (encode y) (encode x)) ∧
  (∀ e, Supply TruthCore.Causality.DerivativeJointPower.H
    TruthCore.Causality.DerivativeJointPower.intrinsic e ↔
    Supply (groups .branch) (intrinsic .branch) (encode e))

/-- Modal/entailing tests hold for EACH of the same four actual interpretations.
Necessity of contribution-bearers and entailing tokens do not select one source
structure. C/N/S incompatibility is consumed, not identified with adequacy. -/
def ModalControls : Prop :=
  (∀ k b e, (modal k b).ExistsAt false e) ∧
  (∀ k b y x, (modal k b).Causes false y x ↔ (groups k).graph.edge y x) ∧
  (∀ k e, NecessaryAt (modal k true) false e) ∧
  (∀ k, ContingentAt (modal k false) false 2) ∧
  (∀ k, ¬ ∃ p, TruthCore.Explanation.HistorySelection.EvidenceOnly
    (fun (_ : Bool) (_ : Unit) => True) (fun _ => True) p ∧
    TruthCore.Explanation.HistorySelection.Selects (history k) p false) ∧
  (∀ k, TruthCore.Causality.BruteFoundationExplanations.NecessaryReasonAt (reasons k) false () ∧
    ¬ TruthCore.Causality.BruteFoundationExplanations.NecessitatesExistenceAt (reasons k) false () 2) ∧
  (∀ k b, TruthCore.Explanation.TargetCopyExpansion.EntailingCoverage
    (TruthCore.Explanation.TargetCopyExpansion.copied
      { ontic := modal k b, concrete := fun _ => True,
        grounds := fun w y x => (modal k b).Causes w y x }))

/-- Formal constraints and comparison, with no independently defended actual
adequacy, existence-as-such or normative entitlement premise. -/
def Certificate : Prop := Structural ∧ ModalControls
end TruthCore.Explanation.UltimateAdequacy

namespace TruthCore.Explanation.UltimateAdequacy
/-- The existing epistemic projection is consumed unchanged, while weak-token
expansion is instantiated at EACH new exact modal extension. These preserve
actual signatures without giving normative entitlement or complete explanation. -/
def EpistemicComparison : Prop :=
  TruthCore.Epistemology.UltimateExplanation.Integration ∧
  (∀ k b, ∃ m : TruthCore.Explanation.ExistencePSR.Model Bool Nat,
    m.ontic = modal k b ∧
    TruthCore.Explanation.ConservativeReasonExpansion.CoverageAndGuardedStability m)
end TruthCore.Explanation.UltimateAdequacy
