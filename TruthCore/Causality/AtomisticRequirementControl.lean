module

public import TruthCore.Causality.AtomisticUniversalCausePriority
public import TruthCore.Logic.ExcludedMiddle
public import TruthCore.Causality.CompleteCauseContributorCover
public import TruthCore.Mereology.SupplementationFusion
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.DeriveFintype

/-! A calibrated STATIC SUBSET control, analyst interpretation; attribution deferred.
The carrier contains four atoms and just two composites, not arbitrary fusions.
Admitted Boolean assignments interpret existential requirement: x requires y iff
x's presence entails y's presence throughout this explicitly restricted space.
Priority is asymmetric requirement (VI p124 fn174). Causal edges stipulate complete
production at the all-present assignment, not a definition of real causation.
Across scenarios activity, participant inheritance and family formation are NOT
asserted. CAI/plural identity, fixed-sum identity and unrestricted fusion remain
open. This control does not refute the whole original argument bundle. -/

@[expose] public section
namespace TruthCore.Causality.AtomisticRequirementControl
open TruthCore.Logic.Regress (Graph)
open TruthCore.Mereology.UniversalFusionBoundary
open TruthCore.Mereology.SupplementationFusion (WeakSupplementation)
open TruthCore.Causality.AtomisticCausalSource
open TruthCore.Causality.AtomisticUniversalCausePriority
open TruthCore.Causality.CompleteCauseContributorCover

inductive Object where
  | r | s | p | q | m | b
  deriving DecidableEq

instance : Fintype Object := ⟨{.r, .s, .p, .q, .m, .b}, by
  intro x; cases x <;> simp⟩

/-- Four non-null singleton atoms; m={p,q}, b={p,s}. -/
def contains : Object → Fin 4 → Bool
  | .r, a => a == 0
  | .s, a => a == 1
  | .p, a => a == 2
  | .q, a => a == 3
  | .m, a => a == 2 || a == 3
  | .b, a => a == 2 || a == 1

def part (x y : Object) : Prop := ∀ a, contains x a = true → contains y a = true
instance (x y : Object) : Decidable (part x y) := inferInstanceAs (Decidable (∀ a, contains x a = true → contains y a = true))
instance : PartialOrder Object where
  le := part
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
instance (x y : Object) : Decidable (x ≤ y) := inferInstanceAs (Decidable (part x y))
instance (x y : Object) : Decidable (x < y) := inferInstanceAs (Decidable (x ≤ y ∧ ¬ y ≤ x))

abbrev Scenario := Bool × Bool × Bool × Bool

def existsAt (v : Scenario) : Object → Prop
  | .r => v.1 = true
  | .s => v.2.1 = true
  | .p => v.2.2.1 = true
  | .q => v.2.2.2 = true
  | .m => v.2.2.1 = true ∧ v.2.2.2 = true
  | .b => v.2.2.1 = true ∧ v.2.1 = true
instance (v : Scenario) (x : Object) : Decidable (existsAt v x) := by cases x <;> unfold existsAt <;> infer_instance

/-- Production requirements p⇒r, s⇒r, q⇒s; nothing forces r⇒s. -/
def admitted (v : Scenario) : Prop :=
  (existsAt v .p → existsAt v .r) ∧
  (existsAt v .s → existsAt v .r) ∧
  (existsAt v .q → existsAt v .s)
instance (v : Scenario) : Decidable (admitted v) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def Requires (x y : Object) : Prop := ∀ v : Scenario, admitted v → existsAt v x → existsAt v y
instance (x y : Object) : Decidable (Requires x y) := inferInstanceAs (Decidable (∀ v : Scenario, admitted v → existsAt v x → existsAt v y))

def prior (x y : Object) : Prop := Requires y x ∧ ¬ Requires x y
instance (x y : Object) : Decidable (prior x y) := inferInstanceAs (Decidable (_ ∧ _))

def graph : Graph Object where
  edge c e := (c = .r ∧ (e = .p ∨ e = .m ∨ e = .b)) ∨ (c = .s ∧ e = .q)
instance (c e : Object) : Decidable (graph.edge c e) := inferInstanceAs (Decidable ((_ ∧ (_ ∨ _ ∨ _)) ∨ (_ ∧ _)))

/-- The supplied productive participants are specified effect by effect, with
no cross-effect inheritance. Here each family contains its whole producer.
Necessary background objects are not thereby productive participants. -/
def participants : Object → Set Object
  | .p | .m | .b => {.r}
  | .q => {.s}
  | _ => ∅

instance (c e : Object) : Decidable (c ∈ participants e) := by
  cases e <;> unfold participants <;> infer_instance

def rank : Object → Nat
  | .m | .b => 1
  | _ => 0

/-- One joint certificate: retained static policies plus full atomic
composition and full fusion of caused simples, nonvacuous P6, calibrated
requirement priority, and the exact failed inheritance instance.
The inline negative formula tests FULL effect universality, not just source
existence, an outgoing edge, or universal priority of the source itself. -/
def Certificate : Prop :=
  TruthCore.Logic.ExcludedMiddle ∧
  ObjectPopulation Object ∧ AtomicParts Object ∧ ProperPartWF Object ∧
  CausalActivity graph ∧ ConditionalCausedSimpleCover graph ∧
  CauseEffectNonoverlap graph ∧ CausedCompositeHasCausedProperPart graph ∧
  UniqueCausePerEffect graph ∧ CausePriorToEffectParts graph prior ∧
  ProperPartsPrior prior ∧ TransitiveExistentialPriority prior ∧
  WeakSupplementation Object ∧ ProducerParticipates graph participants ∧
  CompleteCauseCoversContributors graph participants ∧
  (∀ x : Object, Fusion {a | IsMin a ∧ a ≤ x} x) ∧
  CausedSimples graph = {.p, .q} ∧ Fusion (CausedSimples graph) .m ∧
  (∃ c, graph.edge c .m) ∧ Composite Object.m ∧
  (∃ c, graph.edge c .b) ∧ Composite Object.b ∧
  admitted (true, true, true, true) ∧
  (∀ x, existsAt (true, true, true, true) x) ∧
  (∀ x, ¬ prior x x) ∧
  UniversalCausePriority graph prior ∧
  ¬ (∃ N M, graph.Source N ∧ graph.edge N M ∧
    ∀ x, (∃ c, graph.edge c x) → x ≠ M → prior M x ∨ x ≤ M) ∧
  graph.edge .s .q ∧ Object.q ≤ Object.m ∧ graph.edge .r .m ∧
  ¬ Object.s ≤ Object.r

end TruthCore.Causality.AtomisticRequirementControl
