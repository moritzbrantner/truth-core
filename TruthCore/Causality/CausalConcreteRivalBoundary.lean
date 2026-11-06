module

public import TruthCore.Causality.CausalPowerConcreteness
public import TruthCore.Logic.ExcludedMiddle

/-!
# Productive causal rivals in the adopted esse sense

The old intended profile already assumes the contested commitment. This thinner
interface reuses its Ontic and esse vocabulary without assuming that commitment,
so positive and negative cases can both be tested. Cause means productive action,
not explanation, formal participation or membership. Power is a capacity, distinct
from its exercise at the selected world. No causal order, existence implication,
or generalization to reality is asserted by a field name. The finite dormant
capacity control has an actual manifestation at an accessible other world.
All category-to-esse and explanatory-to-productive bridges remain separate OPEN
propositions. A set-of-two anchor does not classify every impure event-set.
-/

@[expose] public section
namespace TruthCore.Causality.CausalConcreteRivalBoundary
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Ontology.ConcreteAbstract
open TruthCore.Causality.CausalPowerConcreteness

structure Frame where
  World : Type
  Being : Type
  Respect : Type
  ontic : Ontic World Being
  selected : World
  witnessWorld : World
  concrete : Being → Prop
  power : World → Being → Prop
  InAct : Being → Respect → Prop
  esse : Respect
  IsSet : Being → Prop
  IsForm : Being → Prop
  IsMathFact : Being → Prop
  Relevant : Being → Being → Prop

def Esse (f : Frame) := HasEsseInRe f.InAct f.esse
def Calibration (f : Frame) : Prop := ∀ x, f.concrete x ↔ Esse f x
def Anchored (f : Frame) : Prop := Nonempty (Anchors (esseClassification f.InAct f.esse))
def OwnerFails (f : Frame) : Prop :=
  ¬ OwnerCommitmentAt f.ontic f.concrete f.power f.selected

def CounterAt (f : Frame) (w : f.World) : Prop :=
  ∃ x, ¬ Esse f x ∧ (f.power w x ∨ ∃ y, f.ontic.Causes w x y)
def SelectedCounter (f : Frame) : Prop := CounterAt f f.selected
def OtherWorldCounter (f : Frame) : Prop := ∃ w, CounterAt f w
def SuppliedWorldCounter (f : Frame) : Prop := CounterAt f f.witnessWorld
def CounterWorldIsSelected (f : Frame) : Prop := f.witnessWorld = f.selected

def SetCause (f : Frame) : Prop :=
  ∃ x y, f.IsSet x ∧ f.ontic.Causes f.selected x y
def SetCausersNoEsse (f : Frame) : Prop :=
  ∀ x y, f.IsSet x → f.ontic.Causes f.selected x y → ¬ Esse f x
def AllSetsNoEsse (f : Frame) : Prop := ∀ x, f.IsSet x → ¬ Esse f x

def FormCause (f : Frame) : Prop :=
  ∃ x y, f.IsForm x ∧ f.ontic.Causes f.selected x y
def FormCausersNoEsse (f : Frame) : Prop :=
  ∀ x y, f.IsForm x → f.ontic.Causes f.selected x y → ¬ Esse f x

def MathRelevance (f : Frame) : Prop :=
  ∃ x y, f.IsMathFact x ∧ f.Relevant x y
def RelevanceIsProductive (f : Frame) : Prop :=
  ∀ x y, f.IsMathFact x → f.Relevant x y → f.ontic.Causes f.selected x y
def RelevantFactsNoEsse (f : Frame) : Prop :=
  ∀ x y, f.IsMathFact x → f.Relevant x y → ¬ Esse f x

def SetCounter (f : Frame) : Prop :=
  ∃ x y, f.IsSet x ∧ ¬ Esse f x ∧ f.ontic.Causes f.selected x y
def FormCounter (f : Frame) : Prop :=
  ∃ x y, f.IsForm x ∧ ¬ Esse f x ∧ f.ontic.Causes f.selected x y
def MathCounter (f : Frame) : Prop :=
  ∃ x y, f.IsMathFact x ∧ f.Relevant x y ∧ ¬ Esse f x ∧ f.ontic.Causes f.selected x y

def NamedCases (f : Frame) : Prop := SetCounter f ∨ FormCounter f ∨ MathCounter f
/-- OPEN existential-support coverage: if any selected countercase exists, some
named productive countercase exists, not necessarily with the same witness.
This does not classify every countertuple. The remainder requires no named
countercase anywhere, not merely one unclassified witness. -/
def NamedCoverage (f : Frame) : Prop := SelectedCounter f → NamedCases f
def OtherCounter (f : Frame) : Prop := SelectedCounter f ∧ ¬ NamedCases f
def NamedCoverageFails (f : Frame) : Prop := ¬ NamedCoverage f
def NamedCasesFail (f : Frame) : Prop := ¬ SetCounter f ∧ ¬ FormCounter f ∧ ¬ MathCounter f

def StructuralFork (f : Frame) : Prop :=
  OwnerCommitmentAt f.ontic f.concrete f.power f.selected ∨ SelectedCounter f
def CoverageFork (f : Frame) : Prop := NamedCoverage f ∨ OtherCounter f

/-! Finite controls use role labels, not a real-world classification proof. -/
inductive Role where
  | reasoner | anchor | producer | fact | effect
  deriving DecidableEq

def hasEsse : Role → Prop
  | .reasoner | .producer | .effect => True
  | .anchor | .fact => False

def base : Frame where
  World := Bool
  Being := Role
  Respect := Unit
  ontic := { frame := { access := fun _ _ => True }
             ExistsAt := fun _ _ => True
             Causes := fun _ x y => x = .producer ∧ y = .effect }
  selected := false
  witnessWorld := true
  concrete := hasEsse
  power := fun _ x => x = .producer
  InAct := fun x _ => hasEsse x
  esse := ()
  IsSet := fun x => x = .anchor ∨ x = .producer
  IsForm := fun x => x = .producer
  IsMathFact := fun x => x = .fact
  Relevant := fun x y => x = .fact ∧ y = .effect

def elsewhere : Frame := { base with
  ontic := { base.ontic with Causes := fun w x y =>
    (x = .producer ∧ y = .effect) ∨ (w = true ∧ x = .fact ∧ y = .effect) } }

def dormant : Frame := { elsewhere with
  power := fun w x => x = .producer ∨ (w = false ∧ x = .fact) }

def CompatibleControls : Prop :=
  Calibration base ∧ Anchored base ∧
  OwnerCommitmentAt base.ontic base.concrete base.power base.selected ∧
  SetCause base ∧ FormCause base ∧ MathRelevance base ∧
  ¬ SetCausersNoEsse base ∧ ¬ FormCausersNoEsse base ∧ ¬ RelevanceIsProductive base

def WorldControl : Prop :=
  Calibration elsewhere ∧ Anchored elsewhere ∧ OtherWorldCounter elsewhere ∧
  OwnerCommitmentAt elsewhere.ontic elsewhere.concrete elsewhere.power elsewhere.selected ∧
  ¬ SelectedCounter elsewhere

def OtherControl : Prop :=
  Calibration dormant ∧ Anchored dormant ∧ OtherCounter dormant ∧ OwnerFails dormant ∧
  CausersRequireConcreteAt dormant.ontic dormant.concrete dormant.selected ∧
  dormant.power false .fact ∧ dormant.ontic.frame.access false true ∧
  dormant.ontic.Causes true .fact .effect

def Controls : Prop := CompatibleControls ∧ WorldControl ∧ OtherControl

end TruthCore.Causality.CausalConcreteRivalBoundary
